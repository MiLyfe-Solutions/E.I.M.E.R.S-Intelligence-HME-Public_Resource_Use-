import V185TrunkScan20Chunk153

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_937520 : List Nat := [2, 1, 1, 1, 2, 3, 1, 3, 6]
def baseStart_937520 : Nat := 118140960795 + 937520 * 2 ^ 59
def prefixEnd_937520 : Nat := 4983230072969 + 3 ^ 40 * 937520 * 2
def baseEnd_937520 : Nat := 427909673958468606567493

theorem tailTrace_937520 : CollatzResearch.WordTrace tailWord_937520 prefixEnd_937520 427909673958468606567493 := by
  unfold tailWord_937520
  simp only [CollatzResearch.WordTrace]
  refine ⟨17097081781766315256825007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22796109042355087009100009 17097081781766315256825007)
  ·
    refine ⟨25645622672649472885237511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17097081781766315256825007 25645622672649472885237511)
    ·
      refine ⟨38468434008974209327856267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25645622672649472885237511 38468434008974209327856267)
      ·
        refine ⟨57702651013461313991784401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38468434008974209327856267 57702651013461313991784401)
        ·
          refine ⟨43276988260095985493838301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57702651013461313991784401 43276988260095985493838301)
          ·
            refine ⟨16228870597535994560189363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43276988260095985493838301 16228870597535994560189363)
            ·
              refine ⟨24343305896303991840284045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16228870597535994560189363 24343305896303991840284045)
              ·
                refine ⟨9128739711113996940106517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24343305896303991840284045 9128739711113996940106517)
                ·
                  refine ⟨427909673958468606567493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9128739711113996940106517 427909673958468606567493)
                  ·
                    rfl

theorem cell20_937520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 3, 6].length) (baseStart_937520 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_937520 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_937520 prefixEnd_937520 := by exact prefixLift 937520
  have htrace : WordTrace (prefixWord ++ tailWord_937520) baseStart_937520 baseEnd_937520 := by
    simpa [prefixWord, tailWord_937520, baseEnd_937520] using wordTrace_append hprefix tailTrace_937520
  have hstable : (prefixWord ++ tailWord_937520).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937520).length < 2 ^ (prefixWord ++ tailWord_937520).sum := by decide
  have hdescent : baseEnd_937520 < baseStart_937520 := by decide
  rcases family_descends (prefixWord ++ tailWord_937520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937596 : List Nat := [2, 2, 2, 1, 1, 2, 1, 1, 8]
def baseStart_937596 : Nat := 118140960795 + 937596 * 2 ^ 59
def prefixEnd_937596 : Nat := 4983230072969 + 3 ^ 40 * 937596 * 2
def baseEnd_937596 : Nat := 427944362429350120033849

theorem tailTrace_937596 : CollatzResearch.WordTrace tailWord_937596 prefixEnd_937596 427944362429350120033849 := by
  unfold tailWord_937596
  simp only [CollatzResearch.WordTrace]
  refine ⟨17098467755628647746708321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22797957007504863662277761 17098467755628647746708321)
  ·
    refine ⟨12823850816721485810031241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17098467755628647746708321 12823850816721485810031241)
    ·
      refine ⟨9617888112541114357523431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12823850816721485810031241 9617888112541114357523431)
      ·
        refine ⟨14426832168811671536285147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9617888112541114357523431 14426832168811671536285147)
        ·
          refine ⟨21640248253217507304427721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14426832168811671536285147 21640248253217507304427721)
          ·
            refine ⟨16230186189913130478320791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21640248253217507304427721 16230186189913130478320791)
            ·
              refine ⟨24345279284869695717481187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16230186189913130478320791 24345279284869695717481187)
              ·
                refine ⟨36517918927304543576221781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24345279284869695717481187 36517918927304543576221781)
                ·
                  refine ⟨427944362429350120033849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36517918927304543576221781 427944362429350120033849)
                  ·
                    rfl

theorem cell20_937596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 8].length) (baseStart_937596 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_937596 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_937596 prefixEnd_937596 := by exact prefixLift 937596
  have htrace : WordTrace (prefixWord ++ tailWord_937596) baseStart_937596 baseEnd_937596 := by
    simpa [prefixWord, tailWord_937596, baseEnd_937596] using wordTrace_append hprefix tailTrace_937596
  have hstable : (prefixWord ++ tailWord_937596).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937596).length < 2 ^ (prefixWord ++ tailWord_937596).sum := by decide
  have hdescent : baseEnd_937596 < baseStart_937596 := by decide
  rcases family_descends (prefixWord ++ tailWord_937596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937623 : List Nat := [1, 1, 3, 3, 2, 3, 3, 1, 3]
def baseStart_937623 : Nat := 118140960795 + 937623 * 2 ^ 59
def prefixEnd_937623 : Nat := 4983230072969 + 3 ^ 40 * 937623 * 2
def baseEnd_937623 : Nat := 427956685965058026133739

theorem tailTrace_937623 : CollatzResearch.WordTrace tailWord_937623 prefixEnd_937623 427956685965058026133739 := by
  unfold tailWord_937623
  simp only [CollatzResearch.WordTrace]
  refine ⟨34197920282159479104649523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22798613521439652736433015 34197920282159479104649523)
  ·
    refine ⟨51296880423239218656974285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34197920282159479104649523 51296880423239218656974285)
    ·
      refine ⟨19236330158714706996365357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51296880423239218656974285 19236330158714706996365357)
      ·
        refine ⟨7213623809518015123637009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19236330158714706996365357 7213623809518015123637009)
        ·
          refine ⟨5410217857138511342727757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7213623809518015123637009 5410217857138511342727757)
          ·
            refine ⟨2028831696426941753522909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5410217857138511342727757 2028831696426941753522909)
            ·
              refine ⟨760811886160103157571091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2028831696426941753522909 760811886160103157571091)
              ·
                refine ⟨1141217829240154736356637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 760811886160103157571091 1141217829240154736356637)
                ·
                  refine ⟨427956685965058026133739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1141217829240154736356637 427956685965058026133739)
                  ·
                    rfl

theorem cell20_937623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 3, 1, 3].length) (baseStart_937623 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_937623 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_937623 prefixEnd_937623 := by exact prefixLift 937623
  have htrace : WordTrace (prefixWord ++ tailWord_937623) baseStart_937623 baseEnd_937623 := by
    simpa [prefixWord, tailWord_937623, baseEnd_937623] using wordTrace_append hprefix tailTrace_937623
  have hstable : (prefixWord ++ tailWord_937623).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937623).length < 2 ^ (prefixWord ++ tailWord_937623).sum := by decide
  have hdescent : baseEnd_937623 < baseStart_937623 := by decide
  rcases family_descends (prefixWord ++ tailWord_937623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937630 : List Nat := [4, 3, 1, 1, 1, 2, 2, 2, 4]
def baseStart_937630 : Nat := 118140960795 + 937630 * 2 ^ 59
def prefixEnd_937630 : Nat := 4983230072969 + 3 ^ 40 * 937630 * 2
def baseEnd_937630 : Nat := 427959880955797112900377

theorem tailTrace_937630 : CollatzResearch.WordTrace tailWord_937630 prefixEnd_937630 427959880955797112900377 := by
  unfold tailWord_937630
  simp only [CollatzResearch.WordTrace]
  refine ⟨4274771949141764912519293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22798783728756079533436229 4274771949141764912519293)
  ·
    refine ⟨1603039480928161842194735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4274771949141764912519293 1603039480928161842194735)
    ·
      refine ⟨2404559221392242763292103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1603039480928161842194735 2404559221392242763292103)
      ·
        refine ⟨3606838832088364144938155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2404559221392242763292103 3606838832088364144938155)
        ·
          refine ⟨5410258248132546217407233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3606838832088364144938155 5410258248132546217407233)
          ·
            refine ⟨4057693686099409663055425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5410258248132546217407233 4057693686099409663055425)
            ·
              refine ⟨3043270264574557247291569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4057693686099409663055425 3043270264574557247291569)
              ·
                refine ⟨2282452698430917935468677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3043270264574557247291569 2282452698430917935468677)
                ·
                  refine ⟨427959880955797112900377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2282452698430917935468677 427959880955797112900377)
                  ·
                    rfl

theorem cell20_937630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_937630 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_937630 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_937630 prefixEnd_937630 := by exact prefixLift 937630
  have htrace : WordTrace (prefixWord ++ tailWord_937630) baseStart_937630 baseEnd_937630 := by
    simpa [prefixWord, tailWord_937630, baseEnd_937630] using wordTrace_append hprefix tailTrace_937630
  have hstable : (prefixWord ++ tailWord_937630).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937630).length < 2 ^ (prefixWord ++ tailWord_937630).sum := by decide
  have hdescent : baseEnd_937630 < baseStart_937630 := by decide
  rcases family_descends (prefixWord ++ tailWord_937630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937654 : List Nat := [5, 1, 3, 1, 1, 3, 6]
def baseStart_937654 : Nat := 118140960795 + 937654 * 2 ^ 59
def prefixEnd_937654 : Nat := 4983230072969 + 3 ^ 40 * 937654 * 2
def baseEnd_937654 : Nat := 47552315023306632900031

theorem tailTrace_937654 : CollatzResearch.WordTrace tailWord_937654 prefixEnd_937654 47552315023306632900031 := by
  unfold tailWord_937654
  simp only [CollatzResearch.WordTrace]
  refine ⟨2137440684065448212439251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22799367296698114266018677 2137440684065448212439251)
  ·
    refine ⟨3206161026098172318658877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2137440684065448212439251 3206161026098172318658877)
    ·
      refine ⟨1202310384786814619497079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3206161026098172318658877 1202310384786814619497079)
      ·
        refine ⟨1803465577180221929245619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1202310384786814619497079 1803465577180221929245619)
        ·
          refine ⟨2705198365770332893868429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1803465577180221929245619 2705198365770332893868429)
          ·
            refine ⟨1014449387163874835200661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2705198365770332893868429 1014449387163874835200661)
            ·
              refine ⟨47552315023306632900031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1014449387163874835200661 47552315023306632900031)
              ·
                rfl

theorem cell20_937654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 6].length) (baseStart_937654 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_937654 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_937654 prefixEnd_937654 := by exact prefixLift 937654
  have htrace : WordTrace (prefixWord ++ tailWord_937654) baseStart_937654 baseEnd_937654 := by
    simpa [prefixWord, tailWord_937654, baseEnd_937654] using wordTrace_append hprefix tailTrace_937654
  have hstable : (prefixWord ++ tailWord_937654).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937654).length < 2 ^ (prefixWord ++ tailWord_937654).sum := by decide
  have hdescent : baseEnd_937654 < baseStart_937654 := by decide
  rcases family_descends (prefixWord ++ tailWord_937654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937658 : List Nat := [3, 1, 1, 1, 2, 6, 6]
def baseStart_937658 : Nat := 118140960795 + 937658 * 2 ^ 59
def prefixEnd_937658 : Nat := 4983230072969 + 3 ^ 40 * 937658 * 2
def baseEnd_937658 : Nat := 47552517879861495551881

theorem tailTrace_937658 : CollatzResearch.WordTrace tailWord_937658 prefixEnd_937658 47552517879861495551881 := by
  unfold tailWord_937658
  simp only [CollatzResearch.WordTrace]
  refine ⟨8549799209258170020543407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22799464558021786721449085 8549799209258170020543407)
  ·
    refine ⟨12824698813887255030815111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8549799209258170020543407 12824698813887255030815111)
    ·
      refine ⟨19237048220830882546222667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12824698813887255030815111 19237048220830882546222667)
      ·
        refine ⟨28855572331246323819334001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19237048220830882546222667 28855572331246323819334001)
        ·
          refine ⟨21641679248434742864500501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28855572331246323819334001 21641679248434742864500501)
          ·
            refine ⟨1014453714770378571773461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 21641679248434742864500501 1014453714770378571773461)
            ·
              refine ⟨47552517879861495551881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1014453714770378571773461 47552517879861495551881)
              ·
                rfl

theorem cell20_937658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 6].length) (baseStart_937658 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_937658 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_937658 prefixEnd_937658 := by exact prefixLift 937658
  have htrace : WordTrace (prefixWord ++ tailWord_937658) baseStart_937658 baseEnd_937658 := by
    simpa [prefixWord, tailWord_937658, baseEnd_937658] using wordTrace_append hprefix tailTrace_937658
  have hstable : (prefixWord ++ tailWord_937658).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937658).length < 2 ^ (prefixWord ++ tailWord_937658).sum := by decide
  have hdescent : baseEnd_937658 < baseStart_937658 := by decide
  rcases family_descends (prefixWord ++ tailWord_937658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937716 : List Nat := [2, 6, 1, 1, 1, 1, 1, 4, 3]
def baseStart_937716 : Nat := 118140960795 + 937716 * 2 ^ 59
def prefixEnd_937716 : Nat := 4983230072969 + 3 ^ 40 * 937716 * 2
def baseEnd_937716 : Nat := 427999133699163036033359

theorem tailTrace_937716 : CollatzResearch.WordTrace tailWord_937716 prefixEnd_937716 427999133699163036033359 := by
  unfold tailWord_937716
  simp only [CollatzResearch.WordTrace]
  refine ⟨17100656135411277993892501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22800874847215037325190001 17100656135411277993892501)
  ·
    refine ⟨801593256347403655963711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 17100656135411277993892501 801593256347403655963711)
    ·
      refine ⟨1202389884521105483945567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 801593256347403655963711 1202389884521105483945567)
      ·
        refine ⟨1803584826781658225918351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1202389884521105483945567 1803584826781658225918351)
        ·
          refine ⟨2705377240172487338877527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1803584826781658225918351 2705377240172487338877527)
          ·
            refine ⟨4058065860258731008316291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2705377240172487338877527 4058065860258731008316291)
            ·
              refine ⟨6087098790388096512474437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4058065860258731008316291 6087098790388096512474437)
              ·
                refine ⟨1141331023197768096088957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6087098790388096512474437 1141331023197768096088957)
                ·
                  refine ⟨427999133699163036033359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1141331023197768096088957 427999133699163036033359)
                  ·
                    rfl

theorem cell20_937716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_937716 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_937716 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_937716 prefixEnd_937716 := by exact prefixLift 937716
  have htrace : WordTrace (prefixWord ++ tailWord_937716) baseStart_937716 baseEnd_937716 := by
    simpa [prefixWord, tailWord_937716, baseEnd_937716] using wordTrace_append hprefix tailTrace_937716
  have hstable : (prefixWord ++ tailWord_937716).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937716).length < 2 ^ (prefixWord ++ tailWord_937716).sum := by decide
  have hdescent : baseEnd_937716 < baseStart_937716 := by decide
  rcases family_descends (prefixWord ++ tailWord_937716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937751 : List Nat := [1, 1, 3, 4, 2, 2, 3, 4]
def baseStart_937751 : Nat := 118140960795 + 937751 * 2 ^ 59
def prefixEnd_937751 : Nat := 4983230072969 + 3 ^ 40 * 937751 * 2
def baseEnd_937751 : Nat := 142671702884286156622183

theorem tailTrace_937751 : CollatzResearch.WordTrace tailWord_937751 prefixEnd_937751 142671702884286156622183 := by
  unfold tailWord_937751
  simp only [CollatzResearch.WordTrace]
  refine ⟨34202588825695756965309107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22801725883797171310206071 34202588825695756965309107)
  ·
    refine ⟨51303883238543635447963661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34202588825695756965309107 51303883238543635447963661)
    ·
      refine ⟨19238956214453863292986373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51303883238543635447963661 19238956214453863292986373)
      ·
        refine ⟨3607304290210099367434945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19238956214453863292986373 3607304290210099367434945)
        ·
          refine ⟨2705478217657574525576209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3607304290210099367434945 2705478217657574525576209)
          ·
            refine ⟨2029108663243180894182157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2705478217657574525576209 2029108663243180894182157)
            ·
              refine ⟨760915748716192835318309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2029108663243180894182157 760915748716192835318309)
              ·
                refine ⟨142671702884286156622183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 760915748716192835318309 142671702884286156622183)
                ·
                  rfl

theorem cell20_937751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 3, 4].length) (baseStart_937751 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_937751 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_937751 prefixEnd_937751 := by exact prefixLift 937751
  have htrace : WordTrace (prefixWord ++ tailWord_937751) baseStart_937751 baseEnd_937751 := by
    simpa [prefixWord, tailWord_937751, baseEnd_937751] using wordTrace_append hprefix tailTrace_937751
  have hstable : (prefixWord ++ tailWord_937751).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937751).length < 2 ^ (prefixWord ++ tailWord_937751).sum := by decide
  have hdescent : baseEnd_937751 < baseStart_937751 := by decide
  rcases family_descends (prefixWord ++ tailWord_937751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937782 : List Nat := [5, 1, 2, 2, 1, 1, 1, 3, 4]
def baseStart_937782 : Nat := 118140960795 + 937782 * 2 ^ 59
def prefixEnd_937782 : Nat := 4983230072969 + 3 ^ 40 * 937782 * 2
def baseEnd_937782 : Nat := 428029257897560139833089

theorem tailTrace_937782 : CollatzResearch.WordTrace tailWord_937782 prefixEnd_937782 428029257897560139833089 := by
  unfold tailWord_937782
  simp only [CollatzResearch.WordTrace]
  refine ⟨2137732468036465578730475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22802479659055632839791733 2137732468036465578730475)
  ·
    refine ⟨3206598702054698368095713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2137732468036465578730475 3206598702054698368095713)
    ·
      refine ⟨2404949026541023776071785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3206598702054698368095713 2404949026541023776071785)
      ·
        refine ⟨1803711769905767832053839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2404949026541023776071785 1803711769905767832053839)
        ·
          refine ⟨2705567654858651748080759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1803711769905767832053839 2705567654858651748080759)
          ·
            refine ⟨4058351482287977622121139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2705567654858651748080759 4058351482287977622121139)
            ·
              refine ⟨6087527223431966433181709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4058351482287977622121139 6087527223431966433181709)
              ·
                refine ⟨2282822708786987412443141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6087527223431966433181709 2282822708786987412443141)
                ·
                  refine ⟨428029257897560139833089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2282822708786987412443141 428029257897560139833089)
                  ·
                    rfl

theorem cell20_937782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_937782 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_937782 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_937782 prefixEnd_937782 := by exact prefixLift 937782
  have htrace : WordTrace (prefixWord ++ tailWord_937782) baseStart_937782 baseEnd_937782 := by
    simpa [prefixWord, tailWord_937782, baseEnd_937782] using wordTrace_append hprefix tailTrace_937782
  have hstable : (prefixWord ++ tailWord_937782).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937782).length < 2 ^ (prefixWord ++ tailWord_937782).sum := by decide
  have hdescent : baseEnd_937782 < baseStart_937782 := by decide
  rcases family_descends (prefixWord ++ tailWord_937782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937810 : List Nat := [3, 2, 2, 1, 1, 4, 1, 6]
def baseStart_937810 : Nat := 118140960795 + 937810 * 2 ^ 59
def prefixEnd_937810 : Nat := 4983230072969 + 3 ^ 40 * 937810 * 2
def baseEnd_937810 : Nat := 142680679286838828966547

theorem tailTrace_937810 : CollatzResearch.WordTrace tailWord_937810 prefixEnd_937810 142680679286838828966547 := by
  unfold tailWord_937810
  simp only [CollatzResearch.WordTrace]
  refine ⟨8551185183120502510426721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22803160488321340027804589 8551185183120502510426721)
  ·
    refine ⟨6413388887340376882820041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8551185183120502510426721 6413388887340376882820041)
    ·
      refine ⟨4810041665505282662115031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6413388887340376882820041 4810041665505282662115031)
      ·
        refine ⟨7215062498257923993172547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4810041665505282662115031 7215062498257923993172547)
        ·
          refine ⟨10822593747386885989758821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7215062498257923993172547 10822593747386885989758821)
          ·
            refine ⟨2029236327635041123079779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10822593747386885989758821 2029236327635041123079779)
            ·
              refine ⟨3043854491452561684619669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2029236327635041123079779 3043854491452561684619669)
              ·
                refine ⟨142680679286838828966547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3043854491452561684619669 142680679286838828966547)
                ·
                  rfl

theorem cell20_937810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 6].length) (baseStart_937810 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_937810 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_937810 prefixEnd_937810 := by exact prefixLift 937810
  have htrace : WordTrace (prefixWord ++ tailWord_937810) baseStart_937810 baseEnd_937810 := by
    simpa [prefixWord, tailWord_937810, baseEnd_937810] using wordTrace_append hprefix tailTrace_937810
  have hstable : (prefixWord ++ tailWord_937810).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937810).length < 2 ^ (prefixWord ++ tailWord_937810).sum := by decide
  have hdescent : baseEnd_937810 < baseStart_937810 := by decide
  rcases family_descends (prefixWord ++ tailWord_937810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937827 : List Nat := [1, 1, 1, 5, 5, 1, 6]
def baseStart_937827 : Nat := 118140960795 + 937827 * 2 ^ 59
def prefixEnd_937827 : Nat := 4983230072969 + 3 ^ 40 * 937827 * 2
def baseEnd_937827 : Nat := 47561088569304442592545

theorem tailTrace_937827 : CollatzResearch.WordTrace tailWord_937827 prefixEnd_937827 47561088569304442592545 := by
  unfold tailWord_937827
  simp only [CollatzResearch.WordTrace]
  refine ⟨34205360773420421945075735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22803573848946947963383823 34205360773420421945075735)
  ·
    refine ⟨51308041160130632917613603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34205360773420421945075735 51308041160130632917613603)
    ·
      refine ⟨76962061740195949376420405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51308041160130632917613603 76962061740195949376420405)
      ·
        refine ⟨7215193288143370254039413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 76962061740195949376420405 7215193288143370254039413)
        ·
          refine ⟨676424370763440961316195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7215193288143370254039413 676424370763440961316195)
          ·
            refine ⟨1014636556145161441974293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 676424370763440961316195 1014636556145161441974293)
            ·
              refine ⟨47561088569304442592545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1014636556145161441974293 47561088569304442592545)
              ·
                rfl

theorem cell20_937827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 6].length) (baseStart_937827 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_937827 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_937827 prefixEnd_937827 := by exact prefixLift 937827
  have htrace : WordTrace (prefixWord ++ tailWord_937827) baseStart_937827 baseEnd_937827 := by
    simpa [prefixWord, tailWord_937827, baseEnd_937827] using wordTrace_append hprefix tailTrace_937827
  have hstable : (prefixWord ++ tailWord_937827).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937827).length < 2 ^ (prefixWord ++ tailWord_937827).sum := by decide
  have hdescent : baseEnd_937827 < baseStart_937827 := by decide
  rcases family_descends (prefixWord ++ tailWord_937827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937889 : List Nat := [1, 2, 3, 4, 2, 1, 2, 2, 3]
def baseStart_937889 : Nat := 118140960795 + 937889 * 2 ^ 59
def prefixEnd_937889 : Nat := 4983230072969 + 3 ^ 40 * 937889 * 2
def baseEnd_937889 : Nat := 428078095613143323265985

theorem tailTrace_937889 : CollatzResearch.WordTrace tailWord_937889 prefixEnd_937889 428078095613143323265985 := by
  unfold tailWord_937889
  simp only [CollatzResearch.WordTrace]
  refine ⟨34207622099195806533832721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22805081399463871022555147 34207622099195806533832721)
  ·
    refine ⟨25655716574396854900374541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34207622099195806533832721 25655716574396854900374541)
    ·
      refine ⟨9620893715398820587640453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25655716574396854900374541 9620893715398820587640453)
      ·
        refine ⟨1803917571637278860182585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9620893715398820587640453 1803917571637278860182585)
        ·
          refine ⟨1352938178727959145136939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1803917571637278860182585 1352938178727959145136939)
          ·
            refine ⟨2029407268091938717705409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1352938178727959145136939 2029407268091938717705409)
            ·
              refine ⟨1522055451068954038279057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2029407268091938717705409 1522055451068954038279057)
              ·
                refine ⟨1141541588301715528709293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1522055451068954038279057 1141541588301715528709293)
                ·
                  refine ⟨428078095613143323265985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1141541588301715528709293 428078095613143323265985)
                  ·
                    rfl

theorem cell20_937889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 2, 2, 3].length) (baseStart_937889 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_937889 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_937889 prefixEnd_937889 := by exact prefixLift 937889
  have htrace : WordTrace (prefixWord ++ tailWord_937889) baseStart_937889 baseEnd_937889 := by
    simpa [prefixWord, tailWord_937889, baseEnd_937889] using wordTrace_append hprefix tailTrace_937889
  have hstable : (prefixWord ++ tailWord_937889).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937889).length < 2 ^ (prefixWord ++ tailWord_937889).sum := by decide
  have hdescent : baseEnd_937889 < baseStart_937889 := by decide
  rcases family_descends (prefixWord ++ tailWord_937889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937917 : List Nat := [1, 4, 1, 2, 3, 2, 1, 2, 4]
def baseStart_937917 : Nat := 118140960795 + 937917 * 2 ^ 59
def prefixEnd_937917 : Nat := 4983230072969 + 3 ^ 40 * 937917 * 2
def baseEnd_937917 : Nat := 428090875576099670332537

theorem tailTrace_937917 : CollatzResearch.WordTrace tailWord_937917 prefixEnd_937917 428090875576099670332537 := by
  unfold tailWord_937917
  simp only [CollatzResearch.WordTrace]
  refine ⟨34208643343094367315852005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22805762228729578210568003 34208643343094367315852005)
  ·
    refine ⟨6414120626830193871722251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34208643343094367315852005 6414120626830193871722251)
    ·
      refine ⟨9621180940245290807583377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6414120626830193871722251 9621180940245290807583377)
      ·
        refine ⟨7215885705183968105687533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9621180940245290807583377 7215885705183968105687533)
        ·
          refine ⟨2705957139443988039632825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7215885705183968105687533 2705957139443988039632825)
          ·
            refine ⟨2029467854582991029724619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2705957139443988039632825 2029467854582991029724619)
            ·
              refine ⟨3044201781874486544586929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2029467854582991029724619 3044201781874486544586929)
              ·
                refine ⟨2283151336405864908440197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3044201781874486544586929 2283151336405864908440197)
                ·
                  refine ⟨428090875576099670332537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2283151336405864908440197 428090875576099670332537)
                  ·
                    rfl

theorem cell20_937917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 2, 4].length) (baseStart_937917 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_937917 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_937917 prefixEnd_937917 := by exact prefixLift 937917
  have htrace : WordTrace (prefixWord ++ tailWord_937917) baseStart_937917 baseEnd_937917 := by
    simpa [prefixWord, tailWord_937917, baseEnd_937917] using wordTrace_append hprefix tailTrace_937917
  have hstable : (prefixWord ++ tailWord_937917).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937917).length < 2 ^ (prefixWord ++ tailWord_937917).sum := by decide
  have hdescent : baseEnd_937917 < baseStart_937917 := by decide
  rcases family_descends (prefixWord ++ tailWord_937917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937934 : List Nat := [4, 1, 1, 1, 2, 2, 4, 3, 2]
def baseStart_937934 : Nat := 118140960795 + 937934 * 2 ^ 59
def prefixEnd_937934 : Nat := 4983230072969 + 3 ^ 40 * 937934 * 2
def baseEnd_937934 : Nat := 428098634839323166765801

theorem tailTrace_937934 : CollatzResearch.WordTrace tailWord_937934 prefixEnd_937934 428098634839323166765801 := by
  unfold tailWord_937934
  simp only [CollatzResearch.WordTrace]
  refine ⟨4276157923004097402402607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22806175589355186146147237 4276157923004097402402607)
  ·
    refine ⟨6414236884506146103603911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4276157923004097402402607 6414236884506146103603911)
    ·
      refine ⟨9621355326759219155405867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6414236884506146103603911 9621355326759219155405867)
      ·
        refine ⟨14432032990138828733108801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9621355326759219155405867 14432032990138828733108801)
        ·
          refine ⟨10824024742604121549831601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14432032990138828733108801 10824024742604121549831601)
          ·
            refine ⟨8118018556953091162373701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10824024742604121549831601 8118018556953091162373701)
            ·
              refine ⟨1522128479428704592945069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8118018556953091162373701 1522128479428704592945069)
              ·
                refine ⟨570798179785764222354401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1522128479428704592945069 570798179785764222354401)
                ·
                  refine ⟨428098634839323166765801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 570798179785764222354401 428098634839323166765801)
                  ·
                    rfl

theorem cell20_937934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 4, 3, 2].length) (baseStart_937934 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_937934 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_937934 prefixEnd_937934 := by exact prefixLift 937934
  have htrace : WordTrace (prefixWord ++ tailWord_937934) baseStart_937934 baseEnd_937934 := by
    simpa [prefixWord, tailWord_937934, baseEnd_937934] using wordTrace_append hprefix tailTrace_937934
  have hstable : (prefixWord ++ tailWord_937934).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937934).length < 2 ^ (prefixWord ++ tailWord_937934).sum := by decide
  have hdescent : baseEnd_937934 < baseStart_937934 := by decide
  rcases family_descends (prefixWord ++ tailWord_937934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937955 : List Nat := [1, 1, 1, 6, 1, 3, 2, 1, 4]
def baseStart_937955 : Nat := 118140960795 + 937955 * 2 ^ 59
def prefixEnd_937955 : Nat := 4983230072969 + 3 ^ 40 * 937955 * 2
def baseEnd_937955 : Nat := 428108219811540427065715

theorem tailTrace_937955 : CollatzResearch.WordTrace tailWord_937955 prefixEnd_937955 428108219811540427065715 := by
  unfold tailWord_937955
  simp only [CollatzResearch.WordTrace]
  refine ⟨34210029316956699805735319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22806686211304466537156879 34210029316956699805735319)
  ·
    refine ⟨51315043975435049708602979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34210029316956699805735319 51315043975435049708602979)
    ·
      refine ⟨76972565963152574562904469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51315043975435049708602979 76972565963152574562904469)
      ·
        refine ⟨3608089029522776932636147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 76972565963152574562904469 3608089029522776932636147)
        ·
          refine ⟨5412133544284165398954221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3608089029522776932636147 5412133544284165398954221)
          ·
            refine ⟨2029550079106562024607833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5412133544284165398954221 2029550079106562024607833)
            ·
              refine ⟨1522162559329921518455875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2029550079106562024607833 1522162559329921518455875)
              ·
                refine ⟨2283243838994882277683813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1522162559329921518455875 2283243838994882277683813)
                ·
                  refine ⟨428108219811540427065715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2283243838994882277683813 428108219811540427065715)
                  ·
                    rfl

theorem cell20_937955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 2, 1, 4].length) (baseStart_937955 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_937955 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_937955 prefixEnd_937955 := by exact prefixLift 937955
  have htrace : WordTrace (prefixWord ++ tailWord_937955) baseStart_937955 baseEnd_937955 := by
    simpa [prefixWord, tailWord_937955, baseEnd_937955] using wordTrace_append hprefix tailTrace_937955
  have hstable : (prefixWord ++ tailWord_937955).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937955).length < 2 ^ (prefixWord ++ tailWord_937955).sum := by decide
  have hdescent : baseEnd_937955 < baseStart_937955 := by decide
  rcases family_descends (prefixWord ++ tailWord_937955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_937976 : List Nat := [2, 1, 2, 1, 1, 3, 4, 2, 4]
def baseStart_937976 : Nat := 118140960795 + 937976 * 2 ^ 59
def prefixEnd_937976 : Nat := 4983230072969 + 3 ^ 40 * 937976 * 2
def baseEnd_937976 : Nat := 428117804783757687365629

theorem tailTrace_937976 : CollatzResearch.WordTrace tailWord_937976 prefixEnd_937976 428117804783757687365629 := by
  unfold tailWord_937976
  simp only [CollatzResearch.WordTrace]
  refine ⟨17105397624940310196124891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22807196833253746928166521 17105397624940310196124891)
  ·
    refine ⟨25658096437410465294187337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17105397624940310196124891 25658096437410465294187337)
    ·
      refine ⟨19243572328057848970640503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25658096437410465294187337 19243572328057848970640503)
      ·
        refine ⟨28865358492086773455960755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19243572328057848970640503 28865358492086773455960755)
        ·
          refine ⟨43298037738130160183941133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28865358492086773455960755 43298037738130160183941133)
          ·
            refine ⟨16236764151798810068977925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43298037738130160183941133 16236764151798810068977925)
            ·
              refine ⟨3044393278462276887933361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16236764151798810068977925 3044393278462276887933361)
              ·
                refine ⟨2283294958846707665950021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3044393278462276887933361 2283294958846707665950021)
                ·
                  refine ⟨428117804783757687365629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2283294958846707665950021 428117804783757687365629)
                  ·
                    rfl

theorem cell20_937976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 2, 4].length) (baseStart_937976 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_937976 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_937976 prefixEnd_937976 := by exact prefixLift 937976
  have htrace : WordTrace (prefixWord ++ tailWord_937976) baseStart_937976 baseEnd_937976 := by
    simpa [prefixWord, tailWord_937976, baseEnd_937976] using wordTrace_append hprefix tailTrace_937976
  have hstable : (prefixWord ++ tailWord_937976).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_937976).length < 2 ^ (prefixWord ++ tailWord_937976).sum := by decide
  have hdescent : baseEnd_937976 < baseStart_937976 := by decide
  rcases family_descends (prefixWord ++ tailWord_937976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938020 : List Nat := [2, 3, 1, 4, 2, 2, 2, 1, 3]
def baseStart_938020 : Nat := 118140960795 + 938020 * 2 ^ 59
def prefixEnd_938020 : Nat := 4983230072969 + 3 ^ 40 * 938020 * 2
def baseEnd_938020 : Nat := 428137887582689089898783

theorem tailTrace_938020 : CollatzResearch.WordTrace tailWord_938020 prefixEnd_938020 428137887582689089898783 := by
  unfold tailWord_938020
  simp only [CollatzResearch.WordTrace]
  refine ⟨17106200030860607953425757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22808266707814143937901009 17106200030860607953425757)
  ·
    refine ⟨6414825011572727982534659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17106200030860607953425757 6414825011572727982534659)
    ·
      refine ⟨9622237517359091973801989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6414825011572727982534659 9622237517359091973801989)
      ·
        refine ⟨1804169534504829745087873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9622237517359091973801989 1804169534504829745087873)
        ·
          refine ⟨1353127150878622308815905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1804169534504829745087873 1353127150878622308815905)
          ·
            refine ⟨1014845363158966731611929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1353127150878622308815905 1014845363158966731611929)
            ·
              refine ⟨761134022369225048708947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1014845363158966731611929 761134022369225048708947)
              ·
                refine ⟨1141701033553837573063421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 761134022369225048708947 1141701033553837573063421)
                ·
                  refine ⟨428137887582689089898783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1141701033553837573063421 428137887582689089898783)
                  ·
                    rfl

theorem cell20_938020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 2, 1, 3].length) (baseStart_938020 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_938020 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_938020 prefixEnd_938020 := by exact prefixLift 938020
  have htrace : WordTrace (prefixWord ++ tailWord_938020) baseStart_938020 baseEnd_938020 := by
    simpa [prefixWord, tailWord_938020, baseEnd_938020] using wordTrace_append hprefix tailTrace_938020
  have hstable : (prefixWord ++ tailWord_938020).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938020).length < 2 ^ (prefixWord ++ tailWord_938020).sum := by decide
  have hdescent : baseEnd_938020 < baseStart_938020 := by decide
  rcases family_descends (prefixWord ++ tailWord_938020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938021 : List Nat := [1, 3, 1, 2, 2, 3, 1, 7]
def baseStart_938021 : Nat := 118140960795 + 938021 * 2 ^ 59
def prefixEnd_938021 : Nat := 4983230072969 + 3 ^ 40 * 938021 * 2
def baseEnd_938021 : Nat := 142712781336645843621815

theorem tailTrace_938021 : CollatzResearch.WordTrace tailWord_938021 prefixEnd_938021 142712781336645843621815 := by
  unfold tailWord_938021
  simp only [CollatzResearch.WordTrace]
  refine ⟨34212436534717593077637917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22808291023145062051758611 34212436534717593077637917)
  ·
    refine ⟨12829663700519097404114219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34212436534717593077637917 12829663700519097404114219)
    ·
      refine ⟨19244495550778646106171329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12829663700519097404114219 19244495550778646106171329)
      ·
        refine ⟨14433371663083984579628497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19244495550778646106171329 14433371663083984579628497)
        ·
          refine ⟨10825028747312988434721373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14433371663083984579628497 10825028747312988434721373)
          ·
            refine ⟨4059385780242370663020515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10825028747312988434721373 4059385780242370663020515)
            ·
              refine ⟨6089078670363555994530773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4059385780242370663020515 6089078670363555994530773)
              ·
                refine ⟨142712781336645843621815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6089078670363555994530773 142712781336645843621815)
                ·
                  rfl

theorem cell20_938021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 7].length) (baseStart_938021 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_938021 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_938021 prefixEnd_938021 := by exact prefixLift 938021
  have htrace : WordTrace (prefixWord ++ tailWord_938021) baseStart_938021 baseEnd_938021 := by
    simpa [prefixWord, tailWord_938021, baseEnd_938021] using wordTrace_append hprefix tailTrace_938021
  have hstable : (prefixWord ++ tailWord_938021).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938021).length < 2 ^ (prefixWord ++ tailWord_938021).sum := by decide
  have hdescent : baseEnd_938021 < baseStart_938021 := by decide
  rcases family_descends (prefixWord ++ tailWord_938021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938028 : List Nat := [2, 2, 1, 1, 1, 2, 2, 2, 7]
def baseStart_938028 : Nat := 118140960795 + 938028 * 2 ^ 59
def prefixEnd_938028 : Nat := 4983230072969 + 3 ^ 40 * 938028 * 2
def baseEnd_938028 : Nat := 428141539000676617632083

theorem tailTrace_938028 : CollatzResearch.WordTrace tailWord_938028 prefixEnd_938028 428141539000676617632083 := by
  unfold tailWord_938028
  simp only [CollatzResearch.WordTrace]
  refine ⟨17106345922846116636571369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22808461230461488848761825 17106345922846116636571369)
  ·
    refine ⟨12829759442134587477428527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17106345922846116636571369 12829759442134587477428527)
    ·
      refine ⟨19244639163201881216142791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12829759442134587477428527 19244639163201881216142791)
      ·
        refine ⟨28866958744802821824214187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19244639163201881216142791 28866958744802821824214187)
        ·
          refine ⟨43300438117204232736321281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28866958744802821824214187 43300438117204232736321281)
          ·
            refine ⟨32475328587903174552240961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43300438117204232736321281 32475328587903174552240961)
            ·
              refine ⟨24356496440927380914180721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32475328587903174552240961 24356496440927380914180721)
              ·
                refine ⟨18267372330695535685635541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24356496440927380914180721 18267372330695535685635541)
                ·
                  refine ⟨428141539000676617632083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18267372330695535685635541 428141539000676617632083)
                  ·
                    rfl

theorem cell20_938028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 7].length) (baseStart_938028 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_938028 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_938028 prefixEnd_938028 := by exact prefixLift 938028
  have htrace : WordTrace (prefixWord ++ tailWord_938028) baseStart_938028 baseEnd_938028 := by
    simpa [prefixWord, tailWord_938028, baseEnd_938028] using wordTrace_append hprefix tailTrace_938028
  have hstable : (prefixWord ++ tailWord_938028).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938028).length < 2 ^ (prefixWord ++ tailWord_938028).sum := by decide
  have hdescent : baseEnd_938028 < baseStart_938028 := by decide
  rcases family_descends (prefixWord ++ tailWord_938028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938038 : List Nat := [5, 1, 2, 1, 1, 1, 1, 8]
def baseStart_938038 : Nat := 118140960795 + 938038 * 2 ^ 59
def prefixEnd_938038 : Nat := 4983230072969 + 3 ^ 40 * 938038 * 2
def baseEnd_938038 : Nat := 142715367757720342432903

theorem tailTrace_938038 : CollatzResearch.WordTrace tailWord_938038 prefixEnd_938038 142715367757720342432903 := by
  unfold tailWord_938038
  simp only [CollatzResearch.WordTrace]
  refine ⟨2138316035978500311312923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22808704383770669987337845 2138316035978500311312923)
  ·
    refine ⟨3207474053967750466969385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2138316035978500311312923 3207474053967750466969385)
    ·
      refine ⟨2405605540475812850227039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3207474053967750466969385 2405605540475812850227039)
      ·
        refine ⟨3608408310713719275340559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2405605540475812850227039 3608408310713719275340559)
        ·
          refine ⟨5412612466070578913010839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3608408310713719275340559 5412612466070578913010839)
          ·
            refine ⟨8118918699105868369516259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5412612466070578913010839 8118918699105868369516259)
            ·
              refine ⟨12178378048658802554274389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8118918699105868369516259 12178378048658802554274389)
              ·
                refine ⟨142715367757720342432903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12178378048658802554274389 142715367757720342432903)
                ·
                  rfl

theorem cell20_938038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 8].length) (baseStart_938038 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_938038 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_938038 prefixEnd_938038 := by exact prefixLift 938038
  have htrace : WordTrace (prefixWord ++ tailWord_938038) baseStart_938038 baseEnd_938038 := by
    simpa [prefixWord, tailWord_938038, baseEnd_938038] using wordTrace_append hprefix tailTrace_938038
  have hstable : (prefixWord ++ tailWord_938038).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938038).length < 2 ^ (prefixWord ++ tailWord_938038).sum := by decide
  have hdescent : baseEnd_938038 < baseStart_938038 := by decide
  rcases family_descends (prefixWord ++ tailWord_938038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938062 : List Nat := [4, 1, 1, 1, 1, 5, 2, 2, 3]
def baseStart_938062 : Nat := 118140960795 + 938062 * 2 ^ 59
def prefixEnd_938062 : Nat := 4983230072969 + 3 ^ 40 * 938062 * 2
def baseEnd_938062 : Nat := 428157057527123610498611

theorem tailTrace_938062 : CollatzResearch.WordTrace tailWord_938062 prefixEnd_938062 428157057527123610498611 := by
  unfold tailWord_938062
  simp only [CollatzResearch.WordTrace]
  refine ⟨4276741490946132134985055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22809287951712704719920293 4276741490946132134985055)
  ·
    refine ⟨6415112236419198202477583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4276741490946132134985055 6415112236419198202477583)
    ·
      refine ⟨9622668354628797303716375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6415112236419198202477583 9622668354628797303716375)
      ·
        refine ⟨14434002531943195955574563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9622668354628797303716375 14434002531943195955574563)
        ·
          refine ⟨21651003797914793933361845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14434002531943195955574563 21651003797914793933361845)
          ·
            refine ⟨2029781606054511931252673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21651003797914793933361845 2029781606054511931252673)
            ·
              refine ⟨1522336204540883948439505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2029781606054511931252673 1522336204540883948439505)
              ·
                refine ⟨1141752153405662961329629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1522336204540883948439505 1141752153405662961329629)
                ·
                  refine ⟨428157057527123610498611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1141752153405662961329629 428157057527123610498611)
                  ·
                    rfl

theorem cell20_938062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 2, 2, 3].length) (baseStart_938062 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_938062 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_938062 prefixEnd_938062 := by exact prefixLift 938062
  have htrace : WordTrace (prefixWord ++ tailWord_938062) baseStart_938062 baseEnd_938062 := by
    simpa [prefixWord, tailWord_938062, baseEnd_938062] using wordTrace_append hprefix tailTrace_938062
  have hstable : (prefixWord ++ tailWord_938062).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938062).length < 2 ^ (prefixWord ++ tailWord_938062).sum := by decide
  have hdescent : baseEnd_938062 < baseStart_938062 := by decide
  rcases family_descends (prefixWord ++ tailWord_938062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938076 : List Nat := [2, 2, 4, 1, 1, 2, 3, 5]
def baseStart_938076 : Nat := 118140960795 + 938076 * 2 ^ 59
def prefixEnd_938076 : Nat := 4983230072969 + 3 ^ 40 * 938076 * 2
def baseEnd_938076 : Nat := 142721149169533928010629

theorem tailTrace_938076 : CollatzResearch.WordTrace tailWord_938076 prefixEnd_938076 142721149169533928010629 := by
  unfold tailWord_938076
  simp only [CollatzResearch.WordTrace]
  refine ⟨17107221274759168735445041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22809628366345558313926721 17107221274759168735445041)
  ·
    refine ⟨12830415956069376551583781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17107221274759168735445041 12830415956069376551583781)
    ·
      refine ⟨2405702991763008103421959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12830415956069376551583781 2405702991763008103421959)
      ·
        refine ⟨3608554487644512155132939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2405702991763008103421959 3608554487644512155132939)
        ·
          refine ⟨5412831731466768232699409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3608554487644512155132939 5412831731466768232699409)
          ·
            refine ⟨4059623798600076174524557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5412831731466768232699409 4059623798600076174524557)
            ·
              refine ⟨1522358924475028565446709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4059623798600076174524557 1522358924475028565446709)
              ·
                refine ⟨142721149169533928010629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1522358924475028565446709 142721149169533928010629)
                ·
                  rfl

theorem cell20_938076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 3, 5].length) (baseStart_938076 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_938076 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_938076 prefixEnd_938076 := by exact prefixLift 938076
  have htrace : WordTrace (prefixWord ++ tailWord_938076) baseStart_938076 baseEnd_938076 := by
    simpa [prefixWord, tailWord_938076, baseEnd_938076] using wordTrace_append hprefix tailTrace_938076
  have hstable : (prefixWord ++ tailWord_938076).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938076).length < 2 ^ (prefixWord ++ tailWord_938076).sum := by decide
  have hdescent : baseEnd_938076 < baseStart_938076 := by decide
  rcases family_descends (prefixWord ++ tailWord_938076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938083 : List Nat := [1, 1, 1, 5, 1, 1, 4, 3, 3]
def baseStart_938083 : Nat := 118140960795 + 938083 * 2 ^ 59
def prefixEnd_938083 : Nat := 4983230072969 + 3 ^ 40 * 938083 * 2
def baseEnd_938083 : Nat := 428166642499340870798525

theorem tailTrace_938083 : CollatzResearch.WordTrace tailWord_938083 prefixEnd_938083 428166642499340870798525 := by
  unfold tailWord_938083
  simp only [CollatzResearch.WordTrace]
  refine ⟨34214697860492977666394903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22809798573661985110929935 34214697860492977666394903)
  ·
    refine ⟨51322046790739466499592355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34214697860492977666394903 51322046790739466499592355)
    ·
      refine ⟨76983070186109199749388533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51322046790739466499592355 76983070186109199749388533)
      ·
        refine ⟨7217162829947737476505175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 76983070186109199749388533 7217162829947737476505175)
        ·
          refine ⟨10825744244921606214757763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7217162829947737476505175 10825744244921606214757763)
          ·
            refine ⟨16238616367382409322136645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10825744244921606214757763 16238616367382409322136645)
            ·
              refine ⟨3044740568884201747900621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16238616367382409322136645 3044740568884201747900621)
              ·
                refine ⟨1141777713331575655462733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3044740568884201747900621 1141777713331575655462733)
                ·
                  refine ⟨428166642499340870798525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1141777713331575655462733 428166642499340870798525)
                  ·
                    rfl

theorem cell20_938083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 3, 3].length) (baseStart_938083 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_938083 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_938083 prefixEnd_938083 := by exact prefixLift 938083
  have htrace : WordTrace (prefixWord ++ tailWord_938083) baseStart_938083 baseEnd_938083 := by
    simpa [prefixWord, tailWord_938083, baseEnd_938083] using wordTrace_append hprefix tailTrace_938083
  have hstable : (prefixWord ++ tailWord_938083).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938083).length < 2 ^ (prefixWord ++ tailWord_938083).sum := by decide
  have hdescent : baseEnd_938083 < baseStart_938083 := by decide
  rcases family_descends (prefixWord ++ tailWord_938083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938104 : List Nat := [2, 1, 2, 1, 1, 1, 3, 4, 5]
def baseStart_938104 : Nat := 118140960795 + 938104 * 2 ^ 59
def prefixEnd_938104 : Nat := 4983230072969 + 3 ^ 40 * 938104 * 2
def baseEnd_938104 : Nat := 428176227471558131098439

theorem tailTrace_938104 : CollatzResearch.WordTrace tailWord_938104 prefixEnd_938104 428176227471558131098439 := by
  unfold tailWord_938104
  simp only [CollatzResearch.WordTrace]
  refine ⟨17107731896708449126454683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22810309195611265501939577 17107731896708449126454683)
  ·
    refine ⟨25661597845062673689682025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17107731896708449126454683 25661597845062673689682025)
    ·
      refine ⟨19246198383797005267261519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25661597845062673689682025 19246198383797005267261519)
      ·
        refine ⟨28869297575695507900892279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19246198383797005267261519 28869297575695507900892279)
        ·
          refine ⟨43303946363543261851338419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28869297575695507900892279 43303946363543261851338419)
          ·
            refine ⟨64955919545314892777007629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43303946363543261851338419 64955919545314892777007629)
            ·
              refine ⟨24358469829493084791377861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64955919545314892777007629 24358469829493084791377861)
              ·
                refine ⟨4567213093029953398383349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24358469829493084791377861 4567213093029953398383349)
                ·
                  refine ⟨428176227471558131098439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4567213093029953398383349 428176227471558131098439)
                  ·
                    rfl

theorem cell20_938104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 4, 5].length) (baseStart_938104 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_938104 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_938104 prefixEnd_938104 := by exact prefixLift 938104
  have htrace : WordTrace (prefixWord ++ tailWord_938104) baseStart_938104 baseEnd_938104 := by
    simpa [prefixWord, tailWord_938104, baseEnd_938104] using wordTrace_append hprefix tailTrace_938104
  have hstable : (prefixWord ++ tailWord_938104).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938104).length < 2 ^ (prefixWord ++ tailWord_938104).sum := by decide
  have hdescent : baseEnd_938104 < baseStart_938104 := by decide
  rcases family_descends (prefixWord ++ tailWord_938104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938128 : List Nat := [2, 1, 1, 1, 1, 1, 8, 1, 4]
def baseStart_938128 : Nat := 118140960795 + 938128 * 2 ^ 59
def prefixEnd_938128 : Nat := 4983230072969 + 3 ^ 40 * 938128 * 2
def baseEnd_938128 : Nat := 428187181725520714298341

theorem tailTrace_938128 : CollatzResearch.WordTrace tailWord_938128 prefixEnd_938128 428187181725520714298341 := by
  unfold tailWord_938128
  simp only [CollatzResearch.WordTrace]
  refine ⟨17108169572664975175891519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22810892763553300234522025 17108169572664975175891519)
  ·
    refine ⟨25662254358997462763837279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17108169572664975175891519 25662254358997462763837279)
    ·
      refine ⟨38493381538496194145755919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25662254358997462763837279 38493381538496194145755919)
      ·
        refine ⟨57740072307744291218633879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38493381538496194145755919 57740072307744291218633879)
        ·
          refine ⟨86610108461616436827950819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57740072307744291218633879 86610108461616436827950819)
          ·
            refine ⟨129915162692424655241926229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86610108461616436827950819 129915162692424655241926229)
            ·
              refine ⟨1522443312801851428616323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 129915162692424655241926229 1522443312801851428616323)
              ·
                refine ⟨2283664969202777142924485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1522443312801851428616323 2283664969202777142924485)
                ·
                  refine ⟨428187181725520714298341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2283664969202777142924485 428187181725520714298341)
                  ·
                    rfl

theorem cell20_938128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 8, 1, 4].length) (baseStart_938128 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_938128 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_938128 prefixEnd_938128 := by exact prefixLift 938128
  have htrace : WordTrace (prefixWord ++ tailWord_938128) baseStart_938128 baseEnd_938128 := by
    simpa [prefixWord, tailWord_938128, baseEnd_938128] using wordTrace_append hprefix tailTrace_938128
  have hstable : (prefixWord ++ tailWord_938128).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938128).length < 2 ^ (prefixWord ++ tailWord_938128).sum := by decide
  have hdescent : baseEnd_938128 < baseStart_938128 := by decide
  rcases family_descends (prefixWord ++ tailWord_938128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938148 : List Nat := [2, 3, 1, 2, 5, 1, 2, 4]
def baseStart_938148 : Nat := 118140960795 + 938148 * 2 ^ 59
def prefixEnd_938148 : Nat := 4983230072969 + 3 ^ 40 * 938148 * 2
def baseEnd_938148 : Nat := 142732103423496511210531

theorem tailTrace_938148 : CollatzResearch.WordTrace tailWord_938148 prefixEnd_938148 142732103423496511210531 := by
  unfold tailWord_938148
  simp only [CollatzResearch.WordTrace]
  refine ⟨17108534302628746883755549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22811379070171662511674065 17108534302628746883755549)
  ·
    refine ⟨6415700363485780081408331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17108534302628746883755549 6415700363485780081408331)
    ·
      refine ⟨9623550545228670122112497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6415700363485780081408331 9623550545228670122112497)
      ·
        refine ⟨7217662908921502591584373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9623550545228670122112497 7217662908921502591584373)
        ·
          refine ⟨676655897711390867961035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7217662908921502591584373 676655897711390867961035)
          ·
            refine ⟨1014983846567086301941553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 676655897711390867961035 1014983846567086301941553)
            ·
              refine ⟨761237884925314726456165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1014983846567086301941553 761237884925314726456165)
              ·
                refine ⟨142732103423496511210531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 761237884925314726456165 142732103423496511210531)
                ·
                  rfl

theorem cell20_938148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 2, 4].length) (baseStart_938148 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_938148 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_938148 prefixEnd_938148 := by exact prefixLift 938148
  have htrace : WordTrace (prefixWord ++ tailWord_938148) baseStart_938148 baseEnd_938148 := by
    simpa [prefixWord, tailWord_938148, baseEnd_938148] using wordTrace_append hprefix tailTrace_938148
  have hstable : (prefixWord ++ tailWord_938148).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938148).length < 2 ^ (prefixWord ++ tailWord_938148).sum := by decide
  have hdescent : baseEnd_938148 < baseStart_938148 := by decide
  rcases family_descends (prefixWord ++ tailWord_938148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938190 : List Nat := [4, 1, 1, 1, 4, 2, 2, 5]
def baseStart_938190 : Nat := 118140960795 + 938190 * 2 ^ 59
def prefixEnd_938190 : Nat := 4983230072969 + 3 ^ 40 * 938190 * 2
def baseEnd_938190 : Nat := 142738493404974684743807

theorem tailTrace_938190 : CollatzResearch.WordTrace tailWord_938190 prefixEnd_938190 142738493404974684743807 := by
  unfold tailWord_938190
  simp only [CollatzResearch.WordTrace]
  refine ⟨4277325058888166867567503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22812400314070223293693349 4277325058888166867567503)
  ·
    refine ⟨6415987588332250301351255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4277325058888166867567503 6415987588332250301351255)
    ·
      refine ⟨9623981382498375452026883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6415987588332250301351255 9623981382498375452026883)
      ·
        refine ⟨14435972073747563178040325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9623981382498375452026883 14435972073747563178040325)
        ·
          refine ⟨2706744763827668095882561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14435972073747563178040325 2706744763827668095882561)
          ·
            refine ⟨2030058572870751071911921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2706744763827668095882561 2030058572870751071911921)
            ·
              refine ⟨1522543929653063303933941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2030058572870751071911921 1522543929653063303933941)
              ·
                refine ⟨142738493404974684743807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1522543929653063303933941 142738493404974684743807)
                ·
                  rfl

theorem cell20_938190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 2, 5].length) (baseStart_938190 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_938190 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_938190 prefixEnd_938190 := by exact prefixLift 938190
  have htrace : WordTrace (prefixWord ++ tailWord_938190) baseStart_938190 baseEnd_938190 := by
    simpa [prefixWord, tailWord_938190, baseEnd_938190] using wordTrace_append hprefix tailTrace_938190
  have hstable : (prefixWord ++ tailWord_938190).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938190).length < 2 ^ (prefixWord ++ tailWord_938190).sum := by decide
  have hdescent : baseEnd_938190 < baseStart_938190 := by decide
  rcases family_descends (prefixWord ++ tailWord_938190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938228 : List Nat := [2, 6, 1, 11]
def baseStart_938228 : Nat := 118140960795 + 938228 * 2 ^ 59
def prefixEnd_938228 : Nat := 4983230072969 + 3 ^ 40 * 938228 * 2
def baseEnd_938228 : Nat := 1762274997738126794093

theorem tailTrace_938228 : CollatzResearch.WordTrace tailWord_938228 prefixEnd_938228 1762274997738126794093 := by
  unfold tailWord_938228
  simp only [CollatzResearch.WordTrace]
  refine ⟨17109993222483833715211669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22813324296645111620282225 17109993222483833715211669)
  ·
    refine ⟨802030932303929705400547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 17109993222483833715211669 802030932303929705400547)
    ·
      refine ⟨1203046398455894558100821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 802030932303929705400547 1203046398455894558100821)
      ·
        refine ⟨1762274997738126794093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 11 1203046398455894558100821 1762274997738126794093)
        ·
          rfl

theorem cell20_938228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 11].length) (baseStart_938228 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_938228 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_938228 prefixEnd_938228 := by exact prefixLift 938228
  have htrace : WordTrace (prefixWord ++ tailWord_938228) baseStart_938228 baseEnd_938228 := by
    simpa [prefixWord, tailWord_938228, baseEnd_938228] using wordTrace_append hprefix tailTrace_938228
  have hstable : (prefixWord ++ tailWord_938228).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938228).length < 2 ^ (prefixWord ++ tailWord_938228).sum := by decide
  have hdescent : baseEnd_938228 < baseStart_938228 := by decide
  rcases family_descends (prefixWord ++ tailWord_938228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938238 : List Nat := [4, 2, 2, 1, 1, 1, 3, 4, 2]
def baseStart_938238 : Nat := 118140960795 + 938238 * 2 ^ 59
def prefixEnd_938238 : Nat := 4983230072969 + 3 ^ 40 * 938238 * 2
def baseEnd_938238 : Nat := 428237388722849220631225

theorem tailTrace_938238 : CollatzResearch.WordTrace tailWord_938238 prefixEnd_938238 428237388722849220631225 := by
  unfold tailWord_938238
  simp only [CollatzResearch.WordTrace]
  refine ⟨4277543896866429892285921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22813567449954292758858245 4277543896866429892285921)
  ·
    refine ⟨3208157922649822419214441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4277543896866429892285921 3208157922649822419214441)
    ·
      refine ⟨2406118441987366814410831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3208157922649822419214441 2406118441987366814410831)
      ·
        refine ⟨3609177662981050221616247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2406118441987366814410831 3609177662981050221616247)
        ·
          refine ⟨5413766494471575332424371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3609177662981050221616247 5413766494471575332424371)
          ·
            refine ⟨8120649741707362998636557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5413766494471575332424371 8120649741707362998636557)
            ·
              refine ⟨3045243653140261124488709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8120649741707362998636557 3045243653140261124488709)
              ·
                refine ⟨570983184963798960841633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3045243653140261124488709 570983184963798960841633)
                ·
                  refine ⟨428237388722849220631225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 570983184963798960841633 428237388722849220631225)
                  ·
                    rfl

theorem cell20_938238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 4, 2].length) (baseStart_938238 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_938238 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_938238 prefixEnd_938238 := by exact prefixLift 938238
  have htrace : WordTrace (prefixWord ++ tailWord_938238) baseStart_938238 baseEnd_938238 := by
    simpa [prefixWord, tailWord_938238, baseEnd_938238] using wordTrace_append hprefix tailTrace_938238
  have hstable : (prefixWord ++ tailWord_938238).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938238).length < 2 ^ (prefixWord ++ tailWord_938238).sum := by decide
  have hdescent : baseEnd_938238 < baseStart_938238 := by decide
  rcases family_descends (prefixWord ++ tailWord_938238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938249 : List Nat := [1, 2, 1, 1, 3, 4, 3, 5]
def baseStart_938249 : Nat := 118140960795 + 938249 * 2 ^ 59
def prefixEnd_938249 : Nat := 4983230072969 + 3 ^ 40 * 938249 * 2
def baseEnd_938249 : Nat := 142747469807527357088171

theorem tailTrace_938249 : CollatzResearch.WordTrace tailWord_938249 prefixEnd_938249 142747469807527357088171 := by
  unfold tailWord_938249
  simp only [CollatzResearch.WordTrace]
  refine ⟨34220752377891588016937801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22813834918594392011291867 34220752377891588016937801)
  ·
    refine ⟨25665564283418691012703351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34220752377891588016937801 25665564283418691012703351)
    ·
      refine ⟨38498346425128036519055027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25665564283418691012703351 38498346425128036519055027)
      ·
        refine ⟨57747519637692054778582541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38498346425128036519055027 57747519637692054778582541)
        ·
          refine ⟨21655319864134520541968453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57747519637692054778582541 21655319864134520541968453)
          ·
            refine ⟨4060372474525222601619085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21655319864134520541968453 4060372474525222601619085)
            ·
              refine ⟨1522639677946958475607157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4060372474525222601619085 1522639677946958475607157)
              ·
                refine ⟨142747469807527357088171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1522639677946958475607157 142747469807527357088171)
                ·
                  rfl

theorem cell20_938249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 3, 5].length) (baseStart_938249 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_938249 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_938249 prefixEnd_938249 := by exact prefixLift 938249
  have htrace : WordTrace (prefixWord ++ tailWord_938249) baseStart_938249 baseEnd_938249 := by
    simpa [prefixWord, tailWord_938249, baseEnd_938249] using wordTrace_append hprefix tailTrace_938249
  have hstable : (prefixWord ++ tailWord_938249).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938249).length < 2 ^ (prefixWord ++ tailWord_938249).sum := by decide
  have hdescent : baseEnd_938249 < baseStart_938249 := by decide
  rcases family_descends (prefixWord ++ tailWord_938249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938276 : List Nat := [2, 3, 1, 3, 1, 3, 2, 3, 2]
def baseStart_938276 : Nat := 118140960795 + 938276 * 2 ^ 59
def prefixEnd_938276 : Nat := 4983230072969 + 3 ^ 40 * 938276 * 2
def baseEnd_938276 : Nat := 428254732958289977364403

theorem tailTrace_938276 : CollatzResearch.WordTrace tailWord_938276 prefixEnd_938276 428254732958289977364403 := by
  unfold tailWord_938276
  simp only [CollatzResearch.WordTrace]
  refine ⟨17110868574396885814085341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22814491432529181085447121 17110868574396885814085341)
  ·
    refine ⟨6416575715398832180282003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17110868574396885814085341 6416575715398832180282003)
    ·
      refine ⟨9624863573098248270423005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6416575715398832180282003 9624863573098248270423005)
      ·
        refine ⟨3609323839911843101408627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9624863573098248270423005 3609323839911843101408627)
        ·
          refine ⟨5413985759867764652112941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3609323839911843101408627 5413985759867764652112941)
          ·
            refine ⟨2030244659950411744542353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5413985759867764652112941 2030244659950411744542353)
            ·
              refine ⟨1522683494962808808406765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2030244659950411744542353 1522683494962808808406765)
              ·
                refine ⟨571006310611053303152537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1522683494962808808406765 571006310611053303152537)
                ·
                  refine ⟨428254732958289977364403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 571006310611053303152537 428254732958289977364403)
                  ·
                    rfl

theorem cell20_938276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 2, 3, 2].length) (baseStart_938276 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_938276 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_938276 prefixEnd_938276 := by exact prefixLift 938276
  have htrace : WordTrace (prefixWord ++ tailWord_938276) baseStart_938276 baseEnd_938276 := by
    simpa [prefixWord, tailWord_938276, baseEnd_938276] using wordTrace_append hprefix tailTrace_938276
  have hstable : (prefixWord ++ tailWord_938276).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938276).length < 2 ^ (prefixWord ++ tailWord_938276).sum := by decide
  have hdescent : baseEnd_938276 < baseStart_938276 := by decide
  rcases family_descends (prefixWord ++ tailWord_938276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938286 : List Nat := [4, 1, 3, 3, 1, 2, 1, 2, 3]
def baseStart_938286 : Nat := 118140960795 + 938286 * 2 ^ 59
def prefixEnd_938286 : Nat := 4983230072969 + 3 ^ 40 * 938286 * 2
def baseEnd_938286 : Nat := 428259297230774387031029

theorem tailTrace_938286 : CollatzResearch.WordTrace tailWord_938286 prefixEnd_938286 428259297230774387031029 := by
  unfold tailWord_938286
  simp only [CollatzResearch.WordTrace]
  refine ⟨4277762734844692917004339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22814734585838362224023141 4277762734844692917004339)
  ·
    refine ⟨6416644102267039375506509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4277762734844692917004339 6416644102267039375506509)
    ·
      refine ⟨2406241538350139765814941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6416644102267039375506509 2406241538350139765814941)
      ·
        refine ⟨902340576881302412180603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2406241538350139765814941 902340576881302412180603)
        ·
          refine ⟨1353510865321953618270905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 902340576881302412180603 1353510865321953618270905)
          ·
            refine ⟨1015133148991465213703179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1353510865321953618270905 1015133148991465213703179)
            ·
              refine ⟨1522699723487197820554769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1015133148991465213703179 1522699723487197820554769)
              ·
                refine ⟨1142024792615398365416077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1522699723487197820554769 1142024792615398365416077)
                ·
                  refine ⟨428259297230774387031029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1142024792615398365416077 428259297230774387031029)
                  ·
                    rfl

theorem cell20_938286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 1, 2, 3].length) (baseStart_938286 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_938286 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_938286 prefixEnd_938286 := by exact prefixLift 938286
  have htrace : WordTrace (prefixWord ++ tailWord_938286) baseStart_938286 baseEnd_938286 := by
    simpa [prefixWord, tailWord_938286, baseEnd_938286] using wordTrace_append hprefix tailTrace_938286
  have hstable : (prefixWord ++ tailWord_938286).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938286).length < 2 ^ (prefixWord ++ tailWord_938286).sum := by decide
  have hdescent : baseEnd_938286 < baseStart_938286 := by decide
  rcases family_descends (prefixWord ++ tailWord_938286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938297 : List Nat := [1, 2, 1, 6, 1, 2, 2, 1, 4]
def baseStart_938297 : Nat := 118140960795 + 938297 * 2 ^ 59
def prefixEnd_938297 : Nat := 4983230072969 + 3 ^ 40 * 938297 * 2
def baseEnd_938297 : Nat := 428264317930507237664317

theorem tailTrace_938297 : CollatzResearch.WordTrace tailWord_938297 prefixEnd_938297 428264317930507237664317 := by
  unfold tailWord_938297
  simp only [CollatzResearch.WordTrace]
  refine ⟨34222503081717692214685145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22815002054478461476456763 34222503081717692214685145)
  ·
    refine ⟨25666877311288269161013859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34222503081717692214685145 25666877311288269161013859)
    ·
      refine ⟨38500315966932403741520789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25666877311288269161013859 38500315966932403741520789)
      ·
        refine ⟨1804702310949956425383787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 38500315966932403741520789 1804702310949956425383787)
        ·
          refine ⟨2707053466424934638075681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1804702310949956425383787 2707053466424934638075681)
          ·
            refine ⟨2030290099818700978556761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2707053466424934638075681 2030290099818700978556761)
            ·
              refine ⟨1522717574864025733917571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2030290099818700978556761 1522717574864025733917571)
              ·
                refine ⟨2284076362296038600876357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1522717574864025733917571 2284076362296038600876357)
                ·
                  refine ⟨428264317930507237664317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2284076362296038600876357 428264317930507237664317)
                  ·
                    rfl

theorem cell20_938297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 2, 1, 4].length) (baseStart_938297 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_938297 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_938297 prefixEnd_938297 := by exact prefixLift 938297
  have htrace : WordTrace (prefixWord ++ tailWord_938297) baseStart_938297 baseEnd_938297 := by
    simpa [prefixWord, tailWord_938297, baseEnd_938297] using wordTrace_append hprefix tailTrace_938297
  have hstable : (prefixWord ++ tailWord_938297).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938297).length < 2 ^ (prefixWord ++ tailWord_938297).sum := by decide
  have hdescent : baseEnd_938297 < baseStart_938297 := by decide
  rcases family_descends (prefixWord ++ tailWord_938297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938334 : List Nat := [4, 4, 2, 1, 2, 1, 6]
def baseStart_938334 : Nat := 118140960795 + 938334 * 2 ^ 59
def prefixEnd_938334 : Nat := 4983230072969 + 3 ^ 40 * 938334 * 2
def baseEnd_938334 : Nat := 47586800637633283714537

theorem tailTrace_938334 : CollatzResearch.WordTrace tailWord_938334 prefixEnd_938334 47586800637633283714537 := by
  unfold tailWord_938334
  simp only [CollatzResearch.WordTrace]
  refine ⟨4277981572822955941722757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22815901721722431689188037 4277981572822955941722757)
  ·
    refine ⟨802121544904304239073017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4277981572822955941722757 802121544904304239073017)
    ·
      refine ⟨601591158678228179304763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 802121544904304239073017 601591158678228179304763)
      ·
        refine ⟨902386738017342268957145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 601591158678228179304763 902386738017342268957145)
        ·
          refine ⟨676790053513006701717859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 902386738017342268957145 676790053513006701717859)
          ·
            refine ⟨1015185080269510052576789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 676790053513006701717859 1015185080269510052576789)
            ·
              refine ⟨47586800637633283714537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1015185080269510052576789 47586800637633283714537)
              ·
                rfl

theorem cell20_938334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 6].length) (baseStart_938334 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_938334 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_938334 prefixEnd_938334 := by exact prefixLift 938334
  have htrace : WordTrace (prefixWord ++ tailWord_938334) baseStart_938334 baseEnd_938334 := by
    simpa [prefixWord, tailWord_938334, baseEnd_938334] using wordTrace_append hprefix tailTrace_938334
  have hstable : (prefixWord ++ tailWord_938334).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938334).length < 2 ^ (prefixWord ++ tailWord_938334).sum := by decide
  have hdescent : baseEnd_938334 < baseStart_938334 := by decide
  rcases family_descends (prefixWord ++ tailWord_938334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938335 : List Nat := [1, 1, 2, 3, 1, 2, 5, 3, 2]
def baseStart_938335 : Nat := 118140960795 + 938335 * 2 ^ 59
def prefixEnd_938335 : Nat := 4983230072969 + 3 ^ 40 * 938335 * 2
def baseEnd_938335 : Nat := 428281662165947994397495

theorem tailTrace_938335 : CollatzResearch.WordTrace tailWord_938335 prefixEnd_938335 428281662165947994397495 := by
  unfold tailWord_938335
  simp only [CollatzResearch.WordTrace]
  refine ⟨34223889055580024704568459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22815926037053349803045639 34223889055580024704568459)
  ·
    refine ⟨51335833583370037056852689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34223889055580024704568459 51335833583370037056852689)
    ·
      refine ⟨38501875187527527792639517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51335833583370037056852689 38501875187527527792639517)
      ·
        refine ⟨14438203195322822922239819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38501875187527527792639517 14438203195322822922239819)
        ·
          refine ⟨21657304792984234383359729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14438203195322822922239819 21657304792984234383359729)
          ·
            refine ⟨16242978594738175787519797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21657304792984234383359729 16242978594738175787519797)
            ·
              refine ⟨1522779243256703980079981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16242978594738175787519797 1522779243256703980079981)
              ·
                refine ⟨571042216221263992529993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1522779243256703980079981 571042216221263992529993)
                ·
                  refine ⟨428281662165947994397495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 571042216221263992529993 428281662165947994397495)
                  ·
                    rfl

theorem cell20_938335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 5, 3, 2].length) (baseStart_938335 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_938335 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_938335 prefixEnd_938335 := by exact prefixLift 938335
  have htrace : WordTrace (prefixWord ++ tailWord_938335) baseStart_938335 baseEnd_938335 := by
    simpa [prefixWord, tailWord_938335, baseEnd_938335] using wordTrace_append hprefix tailTrace_938335
  have hstable : (prefixWord ++ tailWord_938335).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938335).length < 2 ^ (prefixWord ++ tailWord_938335).sum := by decide
  have hdescent : baseEnd_938335 < baseStart_938335 := by decide
  rcases family_descends (prefixWord ++ tailWord_938335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938349 : List Nat := [1, 5, 1, 1, 1, 2, 2, 4, 3]
def baseStart_938349 : Nat := 118140960795 + 938349 * 2 ^ 59
def prefixEnd_938349 : Nat := 4983230072969 + 3 ^ 40 * 938349 * 2
def baseEnd_938349 : Nat := 428288052147426167930771

theorem tailTrace_938349 : CollatzResearch.WordTrace tailWord_938349 prefixEnd_938349 428288052147426167930771 := by
  unfold tailWord_938349
  simp only [CollatzResearch.WordTrace]
  refine ⟨34224399677529305095578101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22816266451686203397052067 34224399677529305095578101)
  ·
    refine ⟨3208537469768372352710447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34224399677529305095578101 3208537469768372352710447)
    ·
      refine ⟨4812806204652558529065671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3208537469768372352710447 4812806204652558529065671)
      ·
        refine ⟨7219209306978837793598507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4812806204652558529065671 7219209306978837793598507)
        ·
          refine ⟨10828813960468256690397761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7219209306978837793598507 10828813960468256690397761)
          ·
            refine ⟨8121610470351192517798321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10828813960468256690397761 8121610470351192517798321)
            ·
              refine ⟨6091207852763394388348741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8121610470351192517798321 6091207852763394388348741)
              ·
                refine ⟨1142101472393136447815389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6091207852763394388348741 1142101472393136447815389)
                ·
                  refine ⟨428288052147426167930771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1142101472393136447815389 428288052147426167930771)
                  ·
                    rfl

theorem cell20_938349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 4, 3].length) (baseStart_938349 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_938349 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_938349 prefixEnd_938349 := by exact prefixLift 938349
  have htrace : WordTrace (prefixWord ++ tailWord_938349) baseStart_938349 baseEnd_938349 := by
    simpa [prefixWord, tailWord_938349, baseEnd_938349] using wordTrace_append hprefix tailTrace_938349
  have hstable : (prefixWord ++ tailWord_938349).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938349).length < 2 ^ (prefixWord ++ tailWord_938349).sum := by decide
  have hdescent : baseEnd_938349 < baseStart_938349 := by decide
  rcases family_descends (prefixWord ++ tailWord_938349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938352 : List Nat := [2, 1, 1, 1, 4, 4, 3, 2, 2]
def baseStart_938352 : Nat := 118140960795 + 938352 * 2 ^ 59
def prefixEnd_938352 : Nat := 4983230072969 + 3 ^ 40 * 938352 * 2
def baseEnd_938352 : Nat := 428289421429171490830759

theorem tailTrace_938352 : CollatzResearch.WordTrace tailWord_938352 prefixEnd_938352 428289421429171490830759 := by
  unfold tailWord_938352
  simp only [CollatzResearch.WordTrace]
  refine ⟨17112254548259218303968655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22816339397678957738624873 17112254548259218303968655)
  ·
    refine ⟨25668381822388827455952983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17112254548259218303968655 25668381822388827455952983)
    ·
      refine ⟨38502572733583241183929475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25668381822388827455952983 38502572733583241183929475)
      ·
        refine ⟨57753859100374861775894213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38502572733583241183929475 57753859100374861775894213)
        ·
          refine ⟨10828848581320286582980165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57753859100374861775894213 10828848581320286582980165)
          ·
            refine ⟨2030409108997553734308781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10828848581320286582980165 2030409108997553734308781)
            ·
              refine ⟨761403415874082650365793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2030409108997553734308781 761403415874082650365793)
              ·
                refine ⟨571052561905561987774345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 761403415874082650365793 571052561905561987774345)
                ·
                  refine ⟨428289421429171490830759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 571052561905561987774345 428289421429171490830759)
                  ·
                    rfl

theorem cell20_938352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 3, 2, 2].length) (baseStart_938352 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_938352 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_938352 prefixEnd_938352 := by exact prefixLift 938352
  have htrace : WordTrace (prefixWord ++ tailWord_938352) baseStart_938352 baseEnd_938352 := by
    simpa [prefixWord, tailWord_938352, baseEnd_938352] using wordTrace_append hprefix tailTrace_938352
  have hstable : (prefixWord ++ tailWord_938352).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938352).length < 2 ^ (prefixWord ++ tailWord_938352).sum := by decide
  have hdescent : baseEnd_938352 < baseStart_938352 := by decide
  rcases family_descends (prefixWord ++ tailWord_938352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938363 : List Nat := [1, 1, 1, 1, 1, 8, 2, 5]
def baseStart_938363 : Nat := 118140960795 + 938363 * 2 ^ 59
def prefixEnd_938363 : Nat := 4983230072969 + 3 ^ 40 * 938363 * 2
def baseEnd_938363 : Nat := 142764814042968113821349

theorem tailTrace_938363 : CollatzResearch.WordTrace tailWord_938363 prefixEnd_938363 142764814042968113821349 := by
  unfold tailWord_938363
  simp only [CollatzResearch.WordTrace]
  refine ⟨34224910299478585486587743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22816606866319056991058495 34224910299478585486587743)
  ·
    refine ⟨51337365449217878229881615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34224910299478585486587743 51337365449217878229881615)
    ·
      refine ⟨77006048173826817344822423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51337365449217878229881615 77006048173826817344822423)
      ·
        refine ⟨115509072260740226017233635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77006048173826817344822423 115509072260740226017233635)
        ·
          refine ⟨173263608391110339025850453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115509072260740226017233635 173263608391110339025850453)
          ·
            refine ⟨2030432910833324285459185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 173263608391110339025850453 2030432910833324285459185)
            ·
              refine ⟨1522824683124993214094389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2030432910833324285459185 1522824683124993214094389)
              ·
                refine ⟨142764814042968113821349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1522824683124993214094389 142764814042968113821349)
                ·
                  rfl

theorem cell20_938363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 2, 5].length) (baseStart_938363 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_938363 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_938363 prefixEnd_938363 := by exact prefixLift 938363
  have htrace : WordTrace (prefixWord ++ tailWord_938363) baseStart_938363 baseEnd_938363 := by
    simpa [prefixWord, tailWord_938363, baseEnd_938363] using wordTrace_append hprefix tailTrace_938363
  have hstable : (prefixWord ++ tailWord_938363).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938363).length < 2 ^ (prefixWord ++ tailWord_938363).sum := by decide
  have hdescent : baseEnd_938363 < baseStart_938363 := by decide
  rcases family_descends (prefixWord ++ tailWord_938363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938401 : List Nat := [1, 2, 3, 5, 9]
def baseStart_938401 : Nat := 118140960795 + 938401 * 2 ^ 59
def prefixEnd_938401 : Nat := 4983230072969 + 3 ^ 40 * 938401 * 2
def baseEnd_938401 : Nat := 5287799831658581459225

theorem tailTrace_938401 : CollatzResearch.WordTrace tailWord_938401 prefixEnd_938401 5287799831658581459225 := by
  unfold tailWord_938401
  simp only [CollatzResearch.WordTrace]
  refine ⟨34226296273340917976471057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22817530848893945317647371 34226296273340917976471057)
  ·
    refine ⟨25669722205005688482353293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34226296273340917976471057 25669722205005688482353293)
    ·
      refine ⟨9626145826877133180882485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25669722205005688482353293 9626145826877133180882485)
      ·
        refine ⟨902451171269731235707733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9626145826877133180882485 902451171269731235707733)
        ·
          refine ⟨5287799831658581459225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 902451171269731235707733 5287799831658581459225)
          ·
            rfl

theorem cell20_938401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 9].length) (baseStart_938401 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_938401 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_938401 prefixEnd_938401 := by exact prefixLift 938401
  have htrace : WordTrace (prefixWord ++ tailWord_938401) baseStart_938401 baseEnd_938401 := by
    simpa [prefixWord, tailWord_938401, baseEnd_938401] using wordTrace_append hprefix tailTrace_938401
  have hstable : (prefixWord ++ tailWord_938401).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938401).length < 2 ^ (prefixWord ++ tailWord_938401).sum := by decide
  have hdescent : baseEnd_938401 < baseStart_938401 := by decide
  rcases family_descends (prefixWord ++ tailWord_938401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938407 : List Nat := [1, 1, 6, 1, 1, 4, 2, 2, 2]
def baseStart_938407 : Nat := 118140960795 + 938407 * 2 ^ 59
def prefixEnd_938407 : Nat := 4983230072969 + 3 ^ 40 * 938407 * 2
def baseEnd_938407 : Nat := 428314524927835743997201

theorem tailTrace_938407 : CollatzResearch.WordTrace tailWord_938407 prefixEnd_938407 428314524927835743997201 := by
  unfold tailWord_938407
  simp only [CollatzResearch.WordTrace]
  refine ⟨34226515111319181001189475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22817676740879454000792983 34226515111319181001189475)
  ·
    refine ⟨51339772666978771501784213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34226515111319181001189475 51339772666978771501784213)
    ·
      refine ⟨2406551843764629914146135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 51339772666978771501784213 2406551843764629914146135)
      ·
        refine ⟨3609827765646944871219203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2406551843764629914146135 3609827765646944871219203)
        ·
          refine ⟨5414741648470417306828805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3609827765646944871219203 5414741648470417306828805)
          ·
            refine ⟨1015264059088203245030401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5414741648470417306828805 1015264059088203245030401)
            ·
              refine ⟨761448044316152433772801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1015264059088203245030401 761448044316152433772801)
              ·
                refine ⟨571086033237114325329601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 761448044316152433772801 571086033237114325329601)
                ·
                  refine ⟨428314524927835743997201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 571086033237114325329601 428314524927835743997201)
                  ·
                    rfl

theorem cell20_938407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 2, 2, 2].length) (baseStart_938407 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_938407 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_938407 prefixEnd_938407 := by exact prefixLift 938407
  have htrace : WordTrace (prefixWord ++ tailWord_938407) baseStart_938407 baseEnd_938407 := by
    simpa [prefixWord, tailWord_938407, baseEnd_938407] using wordTrace_append hprefix tailTrace_938407
  have hstable : (prefixWord ++ tailWord_938407).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938407).length < 2 ^ (prefixWord ++ tailWord_938407).sum := by decide
  have hdescent : baseEnd_938407 < baseStart_938407 := by decide
  rcases family_descends (prefixWord ++ tailWord_938407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938425 : List Nat := [1, 2, 1, 4, 3, 1, 2, 3, 3]
def baseStart_938425 : Nat := 118140960795 + 938425 * 2 ^ 59
def prefixEnd_938425 : Nat := 4983230072969 + 3 ^ 40 * 938425 * 2
def baseEnd_938425 : Nat := 428322740618307681397127

theorem tailTrace_938425 : CollatzResearch.WordTrace tailWord_938425 prefixEnd_938425 428322740618307681397127 := by
  unfold tailWord_938425
  simp only [CollatzResearch.WordTrace]
  refine ⟨34227171625253970075344729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22818114416835980050229819 34227171625253970075344729)
  ·
    refine ⟨25670378718940477556508547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34227171625253970075344729 25670378718940477556508547)
    ·
      refine ⟨38505568078410716334762821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25670378718940477556508547 38505568078410716334762821)
      ·
        refine ⟨7219794014702009312768029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38505568078410716334762821 7219794014702009312768029)
        ·
          refine ⟨2707422755513253492288011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7219794014702009312768029 2707422755513253492288011)
          ·
            refine ⟨4061134133269880238432017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2707422755513253492288011 4061134133269880238432017)
            ·
              refine ⟨3045850599952410178824013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4061134133269880238432017 3045850599952410178824013)
              ·
                refine ⟨1142193974982153817059005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3045850599952410178824013 1142193974982153817059005)
                ·
                  refine ⟨428322740618307681397127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1142193974982153817059005 428322740618307681397127)
                  ·
                    rfl

theorem cell20_938425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 3, 3].length) (baseStart_938425 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_938425 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_938425 prefixEnd_938425 := by exact prefixLift 938425
  have htrace : WordTrace (prefixWord ++ tailWord_938425) baseStart_938425 baseEnd_938425 := by
    simpa [prefixWord, tailWord_938425, baseEnd_938425] using wordTrace_append hprefix tailTrace_938425
  have hstable : (prefixWord ++ tailWord_938425).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938425).length < 2 ^ (prefixWord ++ tailWord_938425).sum := by decide
  have hdescent : baseEnd_938425 < baseStart_938425 := by decide
  rcases family_descends (prefixWord ++ tailWord_938425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938446 : List Nat := [4, 1, 1, 1, 2, 1, 1, 4, 5]
def baseStart_938446 : Nat := 118140960795 + 938446 * 2 ^ 59
def prefixEnd_938446 : Nat := 4983230072969 + 3 ^ 40 * 938446 * 2
def baseEnd_938446 : Nat := 428332325590524941697041

theorem tailTrace_938446 : CollatzResearch.WordTrace tailWord_938446 prefixEnd_938446 428332325590524941697041 := by
  unfold tailWord_938446
  simp only [CollatzResearch.WordTrace]
  refine ⟨4278492194772236332732399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22818625038785260441239461 4278492194772236332732399)
  ·
    refine ⟨6417738292158354499098599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4278492194772236332732399 6417738292158354499098599)
    ·
      refine ⟨9626607438237531748647899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6417738292158354499098599 9626607438237531748647899)
      ·
        refine ⟨14439911157356297622971849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9626607438237531748647899 14439911157356297622971849)
        ·
          refine ⟨10829933368017223217228887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14439911157356297622971849 10829933368017223217228887)
          ·
            refine ⟨16244900052025834825843331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10829933368017223217228887 16244900052025834825843331)
            ·
              refine ⟨24367350078038752238764997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16244900052025834825843331 24367350078038752238764997)
              ·
                refine ⟨4568878139632266044768437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24367350078038752238764997 4568878139632266044768437)
                ·
                  refine ⟨428332325590524941697041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4568878139632266044768437 428332325590524941697041)
                  ·
                    rfl

theorem cell20_938446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 4, 5].length) (baseStart_938446 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_938446 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_938446 prefixEnd_938446 := by exact prefixLift 938446
  have htrace : WordTrace (prefixWord ++ tailWord_938446) baseStart_938446 baseEnd_938446 := by
    simpa [prefixWord, tailWord_938446, baseEnd_938446] using wordTrace_append hprefix tailTrace_938446
  have hstable : (prefixWord ++ tailWord_938446).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938446).length < 2 ^ (prefixWord ++ tailWord_938446).sum := by decide
  have hdescent : baseEnd_938446 < baseStart_938446 := by decide
  rcases family_descends (prefixWord ++ tailWord_938446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938463 : List Nat := [1, 1, 2, 3, 3, 2, 3, 2, 3]
def baseStart_938463 : Nat := 118140960795 + 938463 * 2 ^ 59
def prefixEnd_938463 : Nat := 4983230072969 + 3 ^ 40 * 938463 * 2
def baseEnd_938463 : Nat := 428340084853748438130305

theorem tailTrace_938463 : CollatzResearch.WordTrace tailWord_938463 prefixEnd_938463 428340084853748438130305 := by
  unfold tailWord_938463
  simp only [CollatzResearch.WordTrace]
  refine ⟨34228557599116302565228043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22819038399410868376818695 34228557599116302565228043)
  ·
    refine ⟨51342836398674453847842065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34228557599116302565228043 51342836398674453847842065)
    ·
      refine ⟨38507127299005840385881549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51342836398674453847842065 38507127299005840385881549)
      ·
        refine ⟨14440172737127190144705581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38507127299005840385881549 14440172737127190144705581)
        ·
          refine ⟨5415064776422696304264593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14440172737127190144705581 5415064776422696304264593)
          ·
            refine ⟨4061298582317022228198445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5415064776422696304264593 4061298582317022228198445)
            ·
              refine ⟨1522986968368883335574417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4061298582317022228198445 1522986968368883335574417)
              ·
                refine ⟨1142240226276662501680813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1522986968368883335574417 1142240226276662501680813)
                ·
                  refine ⟨428340084853748438130305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1142240226276662501680813 428340084853748438130305)
                  ·
                    rfl

theorem cell20_938463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 3, 2, 3].length) (baseStart_938463 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_938463 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_938463 prefixEnd_938463 := by exact prefixLift 938463
  have htrace : WordTrace (prefixWord ++ tailWord_938463) baseStart_938463 baseEnd_938463 := by
    simpa [prefixWord, tailWord_938463, baseEnd_938463] using wordTrace_append hprefix tailTrace_938463
  have hstable : (prefixWord ++ tailWord_938463).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938463).length < 2 ^ (prefixWord ++ tailWord_938463).sum := by decide
  have hdescent : baseEnd_938463 < baseStart_938463 := by decide
  rcases family_descends (prefixWord ++ tailWord_938463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938522 : List Nat := [3, 1, 1, 3, 1, 1, 4, 1, 5]
def baseStart_938522 : Nat := 118140960795 + 938522 * 2 ^ 59
def prefixEnd_938522 : Nat := 4983230072969 + 3 ^ 40 * 938522 * 2
def baseEnd_938522 : Nat := 428367014061406455163397

theorem tailTrace_938522 : CollatzResearch.WordTrace tailWord_938522 prefixEnd_938522 428367014061406455163397 := by
  unfold tailWord_938522
  simp only [CollatzResearch.WordTrace]
  refine ⟨8557677376475638910406455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22820473003935037094417213 8557677376475638910406455)
  ·
    refine ⟨12836516064713458365609683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8557677376475638910406455 12836516064713458365609683)
    ·
      refine ⟨19254774097070187548414525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12836516064713458365609683 19254774097070187548414525)
      ·
        refine ⟨7220540286401320330655447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19254774097070187548414525 7220540286401320330655447)
        ·
          refine ⟨10830810429601980495983171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7220540286401320330655447 10830810429601980495983171)
          ·
            refine ⟨16246215644402970743974757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10830810429601980495983171 16246215644402970743974757)
            ·
              refine ⟨3046165433325557014495267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16246215644402970743974757 3046165433325557014495267)
              ·
                refine ⟨4569248149988335521742901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3046165433325557014495267 4569248149988335521742901)
                ·
                  refine ⟨428367014061406455163397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4569248149988335521742901 428367014061406455163397)
                  ·
                    rfl

theorem cell20_938522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 1, 5].length) (baseStart_938522 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_938522 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_938522 prefixEnd_938522 := by exact prefixLift 938522
  have htrace : WordTrace (prefixWord ++ tailWord_938522) baseStart_938522 baseEnd_938522 := by
    simpa [prefixWord, tailWord_938522, baseEnd_938522] using wordTrace_append hprefix tailTrace_938522
  have hstable : (prefixWord ++ tailWord_938522).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938522).length < 2 ^ (prefixWord ++ tailWord_938522).sum := by decide
  have hdescent : baseEnd_938522 < baseStart_938522 := by decide
  rcases family_descends (prefixWord ++ tailWord_938522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938525 : List Nat := [1, 4, 2, 2, 1, 4, 1, 1, 4]
def baseStart_938525 : Nat := 118140960795 + 938525 * 2 ^ 59
def prefixEnd_938525 : Nat := 4983230072969 + 3 ^ 40 * 938525 * 2
def baseEnd_938525 : Nat := 428368383343151778063385

theorem tailTrace_938525 : CollatzResearch.WordTrace tailWord_938525 prefixEnd_938525 428368383343151778063385 := by
  unfold tailWord_938525
  simp only [CollatzResearch.WordTrace]
  refine ⟨34230818924891687153985029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22820545949927791435990019 34230818924891687153985029)
  ·
    refine ⟨6418278548417191341372193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34230818924891687153985029 6418278548417191341372193)
    ·
      refine ⟨4813708911312893506029145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6418278548417191341372193 4813708911312893506029145)
      ·
        refine ⟨3610281683484670129521859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4813708911312893506029145 3610281683484670129521859)
        ·
          refine ⟨5415422525227005194282789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3610281683484670129521859 5415422525227005194282789)
          ·
            refine ⟨1015391723480063473928023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5415422525227005194282789 1015391723480063473928023)
            ·
              refine ⟨1523087585220095210892035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1015391723480063473928023 1523087585220095210892035)
              ·
                refine ⟨2284631377830142816338053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1523087585220095210892035 2284631377830142816338053)
                ·
                  refine ⟨428368383343151778063385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2284631377830142816338053 428368383343151778063385)
                  ·
                    rfl

theorem cell20_938525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 1, 1, 4].length) (baseStart_938525 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_938525 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_938525 prefixEnd_938525 := by exact prefixLift 938525
  have htrace : WordTrace (prefixWord ++ tailWord_938525) baseStart_938525 baseEnd_938525 := by
    simpa [prefixWord, tailWord_938525, baseEnd_938525] using wordTrace_append hprefix tailTrace_938525
  have hstable : (prefixWord ++ tailWord_938525).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938525).length < 2 ^ (prefixWord ++ tailWord_938525).sum := by decide
  have hdescent : baseEnd_938525 < baseStart_938525 := by decide
  rcases family_descends (prefixWord ++ tailWord_938525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938535 : List Nat := [1, 1, 7, 2, 1, 1, 1, 3, 3]
def baseStart_938535 : Nat := 118140960795 + 938535 * 2 ^ 59
def prefixEnd_938535 : Nat := 4983230072969 + 3 ^ 40 * 938535 * 2
def baseEnd_938535 : Nat := 428372947615636187730011

theorem tailTrace_938535 : CollatzResearch.WordTrace tailWord_938535 prefixEnd_938535 428372947615636187730011 := by
  unfold tailWord_938535
  simp only [CollatzResearch.WordTrace]
  refine ⟨34231183654855458861849059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22820789103236972574566039 34231183654855458861849059)
  ·
    refine ⟨51346775482283188292773589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34231183654855458861849059 51346775482283188292773589)
    ·
      refine ⟨1203440050366012225611881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 51346775482283188292773589 1203440050366012225611881)
      ·
        refine ⟨902580037774509169208911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1203440050366012225611881 902580037774509169208911)
        ·
          refine ⟨1353870056661763753813367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 902580037774509169208911 1353870056661763753813367)
          ·
            refine ⟨2030805084992645630720051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1353870056661763753813367 2030805084992645630720051)
            ·
              refine ⟨3046207627488968446080077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2030805084992645630720051 3046207627488968446080077)
              ·
                refine ⟨1142327860308363167280029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3046207627488968446080077 1142327860308363167280029)
                ·
                  refine ⟨428372947615636187730011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1142327860308363167280029 428372947615636187730011)
                  ·
                    rfl

theorem cell20_938535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 3, 3].length) (baseStart_938535 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_938535 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_938535 prefixEnd_938535 := by exact prefixLift 938535
  have htrace : WordTrace (prefixWord ++ tailWord_938535) baseStart_938535 baseEnd_938535 := by
    simpa [prefixWord, tailWord_938535, baseEnd_938535] using wordTrace_append hprefix tailTrace_938535
  have hstable : (prefixWord ++ tailWord_938535).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938535).length < 2 ^ (prefixWord ++ tailWord_938535).sum := by decide
  have hdescent : baseEnd_938535 < baseStart_938535 := by decide
  rcases family_descends (prefixWord ++ tailWord_938535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938577 : List Nat := [1, 2, 2, 1, 3, 4, 2, 2, 3]
def baseStart_938577 : Nat := 118140960795 + 938577 * 2 ^ 59
def prefixEnd_938577 : Nat := 4983230072969 + 3 ^ 40 * 938577 * 2
def baseEnd_938577 : Nat := 428392117560070708329839

theorem tailTrace_938577 : CollatzResearch.WordTrace tailWord_938577 prefixEnd_938577 428392117560070708329839 := by
  unfold tailWord_938577
  simp only [CollatzResearch.WordTrace]
  refine ⟨34232715520703300034877985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22821810347135533356585323 34232715520703300034877985)
  ·
    refine ⟨25674536640527475026158489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34232715520703300034877985 25674536640527475026158489)
    ·
      refine ⟨19255902480395606269618867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25674536640527475026158489 19255902480395606269618867)
      ·
        refine ⟨28883853720593409404428301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19255902480395606269618867 28883853720593409404428301)
        ·
          refine ⟨10831445145222528526660613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28883853720593409404428301 10831445145222528526660613)
          ·
            refine ⟨2030895964729224098748865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10831445145222528526660613 2030895964729224098748865)
            ·
              refine ⟨1523171973546918074061649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2030895964729224098748865 1523171973546918074061649)
              ·
                refine ⟨1142378980160188555546237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1523171973546918074061649 1142378980160188555546237)
                ·
                  refine ⟨428392117560070708329839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1142378980160188555546237 428392117560070708329839)
                  ·
                    rfl

theorem cell20_938577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 2, 2, 3].length) (baseStart_938577 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_938577 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_938577 prefixEnd_938577 := by exact prefixLift 938577
  have htrace : WordTrace (prefixWord ++ tailWord_938577) baseStart_938577 baseEnd_938577 := by
    simpa [prefixWord, tailWord_938577, baseEnd_938577] using wordTrace_append hprefix tailTrace_938577
  have hstable : (prefixWord ++ tailWord_938577).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938577).length < 2 ^ (prefixWord ++ tailWord_938577).sum := by decide
  have hdescent : baseEnd_938577 < baseStart_938577 := by decide
  rcases family_descends (prefixWord ++ tailWord_938577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938580 : List Nat := [2, 4, 1, 1, 1, 3, 4, 2, 2]
def baseStart_938580 : Nat := 118140960795 + 938580 * 2 ^ 59
def prefixEnd_938580 : Nat := 4983230072969 + 3 ^ 40 * 938580 * 2
def baseEnd_938580 : Nat := 428393486841816031229827

theorem tailTrace_938580 : CollatzResearch.WordTrace tailWord_938580 prefixEnd_938580 428393486841816031229827 := by
  unfold tailWord_938580
  simp only [CollatzResearch.WordTrace]
  refine ⟨17116412469846215773618597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22821883293128287698158129 17116412469846215773618597)
  ·
    refine ⟨3209327338096165457553487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17116412469846215773618597 3209327338096165457553487)
    ·
      refine ⟨4813991007144248186330231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3209327338096165457553487 4813991007144248186330231)
      ·
        refine ⟨7220986510716372279495347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4813991007144248186330231 7220986510716372279495347)
        ·
          refine ⟨10831479766074558419243021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7220986510716372279495347 10831479766074558419243021)
          ·
            refine ⟨4061804912277959407216133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10831479766074558419243021 4061804912277959407216133)
            ·
              refine ⟨761588421052117388853025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4061804912277959407216133 761588421052117388853025)
              ·
                refine ⟨571191315789088041639769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 761588421052117388853025 571191315789088041639769)
                ·
                  refine ⟨428393486841816031229827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 571191315789088041639769 428393486841816031229827)
                  ·
                    rfl

theorem cell20_938580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 4, 2, 2].length) (baseStart_938580 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_938580 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_938580 prefixEnd_938580 := by exact prefixLift 938580
  have htrace : WordTrace (prefixWord ++ tailWord_938580) baseStart_938580 baseEnd_938580 := by
    simpa [prefixWord, tailWord_938580, baseEnd_938580] using wordTrace_append hprefix tailTrace_938580
  have hstable : (prefixWord ++ tailWord_938580).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938580).length < 2 ^ (prefixWord ++ tailWord_938580).sum := by decide
  have hdescent : baseEnd_938580 < baseStart_938580 := by decide
  rcases family_descends (prefixWord ++ tailWord_938580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938608 : List Nat := [2, 1, 1, 1, 7, 1, 3, 4]
def baseStart_938608 : Nat := 118140960795 + 938608 * 2 ^ 59
def prefixEnd_938608 : Nat := 4983230072969 + 3 ^ 40 * 938608 * 2
def baseEnd_938608 : Nat := 142802088934924126098793

theorem tailTrace_938608 : CollatzResearch.WordTrace tailWord_938608 prefixEnd_938608 142802088934924126098793 := by
  unfold tailWord_938608
  simp only [CollatzResearch.WordTrace]
  refine ⟨17116923091795496164628239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22822564122393994886170985 17116923091795496164628239)
  ·
    refine ⟨25675384637693244246942359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17116923091795496164628239 25675384637693244246942359)
    ·
      refine ⟨38513076956539866370413539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25675384637693244246942359 38513076956539866370413539)
      ·
        refine ⟨57769615434809799555620309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38513076956539866370413539 57769615434809799555620309)
        ·
          refine ⟨1353975361753354677084851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 57769615434809799555620309 1353975361753354677084851)
          ·
            refine ⟨2030963042630032015627277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1353975361753354677084851 2030963042630032015627277)
            ·
              refine ⟨761611140986262005860229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2030963042630032015627277 761611140986262005860229)
              ·
                refine ⟨142802088934924126098793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 761611140986262005860229 142802088934924126098793)
                ·
                  rfl

theorem cell20_938608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 3, 4].length) (baseStart_938608 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_938608 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_938608 prefixEnd_938608 := by exact prefixLift 938608
  have htrace : WordTrace (prefixWord ++ tailWord_938608) baseStart_938608 baseEnd_938608 := by
    simpa [prefixWord, tailWord_938608, baseEnd_938608] using wordTrace_append hprefix tailTrace_938608
  have hstable : (prefixWord ++ tailWord_938608).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938608).length < 2 ^ (prefixWord ++ tailWord_938608).sum := by decide
  have hdescent : baseEnd_938608 < baseStart_938608 := by decide
  rcases family_descends (prefixWord ++ tailWord_938608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938636 : List Nat := [2, 2, 1, 2, 1, 1, 2, 6, 3]
def baseStart_938636 : Nat := 118140960795 + 938636 * 2 ^ 59
def prefixEnd_938636 : Nat := 4983230072969 + 3 ^ 40 * 938636 * 2
def baseEnd_938636 : Nat := 428419046767728725362931

theorem tailTrace_938636 : CollatzResearch.WordTrace tailWord_938636 prefixEnd_938636 428419046767728725362931 := by
  unfold tailWord_938636
  simp only [CollatzResearch.WordTrace]
  refine ⟨17117433713744776555637881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22823244951659702074183841 17117433713744776555637881)
  ·
    refine ⟨12838075285308582416728411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17117433713744776555637881 12838075285308582416728411)
    ·
      refine ⟨19257112927962873625092617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12838075285308582416728411 19257112927962873625092617)
      ·
        refine ⟨14442834695972155218819463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19257112927962873625092617 14442834695972155218819463)
        ·
          refine ⟨21664252043958232828229195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14442834695972155218819463 21664252043958232828229195)
          ·
            refine ⟨32496378065937349242343793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21664252043958232828229195 32496378065937349242343793)
            ·
              refine ⟨24372283549453011931757845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32496378065937349242343793 24372283549453011931757845)
              ·
                refine ⟨1142450791380609934301149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 24372283549453011931757845 1142450791380609934301149)
                ·
                  refine ⟨428419046767728725362931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1142450791380609934301149 428419046767728725362931)
                  ·
                    rfl

theorem cell20_938636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 6, 3].length) (baseStart_938636 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_938636 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_938636 prefixEnd_938636 := by exact prefixLift 938636
  have htrace : WordTrace (prefixWord ++ tailWord_938636) baseStart_938636 baseEnd_938636 := by
    simpa [prefixWord, tailWord_938636, baseEnd_938636] using wordTrace_append hprefix tailTrace_938636
  have hstable : (prefixWord ++ tailWord_938636).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938636).length < 2 ^ (prefixWord ++ tailWord_938636).sum := by decide
  have hdescent : baseEnd_938636 < baseStart_938636 := by decide
  rcases family_descends (prefixWord ++ tailWord_938636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938673 : List Nat := [1, 2, 2, 6, 1, 2, 1, 3, 2]
def baseStart_938673 : Nat := 118140960795 + 938673 * 2 ^ 59
def prefixEnd_938673 : Nat := 4983230072969 + 3 ^ 40 * 938673 * 2
def baseEnd_938673 : Nat := 428435934575921041129447

theorem tailTrace_938673 : CollatzResearch.WordTrace tailWord_938673 prefixEnd_938673 428435934575921041129447 := by
  unfold tailWord_938673
  simp only [CollatzResearch.WordTrace]
  refine ⟨34236216928355508430372673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22824144618903672286915115 34236216928355508430372673)
  ·
    refine ⟨25677162696266631322779505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34236216928355508430372673 25677162696266631322779505)
    ·
      refine ⟨19257872022199973492084629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25677162696266631322779505 19257872022199973492084629)
      ·
        refine ⟨902712751040623757441467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 19257872022199973492084629 902712751040623757441467)
        ·
          refine ⟨1354069126560935636162201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 902712751040623757441467 1354069126560935636162201)
          ·
            refine ⟨1015551844920701727121651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1354069126560935636162201 1015551844920701727121651)
            ·
              refine ⟨1523327767381052590682477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1015551844920701727121651 1523327767381052590682477)
              ·
                refine ⟨571247912767894721505929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1523327767381052590682477 571247912767894721505929)
                ·
                  refine ⟨428435934575921041129447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 571247912767894721505929 428435934575921041129447)
                  ·
                    rfl

theorem cell20_938673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 1, 3, 2].length) (baseStart_938673 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_938673 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_938673 prefixEnd_938673 := by exact prefixLift 938673
  have htrace : WordTrace (prefixWord ++ tailWord_938673) baseStart_938673 baseEnd_938673 := by
    simpa [prefixWord, tailWord_938673, baseEnd_938673] using wordTrace_append hprefix tailTrace_938673
  have hstable : (prefixWord ++ tailWord_938673).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938673).length < 2 ^ (prefixWord ++ tailWord_938673).sum := by decide
  have hdescent : baseEnd_938673 < baseStart_938673 := by decide
  rcases family_descends (prefixWord ++ tailWord_938673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938688 : List Nat := [2, 1, 1, 2, 4, 2, 8]
def baseStart_938688 : Nat := 118140960795 + 938688 * 2 ^ 59
def prefixEnd_938688 : Nat := 4983230072969 + 3 ^ 40 * 938688 * 2
def baseEnd_938688 : Nat := 47604753442738628403265

theorem tailTrace_938688 : CollatzResearch.WordTrace tailWord_938688 prefixEnd_938688 47604753442738628403265 := by
  unfold tailWord_938688
  simp only [CollatzResearch.WordTrace]
  refine ⟨17118382011650582996084359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22824509348867443994779145 17118382011650582996084359)
  ·
    refine ⟨25677573017475874494126539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17118382011650582996084359 25677573017475874494126539)
    ·
      refine ⟨38516359526213811741189809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25677573017475874494126539 38516359526213811741189809)
      ·
        refine ⟨28887269644660358805892357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38516359526213811741189809 28887269644660358805892357)
        ·
          refine ⟨5416363058373817276104817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28887269644660358805892357 5416363058373817276104817)
          ·
            refine ⟨4062272293780362957078613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5416363058373817276104817 4062272293780362957078613)
            ·
              refine ⟨47604753442738628403265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4062272293780362957078613 47604753442738628403265)
              ·
                rfl

theorem cell20_938688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 8].length) (baseStart_938688 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_938688 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_938688 prefixEnd_938688 := by exact prefixLift 938688
  have htrace : WordTrace (prefixWord ++ tailWord_938688) baseStart_938688 baseEnd_938688 := by
    simpa [prefixWord, tailWord_938688, baseEnd_938688] using wordTrace_append hprefix tailTrace_938688
  have hstable : (prefixWord ++ tailWord_938688).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938688).length < 2 ^ (prefixWord ++ tailWord_938688).sum := by decide
  have hdescent : baseEnd_938688 < baseStart_938688 := by decide
  rcases family_descends (prefixWord ++ tailWord_938688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938698 : List Nat := [3, 1, 2, 1, 4, 1, 3, 1, 4]
def baseStart_938698 : Nat := 118140960795 + 938698 * 2 ^ 59
def prefixEnd_938698 : Nat := 4983230072969 + 3 ^ 40 * 938698 * 2
def baseEnd_938698 : Nat := 428447345257132065296011

theorem tailTrace_938698 : CollatzResearch.WordTrace tailWord_938698 prefixEnd_938698 428447345257132065296011 := by
  unfold tailWord_938698
  simp only [CollatzResearch.WordTrace]
  refine ⟨8559282188316234425008187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22824752502176625133355165 8559282188316234425008187)
  ·
    refine ⟨12838923282474351637512281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8559282188316234425008187 12838923282474351637512281)
    ·
      refine ⟨9629192461855763728134211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12838923282474351637512281 9629192461855763728134211)
      ·
        refine ⟨14443788692783645592201317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9629192461855763728134211 14443788692783645592201317)
        ·
          refine ⟨2708210379896933548537747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14443788692783645592201317 2708210379896933548537747)
          ·
            refine ⟨4062315569845400322806621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2708210379896933548537747 4062315569845400322806621)
            ·
              refine ⟨1523368338692025121052483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4062315569845400322806621 1523368338692025121052483)
              ·
                refine ⟨2285052508038037681578725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1523368338692025121052483 2285052508038037681578725)
                ·
                  refine ⟨428447345257132065296011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2285052508038037681578725 428447345257132065296011)
                  ·
                    rfl

theorem cell20_938698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 3, 1, 4].length) (baseStart_938698 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_938698 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_938698 prefixEnd_938698 := by exact prefixLift 938698
  have htrace : WordTrace (prefixWord ++ tailWord_938698) baseStart_938698 baseEnd_938698 := by
    simpa [prefixWord, tailWord_938698, baseEnd_938698] using wordTrace_append hprefix tailTrace_938698
  have hstable : (prefixWord ++ tailWord_938698).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938698).length < 2 ^ (prefixWord ++ tailWord_938698).sum := by decide
  have hdescent : baseEnd_938698 < baseStart_938698 := by decide
  rcases family_descends (prefixWord ++ tailWord_938698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938701 : List Nat := [1, 6, 2, 1, 2, 1, 2, 5]
def baseStart_938701 : Nat := 118140960795 + 938701 * 2 ^ 59
def prefixEnd_938701 : Nat := 4983230072969 + 3 ^ 40 * 938701 * 2
def baseEnd_938701 : Nat := 142816238179625796065333

theorem tailTrace_938701 : CollatzResearch.WordTrace tailWord_938701 prefixEnd_938701 142816238179625796065333 := by
  unfold tailWord_938701
  simp only [CollatzResearch.WordTrace]
  refine ⟨34237238172254069212391957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22824825448169379474927971 34237238172254069212391957)
  ·
    refine ⟨1604870539324409494330873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 34237238172254069212391957 1604870539324409494330873)
    ·
      refine ⟨1203652904493307120748155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1604870539324409494330873 1203652904493307120748155)
      ·
        refine ⟨1805479356739960681122233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1203652904493307120748155 1805479356739960681122233)
        ·
          refine ⟨1354109517554970510841675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1805479356739960681122233 1354109517554970510841675)
          ·
            refine ⟨2031164276332455766262513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1354109517554970510841675 2031164276332455766262513)
            ·
              refine ⟨1523373207249341824696885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2031164276332455766262513 1523373207249341824696885)
              ·
                refine ⟨142816238179625796065333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1523373207249341824696885 142816238179625796065333)
                ·
                  rfl

theorem cell20_938701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 2, 5].length) (baseStart_938701 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_938701 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_938701 prefixEnd_938701 := by exact prefixLift 938701
  have htrace : WordTrace (prefixWord ++ tailWord_938701) baseStart_938701 baseEnd_938701 := by
    simpa [prefixWord, tailWord_938701, baseEnd_938701] using wordTrace_append hprefix tailTrace_938701
  have hstable : (prefixWord ++ tailWord_938701).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938701).length < 2 ^ (prefixWord ++ tailWord_938701).sum := by decide
  have hdescent : baseEnd_938701 < baseStart_938701 := by decide
  rcases family_descends (prefixWord ++ tailWord_938701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938708 : List Nat := [2, 4, 1, 3, 2, 1, 1, 3, 3]
def baseStart_938708 : Nat := 118140960795 + 938708 * 2 ^ 59
def prefixEnd_938708 : Nat := 4983230072969 + 3 ^ 40 * 938708 * 2
def baseEnd_938708 : Nat := 428451909529616474962637

theorem tailTrace_938708 : CollatzResearch.WordTrace tailWord_938708 prefixEnd_938708 428451909529616474962637 := by
  unfold tailWord_938708
  simp only [CollatzResearch.WordTrace]
  refine ⟨17118746741614354703948389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22824995655485806271931185 17118746741614354703948389)
  ·
    refine ⟨3209765014052691506990323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17118746741614354703948389 3209765014052691506990323)
    ·
      refine ⟨4814647521079037260485485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3209765014052691506990323 4814647521079037260485485)
      ·
        refine ⟨1805492820404638972682057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4814647521079037260485485 1805492820404638972682057)
        ·
          refine ⟨1354119615303479229511543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1805492820404638972682057 1354119615303479229511543)
          ·
            refine ⟨2031179422955218844267315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1354119615303479229511543 2031179422955218844267315)
            ·
              refine ⟨3046769134432828266400973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2031179422955218844267315 3046769134432828266400973)
              ·
                refine ⟨1142538425412310599900365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3046769134432828266400973 1142538425412310599900365)
                ·
                  refine ⟨428451909529616474962637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1142538425412310599900365 428451909529616474962637)
                  ·
                    rfl

theorem cell20_938708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 3, 3].length) (baseStart_938708 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_938708 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_938708 prefixEnd_938708 := by exact prefixLift 938708
  have htrace : WordTrace (prefixWord ++ tailWord_938708) baseStart_938708 baseEnd_938708 := by
    simpa [prefixWord, tailWord_938708, baseEnd_938708] using wordTrace_append hprefix tailTrace_938708
  have hstable : (prefixWord ++ tailWord_938708).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938708).length < 2 ^ (prefixWord ++ tailWord_938708).sum := by decide
  have hdescent : baseEnd_938708 < baseStart_938708 := by decide
  rcases family_descends (prefixWord ++ tailWord_938708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938736 : List Nat := [2, 1, 1, 1, 3, 1, 4, 5, 2]
def baseStart_938736 : Nat := 118140960795 + 938736 * 2 ^ 59
def prefixEnd_938736 : Nat := 4983230072969 + 3 ^ 40 * 938736 * 2
def baseEnd_938736 : Nat := 428464689492572822029189

theorem tailTrace_938736 : CollatzResearch.WordTrace tailWord_938736 prefixEnd_938736 428464689492572822029189 := by
  unfold tailWord_938736
  simp only [CollatzResearch.WordTrace]
  refine ⟨17119257363563635094958031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22825676484751513459944041 17119257363563635094958031)
  ·
    refine ⟨25678886045345452642437047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17119257363563635094958031 25678886045345452642437047)
    ·
      refine ⟨38518329068018178963655571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25678886045345452642437047 38518329068018178963655571)
      ·
        refine ⟨57777493602027268445483357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38518329068018178963655571 57777493602027268445483357)
        ·
          refine ⟨21666560100760225667056259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57777493602027268445483357 21666560100760225667056259)
          ·
            refine ⟨32499840151140338500584389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21666560100760225667056259 32499840151140338500584389)
            ·
              refine ⟨6093720028338813468859573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32499840151140338500584389 6093720028338813468859573)
              ·
                refine ⟨571286252656763762705585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6093720028338813468859573 571286252656763762705585)
                ·
                  refine ⟨428464689492572822029189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 571286252656763762705585 428464689492572822029189)
                  ·
                    rfl

theorem cell20_938736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 5, 2].length) (baseStart_938736 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_938736 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_938736 prefixEnd_938736 := by exact prefixLift 938736
  have htrace : WordTrace (prefixWord ++ tailWord_938736) baseStart_938736 baseEnd_938736 := by
    simpa [prefixWord, tailWord_938736, baseEnd_938736] using wordTrace_append hprefix tailTrace_938736
  have hstable : (prefixWord ++ tailWord_938736).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938736).length < 2 ^ (prefixWord ++ tailWord_938736).sum := by decide
  have hdescent : baseEnd_938736 < baseStart_938736 := by decide
  rcases family_descends (prefixWord ++ tailWord_938736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938802 : List Nat := [3, 2, 1, 1, 3, 1, 9]
def baseStart_938802 : Nat := 118140960795 + 938802 * 2 ^ 59
def prefixEnd_938802 : Nat := 4983230072969 + 3 ^ 40 * 938802 * 2
def baseEnd_938802 : Nat := 47610534854552213980991

theorem tailTrace_938802 : CollatzResearch.WordTrace tailWord_938802 prefixEnd_938802 47610534854552213980991 := by
  unfold tailWord_938802
  simp only [CollatzResearch.WordTrace]
  refine ⟨8560230486222040865454665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22827281296592108974545773 8560230486222040865454665)
  ·
    refine ⟨6420172864666530649090999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8560230486222040865454665 6420172864666530649090999)
    ·
      refine ⟨9630259296999795973636499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6420172864666530649090999 9630259296999795973636499)
      ·
        refine ⟨14445388945499693960454749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9630259296999795973636499 14445388945499693960454749)
        ·
          refine ⟨5417020854562385235170531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14445388945499693960454749 5417020854562385235170531)
          ·
            refine ⟨8125531281843577852755797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5417020854562385235170531 8125531281843577852755797)
            ·
              refine ⟨47610534854552213980991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8125531281843577852755797 47610534854552213980991)
              ·
                rfl

theorem cell20_938802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 9].length) (baseStart_938802 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_938802 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_938802 prefixEnd_938802 := by exact prefixLift 938802
  have htrace : WordTrace (prefixWord ++ tailWord_938802) baseStart_938802 baseEnd_938802 := by
    simpa [prefixWord, tailWord_938802, baseEnd_938802] using wordTrace_append hprefix tailTrace_938802
  have hstable : (prefixWord ++ tailWord_938802).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938802).length < 2 ^ (prefixWord ++ tailWord_938802).sum := by decide
  have hdescent : baseEnd_938802 < baseStart_938802 := by decide
  rcases family_descends (prefixWord ++ tailWord_938802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938805 : List Nat := [1, 3, 3, 1, 3, 1, 3, 2, 3]
def baseStart_938805 : Nat := 118140960795 + 938805 * 2 ^ 59
def prefixEnd_938805 : Nat := 4983230072969 + 3 ^ 40 * 938805 * 2
def baseEnd_938805 : Nat := 428496182972715248728907

theorem tailTrace_938805 : CollatzResearch.WordTrace tailWord_938805 prefixEnd_938805 428496182972715248728907 := by
  unfold tailWord_938805
  simp only [CollatzResearch.WordTrace]
  refine ⟨34241031363877294974177869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22827354242584863316118579 34241031363877294974177869)
  ·
    refine ⟨12840386761453985615316701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34241031363877294974177869 12840386761453985615316701)
    ·
      refine ⟨4815145035545244605743763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12840386761453985615316701 4815145035545244605743763)
      ·
        refine ⟨7222717553317866908615645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4815145035545244605743763 7222717553317866908615645)
        ·
          refine ⟨2708519082494200090730867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7222717553317866908615645 2708519082494200090730867)
          ·
            refine ⟨4062778623741300136096301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2708519082494200090730867 4062778623741300136096301)
            ·
              refine ⟨1523541983902987551036113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4062778623741300136096301 1523541983902987551036113)
              ·
                refine ⟨1142656487927240663277085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1523541983902987551036113 1142656487927240663277085)
                ·
                  refine ⟨428496182972715248728907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1142656487927240663277085 428496182972715248728907)
                  ·
                    rfl

theorem cell20_938805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 3, 2, 3].length) (baseStart_938805 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_938805 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_938805 prefixEnd_938805 := by exact prefixLift 938805
  have htrace : WordTrace (prefixWord ++ tailWord_938805) baseStart_938805 baseEnd_938805 := by
    simpa [prefixWord, tailWord_938805, baseEnd_938805] using wordTrace_append hprefix tailTrace_938805
  have hstable : (prefixWord ++ tailWord_938805).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938805).length < 2 ^ (prefixWord ++ tailWord_938805).sum := by decide
  have hdescent : baseEnd_938805 < baseStart_938805 := by decide
  rcases family_descends (prefixWord ++ tailWord_938805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938847 : List Nat := [1, 1, 2, 3, 1, 3, 1, 1, 7]
def baseStart_938847 : Nat := 118140960795 + 938847 * 2 ^ 59
def prefixEnd_938847 : Nat := 4983230072969 + 3 ^ 40 * 938847 * 2
def baseEnd_938847 : Nat := 428515352917149769328735

theorem tailTrace_938847 : CollatzResearch.WordTrace tailWord_938847 prefixEnd_938847 428515352917149769328735 := by
  unfold tailWord_938847
  simp only [CollatzResearch.WordTrace]
  refine ⟨34242563229725136147206795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22828375486483424098137863 34242563229725136147206795)
  ·
    refine ⟨51363844844587704220810193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34242563229725136147206795 51363844844587704220810193)
    ·
      refine ⟨38522883633440778165607645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51363844844587704220810193 38522883633440778165607645)
      ·
        refine ⟨14446081362540291812102867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38522883633440778165607645 14446081362540291812102867)
        ·
          refine ⟨21669122043810437718154301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14446081362540291812102867 21669122043810437718154301)
          ·
            refine ⟨8125920766428914144307863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21669122043810437718154301 8125920766428914144307863)
            ·
              refine ⟨12188881149643371216461795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8125920766428914144307863 12188881149643371216461795)
              ·
                refine ⟨18283321724465056824692693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12188881149643371216461795 18283321724465056824692693)
                ·
                  refine ⟨428515352917149769328735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18283321724465056824692693 428515352917149769328735)
                  ·
                    rfl

theorem cell20_938847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 7].length) (baseStart_938847 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_938847 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_938847 prefixEnd_938847 := by exact prefixLift 938847
  have htrace : WordTrace (prefixWord ++ tailWord_938847) baseStart_938847 baseEnd_938847 := by
    simpa [prefixWord, tailWord_938847, baseEnd_938847] using wordTrace_append hprefix tailTrace_938847
  have hstable : (prefixWord ++ tailWord_938847).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938847).length < 2 ^ (prefixWord ++ tailWord_938847).sum := by decide
  have hdescent : baseEnd_938847 < baseStart_938847 := by decide
  rcases family_descends (prefixWord ++ tailWord_938847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938961 : List Nat := [1, 2, 2, 1, 2, 1, 4, 2, 5]
def baseStart_938961 : Nat := 118140960795 + 938961 * 2 ^ 59
def prefixEnd_938961 : Nat := 4983230072969 + 3 ^ 40 * 938961 * 2
def baseEnd_938961 : Nat := 428567385623472039528269

theorem tailTrace_938961 : CollatzResearch.WordTrace tailWord_938961 prefixEnd_938961 428567385623472039528269 := by
  unfold tailWord_938961
  simp only [CollatzResearch.WordTrace]
  refine ⟨34246721151312133616856737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22831147434208089077904491 34246721151312133616856737)
  ·
    refine ⟨25685040863484100212642553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34246721151312133616856737 25685040863484100212642553)
    ·
      refine ⟨19263780647613075159481915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25685040863484100212642553 19263780647613075159481915)
      ·
        refine ⟨28895670971419612739222873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19263780647613075159481915 28895670971419612739222873)
        ·
          refine ⟨21671753228564709554417155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28895670971419612739222873 21671753228564709554417155)
          ·
            refine ⟨32507629842847064331625733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21671753228564709554417155 32507629842847064331625733)
            ·
              refine ⟨6095180595533824562179825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32507629842847064331625733 6095180595533824562179825)
              ·
                refine ⟨4571385446650368421634869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6095180595533824562179825 4571385446650368421634869)
                ·
                  refine ⟨428567385623472039528269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4571385446650368421634869 428567385623472039528269)
                  ·
                    rfl

theorem cell20_938961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 2, 5].length) (baseStart_938961 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_938961 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_938961 prefixEnd_938961 := by exact prefixLift 938961
  have htrace : WordTrace (prefixWord ++ tailWord_938961) baseStart_938961 baseEnd_938961 := by
    simpa [prefixWord, tailWord_938961, baseEnd_938961] using wordTrace_append hprefix tailTrace_938961
  have hstable : (prefixWord ++ tailWord_938961).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938961).length < 2 ^ (prefixWord ++ tailWord_938961).sum := by decide
  have hdescent : baseEnd_938961 < baseStart_938961 := by decide
  rcases family_descends (prefixWord ++ tailWord_938961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_938981 : List Nat := [1, 3, 1, 6, 1, 1, 2, 1, 4]
def baseStart_938981 : Nat := 118140960795 + 938981 * 2 ^ 59
def prefixEnd_938981 : Nat := 4983230072969 + 3 ^ 40 * 938981 * 2
def baseEnd_938981 : Nat := 428576514168440858861521

theorem tailTrace_938981 : CollatzResearch.WordTrace tailWord_938981 prefixEnd_938981 428576514168440858861521 := by
  unfold tailWord_938981
  simp only [CollatzResearch.WordTrace]
  refine ⟨34247450611239677032584797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22831633740826451355056531 34247450611239677032584797)
  ·
    refine ⟨12842793979214878887219299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34247450611239677032584797 12842793979214878887219299)
    ·
      refine ⟨19264190968822318330828949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12842793979214878887219299 19264190968822318330828949)
      ·
        refine ⟨903008951663546171757607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 19264190968822318330828949 903008951663546171757607)
        ·
          refine ⟨1354513427495319257636411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 903008951663546171757607 1354513427495319257636411)
          ·
            refine ⟨2031770141242978886454617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1354513427495319257636411 2031770141242978886454617)
            ·
              refine ⟨1523827605932234164840963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2031770141242978886454617 1523827605932234164840963)
              ·
                refine ⟨2285741408898351247261445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1523827605932234164840963 2285741408898351247261445)
                ·
                  refine ⟨428576514168440858861521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2285741408898351247261445 428576514168440858861521)
                  ·
                    rfl

theorem cell20_938981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 2, 1, 4].length) (baseStart_938981 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_938981 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_938981 prefixEnd_938981 := by exact prefixLift 938981
  have htrace : WordTrace (prefixWord ++ tailWord_938981) baseStart_938981 baseEnd_938981 := by
    simpa [prefixWord, tailWord_938981, baseEnd_938981] using wordTrace_append hprefix tailTrace_938981
  have hstable : (prefixWord ++ tailWord_938981).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_938981).length < 2 ^ (prefixWord ++ tailWord_938981).sum := by decide
  have hdescent : baseEnd_938981 < baseStart_938981 := by decide
  rcases family_descends (prefixWord ++ tailWord_938981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939009 : List Nat := [1, 2, 4, 1, 2, 2, 4, 4]
def baseStart_939009 : Nat := 118140960795 + 939009 * 2 ^ 59
def prefixEnd_939009 : Nat := 4983230072969 + 3 ^ 40 * 939009 * 2
def baseEnd_939009 : Nat := 142863098043799068642691

theorem tailTrace_939009 : CollatzResearch.WordTrace tailWord_939009 prefixEnd_939009 142863098043799068642691 := by
  unfold tailWord_939009
  simp only [CollatzResearch.WordTrace]
  refine ⟨34248471855138237814604081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22832314570092158543069387 34248471855138237814604081)
  ·
    refine ⟨25686353891353678360953061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34248471855138237814604081 25686353891353678360953061)
    ·
      refine ⟨4816191354628814692678699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25686353891353678360953061 4816191354628814692678699)
      ·
        refine ⟨7224287031943222039018049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4816191354628814692678699 7224287031943222039018049)
        ·
          refine ⟨5418215273957416529263537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7224287031943222039018049 5418215273957416529263537)
          ·
            refine ⟨4063661455468062396947653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5418215273957416529263537 4063661455468062396947653)
            ·
              refine ⟨761936522900261699427685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4063661455468062396947653 761936522900261699427685)
              ·
                refine ⟨142863098043799068642691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 761936522900261699427685 142863098043799068642691)
                ·
                  rfl

theorem cell20_939009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 4, 4].length) (baseStart_939009 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_939009 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_939009 prefixEnd_939009 := by exact prefixLift 939009
  have htrace : WordTrace (prefixWord ++ tailWord_939009) baseStart_939009 baseEnd_939009 := by
    simpa [prefixWord, tailWord_939009, baseEnd_939009] using wordTrace_append hprefix tailTrace_939009
  have hstable : (prefixWord ++ tailWord_939009).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939009).length < 2 ^ (prefixWord ++ tailWord_939009).sum := by decide
  have hdescent : baseEnd_939009 < baseStart_939009 := by decide
  rcases family_descends (prefixWord ++ tailWord_939009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939019 : List Nat := [1, 1, 1, 1, 6, 4, 1, 3, 2]
def baseStart_939019 : Nat := 118140960795 + 939019 * 2 ^ 59
def prefixEnd_939019 : Nat := 4983230072969 + 3 ^ 40 * 939019 * 2
def baseEnd_939019 : Nat := 428593858403881615594699

theorem tailTrace_939019 : CollatzResearch.WordTrace tailWord_939019 prefixEnd_939019 428593858403881615594699 := by
  unfold tailWord_939019
  simp only [CollatzResearch.WordTrace]
  refine ⟨34248836585102009522468111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22832557723401339681645407 34248836585102009522468111)
  ·
    refine ⟨51373254877653014283702167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34248836585102009522468111 51373254877653014283702167)
    ·
      refine ⟨77059882316479521425553251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51373254877653014283702167 77059882316479521425553251)
      ·
        refine ⟨115589823474719282138329877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77059882316479521425553251 115589823474719282138329877)
        ·
          refine ⟨5418272975377466350234213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 115589823474719282138329877 5418272975377466350234213)
          ·
            refine ⟨1015926182883274940668915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5418272975377466350234213 1015926182883274940668915)
            ·
              refine ⟨1523889274324912411003373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1015926182883274940668915 1523889274324912411003373)
              ·
                refine ⟨571458477871842154126265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1523889274324912411003373 571458477871842154126265)
                ·
                  refine ⟨428593858403881615594699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 571458477871842154126265 428593858403881615594699)
                  ·
                    rfl

theorem cell20_939019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 1, 3, 2].length) (baseStart_939019 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_939019 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_939019 prefixEnd_939019 := by exact prefixLift 939019
  have htrace : WordTrace (prefixWord ++ tailWord_939019) baseStart_939019 baseEnd_939019 := by
    simpa [prefixWord, tailWord_939019, baseEnd_939019] using wordTrace_append hprefix tailTrace_939019
  have hstable : (prefixWord ++ tailWord_939019).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939019).length < 2 ^ (prefixWord ++ tailWord_939019).sum := by decide
  have hdescent : baseEnd_939019 < baseStart_939019 := by decide
  rcases family_descends (prefixWord ++ tailWord_939019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939036 : List Nat := [2, 2, 3, 1, 4, 1, 3, 2, 2]
def baseStart_939036 : Nat := 118140960795 + 939036 * 2 ^ 59
def prefixEnd_939036 : Nat := 4983230072969 + 3 ^ 40 * 939036 * 2
def baseEnd_939036 : Nat := 428601617667105112027963

theorem tailTrace_939036 : CollatzResearch.WordTrace tailWord_939036 prefixEnd_939036 428601617667105112027963 := by
  unfold tailWord_939036
  simp only [CollatzResearch.WordTrace]
  refine ⟨17124728313020210712918481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22832971084026947617224641 17124728313020210712918481)
  ·
    refine ⟨12843546234765158034688861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17124728313020210712918481 12843546234765158034688861)
    ·
      refine ⟨4816329838036934263008323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12843546234765158034688861 4816329838036934263008323)
      ·
        refine ⟨7224494757055401394512485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4816329838036934263008323 7224494757055401394512485)
        ·
          refine ⟨1354592766947887761471091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7224494757055401394512485 1354592766947887761471091)
          ·
            refine ⟨2031889150421831642206637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1354592766947887761471091 2031889150421831642206637)
            ·
              refine ⟨761958431408186865827489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2031889150421831642206637 761958431408186865827489)
              ·
                refine ⟨571468823556140149370617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 761958431408186865827489 571468823556140149370617)
                ·
                  refine ⟨428601617667105112027963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 571468823556140149370617 428601617667105112027963)
                  ·
                    rfl

theorem cell20_939036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 3, 2, 2].length) (baseStart_939036 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_939036 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_939036 prefixEnd_939036 := by exact prefixLift 939036
  have htrace : WordTrace (prefixWord ++ tailWord_939036) baseStart_939036 baseEnd_939036 := by
    simpa [prefixWord, tailWord_939036, baseEnd_939036] using wordTrace_append hprefix tailTrace_939036
  have hstable : (prefixWord ++ tailWord_939036).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939036).length < 2 ^ (prefixWord ++ tailWord_939036).sum := by decide
  have hdescent : baseEnd_939036 < baseStart_939036 := by decide
  rcases family_descends (prefixWord ++ tailWord_939036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939047 : List Nat := [1, 1, 7, 1, 1, 1, 1, 7]
def baseStart_939047 : Nat := 118140960795 + 939047 * 2 ^ 59
def prefixEnd_939047 : Nat := 4983230072969 + 3 ^ 40 * 939047 * 2
def baseEnd_939047 : Nat := 142868879455612654220417

theorem tailTrace_939047 : CollatzResearch.WordTrace tailWord_939047 prefixEnd_939047 142868879455612654220417 := by
  unfold tailWord_939047
  simp only [CollatzResearch.WordTrace]
  refine ⟨34249857829000570304487395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22833238552667046869658263 34249857829000570304487395)
  ·
    refine ⟨51374786743500855456731093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34249857829000570304487395 51374786743500855456731093)
    ·
      refine ⟨1204096564300801299767135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 51374786743500855456731093 1204096564300801299767135)
      ·
        refine ⟨1806144846451201949650703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1204096564300801299767135 1806144846451201949650703)
        ·
          refine ⟨2709217269676802924476055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1806144846451201949650703 2709217269676802924476055)
          ·
            refine ⟨4063825904515204386714083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2709217269676802924476055 4063825904515204386714083)
            ·
              refine ⟨6095738856772806580071125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4063825904515204386714083 6095738856772806580071125)
              ·
                refine ⟨142868879455612654220417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6095738856772806580071125 142868879455612654220417)
                ·
                  rfl

theorem cell20_939047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 7].length) (baseStart_939047 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_939047 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_939047 prefixEnd_939047 := by exact prefixLift 939047
  have htrace : WordTrace (prefixWord ++ tailWord_939047) baseStart_939047 baseEnd_939047 := by
    simpa [prefixWord, tailWord_939047, baseEnd_939047] using wordTrace_append hprefix tailTrace_939047
  have hstable : (prefixWord ++ tailWord_939047).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939047).length < 2 ^ (prefixWord ++ tailWord_939047).sum := by decide
  have hdescent : baseEnd_939047 < baseStart_939047 := by decide
  rcases family_descends (prefixWord ++ tailWord_939047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939068 : List Nat := [2, 2, 2, 2, 2, 2, 2, 6]
def baseStart_939068 : Nat := 118140960795 + 939068 * 2 ^ 59
def prefixEnd_939068 : Nat := 4983230072969 + 3 ^ 40 * 939068 * 2
def baseEnd_939068 : Nat := 142872074446351740987055

theorem tailTrace_939068 : CollatzResearch.WordTrace tailWord_939068 prefixEnd_939068 142872074446351740987055 := by
  unfold tailWord_939068
  simp only [CollatzResearch.WordTrace]
  refine ⟨17125311880962245445500929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22833749174616327260667905 17125311880962245445500929)
  ·
    refine ⟨12843983910721684084125697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17125311880962245445500929 12843983910721684084125697)
    ·
      refine ⟨9632987933041263063094273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12843983910721684084125697 9632987933041263063094273)
      ·
        refine ⟨7224740949780947297320705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9632987933041263063094273 7224740949780947297320705)
        ·
          refine ⟨5418555712335710472990529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7224740949780947297320705 5418555712335710472990529)
          ·
            refine ⟨4063916784251782854742897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5418555712335710472990529 4063916784251782854742897)
            ·
              refine ⟨3047937588188837141057173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4063916784251782854742897 3047937588188837141057173)
              ·
                refine ⟨142872074446351740987055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3047937588188837141057173 142872074446351740987055)
                ·
                  rfl

theorem cell20_939068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 6].length) (baseStart_939068 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_939068 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_939068 prefixEnd_939068 := by exact prefixLift 939068
  have htrace : WordTrace (prefixWord ++ tailWord_939068) baseStart_939068 baseEnd_939068 := by
    simpa [prefixWord, tailWord_939068, baseEnd_939068] using wordTrace_append hprefix tailTrace_939068
  have hstable : (prefixWord ++ tailWord_939068).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939068).length < 2 ^ (prefixWord ++ tailWord_939068).sum := by decide
  have hdescent : baseEnd_939068 < baseStart_939068 := by decide
  rcases family_descends (prefixWord ++ tailWord_939068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939092 : List Nat := [2, 4, 1, 1, 1, 1, 3, 4, 3]
def baseStart_939092 : Nat := 118140960795 + 939092 * 2 ^ 59
def prefixEnd_939092 : Nat := 4983230072969 + 3 ^ 40 * 939092 * 2
def baseEnd_939092 : Nat := 428627177593017806161067

theorem tailTrace_939092 : CollatzResearch.WordTrace tailWord_939092 prefixEnd_939092 428627177593017806161067 := by
  unfold tailWord_939092
  simp only [CollatzResearch.WordTrace]
  refine ⟨17125749556918771494937765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22834332742558361993250353 17125749556918771494937765)
  ·
    refine ⟨3211078041922269655300831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17125749556918771494937765 3211078041922269655300831)
    ·
      refine ⟨4816617062883404482951247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3211078041922269655300831 4816617062883404482951247)
      ·
        refine ⟨7224925594325106724426871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4816617062883404482951247 7224925594325106724426871)
        ·
          refine ⟨10837388391487660086640307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7224925594325106724426871 10837388391487660086640307)
          ·
            refine ⟨16256082587231490129960461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10837388391487660086640307 16256082587231490129960461)
            ·
              refine ⟨6096030970211808798735173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16256082587231490129960461 6096030970211808798735173)
              ·
                refine ⟨1143005806914714149762845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6096030970211808798735173 1143005806914714149762845)
                ·
                  refine ⟨428627177593017806161067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1143005806914714149762845 428627177593017806161067)
                  ·
                    rfl

theorem cell20_939092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 4, 3].length) (baseStart_939092 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_939092 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_939092 prefixEnd_939092 := by exact prefixLift 939092
  have htrace : WordTrace (prefixWord ++ tailWord_939092) baseStart_939092 baseEnd_939092 := by
    simpa [prefixWord, tailWord_939092, baseEnd_939092] using wordTrace_append hprefix tailTrace_939092
  have hstable : (prefixWord ++ tailWord_939092).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939092).length < 2 ^ (prefixWord ++ tailWord_939092).sum := by decide
  have hdescent : baseEnd_939092 < baseStart_939092 := by decide
  rcases family_descends (prefixWord ++ tailWord_939092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939154 : List Nat := [3, 2, 3, 1, 1, 3, 2, 1, 4]
def baseStart_939154 : Nat := 118140960795 + 939154 * 2 ^ 59
def prefixEnd_939154 : Nat := 4983230072969 + 3 ^ 40 * 939154 * 2
def baseEnd_939154 : Nat := 428655476082421146094147

theorem tailTrace_939154 : CollatzResearch.WordTrace tailWord_939154 prefixEnd_939154 428655476082421146094147 := by
  unfold tailWord_939154
  simp only [CollatzResearch.WordTrace]
  refine ⟨8563440109903231894658129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22835840293075285052421677 8563440109903231894658129)
  ·
    refine ⟨6422580082427423920993597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8563440109903231894658129 6422580082427423920993597)
    ·
      refine ⟨2408467530910283970372599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6422580082427423920993597 2408467530910283970372599)
      ·
        refine ⟨3612701296365425955558899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2408467530910283970372599 3612701296365425955558899)
        ·
          refine ⟨5419051944548138933338349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3612701296365425955558899 5419051944548138933338349)
          ·
            refine ⟨2032144479205552100001881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5419051944548138933338349 2032144479205552100001881)
            ·
              refine ⟨1524108359404164075001411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2032144479205552100001881 1524108359404164075001411)
              ·
                refine ⟨2286162539106246112502117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1524108359404164075001411 2286162539106246112502117)
                ·
                  refine ⟨428655476082421146094147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2286162539106246112502117 428655476082421146094147)
                  ·
                    rfl

theorem cell20_939154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 2, 1, 4].length) (baseStart_939154 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_939154 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_939154 prefixEnd_939154 := by exact prefixLift 939154
  have htrace : WordTrace (prefixWord ++ tailWord_939154) baseStart_939154 baseEnd_939154 := by
    simpa [prefixWord, tailWord_939154, baseEnd_939154] using wordTrace_append hprefix tailTrace_939154
  have hstable : (prefixWord ++ tailWord_939154).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939154).length < 2 ^ (prefixWord ++ tailWord_939154).sum := by decide
  have hdescent : baseEnd_939154 < baseStart_939154 := by decide
  rcases family_descends (prefixWord ++ tailWord_939154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939178 : List Nat := [3, 1, 5, 1, 1, 1, 4, 4]
def baseStart_939178 : Nat := 118140960795 + 939178 * 2 ^ 59
def prefixEnd_939178 : Nat := 4983230072969 + 3 ^ 40 * 939178 * 2
def baseEnd_939178 : Nat := 142888810112127909764683

theorem tailTrace_939178 : CollatzResearch.WordTrace tailWord_939178 prefixEnd_939178 142888810112127909764683 := by
  unfold tailWord_939178
  simp only [CollatzResearch.WordTrace]
  refine ⟨8563658947881494919376547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22836423861017319785004125 8563658947881494919376547)
  ·
    refine ⟨12845488421822242379064821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8563658947881494919376547 12845488421822242379064821)
    ·
      refine ⟨1204264539545835223037327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12845488421822242379064821 1204264539545835223037327)
      ·
        refine ⟨1806396809318752834555991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1204264539545835223037327 1806396809318752834555991)
        ·
          refine ⟨2709595213978129251833987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1806396809318752834555991 2709595213978129251833987)
          ·
            refine ⟨4064392820967193877750981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2709595213978129251833987 4064392820967193877750981)
            ·
              refine ⟨762073653931348852078309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4064392820967193877750981 762073653931348852078309)
              ·
                refine ⟨142888810112127909764683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 762073653931348852078309 142888810112127909764683)
                ·
                  rfl

theorem cell20_939178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 4, 4].length) (baseStart_939178 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_939178 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_939178 prefixEnd_939178 := by exact prefixLift 939178
  have htrace : WordTrace (prefixWord ++ tailWord_939178) baseStart_939178 baseEnd_939178 := by
    simpa [prefixWord, tailWord_939178, baseEnd_939178] using wordTrace_append hprefix tailTrace_939178
  have hstable : (prefixWord ++ tailWord_939178).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939178).length < 2 ^ (prefixWord ++ tailWord_939178).sum := by decide
  have hdescent : baseEnd_939178 < baseStart_939178 := by decide
  rcases family_descends (prefixWord ++ tailWord_939178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939327 : List Nat := [1, 1, 2, 2, 4, 3, 2, 1, 4]
def baseStart_939327 : Nat := 118140960795 + 939327 * 2 ^ 59
def prefixEnd_939327 : Nat := 4983230072969 + 3 ^ 40 * 939327 * 2
def baseEnd_939327 : Nat := 428734437996401433326773

theorem tailTrace_939327 : CollatzResearch.WordTrace tailWord_939327 prefixEnd_939327 428734437996401433326773 := by
  unfold tailWord_939327
  simp only [CollatzResearch.WordTrace]
  refine ⟨34260070267986178124680235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22840046845324118749786823 34260070267986178124680235)
  ·
    refine ⟨51390105401979267187020353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34260070267986178124680235 51390105401979267187020353)
    ·
      refine ⟨38542579051484450390265265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51390105401979267187020353 38542579051484450390265265)
      ·
        refine ⟨28906934288613337792698949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38542579051484450390265265 28906934288613337792698949)
        ·
          refine ⟨5420050179115000836131053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28906934288613337792698949 5420050179115000836131053)
          ·
            refine ⟨2032518817168125313549145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5420050179115000836131053 2032518817168125313549145)
            ·
              refine ⟨1524389112876093985161859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2032518817168125313549145 1524389112876093985161859)
              ·
                refine ⟨2286583669314140977742789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1524389112876093985161859 2286583669314140977742789)
                ·
                  refine ⟨428734437996401433326773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2286583669314140977742789 428734437996401433326773)
                  ·
                    rfl

theorem cell20_939327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 2, 1, 4].length) (baseStart_939327 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_939327 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_939327 prefixEnd_939327 := by exact prefixLift 939327
  have htrace : WordTrace (prefixWord ++ tailWord_939327) baseStart_939327 baseEnd_939327 := by
    simpa [prefixWord, tailWord_939327, baseEnd_939327] using wordTrace_append hprefix tailTrace_939327
  have hstable : (prefixWord ++ tailWord_939327).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939327).length < 2 ^ (prefixWord ++ tailWord_939327).sum := by decide
  have hdescent : baseEnd_939327 < baseStart_939327 := by decide
  rcases family_descends (prefixWord ++ tailWord_939327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939351 : List Nat := [1, 1, 3, 2, 3, 4, 2, 4]
def baseStart_939351 : Nat := 118140960795 + 939351 * 2 ^ 59
def prefixEnd_939351 : Nat := 4983230072969 + 3 ^ 40 * 939351 * 2
def baseEnd_939351 : Nat := 142915130750121338842225

theorem tailTrace_939351 : CollatzResearch.WordTrace tailWord_939351 prefixEnd_939351 142915130750121338842225 := by
  unfold tailWord_939351
  simp only [CollatzResearch.WordTrace]
  refine ⟨34260945619899230223553907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22840630413266153482369271 34260945619899230223553907)
  ·
    refine ⟨51391418429848845335330861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34260945619899230223553907 51391418429848845335330861)
    ·
      refine ⟨19271781911193317000749073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51391418429848845335330861 19271781911193317000749073)
      ·
        refine ⟨14453836433394987750561805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19271781911193317000749073 14453836433394987750561805)
        ·
          refine ⟨5420188662523120406460677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14453836433394987750561805 5420188662523120406460677)
          ·
            refine ⟨1016285374223085076211377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5420188662523120406460677 1016285374223085076211377)
            ·
              refine ⟨762214030667313807158533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1016285374223085076211377 762214030667313807158533)
              ·
                refine ⟨142915130750121338842225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 762214030667313807158533 142915130750121338842225)
                ·
                  rfl

theorem cell20_939351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 2, 4].length) (baseStart_939351 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_939351 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_939351 prefixEnd_939351 := by exact prefixLift 939351
  have htrace : WordTrace (prefixWord ++ tailWord_939351) baseStart_939351 baseEnd_939351 := by
    simpa [prefixWord, tailWord_939351, baseEnd_939351] using wordTrace_append hprefix tailTrace_939351
  have hstable : (prefixWord ++ tailWord_939351).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939351).length < 2 ^ (prefixWord ++ tailWord_939351).sum := by decide
  have hdescent : baseEnd_939351 < baseStart_939351 := by decide
  rcases family_descends (prefixWord ++ tailWord_939351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939372 : List Nat := [2, 2, 1, 1, 5, 3, 6]
def baseStart_939372 : Nat := 118140960795 + 939372 * 2 ^ 59
def prefixEnd_939372 : Nat := 4983230072969 + 3 ^ 40 * 939372 * 2
def baseEnd_939372 : Nat := 47639441913620141869621

theorem tailTrace_939372 : CollatzResearch.WordTrace tailWord_939372 prefixEnd_939372 47639441913620141869621 := by
  unfold tailWord_939372
  simp only [CollatzResearch.WordTrace]
  refine ⟨17130855776411575405034185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22841141035215433873378913 17130855776411575405034185)
  ·
    refine ⟨12848141832308681553775639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17130855776411575405034185 12848141832308681553775639)
    ·
      refine ⟨19272212748463022330663459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12848141832308681553775639 19272212748463022330663459)
      ·
        refine ⟨28908319122694533495995189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19272212748463022330663459 28908319122694533495995189)
        ·
          refine ⟨2710154917752612515249549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28908319122694533495995189 2710154917752612515249549)
          ·
            refine ⟨1016308094157229693218581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2710154917752612515249549 1016308094157229693218581)
            ·
              refine ⟨47639441913620141869621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1016308094157229693218581 47639441913620141869621)
              ·
                rfl

theorem cell20_939372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 6].length) (baseStart_939372 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_939372 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_939372 prefixEnd_939372 := by exact prefixLift 939372
  have htrace : WordTrace (prefixWord ++ tailWord_939372) baseStart_939372 baseEnd_939372 := by
    simpa [prefixWord, tailWord_939372, baseEnd_939372] using wordTrace_append hprefix tailTrace_939372
  have hstable : (prefixWord ++ tailWord_939372).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939372).length < 2 ^ (prefixWord ++ tailWord_939372).sum := by decide
  have hdescent : baseEnd_939372 < baseStart_939372 := by decide
  rcases family_descends (prefixWord ++ tailWord_939372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939396 : List Nat := [2, 3, 2, 1, 1, 4, 1, 3, 3]
def baseStart_939396 : Nat := 118140960795 + 939396 * 2 ^ 59
def prefixEnd_939396 : Nat := 4983230072969 + 3 ^ 40 * 939396 * 2
def baseEnd_939396 : Nat := 428765931476543860026491

theorem tailTrace_939396 : CollatzResearch.WordTrace tailWord_939396 prefixEnd_939396 428765931476543860026491 := by
  unfold tailWord_939396
  simp only [CollatzResearch.WordTrace]
  refine ⟨17131293452368101454471021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22841724603157468605961361 17131293452368101454471021)
  ·
    refine ⟨6424235044638038045426633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17131293452368101454471021 6424235044638038045426633)
    ·
      refine ⟨4818176283478528534069975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6424235044638038045426633 4818176283478528534069975)
      ·
        refine ⟨7227264425217792801104963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4818176283478528534069975 7227264425217792801104963)
        ·
          refine ⟨10840896637826689201657445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7227264425217792801104963 10840896637826689201657445)
          ·
            refine ⟨2032668119592504225310771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10840896637826689201657445 2032668119592504225310771)
            ·
              refine ⟨3049002179388756337966157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2032668119592504225310771 3049002179388756337966157)
              ·
                refine ⟨1143375817270783626737309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3049002179388756337966157 1143375817270783626737309)
                ·
                  refine ⟨428765931476543860026491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1143375817270783626737309 428765931476543860026491)
                  ·
                    rfl

theorem cell20_939396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 3, 3].length) (baseStart_939396 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_939396 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_939396 prefixEnd_939396 := by exact prefixLift 939396
  have htrace : WordTrace (prefixWord ++ tailWord_939396) baseStart_939396 baseEnd_939396 := by
    simpa [prefixWord, tailWord_939396, baseEnd_939396] using wordTrace_append hprefix tailTrace_939396
  have hstable : (prefixWord ++ tailWord_939396).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939396).length < 2 ^ (prefixWord ++ tailWord_939396).sum := by decide
  have hdescent : baseEnd_939396 < baseStart_939396 := by decide
  rcases family_descends (prefixWord ++ tailWord_939396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939437 : List Nat := [1, 5, 2, 2, 1, 2, 1, 4, 2]
def baseStart_939437 : Nat := 118140960795 + 939437 * 2 ^ 59
def prefixEnd_939437 : Nat := 4983230072969 + 3 ^ 40 * 939437 * 2
def baseEnd_939437 : Nat := 428784644993729939659657

theorem tailTrace_939437 : CollatzResearch.WordTrace tailWord_939437 prefixEnd_939437 428784644993729939659657 := by
  unfold tailWord_939437
  simp only [CollatzResearch.WordTrace]
  refine ⟨34264082297587666911184565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22842721531725111274123043 34264082297587666911184565)
  ·
    refine ⟨3212257715398843772923553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34264082297587666911184565 3212257715398843772923553)
    ·
      refine ⟨2409193286549132829692665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3212257715398843772923553 2409193286549132829692665)
      ·
        refine ⟨1806894964911849622269499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2409193286549132829692665 1806894964911849622269499)
        ·
          refine ⟨2710342447367774433404249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1806894964911849622269499 2710342447367774433404249)
          ·
            refine ⟨2032756835525830825053187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2710342447367774433404249 2032756835525830825053187)
            ·
              refine ⟨3049135253288746237579781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2032756835525830825053187 3049135253288746237579781)
              ·
                refine ⟨571712859991639919546209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3049135253288746237579781 571712859991639919546209)
                ·
                  refine ⟨428784644993729939659657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 571712859991639919546209 428784644993729939659657)
                  ·
                    rfl

theorem cell20_939437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 4, 2].length) (baseStart_939437 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_939437 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_939437 prefixEnd_939437 := by exact prefixLift 939437
  have htrace : WordTrace (prefixWord ++ tailWord_939437) baseStart_939437 baseEnd_939437 := by
    simpa [prefixWord, tailWord_939437, baseEnd_939437] using wordTrace_append hprefix tailTrace_939437
  have hstable : (prefixWord ++ tailWord_939437).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939437).length < 2 ^ (prefixWord ++ tailWord_939437).sum := by decide
  have hdescent : baseEnd_939437 < baseStart_939437 := by decide
  rcases family_descends (prefixWord ++ tailWord_939437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939526 : List Nat := [6, 2, 1, 1, 2, 2, 1, 3, 2]
def baseStart_939526 : Nat := 118140960795 + 939526 * 2 ^ 59
def prefixEnd_939526 : Nat := 4983230072969 + 3 ^ 40 * 939526 * 2
def baseEnd_939526 : Nat := 428825267018841185692627

theorem tailTrace_939526 : CollatzResearch.WordTrace tailWord_939526 prefixEnd_939526 428825267018841185692627 := by
  unfold tailWord_939526
  simp only [CollatzResearch.WordTrace]
  refine ⟨1070854012320788597224201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 22844885596176823407449621 1070854012320788597224201)
  ·
    refine ⟨803140509240591447918151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1070854012320788597224201 803140509240591447918151)
    ·
      refine ⟨1204710763860887171877227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 803140509240591447918151 1204710763860887171877227)
      ·
        refine ⟨1807066145791330757815841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1204710763860887171877227 1807066145791330757815841)
        ·
          refine ⟨1355299609343498068361881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1807066145791330757815841 1355299609343498068361881)
          ·
            refine ⟨1016474707007623551271411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1355299609343498068361881 1016474707007623551271411)
            ·
              refine ⟨1524712060511435326907117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1016474707007623551271411 1524712060511435326907117)
              ·
                refine ⟨571767022691788247590169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1524712060511435326907117 571767022691788247590169)
                ·
                  refine ⟨428825267018841185692627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 571767022691788247590169 428825267018841185692627)
                  ·
                    rfl

theorem cell20_939526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_939526 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_939526 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_939526 prefixEnd_939526 := by exact prefixLift 939526
  have htrace : WordTrace (prefixWord ++ tailWord_939526) baseStart_939526 baseEnd_939526 := by
    simpa [prefixWord, tailWord_939526, baseEnd_939526] using wordTrace_append hprefix tailTrace_939526
  have hstable : (prefixWord ++ tailWord_939526).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939526).length < 2 ^ (prefixWord ++ tailWord_939526).sum := by decide
  have hdescent : baseEnd_939526 < baseStart_939526 := by decide
  rcases family_descends (prefixWord ++ tailWord_939526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939562 : List Nat := [3, 1, 4, 1, 1, 1, 4, 5]
def baseStart_939562 : Nat := 118140960795 + 939562 * 2 ^ 59
def prefixEnd_939562 : Nat := 4983230072969 + 3 ^ 40 * 939562 * 2
def baseEnd_939562 : Nat := 142947232799928353497493

theorem tailTrace_939562 : CollatzResearch.WordTrace tailWord_939562 prefixEnd_939562 142947232799928353497493 := by
  unfold tailWord_939562
  simp only [CollatzResearch.WordTrace]
  refine ⟨8567160355533703314871235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22845760948089875506323293 8567160355533703314871235)
  ·
    refine ⟨12850740533300554972306853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8567160355533703314871235 12850740533300554972306853)
    ·
      refine ⟨2409513849993854057307535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12850740533300554972306853 2409513849993854057307535)
      ·
        refine ⟨3614270774990781085961303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2409513849993854057307535 3614270774990781085961303)
        ·
          refine ⟨5421406162486171628941955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3614270774990781085961303 5421406162486171628941955)
          ·
            refine ⟨8132109243729257443412933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5421406162486171628941955 8132109243729257443412933)
            ·
              refine ⟨1524770483199235770639925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8132109243729257443412933 1524770483199235770639925)
              ·
                refine ⟨142947232799928353497493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1524770483199235770639925 142947232799928353497493)
                ·
                  rfl

theorem cell20_939562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 4, 5].length) (baseStart_939562 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_939562 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_939562 prefixEnd_939562 := by exact prefixLift 939562
  have htrace : WordTrace (prefixWord ++ tailWord_939562) baseStart_939562 baseEnd_939562 := by
    simpa [prefixWord, tailWord_939562, baseEnd_939562] using wordTrace_append hprefix tailTrace_939562
  have hstable : (prefixWord ++ tailWord_939562).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939562).length < 2 ^ (prefixWord ++ tailWord_939562).sum := by decide
  have hdescent : baseEnd_939562 < baseStart_939562 := by decide
  rcases family_descends (prefixWord ++ tailWord_939562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939583 : List Nat := [1, 1, 2, 2, 3, 3, 2, 6]
def baseStart_939583 : Nat := 118140960795 + 939583 * 2 ^ 59
def prefixEnd_939583 : Nat := 4983230072969 + 3 ^ 40 * 939583 * 2
def baseEnd_939583 : Nat := 142950427790667440264131

theorem tailTrace_939583 : CollatzResearch.WordTrace tailWord_939583 prefixEnd_939583 142950427790667440264131 := by
  unfold tailWord_939583
  simp only [CollatzResearch.WordTrace]
  refine ⟨34269407355058733845999403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22846271570039155897332935 34269407355058733845999403)
  ·
    refine ⟨51404111032588100768999105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34269407355058733845999403 51404111032588100768999105)
    ·
      refine ⟨38553083274441075576749329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51404111032588100768999105 38553083274441075576749329)
      ·
        refine ⟨28914812455830806682561997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38553083274441075576749329 28914812455830806682561997)
        ·
          refine ⟨10843054670936552505960749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28914812455830806682561997 10843054670936552505960749)
          ·
            refine ⟨4066145501601207189735281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10843054670936552505960749 4066145501601207189735281)
            ·
              refine ⟨3049609126200905392301461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4066145501601207189735281 3049609126200905392301461)
              ·
                refine ⟨142950427790667440264131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3049609126200905392301461 142950427790667440264131)
                ·
                  rfl

theorem cell20_939583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 6].length) (baseStart_939583 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_939583 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_939583 prefixEnd_939583 := by exact prefixLift 939583
  have htrace : WordTrace (prefixWord ++ tailWord_939583) baseStart_939583 baseEnd_939583 := by
    simpa [prefixWord, tailWord_939583, baseEnd_939583] using wordTrace_append hprefix tailTrace_939583
  have hstable : (prefixWord ++ tailWord_939583).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939583).length < 2 ^ (prefixWord ++ tailWord_939583).sum := by decide
  have hdescent : baseEnd_939583 < baseStart_939583 := by decide
  rcases family_descends (prefixWord ++ tailWord_939583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939607 : List Nat := [1, 1, 3, 2, 2, 3, 1, 4, 3]
def baseStart_939607 : Nat := 118140960795 + 939607 * 2 ^ 59
def prefixEnd_939607 : Nat := 4983230072969 + 3 ^ 40 * 939607 * 2
def baseEnd_939607 : Nat := 428862237625964903992295

theorem tailTrace_939607 : CollatzResearch.WordTrace tailWord_939607 prefixEnd_939607 428862237625964903992295 := by
  unfold tailWord_939607
  simp only [CollatzResearch.WordTrace]
  refine ⟨34270282706971785944873075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22846855137981190629915383 34270282706971785944873075)
  ·
    refine ⟨51405424060457678917309613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34270282706971785944873075 51405424060457678917309613)
    ·
      refine ⟨19277034022671629593991105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51405424060457678917309613 19277034022671629593991105)
      ·
        refine ⟨14457775517003722195493329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19277034022671629593991105 14457775517003722195493329)
        ·
          refine ⟨10843331637752791646619997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14457775517003722195493329 10843331637752791646619997)
          ·
            refine ⟨4066249364157296867482499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10843331637752791646619997 4066249364157296867482499)
            ·
              refine ⟨6099374046235945301223749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4066249364157296867482499 6099374046235945301223749)
              ·
                refine ⟨1143632633669239743979453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6099374046235945301223749 1143632633669239743979453)
                ·
                  refine ⟨428862237625964903992295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1143632633669239743979453 428862237625964903992295)
                  ·
                    rfl

theorem cell20_939607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 4, 3].length) (baseStart_939607 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_939607 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_939607 prefixEnd_939607 := by exact prefixLift 939607
  have htrace : WordTrace (prefixWord ++ tailWord_939607) baseStart_939607 baseEnd_939607 := by
    simpa [prefixWord, tailWord_939607, baseEnd_939607] using wordTrace_append hprefix tailTrace_939607
  have hstable : (prefixWord ++ tailWord_939607).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939607).length < 2 ^ (prefixWord ++ tailWord_939607).sum := by decide
  have hdescent : baseEnd_939607 < baseStart_939607 := by decide
  rcases family_descends (prefixWord ++ tailWord_939607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939613 : List Nat := [1, 4, 4, 2, 2, 1, 1, 5]
def baseStart_939613 : Nat := 118140960795 + 939613 * 2 ^ 59
def prefixEnd_939613 : Nat := 4983230072969 + 3 ^ 40 * 939613 * 2
def baseEnd_939613 : Nat := 142954992063151849930757

theorem tailTrace_939613 : CollatzResearch.WordTrace tailWord_939613 prefixEnd_939613 142954992063151849930757 := by
  unfold tailWord_939613
  simp only [CollatzResearch.WordTrace]
  refine ⟨34270501544950048969591493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22847001029966699313060995 34270501544950048969591493)
  ·
    refine ⟨6425719039678134181798405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34270501544950048969591493 6425719039678134181798405)
    ·
      refine ⟨1204822319939650159087201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6425719039678134181798405 1204822319939650159087201)
      ·
        refine ⟨903616739954737619315401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1204822319939650159087201 903616739954737619315401)
        ·
          refine ⟨677712554966053214486551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 903616739954737619315401 677712554966053214486551)
          ·
            refine ⟨1016568832449079821729827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 677712554966053214486551 1016568832449079821729827)
            ·
              refine ⟨1524853248673619732594741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1016568832449079821729827 1524853248673619732594741)
              ·
                refine ⟨142954992063151849930757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1524853248673619732594741 142954992063151849930757)
                ·
                  rfl

theorem cell20_939613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 1, 5].length) (baseStart_939613 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_939613 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_939613 prefixEnd_939613 := by exact prefixLift 939613
  have htrace : WordTrace (prefixWord ++ tailWord_939613) baseStart_939613 baseEnd_939613 := by
    simpa [prefixWord, tailWord_939613, baseEnd_939613] using wordTrace_append hprefix tailTrace_939613
  have hstable : (prefixWord ++ tailWord_939613).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939613).length < 2 ^ (prefixWord ++ tailWord_939613).sum := by decide
  have hdescent : baseEnd_939613 < baseStart_939613 := by decide
  rcases family_descends (prefixWord ++ tailWord_939613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939624 : List Nat := [2, 1, 4, 3, 1, 1, 2, 3, 3]
def baseStart_939624 : Nat := 118140960795 + 939624 * 2 ^ 59
def prefixEnd_939624 : Nat := 4983230072969 + 3 ^ 40 * 939624 * 2
def baseEnd_939624 : Nat := 428869996889188400425559

theorem tailTrace_939624 : CollatzResearch.WordTrace tailWord_939624 prefixEnd_939624 428869996889188400425559 := by
  unfold tailWord_939624
  simp only [CollatzResearch.WordTrace]
  refine ⟨17135451373955098924120963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22847268498606798565494617 17135451373955098924120963)
  ·
    refine ⟨25703177060932648386181445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17135451373955098924120963 25703177060932648386181445)
    ·
      refine ⟨4819345698924871572409021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25703177060932648386181445 4819345698924871572409021)
      ·
        refine ⟨1807254637096826839653383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4819345698924871572409021 1807254637096826839653383)
        ·
          refine ⟨2710881955645240259480075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1807254637096826839653383 2710881955645240259480075)
          ·
            refine ⟨4066322933467860389220113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2710881955645240259480075 4066322933467860389220113)
            ·
              refine ⟨3049742200100895291915085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4066322933467860389220113 3049742200100895291915085)
              ·
                refine ⟨1143653325037835734468157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3049742200100895291915085 1143653325037835734468157)
                ·
                  refine ⟨428869996889188400425559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1143653325037835734468157 428869996889188400425559)
                  ·
                    rfl

theorem cell20_939624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 3, 3].length) (baseStart_939624 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_939624 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_939624 prefixEnd_939624 := by exact prefixLift 939624
  have htrace : WordTrace (prefixWord ++ tailWord_939624) baseStart_939624 baseEnd_939624 := by
    simpa [prefixWord, tailWord_939624, baseEnd_939624] using wordTrace_append hprefix tailTrace_939624
  have hstable : (prefixWord ++ tailWord_939624).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939624).length < 2 ^ (prefixWord ++ tailWord_939624).sum := by decide
  have hdescent : baseEnd_939624 < baseStart_939624 := by decide
  rcases family_descends (prefixWord ++ tailWord_939624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939628 : List Nat := [2, 2, 1, 1, 3, 1, 1, 2, 7]
def baseStart_939628 : Nat := 118140960795 + 939628 * 2 ^ 59
def prefixEnd_939628 : Nat := 4983230072969 + 3 ^ 40 * 939628 * 2
def baseEnd_939628 : Nat := 428871822598182164292209

theorem tailTrace_939628 : CollatzResearch.WordTrace tailWord_939628 prefixEnd_939628 428871822598182164292209 := by
  unfold tailWord_939628
  simp only [CollatzResearch.WordTrace]
  refine ⟨17135524319947853265693769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22847365759930471020925025 17135524319947853265693769)
  ·
    refine ⟨12851643239960889949270327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17135524319947853265693769 12851643239960889949270327)
    ·
      refine ⟨19277464859941334923905491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12851643239960889949270327 19277464859941334923905491)
      ·
        refine ⟨28916197289912002385858237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19277464859941334923905491 28916197289912002385858237)
        ·
          refine ⟨10843573983717000894696839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28916197289912002385858237 10843573983717000894696839)
          ·
            refine ⟨16265360975575501342045259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10843573983717000894696839 16265360975575501342045259)
            ·
              refine ⟨24398041463363252013067889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16265360975575501342045259 24398041463363252013067889)
              ·
                refine ⟨18298531097522439009800917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24398041463363252013067889 18298531097522439009800917)
                ·
                  refine ⟨428871822598182164292209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18298531097522439009800917 428871822598182164292209)
                  ·
                    rfl

theorem cell20_939628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 7].length) (baseStart_939628 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_939628 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_939628 prefixEnd_939628 := by exact prefixLift 939628
  have htrace : WordTrace (prefixWord ++ tailWord_939628) baseStart_939628 baseEnd_939628 := by
    simpa [prefixWord, tailWord_939628, baseEnd_939628] using wordTrace_append hprefix tailTrace_939628
  have hstable : (prefixWord ++ tailWord_939628).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939628).length < 2 ^ (prefixWord ++ tailWord_939628).sum := by decide
  have hdescent : baseEnd_939628 < baseStart_939628 := by decide
  rcases family_descends (prefixWord ++ tailWord_939628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939662 : List Nat := [4, 1, 1, 3, 1, 2, 3, 2, 3]
def baseStart_939662 : Nat := 118140960795 + 939662 * 2 ^ 59
def prefixEnd_939662 : Nat := 4983230072969 + 3 ^ 40 * 939662 * 2
def baseEnd_939662 : Nat := 428887341124629157158737

theorem tailTrace_939662 : CollatzResearch.WordTrace tailWord_939662 prefixEnd_939662 428887341124629157158737 := by
  unfold tailWord_939662
  simp only [CollatzResearch.WordTrace]
  refine ⟨4284036090221566292265655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22848192481181686892083493 4284036090221566292265655)
  ·
    refine ⟨6426054135332349438398483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4284036090221566292265655 6426054135332349438398483)
    ·
      refine ⟨9639081202998524157597725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6426054135332349438398483 9639081202998524157597725)
      ·
        refine ⟨3614655451124446559099147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9639081202998524157597725 3614655451124446559099147)
        ·
          refine ⟨5421983176686669838648721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3614655451124446559099147 5421983176686669838648721)
          ·
            refine ⟨4066487382515002378986541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5421983176686669838648721 4066487382515002378986541)
            ·
              refine ⟨1524932768443125892119953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4066487382515002378986541 1524932768443125892119953)
              ·
                refine ⟨1143699576332344419089965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1524932768443125892119953 1143699576332344419089965)
                ·
                  refine ⟨428887341124629157158737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1143699576332344419089965 428887341124629157158737)
                  ·
                    rfl

theorem cell20_939662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 3, 2, 3].length) (baseStart_939662 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_939662 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_939662 prefixEnd_939662 := by exact prefixLift 939662
  have htrace : WordTrace (prefixWord ++ tailWord_939662) baseStart_939662 baseEnd_939662 := by
    simpa [prefixWord, tailWord_939662, baseEnd_939662] using wordTrace_append hprefix tailTrace_939662
  have hstable : (prefixWord ++ tailWord_939662).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939662).length < 2 ^ (prefixWord ++ tailWord_939662).sum := by decide
  have hdescent : baseEnd_939662 < baseStart_939662 := by decide
  rcases family_descends (prefixWord ++ tailWord_939662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939724 : List Nat := [2, 2, 1, 5, 2, 2, 1, 1, 4]
def baseStart_939724 : Nat := 118140960795 + 939724 * 2 ^ 59
def prefixEnd_939724 : Nat := 4983230072969 + 3 ^ 40 * 939724 * 2
def baseEnd_939724 : Nat := 428915639614032497091817

theorem tailTrace_939724 : CollatzResearch.WordTrace tailWord_939724 prefixEnd_939724 428915639614032497091817 := by
  unfold tailWord_939724
  simp only [CollatzResearch.WordTrace]
  refine ⟨17137275023773957463441113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22849700031698609951254817 17137275023773957463441113)
  ·
    refine ⟨12852956267830468097580835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17137275023773957463441113 12852956267830468097580835)
    ·
      refine ⟨19279434401745702146371253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12852956267830468097580835 19279434401745702146371253)
      ·
        refine ⟨1807446975163659576222305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19279434401745702146371253 1807446975163659576222305)
        ·
          refine ⟨1355585231372744682166729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1807446975163659576222305 1355585231372744682166729)
          ·
            refine ⟨1016688923529558511625047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1355585231372744682166729 1016688923529558511625047)
            ·
              refine ⟨1525033385294337767437571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1016688923529558511625047 1525033385294337767437571)
              ·
                refine ⟨2287550077941506651156357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1525033385294337767437571 2287550077941506651156357)
                ·
                  refine ⟨428915639614032497091817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2287550077941506651156357 428915639614032497091817)
                  ·
                    rfl

theorem cell20_939724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 1, 1, 4].length) (baseStart_939724 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_939724 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_939724 prefixEnd_939724 := by exact prefixLift 939724
  have htrace : WordTrace (prefixWord ++ tailWord_939724) baseStart_939724 baseEnd_939724 := by
    simpa [prefixWord, tailWord_939724, baseEnd_939724] using wordTrace_append hprefix tailTrace_939724
  have hstable : (prefixWord ++ tailWord_939724).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939724).length < 2 ^ (prefixWord ++ tailWord_939724).sum := by decide
  have hdescent : baseEnd_939724 < baseStart_939724 := by decide
  rcases family_descends (prefixWord ++ tailWord_939724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939734 : List Nat := [5, 2, 1, 3, 1, 1, 1, 3, 3]
def baseStart_939734 : Nat := 118140960795 + 939734 * 2 ^ 59
def prefixEnd_939734 : Nat := 4983230072969 + 3 ^ 40 * 939734 * 2
def baseEnd_939734 : Nat := 428920203886516906758443

theorem tailTrace_939734 : CollatzResearch.WordTrace tailWord_939734 prefixEnd_939734 428920203886516906758443 := by
  unfold tailWord_939734
  simp only [CollatzResearch.WordTrace]
  refine ⟨2142182173594480414671641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22849943185007791089830837 2142182173594480414671641)
  ·
    refine ⟨1606636630195860311003731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2142182173594480414671641 1606636630195860311003731)
    ·
      refine ⟨2409954945293790466505597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1606636630195860311003731 2409954945293790466505597)
      ·
        refine ⟨903733104485171424939599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2409954945293790466505597 903733104485171424939599)
        ·
          refine ⟨1355599656727757137409399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 903733104485171424939599 1355599656727757137409399)
          ·
            refine ⟨2033399485091635706114099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1355599656727757137409399 2033399485091635706114099)
            ·
              refine ⟨3050099227637453559171149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2033399485091635706114099 3050099227637453559171149)
              ·
                refine ⟨1143787210364045084689181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3050099227637453559171149 1143787210364045084689181)
                ·
                  refine ⟨428920203886516906758443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1143787210364045084689181 428920203886516906758443)
                  ·
                    rfl

theorem cell20_939734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_939734 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_939734 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_939734 prefixEnd_939734 := by exact prefixLift 939734
  have htrace : WordTrace (prefixWord ++ tailWord_939734) baseStart_939734 baseEnd_939734 := by
    simpa [prefixWord, tailWord_939734, baseEnd_939734] using wordTrace_append hprefix tailTrace_939734
  have hstable : (prefixWord ++ tailWord_939734).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939734).length < 2 ^ (prefixWord ++ tailWord_939734).sum := by decide
  have hdescent : baseEnd_939734 < baseStart_939734 := by decide
  rcases family_descends (prefixWord ++ tailWord_939734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939735 : List Nat := [1, 1, 3, 2, 1, 3, 4, 5]
def baseStart_939735 : Nat := 118140960795 + 939735 * 2 ^ 59
def prefixEnd_939735 : Nat := 4983230072969 + 3 ^ 40 * 939735 * 2
def baseEnd_939735 : Nat := 142973553437921782575035

theorem tailTrace_939735 : CollatzResearch.WordTrace tailWord_939735 prefixEnd_939735 142973553437921782575035 := by
  unfold tailWord_939735
  simp only [CollatzResearch.WordTrace]
  refine ⟨34274951250508063805532659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22849967500338709203688439 34274951250508063805532659)
  ·
    refine ⟨51412426875762095708298989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34274951250508063805532659 51412426875762095708298989)
    ·
      refine ⟨19279660078410785890612121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51412426875762095708298989 19279660078410785890612121)
      ·
        refine ⟨14459745058808089417959091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19279660078410785890612121 14459745058808089417959091)
        ·
          refine ⟨21689617588212134126938637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14459745058808089417959091 21689617588212134126938637)
          ·
            refine ⟨8133606595579550297601989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21689617588212134126938637 8133606595579550297601989)
            ·
              refine ⟨1525051236671165680800373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8133606595579550297601989 1525051236671165680800373)
              ·
                refine ⟨142973553437921782575035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1525051236671165680800373 142973553437921782575035)
                ·
                  rfl

theorem cell20_939735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 4, 5].length) (baseStart_939735 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_939735 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_939735 prefixEnd_939735 := by exact prefixLift 939735
  have htrace : WordTrace (prefixWord ++ tailWord_939735) baseStart_939735 baseEnd_939735 := by
    simpa [prefixWord, tailWord_939735, baseEnd_939735] using wordTrace_append hprefix tailTrace_939735
  have hstable : (prefixWord ++ tailWord_939735).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939735).length < 2 ^ (prefixWord ++ tailWord_939735).sum := by decide
  have hdescent : baseEnd_939735 < baseStart_939735 := by decide
  rcases family_descends (prefixWord ++ tailWord_939735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939738 : List Nat := [3, 1, 1, 2, 2, 3, 4, 1, 3]
def baseStart_939738 : Nat := 118140960795 + 939738 * 2 ^ 59
def prefixEnd_939738 : Nat := 4983230072969 + 3 ^ 40 * 939738 * 2
def baseEnd_939738 : Nat := 428922029595510670625093

theorem tailTrace_939738 : CollatzResearch.WordTrace tailWord_939738 prefixEnd_939738 428922029595510670625093 := by
  unfold tailWord_939738
  simp only [CollatzResearch.WordTrace]
  refine ⟨8568765167374298829472967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22850040446331463545261245 8568765167374298829472967)
  ·
    refine ⟨12853147751061448244209451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8568765167374298829472967 12853147751061448244209451)
    ·
      refine ⟨19279721626592172366314177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12853147751061448244209451 19279721626592172366314177)
      ·
        refine ⟨14459791219944129274735633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19279721626592172366314177 14459791219944129274735633)
        ·
          refine ⟨10844843414958096956051725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14459791219944129274735633 10844843414958096956051725)
          ·
            refine ⟨4066816280609286358519397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10844843414958096956051725 4066816280609286358519397)
            ·
              refine ⟨762528052614241192222387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4066816280609286358519397 762528052614241192222387)
              ·
                refine ⟨1143792078921361788333581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 762528052614241192222387 1143792078921361788333581)
                ·
                  refine ⟨428922029595510670625093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1143792078921361788333581 428922029595510670625093)
                  ·
                    rfl

theorem cell20_939738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 4, 1, 3].length) (baseStart_939738 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_939738 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_939738 prefixEnd_939738 := by exact prefixLift 939738
  have htrace : WordTrace (prefixWord ++ tailWord_939738) baseStart_939738 baseEnd_939738 := by
    simpa [prefixWord, tailWord_939738, baseEnd_939738] using wordTrace_append hprefix tailTrace_939738
  have hstable : (prefixWord ++ tailWord_939738).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939738).length < 2 ^ (prefixWord ++ tailWord_939738).sum := by decide
  have hdescent : baseEnd_939738 < baseStart_939738 := by decide
  rcases family_descends (prefixWord ++ tailWord_939738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939797 : List Nat := [1, 3, 2, 1, 2, 3, 2, 3, 3]
def baseStart_939797 : Nat := 118140960795 + 939797 * 2 ^ 59
def prefixEnd_939797 : Nat := 4983230072969 + 3 ^ 40 * 939797 * 2
def baseEnd_939797 : Nat := 428948958803168687658185

theorem tailTrace_939797 : CollatzResearch.WordTrace tailWord_939797 prefixEnd_939797 428948958803168687658185 := by
  unfold tailWord_939797
  simp only [CollatzResearch.WordTrace]
  refine ⟨34277212576283448394289645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22851475050855632262859763 34277212576283448394289645)
  ·
    refine ⟨12853954716106293147858617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34277212576283448394289645 12853954716106293147858617)
    ·
      refine ⟨9640466037079719860893963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12853954716106293147858617 9640466037079719860893963)
      ·
        refine ⟨14460699055619579791340945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9640466037079719860893963 14460699055619579791340945)
        ·
          refine ⟨10845524291714684843505709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14460699055619579791340945 10845524291714684843505709)
          ·
            refine ⟨4067071609393006816314641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10845524291714684843505709 4067071609393006816314641)
            ·
              refine ⟨3050303707044755112235981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4067071609393006816314641 3050303707044755112235981)
              ·
                refine ⟨1143863890141783167088493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3050303707044755112235981 1143863890141783167088493)
                ·
                  refine ⟨428948958803168687658185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1143863890141783167088493 428948958803168687658185)
                  ·
                    rfl

theorem cell20_939797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 3, 3].length) (baseStart_939797 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_939797 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_939797 prefixEnd_939797 := by exact prefixLift 939797
  have htrace : WordTrace (prefixWord ++ tailWord_939797) baseStart_939797 baseEnd_939797 := by
    simpa [prefixWord, tailWord_939797, baseEnd_939797] using wordTrace_append hprefix tailTrace_939797
  have hstable : (prefixWord ++ tailWord_939797).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939797).length < 2 ^ (prefixWord ++ tailWord_939797).sum := by decide
  have hdescent : baseEnd_939797 < baseStart_939797 := by decide
  rcases family_descends (prefixWord ++ tailWord_939797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939804 : List Nat := [2, 2, 3, 1, 1, 2, 3, 2, 4]
def baseStart_939804 : Nat := 118140960795 + 939804 * 2 ^ 59
def prefixEnd_939804 : Nat := 4983230072969 + 3 ^ 40 * 939804 * 2
def baseEnd_939804 : Nat := 428952153793907774424823

theorem tailTrace_939804 : CollatzResearch.WordTrace tailWord_939804 prefixEnd_939804 428952153793907774424823 := by
  unfold tailWord_939804
  simp only [CollatzResearch.WordTrace]
  refine ⟨17138733943629044294897233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22851645258172059059862977 17138733943629044294897233)
  ·
    refine ⟨12854050457721783221172925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17138733943629044294897233 12854050457721783221172925)
    ·
      refine ⟨4820268921645668707939847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12854050457721783221172925 4820268921645668707939847)
      ·
        refine ⟨7230403382468503061909771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4820268921645668707939847 7230403382468503061909771)
        ·
          refine ⟨10845605073702754592864657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7230403382468503061909771 10845605073702754592864657)
          ·
            refine ⟨8134203805277065944648493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10845605073702754592864657 8134203805277065944648493)
            ·
              refine ⟨3050326426978899729243185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8134203805277065944648493 3050326426978899729243185)
              ·
                refine ⟨2287744820234174796932389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3050326426978899729243185 2287744820234174796932389)
                ·
                  refine ⟨428952153793907774424823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2287744820234174796932389 428952153793907774424823)
                  ·
                    rfl

theorem cell20_939804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 2, 4].length) (baseStart_939804 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_939804 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_939804 prefixEnd_939804 := by exact prefixLift 939804
  have htrace : WordTrace (prefixWord ++ tailWord_939804) baseStart_939804 baseEnd_939804 := by
    simpa [prefixWord, tailWord_939804, baseEnd_939804] using wordTrace_append hprefix tailTrace_939804
  have hstable : (prefixWord ++ tailWord_939804).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939804).length < 2 ^ (prefixWord ++ tailWord_939804).sum := by decide
  have hdescent : baseEnd_939804 < baseStart_939804 := by decide
  rcases family_descends (prefixWord ++ tailWord_939804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939828 : List Nat := [2, 5, 1, 1, 2, 2, 7]
def baseStart_939828 : Nat := 118140960795 + 939828 * 2 ^ 59
def prefixEnd_939828 : Nat := 4983230072969 + 3 ^ 40 * 939828 * 2
def baseEnd_939828 : Nat := 47662567560874484180525

theorem tailTrace_939828 : CollatzResearch.WordTrace tailWord_939828 prefixEnd_939828 47662567560874484180525 := by
  unfold tailWord_939828
  simp only [CollatzResearch.WordTrace]
  refine ⟨17139171619585570344334069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22852228826114093792445425 17139171619585570344334069)
  ·
    refine ⟨1606797339336147219781319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17139171619585570344334069 1606797339336147219781319)
    ·
      refine ⟨2410196009004220829671979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1606797339336147219781319 2410196009004220829671979)
      ·
        refine ⟨3615294013506331244507969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2410196009004220829671979 3615294013506331244507969)
        ·
          refine ⟨2711470510129748433380977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3615294013506331244507969 2711470510129748433380977)
          ·
            refine ⟨2033602882597311325035733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2711470510129748433380977 2033602882597311325035733)
            ·
              refine ⟨47662567560874484180525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2033602882597311325035733 47662567560874484180525)
              ·
                rfl

theorem cell20_939828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 7].length) (baseStart_939828 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_939828 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_939828 prefixEnd_939828 := by exact prefixLift 939828
  have htrace : WordTrace (prefixWord ++ tailWord_939828) baseStart_939828 baseEnd_939828 := by
    simpa [prefixWord, tailWord_939828, baseEnd_939828] using wordTrace_append hprefix tailTrace_939828
  have hstable : (prefixWord ++ tailWord_939828).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939828).length < 2 ^ (prefixWord ++ tailWord_939828).sum := by decide
  have hdescent : baseEnd_939828 < baseStart_939828 := by decide
  rcases family_descends (prefixWord ++ tailWord_939828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939838 : List Nat := [4, 2, 1, 2, 2, 1, 2, 4, 2]
def baseStart_939838 : Nat := 118140960795 + 939838 * 2 ^ 59
def prefixEnd_939838 : Nat := 4983230072969 + 3 ^ 40 * 939838 * 2
def baseEnd_939838 : Nat := 428967672320354767291351

theorem tailTrace_939838 : CollatzResearch.WordTrace tailWord_939838 prefixEnd_939838 428967672320354767291351 := by
  unfold tailWord_939838
  simp only [CollatzResearch.WordTrace]
  refine ⟨4284838496141864049566521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22852471979423274931021445 4284838496141864049566521)
  ·
    refine ⟨3213628872106398037174891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4284838496141864049566521 3213628872106398037174891)
    ·
      refine ⟨4820443308159597055762337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3213628872106398037174891 4820443308159597055762337)
      ·
        refine ⟨3615332481119697791821753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4820443308159597055762337 3615332481119697791821753)
        ·
          refine ⟨2711499360839773343866315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3615332481119697791821753 2711499360839773343866315)
          ·
            refine ⟨4067249041259660015799473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2711499360839773343866315 4067249041259660015799473)
            ·
              refine ⟨3050436780944745011849605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4067249041259660015799473 3050436780944745011849605)
              ·
                refine ⟨571956896427139689721801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3050436780944745011849605 571956896427139689721801)
                ·
                  refine ⟨428967672320354767291351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 571956896427139689721801 428967672320354767291351)
                  ·
                    rfl

theorem cell20_939838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 4, 2].length) (baseStart_939838 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_939838 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_939838 prefixEnd_939838 := by exact prefixLift 939838
  have htrace : WordTrace (prefixWord ++ tailWord_939838) baseStart_939838 baseEnd_939838 := by
    simpa [prefixWord, tailWord_939838, baseEnd_939838] using wordTrace_append hprefix tailTrace_939838
  have hstable : (prefixWord ++ tailWord_939838).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939838).length < 2 ^ (prefixWord ++ tailWord_939838).sum := by decide
  have hdescent : baseEnd_939838 < baseStart_939838 := by decide
  rcases family_descends (prefixWord ++ tailWord_939838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939946 : List Nat := [3, 1, 16]
def baseStart_939946 : Nat := 118140960795 + 939946 * 2 ^ 59
def prefixEnd_939946 : Nat := 4983230072969 + 3 ^ 40 * 939946 * 2
def baseEnd_939946 : Nat := 588500639867196696421

theorem tailTrace_939946 : CollatzResearch.WordTrace tailWord_939946 prefixEnd_939946 588500639867196696421 := by
  unfold tailWord_939946
  simp only [CollatzResearch.WordTrace]
  refine ⟨8570661763185911710365923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22855098035162431227642461 8570661763185911710365923)
  ·
    refine ⟨12855992644778867565548885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8570661763185911710365923 12855992644778867565548885)
    ·
      refine ⟨588500639867196696421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 16 12855992644778867565548885 588500639867196696421)
      ·
        rfl

theorem cell20_939946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 16].length) (baseStart_939946 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_939946 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_939946 prefixEnd_939946 := by exact prefixLift 939946
  have htrace : WordTrace (prefixWord ++ tailWord_939946) baseStart_939946 baseEnd_939946 := by
    simpa [prefixWord, tailWord_939946, baseEnd_939946] using wordTrace_append hprefix tailTrace_939946
  have hstable : (prefixWord ++ tailWord_939946).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939946).length < 2 ^ (prefixWord ++ tailWord_939946).sum := by decide
  have hdescent : baseEnd_939946 < baseStart_939946 := by decide
  rcases family_descends (prefixWord ++ tailWord_939946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939977 : List Nat := [1, 2, 1, 1, 2, 1, 2, 6, 4]
def baseStart_939977 : Nat := 118140960795 + 939977 * 2 ^ 59
def prefixEnd_939977 : Nat := 4983230072969 + 3 ^ 40 * 939977 * 2
def baseEnd_939977 : Nat := 429031115707888061657449

theorem tailTrace_939977 : CollatzResearch.WordTrace tailWord_939977 prefixEnd_939977 429031115707888061657449 := by
  unfold tailWord_939977
  simp only [CollatzResearch.WordTrace]
  refine ⟨34283777715631339135842185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22855851810420892757228123 34283777715631339135842185)
  ·
    refine ⟨25712833286723504351881639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34283777715631339135842185 25712833286723504351881639)
    ·
      refine ⟨38569249930085256527822459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25712833286723504351881639 38569249930085256527822459)
      ·
        refine ⟨57853874895127884791733689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38569249930085256527822459 57853874895127884791733689)
        ·
          refine ⟨43390406171345913593800267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57853874895127884791733689 43390406171345913593800267)
          ·
            refine ⟨65085609257018870390700401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43390406171345913593800267 65085609257018870390700401)
            ·
              refine ⟨48814206942764152793025301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65085609257018870390700401 48814206942764152793025301)
              ·
                refine ⟨2288165950442069662173061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 48814206942764152793025301 2288165950442069662173061)
                ·
                  refine ⟨429031115707888061657449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2288165950442069662173061 429031115707888061657449)
                  ·
                    rfl

theorem cell20_939977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 6, 4].length) (baseStart_939977 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_939977 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_939977 prefixEnd_939977 := by exact prefixLift 939977
  have htrace : WordTrace (prefixWord ++ tailWord_939977) baseStart_939977 baseEnd_939977 := by
    simpa [prefixWord, tailWord_939977, baseEnd_939977] using wordTrace_append hprefix tailTrace_939977
  have hstable : (prefixWord ++ tailWord_939977).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939977).length < 2 ^ (prefixWord ++ tailWord_939977).sum := by decide
  have hdescent : baseEnd_939977 < baseStart_939977 := by decide
  rcases family_descends (prefixWord ++ tailWord_939977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939980 : List Nat := [2, 2, 1, 4, 1, 3, 3, 4]
def baseStart_939980 : Nat := 118140960795 + 939980 * 2 ^ 59
def prefixEnd_939980 : Nat := 4983230072969 + 3 ^ 40 * 939980 * 2
def baseEnd_939980 : Nat := 143010828329877794852479

theorem tailTrace_939980 : CollatzResearch.WordTrace tailWord_939980 prefixEnd_939980 143010828329877794852479 := by
  unfold tailWord_939980
  simp only [CollatzResearch.WordTrace]
  refine ⟨17141943567310235324100697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22855924756413647098800929 17141943567310235324100697)
  ·
    refine ⟨12856457675482676493075523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17141943567310235324100697 12856457675482676493075523)
    ·
      refine ⟨19284686513224014739613285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12856457675482676493075523 19284686513224014739613285)
      ·
        refine ⟨3615878721229502763677491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19284686513224014739613285 3615878721229502763677491)
        ·
          refine ⟨5423818081844254145516237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3615878721229502763677491 5423818081844254145516237)
          ·
            refine ⟨2033931780691595304568589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5423818081844254145516237 2033931780691595304568589)
            ·
              refine ⟨762724417759348239213221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2033931780691595304568589 762724417759348239213221)
              ·
                refine ⟨143010828329877794852479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 762724417759348239213221 143010828329877794852479)
                ·
                  rfl

theorem cell20_939980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 3, 4].length) (baseStart_939980 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_939980 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_939980 prefixEnd_939980 := by exact prefixLift 939980
  have htrace : WordTrace (prefixWord ++ tailWord_939980) baseStart_939980 baseEnd_939980 := by
    simpa [prefixWord, tailWord_939980, baseEnd_939980] using wordTrace_append hprefix tailTrace_939980
  have hstable : (prefixWord ++ tailWord_939980).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939980).length < 2 ^ (prefixWord ++ tailWord_939980).sum := by decide
  have hdescent : baseEnd_939980 < baseStart_939980 := by decide
  rcases family_descends (prefixWord ++ tailWord_939980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_939984 : List Nat := [2, 1, 1, 1, 1, 2, 4, 8]
def baseStart_939984 : Nat := 118140960795 + 939984 * 2 ^ 59
def prefixEnd_939984 : Nat := 4983230072969 + 3 ^ 40 * 939984 * 2
def baseEnd_939984 : Nat := 143011436899542382808029

theorem tailTrace_939984 : CollatzResearch.WordTrace tailWord_939984 prefixEnd_939984 143011436899542382808029 := by
  unfold tailWord_939984
  simp only [CollatzResearch.WordTrace]
  refine ⟨17142016513302989665673503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22856022017737319554231337 17142016513302989665673503)
  ·
    refine ⟨25713024769954484498510255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17142016513302989665673503 25713024769954484498510255)
    ·
      refine ⟨38569537154931726747765383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25713024769954484498510255 38569537154931726747765383)
      ·
        refine ⟨57854305732397590121648075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38569537154931726747765383 57854305732397590121648075)
        ·
          refine ⟨86781458598596385182472113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57854305732397590121648075 86781458598596385182472113)
          ·
            refine ⟨65086093948947288886854085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86781458598596385182472113 65086093948947288886854085)
            ·
              refine ⟨12203642615427616666285141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65086093948947288886854085 12203642615427616666285141)
              ·
                refine ⟨143011436899542382808029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12203642615427616666285141 143011436899542382808029)
                ·
                  rfl

theorem cell20_939984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 8].length) (baseStart_939984 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_939984 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_939984 prefixEnd_939984 := by exact prefixLift 939984
  have htrace : WordTrace (prefixWord ++ tailWord_939984) baseStart_939984 baseEnd_939984 := by
    simpa [prefixWord, tailWord_939984, baseEnd_939984] using wordTrace_append hprefix tailTrace_939984
  have hstable : (prefixWord ++ tailWord_939984).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_939984).length < 2 ^ (prefixWord ++ tailWord_939984).sum := by decide
  have hdescent : baseEnd_939984 < baseStart_939984 := by decide
  rcases family_descends (prefixWord ++ tailWord_939984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940039 : List Nat := [1, 1, 4, 3, 1, 3, 1, 6]
def baseStart_940039 : Nat := 118140960795 + 940039 * 2 ^ 59
def prefixEnd_940039 : Nat := 4983230072969 + 3 ^ 40 * 940039 * 2
def baseEnd_940039 : Nat := 143019804732430467196843

theorem tailTrace_940039 : CollatzResearch.WordTrace tailWord_940039 prefixEnd_940039 143019804732430467196843 := by
  unfold tailWord_940039
  simp only [CollatzResearch.WordTrace]
  refine ⟨34286039041406723724599171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22857359360937815816399447 34286039041406723724599171)
  ·
    refine ⟨51429058562110085586898757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34286039041406723724599171 51429058562110085586898757)
    ·
      refine ⟨9642948480395641047543517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51429058562110085586898757 9642948480395641047543517)
      ·
        refine ⟨3616105680148365392828819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9642948480395641047543517 3616105680148365392828819)
        ·
          refine ⟨5424158520222548089243229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3616105680148365392828819 5424158520222548089243229)
          ·
            refine ⟨2034059445083455533466211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5424158520222548089243229 2034059445083455533466211)
            ·
              refine ⟨3051089167625183300199317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2034059445083455533466211 3051089167625183300199317)
              ·
                refine ⟨143019804732430467196843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3051089167625183300199317 143019804732430467196843)
                ·
                  rfl

theorem cell20_940039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 6].length) (baseStart_940039 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_940039 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_940039 prefixEnd_940039 := by exact prefixLift 940039
  have htrace : WordTrace (prefixWord ++ tailWord_940039) baseStart_940039 baseEnd_940039 := by
    simpa [prefixWord, tailWord_940039, baseEnd_940039] using wordTrace_append hprefix tailTrace_940039
  have hstable : (prefixWord ++ tailWord_940039).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940039).length < 2 ^ (prefixWord ++ tailWord_940039).sum := by decide
  have hdescent : baseEnd_940039 < baseStart_940039 := by decide
  rcases family_descends (prefixWord ++ tailWord_940039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940046 : List Nat := [4, 1, 1, 2, 2, 1, 1, 1, 7]
def baseStart_940046 : Nat := 118140960795 + 940046 * 2 ^ 59
def prefixEnd_940046 : Nat := 4983230072969 + 3 ^ 40 * 940046 * 2
def baseEnd_940046 : Nat := 429062609188030488357167

theorem tailTrace_940046 : CollatzResearch.WordTrace tailWord_940046 prefixEnd_940046 429062609188030488357167 := by
  unfold tailWord_940046
  simp only [CollatzResearch.WordTrace]
  refine ⟨4285786794047670490012999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22857529568254242613402661 4285786794047670490012999)
  ·
    refine ⟨6428680191071505735019499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4285786794047670490012999 6428680191071505735019499)
    ·
      refine ⟨9643020286607258602529249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6428680191071505735019499 9643020286607258602529249)
      ·
        refine ⟨7232265214955443951896937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9643020286607258602529249 7232265214955443951896937)
        ·
          refine ⟨5424198911216582963922703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7232265214955443951896937 5424198911216582963922703)
          ·
            refine ⟨8136298366824874445884055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5424198911216582963922703 8136298366824874445884055)
            ·
              refine ⟨12204447550237311668826083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8136298366824874445884055 12204447550237311668826083)
              ·
                refine ⟨18306671325355967503239125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12204447550237311668826083 18306671325355967503239125)
                ·
                  refine ⟨429062609188030488357167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18306671325355967503239125 429062609188030488357167)
                  ·
                    rfl

theorem cell20_940046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 7].length) (baseStart_940046 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_940046 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_940046 prefixEnd_940046 := by exact prefixLift 940046
  have htrace : WordTrace (prefixWord ++ tailWord_940046) baseStart_940046 baseEnd_940046 := by
    simpa [prefixWord, tailWord_940046, baseEnd_940046] using wordTrace_append hprefix tailTrace_940046
  have hstable : (prefixWord ++ tailWord_940046).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940046).length < 2 ^ (prefixWord ++ tailWord_940046).sum := by decide
  have hdescent : baseEnd_940046 < baseStart_940046 := by decide
  rcases family_descends (prefixWord ++ tailWord_940046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940052 : List Nat := [2, 4, 3, 2, 2, 1, 6]
def baseStart_940052 : Nat := 118140960795 + 940052 * 2 ^ 59
def prefixEnd_940052 : Nat := 4983230072969 + 3 ^ 40 * 940052 * 2
def baseEnd_940052 : Nat := 47673927527946792684127

theorem tailTrace_940052 : CollatzResearch.WordTrace tailWord_940052 prefixEnd_940052 47673927527946792684127 := by
  unfold tailWord_940052
  simp only [CollatzResearch.WordTrace]
  refine ⟨17143256595179813472411205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22857675460239751296548273 17143256595179813472411205)
  ·
    refine ⟨3214360611596215026077101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17143256595179813472411205 3214360611596215026077101)
    ·
      refine ⟨1205385229348580634778913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3214360611596215026077101 1205385229348580634778913)
      ·
        refine ⟨904038922011435476084185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1205385229348580634778913 904038922011435476084185)
        ·
          refine ⟨678029191508576607063139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 904038922011435476084185 678029191508576607063139)
          ·
            refine ⟨1017043787262864910594709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 678029191508576607063139 1017043787262864910594709)
            ·
              refine ⟨47673927527946792684127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1017043787262864910594709 47673927527946792684127)
              ·
                rfl

theorem cell20_940052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 6].length) (baseStart_940052 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_940052 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_940052 prefixEnd_940052 := by exact prefixLift 940052
  have htrace : WordTrace (prefixWord ++ tailWord_940052) baseStart_940052 baseEnd_940052 := by
    simpa [prefixWord, tailWord_940052, baseEnd_940052] using wordTrace_append hprefix tailTrace_940052
  have hstable : (prefixWord ++ tailWord_940052).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940052).length < 2 ^ (prefixWord ++ tailWord_940052).sum := by decide
  have hdescent : baseEnd_940052 < baseStart_940052 := by decide
  rcases family_descends (prefixWord ++ tailWord_940052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940066 : List Nat := [3, 3, 1, 1, 1, 2, 5, 2, 2]
def baseStart_940066 : Nat := 118140960795 + 940066 * 2 ^ 59
def prefixEnd_940066 : Nat := 4983230072969 + 3 ^ 40 * 940066 * 2
def baseEnd_940066 : Nat := 429071737732999307690419

theorem tailTrace_940066 : CollatzResearch.WordTrace tailWord_940066 prefixEnd_940066 429071737732999307690419 := by
  unfold tailWord_940066
  simp only [CollatzResearch.WordTrace]
  refine ⟨8571755953077226833958013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22858015874872604890554701 8571755953077226833958013)
  ·
    refine ⟨3214408482403960062734255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8571755953077226833958013 3214408482403960062734255)
    ·
      refine ⟨4821612723605940094101383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3214408482403960062734255 4821612723605940094101383)
      ·
        refine ⟨7232419085408910141152075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4821612723605940094101383 7232419085408910141152075)
        ·
          refine ⟨10848628628113365211728113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7232419085408910141152075 10848628628113365211728113)
          ·
            refine ⟨8136471471085023908796085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10848628628113365211728113 8136471471085023908796085)
            ·
              refine ⟨762794200414220991449633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8136471471085023908796085 762794200414220991449633)
              ·
                refine ⟨572095650310665743587225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 762794200414220991449633 572095650310665743587225)
                ·
                  refine ⟨429071737732999307690419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 572095650310665743587225 429071737732999307690419)
                  ·
                    rfl

theorem cell20_940066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 5, 2, 2].length) (baseStart_940066 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_940066 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_940066 prefixEnd_940066 := by exact prefixLift 940066
  have htrace : WordTrace (prefixWord ++ tailWord_940066) baseStart_940066 baseEnd_940066 := by
    simpa [prefixWord, tailWord_940066, baseEnd_940066] using wordTrace_append hprefix tailTrace_940066
  have hstable : (prefixWord ++ tailWord_940066).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940066).length < 2 ^ (prefixWord ++ tailWord_940066).sum := by decide
  have hdescent : baseEnd_940066 < baseStart_940066 := by decide
  rcases family_descends (prefixWord ++ tailWord_940066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940080 : List Nat := [2, 1, 1, 1, 2, 7, 2, 1, 3]
def baseStart_940080 : Nat := 118140960795 + 940080 * 2 ^ 59
def prefixEnd_940080 : Nat := 4983230072969 + 3 ^ 40 * 940080 * 2
def baseEnd_940080 : Nat := 429078127714477481223695

theorem tailTrace_940080 : CollatzResearch.WordTrace tailWord_940080 prefixEnd_940080 429078127714477481223695 := by
  unfold tailWord_940080
  simp only [CollatzResearch.WordTrace]
  refine ⟨17143767217129093863420847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22858356289505458484561129 17143767217129093863420847)
  ·
    refine ⟨25715650825693640795131271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17143767217129093863420847 25715650825693640795131271)
    ·
      refine ⟨38573476238540461192696907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25715650825693640795131271 38573476238540461192696907)
      ·
        refine ⟨57860214357810691789045361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38573476238540461192696907 57860214357810691789045361)
        ·
          refine ⟨43395160768358018841784021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57860214357810691789045361 43395160768358018841784021)
          ·
            refine ⟨1017074080508391066604313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 43395160768358018841784021 1017074080508391066604313)
            ·
              refine ⟨762805560381293299953235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1017074080508391066604313 762805560381293299953235)
              ·
                refine ⟨1144208340571939949929853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 762805560381293299953235 1144208340571939949929853)
                ·
                  refine ⟨429078127714477481223695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1144208340571939949929853 429078127714477481223695)
                  ·
                    rfl

theorem cell20_940080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 2, 1, 3].length) (baseStart_940080 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_940080 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_940080 prefixEnd_940080 := by exact prefixLift 940080
  have htrace : WordTrace (prefixWord ++ tailWord_940080) baseStart_940080 baseEnd_940080 := by
    simpa [prefixWord, tailWord_940080, baseEnd_940080] using wordTrace_append hprefix tailTrace_940080
  have hstable : (prefixWord ++ tailWord_940080).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940080).length < 2 ^ (prefixWord ++ tailWord_940080).sum := by decide
  have hdescent : baseEnd_940080 < baseStart_940080 := by decide
  rcases family_descends (prefixWord ++ tailWord_940080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940129 : List Nat := [1, 2, 3, 1, 1, 2, 1, 5, 4]
def baseStart_940129 : Nat := 118140960795 + 940129 * 2 ^ 59
def prefixEnd_940129 : Nat := 4983230072969 + 3 ^ 40 * 940129 * 2
def baseEnd_940129 : Nat := 429100492649651088590161

theorem tailTrace_940129 : CollatzResearch.WordTrace tailWord_940129 prefixEnd_940129 429100492649651088590161 := by
  unfold tailWord_940129
  simp only [CollatzResearch.WordTrace]
  refine ⟨34289321611080669095375441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22859547740720446063583627 34289321611080669095375441)
  ·
    refine ⟨25716991208310501821531581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34289321611080669095375441 25716991208310501821531581)
    ·
      refine ⟨9643871703116438183074343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25716991208310501821531581 9643871703116438183074343)
      ·
        refine ⟨14465807554674657274611515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9643871703116438183074343 14465807554674657274611515)
        ·
          refine ⟨21698711332011985911917273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14465807554674657274611515 21698711332011985911917273)
          ·
            refine ⟨16274033499008989433937955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21698711332011985911917273 16274033499008989433937955)
            ·
              refine ⟨24411050248513484150906933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16274033499008989433937955 24411050248513484150906933)
              ·
                refine ⟨2288535960798139139147525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24411050248513484150906933 2288535960798139139147525)
                ·
                  refine ⟨429100492649651088590161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2288535960798139139147525 429100492649651088590161)
                  ·
                    rfl

theorem cell20_940129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 5, 4].length) (baseStart_940129 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_940129 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_940129 prefixEnd_940129 := by exact prefixLift 940129
  have htrace : WordTrace (prefixWord ++ tailWord_940129) baseStart_940129 baseEnd_940129 := by
    simpa [prefixWord, tailWord_940129, baseEnd_940129] using wordTrace_append hprefix tailTrace_940129
  have hstable : (prefixWord ++ tailWord_940129).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940129).length < 2 ^ (prefixWord ++ tailWord_940129).sum := by decide
  have hdescent : baseEnd_940129 < baseStart_940129 := by decide
  rcases family_descends (prefixWord ++ tailWord_940129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940146 : List Nat := [3, 2, 1, 2, 2, 3, 1, 2, 4]
def baseStart_940146 : Nat := 118140960795 + 940146 * 2 ^ 59
def prefixEnd_940146 : Nat := 4983230072969 + 3 ^ 40 * 940146 * 2
def baseEnd_940146 : Nat := 429108251912874585023425

theorem tailTrace_940146 : CollatzResearch.WordTrace tailWord_940146 prefixEnd_940146 429108251912874585023425 := by
  unfold tailWord_940146
  simp only [CollatzResearch.WordTrace]
  refine ⟨8572485413004770249686073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22859961101346053999162861 8572485413004770249686073)
  ·
    refine ⟨6429364059753577687264555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8572485413004770249686073 6429364059753577687264555)
    ·
      refine ⟨9644046089630366530896833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6429364059753577687264555 9644046089630366530896833)
      ·
        refine ⟨7233034567222774898172625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9644046089630366530896833 7233034567222774898172625)
        ·
          refine ⟨5424775925417081173629469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7233034567222774898172625 5424775925417081173629469)
          ·
            refine ⟨2034290972031405440111051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5424775925417081173629469 2034290972031405440111051)
            ·
              refine ⟨3051436458047108160166577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2034290972031405440111051 3051436458047108160166577)
              ·
                refine ⟨2288577343535331120124933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3051436458047108160166577 2288577343535331120124933)
                ·
                  refine ⟨429108251912874585023425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2288577343535331120124933 429108251912874585023425)
                  ·
                    rfl

theorem cell20_940146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 2, 4].length) (baseStart_940146 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_940146 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_940146 prefixEnd_940146 := by exact prefixLift 940146
  have htrace : WordTrace (prefixWord ++ tailWord_940146) baseStart_940146 baseEnd_940146 := by
    simpa [prefixWord, tailWord_940146, baseEnd_940146] using wordTrace_append hprefix tailTrace_940146
  have hstable : (prefixWord ++ tailWord_940146).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940146).length < 2 ^ (prefixWord ++ tailWord_940146).sum := by decide
  have hdescent : baseEnd_940146 < baseStart_940146 := by decide
  rcases family_descends (prefixWord ++ tailWord_940146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940163 : List Nat := [1, 1, 1, 3, 3, 4, 2, 3, 2]
def baseStart_940163 : Nat := 118140960795 + 940163 * 2 ^ 59
def prefixEnd_940163 : Nat := 4983230072969 + 3 ^ 40 * 940163 * 2
def baseEnd_940163 : Nat := 429116011176098081456689

theorem tailTrace_940163 : CollatzResearch.WordTrace tailWord_940163 prefixEnd_940163 429116011176098081456689 := by
  unfold tailWord_940163
  simp only [CollatzResearch.WordTrace]
  refine ⟨34290561692957492902113143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22860374461971661934742095 34290561692957492902113143)
  ·
    refine ⟨51435842539436239353169715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34290561692957492902113143 51435842539436239353169715)
    ·
      refine ⟨77153763809154359029754573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51435842539436239353169715 77153763809154359029754573)
      ·
        refine ⟨28932661428432884636157965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77153763809154359029754573 28932661428432884636157965)
        ·
          refine ⟨10849748035662331738559237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28932661428432884636157965 10849748035662331738559237)
          ·
            refine ⟨2034327756686687200979857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10849748035662331738559237 2034327756686687200979857)
            ·
              refine ⟨1525745817515015400734893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2034327756686687200979857 1525745817515015400734893)
              ·
                refine ⟨572154681568130775275585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1525745817515015400734893 572154681568130775275585)
                ·
                  refine ⟨429116011176098081456689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 572154681568130775275585 429116011176098081456689)
                  ·
                    rfl

theorem cell20_940163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 2, 3, 2].length) (baseStart_940163 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_940163 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_940163 prefixEnd_940163 := by exact prefixLift 940163
  have htrace : WordTrace (prefixWord ++ tailWord_940163) baseStart_940163 baseEnd_940163 := by
    simpa [prefixWord, tailWord_940163, baseEnd_940163] using wordTrace_append hprefix tailTrace_940163
  have hstable : (prefixWord ++ tailWord_940163).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940163).length < 2 ^ (prefixWord ++ tailWord_940163).sum := by decide
  have hdescent : baseEnd_940163 < baseStart_940163 := by decide
  rcases family_descends (prefixWord ++ tailWord_940163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940180 : List Nat := [2, 4, 2, 3, 1, 1, 2, 1, 4]
def baseStart_940180 : Nat := 118140960795 + 940180 * 2 ^ 59
def prefixEnd_940180 : Nat := 4983230072969 + 3 ^ 40 * 940180 * 2
def baseEnd_940180 : Nat := 429123770439321577889953

theorem tailTrace_940180 : CollatzResearch.WordTrace tailWord_940180 prefixEnd_940180 429123770439321577889953 := by
  unfold tailWord_940180
  simp only [CollatzResearch.WordTrace]
  refine ⟨17145590866947952402740997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22860787822597269870321329 17145590866947952402740997)
  ·
    refine ⟨3214798287552741075513937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17145590866947952402740997 3214798287552741075513937)
    ·
      refine ⟨2411098715664555806635453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3214798287552741075513937 2411098715664555806635453)
      ·
        refine ⟨904162018374208427488295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2411098715664555806635453 904162018374208427488295)
        ·
          refine ⟨1356243027561312641232443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 904162018374208427488295 1356243027561312641232443)
          ·
            refine ⟨2034364541341968961848665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1356243027561312641232443 2034364541341968961848665)
            ·
              refine ⟨1525773406006476721386499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2034364541341968961848665 1525773406006476721386499)
              ·
                refine ⟨2288660109009715082079749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1525773406006476721386499 2288660109009715082079749)
                ·
                  refine ⟨429123770439321577889953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2288660109009715082079749 429123770439321577889953)
                  ·
                    rfl

theorem cell20_940180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 2, 1, 4].length) (baseStart_940180 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_940180 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_940180 prefixEnd_940180 := by exact prefixLift 940180
  have htrace : WordTrace (prefixWord ++ tailWord_940180) baseStart_940180 baseEnd_940180 := by
    simpa [prefixWord, tailWord_940180, baseEnd_940180] using wordTrace_append hprefix tailTrace_940180
  have hstable : (prefixWord ++ tailWord_940180).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940180).length < 2 ^ (prefixWord ++ tailWord_940180).sum := by decide
  have hdescent : baseEnd_940180 < baseStart_940180 := by decide
  rcases family_descends (prefixWord ++ tailWord_940180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940219 : List Nat := [1, 1, 1, 1, 1, 2, 5, 1, 7]
def baseStart_940219 : Nat := 118140960795 + 940219 * 2 ^ 59
def prefixEnd_940219 : Nat := 4983230072969 + 3 ^ 40 * 940219 * 2
def baseEnd_940219 : Nat := 429141571102010775589793

theorem tailTrace_940219 : CollatzResearch.WordTrace tailWord_940219 prefixEnd_940219 429141571102010775589793 := by
  unfold tailWord_940219
  simp only [CollatzResearch.WordTrace]
  refine ⟨34292604180754614466151711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22861736120503076310767807 34292604180754614466151711)
  ·
    refine ⟨51438906271131921699227567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34292604180754614466151711 51438906271131921699227567)
    ·
      refine ⟨77158359406697882548841351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51438906271131921699227567 77158359406697882548841351)
      ·
        refine ⟨115737539110046823823262027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77158359406697882548841351 115737539110046823823262027)
        ·
          refine ⟨173606308665070235734893041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115737539110046823823262027 173606308665070235734893041)
          ·
            refine ⟨130204731498802676801169781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173606308665070235734893041 130204731498802676801169781)
            ·
              refine ⟨12206693578012750950109667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 130204731498802676801169781 12206693578012750950109667)
              ·
                refine ⟨18310040367019126425164501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12206693578012750950109667 18310040367019126425164501)
                ·
                  refine ⟨429141571102010775589793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18310040367019126425164501 429141571102010775589793)
                  ·
                    rfl

theorem cell20_940219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 7].length) (baseStart_940219 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_940219 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_940219 prefixEnd_940219 := by exact prefixLift 940219
  have htrace : WordTrace (prefixWord ++ tailWord_940219) baseStart_940219 baseEnd_940219 := by
    simpa [prefixWord, tailWord_940219, baseEnd_940219] using wordTrace_append hprefix tailTrace_940219
  have hstable : (prefixWord ++ tailWord_940219).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940219).length < 2 ^ (prefixWord ++ tailWord_940219).sum := by decide
  have hdescent : baseEnd_940219 < baseStart_940219 := by decide
  rcases family_descends (prefixWord ++ tailWord_940219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940225 : List Nat := [1, 2, 6, 1, 3, 1, 6]
def baseStart_940225 : Nat := 118140960795 + 940225 * 2 ^ 59
def prefixEnd_940225 : Nat := 4983230072969 + 3 ^ 40 * 940225 * 2
def baseEnd_940225 : Nat := 47682701073944602376641

theorem tailTrace_940225 : CollatzResearch.WordTrace tailWord_940225 prefixEnd_940225 47682701073944602376641 := by
  unfold tailWord_940225
  simp only [CollatzResearch.WordTrace]
  refine ⟨34292823018732877490870129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22861882012488584993913419 34292823018732877490870129)
  ·
    refine ⟨25719617264049658118152597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34292823018732877490870129 25719617264049658118152597)
    ·
      refine ⟨1205607059252327724288403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 25719617264049658118152597 1205607059252327724288403)
      ·
        refine ⟨1808410588878491586432605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1205607059252327724288403 1808410588878491586432605)
        ·
          refine ⟨678153970829434344912227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1808410588878491586432605 678153970829434344912227)
          ·
            refine ⟨1017230956244151517368341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 678153970829434344912227 1017230956244151517368341)
            ·
              refine ⟨47682701073944602376641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1017230956244151517368341 47682701073944602376641)
              ·
                rfl

theorem cell20_940225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 6].length) (baseStart_940225 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_940225 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_940225 prefixEnd_940225 := by exact prefixLift 940225
  have htrace : WordTrace (prefixWord ++ tailWord_940225) baseStart_940225 baseEnd_940225 := by
    simpa [prefixWord, tailWord_940225, baseEnd_940225] using wordTrace_append hprefix tailTrace_940225
  have hstable : (prefixWord ++ tailWord_940225).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940225).length < 2 ^ (prefixWord ++ tailWord_940225).sum := by decide
  have hdescent : baseEnd_940225 < baseStart_940225 := by decide
  rcases family_descends (prefixWord ++ tailWord_940225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940239 : List Nat := [1, 1, 2, 1, 1, 3, 7, 2, 2]
def baseStart_940239 : Nat := 118140960795 + 940239 * 2 ^ 59
def prefixEnd_940239 : Nat := 4983230072969 + 3 ^ 40 * 940239 * 2
def baseEnd_940239 : Nat := 429150699646979594923045

theorem tailTrace_940239 : CollatzResearch.WordTrace tailWord_940239 prefixEnd_940239 429150699646979594923045 := by
  unfold tailWord_940239
  simp only [CollatzResearch.WordTrace]
  refine ⟨34293333640682157881879771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22862222427121438587919847 34293333640682157881879771)
  ·
    refine ⟨51440000461023236822819657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34293333640682157881879771 51440000461023236822819657)
    ·
      refine ⟨38580000345767427617114743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51440000461023236822819657 38580000345767427617114743)
      ·
        refine ⟨57870000518651141425672115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38580000345767427617114743 57870000518651141425672115)
        ·
          refine ⟨86805000777976712138508173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57870000518651141425672115 86805000777976712138508173)
          ·
            refine ⟨32551875291741267051940565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86805000777976712138508173 32551875291741267051940565)
            ·
              refine ⟨762934577150185946529857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 32551875291741267051940565 762934577150185946529857)
              ·
                refine ⟨572200932862639459897393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 762934577150185946529857 572200932862639459897393)
                ·
                  refine ⟨429150699646979594923045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 572200932862639459897393 429150699646979594923045)
                  ·
                    rfl

theorem cell20_940239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 7, 2, 2].length) (baseStart_940239 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_940239 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_940239 prefixEnd_940239 := by exact prefixLift 940239
  have htrace : WordTrace (prefixWord ++ tailWord_940239) baseStart_940239 baseEnd_940239 := by
    simpa [prefixWord, tailWord_940239, baseEnd_940239] using wordTrace_append hprefix tailTrace_940239
  have hstable : (prefixWord ++ tailWord_940239).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940239).length < 2 ^ (prefixWord ++ tailWord_940239).sum := by decide
  have hdescent : baseEnd_940239 < baseStart_940239 := by decide
  rcases family_descends (prefixWord ++ tailWord_940239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940246 : List Nat := [5, 2, 1, 2, 1, 1, 1, 7]
def baseStart_940246 : Nat := 118140960795 + 940246 * 2 ^ 59
def prefixEnd_940246 : Nat := 4983230072969 + 3 ^ 40 * 940246 * 2
def baseEnd_940246 : Nat := 143051298212572893896561

theorem tailTrace_940246 : CollatzResearch.WordTrace tailWord_940246 prefixEnd_940246 143051298212572893896561 := by
  unfold tailWord_940246
  simp only [CollatzResearch.WordTrace]
  refine ⟨2143349309478549879836537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22862392634437865384923061 2143349309478549879836537)
  ·
    refine ⟨1607511982108912409877403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2143349309478549879836537 1607511982108912409877403)
    ·
      refine ⟨2411267973163368614816105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1607511982108912409877403 2411267973163368614816105)
      ·
        refine ⟨1808450979872526461112079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2411267973163368614816105 1808450979872526461112079)
        ·
          refine ⟨2712676469808789691668119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1808450979872526461112079 2712676469808789691668119)
          ·
            refine ⟨4069014704713184537502179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2712676469808789691668119 4069014704713184537502179)
            ·
              refine ⟨6103522057069776806253269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4069014704713184537502179 6103522057069776806253269)
              ·
                refine ⟨143051298212572893896561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6103522057069776806253269 143051298212572893896561)
                ·
                  rfl

theorem cell20_940246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 7].length) (baseStart_940246 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_940246 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_940246 prefixEnd_940246 := by exact prefixLift 940246
  have htrace : WordTrace (prefixWord ++ tailWord_940246) baseStart_940246 baseEnd_940246 := by
    simpa [prefixWord, tailWord_940246, baseEnd_940246] using wordTrace_append hprefix tailTrace_940246
  have hstable : (prefixWord ++ tailWord_940246).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940246).length < 2 ^ (prefixWord ++ tailWord_940246).sum := by decide
  have hdescent : baseEnd_940246 < baseStart_940246 := by decide
  rcases family_descends (prefixWord ++ tailWord_940246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940250 : List Nat := [3, 1, 1, 2, 2, 1, 3, 7]
def baseStart_940250 : Nat := 118140960795 + 940250 * 2 ^ 59
def prefixEnd_940250 : Nat := 4983230072969 + 3 ^ 40 * 940250 * 2
def baseEnd_940250 : Nat := 143051906782237481852111

theorem tailTrace_940250 : CollatzResearch.WordTrace tailWord_940250 prefixEnd_940250 143051906782237481852111 := by
  unfold tailWord_940250
  simp only [CollatzResearch.WordTrace]
  refine ⟨8573433710910576690132551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22862489895761537840353469 8573433710910576690132551)
  ·
    refine ⟨12860150566365865035198827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8573433710910576690132551 12860150566365865035198827)
    ·
      refine ⟨19290225849548797552798241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12860150566365865035198827 19290225849548797552798241)
      ·
        refine ⟨14467669387161598164598681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19290225849548797552798241 14467669387161598164598681)
        ·
          refine ⟨10850752040371198623449011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14467669387161598164598681 10850752040371198623449011)
          ·
            refine ⟨16276128060556797935173517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10850752040371198623449011 16276128060556797935173517)
            ·
              refine ⟨6103548022708799225690069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16276128060556797935173517 6103548022708799225690069)
              ·
                refine ⟨143051906782237481852111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6103548022708799225690069 143051906782237481852111)
                ·
                  rfl

theorem cell20_940250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 7].length) (baseStart_940250 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_940250 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_940250 prefixEnd_940250 := by exact prefixLift 940250
  have htrace : WordTrace (prefixWord ++ tailWord_940250) baseStart_940250 baseEnd_940250 := by
    simpa [prefixWord, tailWord_940250, baseEnd_940250] using wordTrace_append hprefix tailTrace_940250
  have hstable : (prefixWord ++ tailWord_940250).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940250).length < 2 ^ (prefixWord ++ tailWord_940250).sum := by decide
  have hdescent : baseEnd_940250 < baseStart_940250 := by decide
  rcases family_descends (prefixWord ++ tailWord_940250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940305 : List Nat := [1, 2, 2, 1, 1, 7, 1, 5]
def baseStart_940305 : Nat := 118140960795 + 940305 * 2 ^ 59
def prefixEnd_940305 : Nat := 4983230072969 + 3 ^ 40 * 940305 * 2
def baseEnd_940305 : Nat := 143060274615125566240925

theorem tailTrace_940305 : CollatzResearch.WordTrace tailWord_940305 prefixEnd_940305 143060274615125566240925 := by
  unfold tailWord_940305
  simp only [CollatzResearch.WordTrace]
  refine ⟨34295740858443051153782369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22863827238962034102521579 34295740858443051153782369)
  ·
    refine ⟨25721805643832288365336777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34295740858443051153782369 25721805643832288365336777)
    ·
      refine ⟨19291354232874216274002583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25721805643832288365336777 19291354232874216274002583)
      ·
        refine ⟨28937031349311324411003875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19291354232874216274002583 28937031349311324411003875)
        ·
          refine ⟨43405547023966986616505813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28937031349311324411003875 43405547023966986616505813)
          ·
            refine ⟨1017317508374226248824355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 43405547023966986616505813 1017317508374226248824355)
            ·
              refine ⟨1525976262561339373236533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1017317508374226248824355 1525976262561339373236533)
              ·
                refine ⟨143060274615125566240925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1525976262561339373236533 143060274615125566240925)
                ·
                  rfl

theorem cell20_940305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 1, 5].length) (baseStart_940305 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_940305 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_940305 prefixEnd_940305 := by exact prefixLift 940305
  have htrace : WordTrace (prefixWord ++ tailWord_940305) baseStart_940305 baseEnd_940305 := by
    simpa [prefixWord, tailWord_940305, baseEnd_940305] using wordTrace_append hprefix tailTrace_940305
  have hstable : (prefixWord ++ tailWord_940305).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940305).length < 2 ^ (prefixWord ++ tailWord_940305).sum := by decide
  have hdescent : baseEnd_940305 < baseStart_940305 := by decide
  rcases family_descends (prefixWord ++ tailWord_940305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940312 : List Nat := [2, 1, 2, 3, 1, 2, 1, 5, 3]
def baseStart_940312 : Nat := 118140960795 + 940312 * 2 ^ 59
def prefixEnd_940312 : Nat := 4983230072969 + 3 ^ 40 * 940312 * 2
def baseEnd_940312 : Nat := 429184018836115785489413

theorem tailTrace_940312 : CollatzResearch.WordTrace tailWord_940312 prefixEnd_940312 429184018836115785489413 := by
  unfold tailWord_940312
  simp only [CollatzResearch.WordTrace]
  refine ⟨17147998084708845674643595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22863997446278460899524793 17147998084708845674643595)
  ·
    refine ⟨25721997127063268511965393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17147998084708845674643595 25721997127063268511965393)
    ·
      refine ⟨19291497845297451383974045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25721997127063268511965393 19291497845297451383974045)
      ·
        refine ⟨7234311691986544268990267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19291497845297451383974045 7234311691986544268990267)
        ·
          refine ⟨10851467537979816403485401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7234311691986544268990267 10851467537979816403485401)
          ·
            refine ⟨8138600653484862302614051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10851467537979816403485401 8138600653484862302614051)
            ·
              refine ⟨12207900980227293453921077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8138600653484862302614051 12207900980227293453921077)
              ·
                refine ⟨1144490716896308761305101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12207900980227293453921077 1144490716896308761305101)
                ·
                  refine ⟨429184018836115785489413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1144490716896308761305101 429184018836115785489413)
                  ·
                    rfl

theorem cell20_940312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 5, 3].length) (baseStart_940312 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_940312 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_940312 prefixEnd_940312 := by exact prefixLift 940312
  have htrace : WordTrace (prefixWord ++ tailWord_940312) baseStart_940312 baseEnd_940312 := by
    simpa [prefixWord, tailWord_940312, baseEnd_940312] using wordTrace_append hprefix tailTrace_940312
  have hstable : (prefixWord ++ tailWord_940312).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940312).length < 2 ^ (prefixWord ++ tailWord_940312).sum := by decide
  have hdescent : baseEnd_940312 < baseStart_940312 := by decide
  rcases family_descends (prefixWord ++ tailWord_940312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940319 : List Nat := [1, 1, 2, 4, 3, 1, 1, 1, 6]
def baseStart_940319 : Nat := 118140960795 + 940319 * 2 ^ 59
def prefixEnd_940319 : Nat := 4983230072969 + 3 ^ 40 * 940319 * 2
def baseEnd_940319 : Nat := 429187213826854872256051

theorem tailTrace_940319 : CollatzResearch.WordTrace tailWord_940319 prefixEnd_940319 429187213826854872256051 := by
  unfold tailWord_940319
  simp only [CollatzResearch.WordTrace]
  refine ⟨34296251480392331544792011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22864167653594887696528007 34296251480392331544792011)
  ·
    refine ⟨51444377220588497317188017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34296251480392331544792011 51444377220588497317188017)
    ·
      refine ⟨38583282915441372987891013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51444377220588497317188017 38583282915441372987891013)
      ·
        refine ⟨7234365546645257435229565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38583282915441372987891013 7234365546645257435229565)
        ·
          refine ⟨2712887079991971538211087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7234365546645257435229565 2712887079991971538211087)
          ·
            refine ⟨4069330619987957307316631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2712887079991971538211087 4069330619987957307316631)
            ·
              refine ⟨6103995929981935960974947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4069330619987957307316631 6103995929981935960974947)
              ·
                refine ⟨9155993894972903941462421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6103995929981935960974947 9155993894972903941462421)
                ·
                  refine ⟨429187213826854872256051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9155993894972903941462421 429187213826854872256051)
                  ·
                    rfl

theorem cell20_940319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 1, 6].length) (baseStart_940319 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_940319 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_940319 prefixEnd_940319 := by exact prefixLift 940319
  have htrace : WordTrace (prefixWord ++ tailWord_940319) baseStart_940319 baseEnd_940319 := by
    simpa [prefixWord, tailWord_940319, baseEnd_940319] using wordTrace_append hprefix tailTrace_940319
  have hstable : (prefixWord ++ tailWord_940319).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940319).length < 2 ^ (prefixWord ++ tailWord_940319).sum := by decide
  have hdescent : baseEnd_940319 < baseStart_940319 := by decide
  rcases family_descends (prefixWord ++ tailWord_940319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940322 : List Nat := [3, 3, 1, 1, 3, 2, 3, 4]
def baseStart_940322 : Nat := 118140960795 + 940322 * 2 ^ 59
def prefixEnd_940322 : Nat := 4983230072969 + 3 ^ 40 * 940322 * 2
def baseEnd_940322 : Nat := 143062861036200065052013

theorem tailTrace_940322 : CollatzResearch.WordTrace tailWord_940322 prefixEnd_940322 143062861036200065052013 := by
  unfold tailWord_940322
  simp only [CollatzResearch.WordTrace]
  refine ⟨8574090224845365764287805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22864240599587642038100813 8574090224845365764287805)
  ·
    refine ⟨3215283834317012161607927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8574090224845365764287805 3215283834317012161607927)
    ·
      refine ⟨4822925751475518242411891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3215283834317012161607927 4822925751475518242411891)
      ·
        refine ⟨7234388627213277363617837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4822925751475518242411891 7234388627213277363617837)
        ·
          refine ⟨2712895735204979011356689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7234388627213277363617837 2712895735204979011356689)
          ·
            refine ⟨2034671801403734258517517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2712895735204979011356689 2034671801403734258517517)
            ·
              refine ⟨763001925526400346944069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2034671801403734258517517 763001925526400346944069)
              ·
                refine ⟨143062861036200065052013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 763001925526400346944069 143062861036200065052013)
                ·
                  rfl

theorem cell20_940322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 3, 4].length) (baseStart_940322 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_940322 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_940322 prefixEnd_940322 := by exact prefixLift 940322
  have htrace : WordTrace (prefixWord ++ tailWord_940322) baseStart_940322 baseEnd_940322 := by
    simpa [prefixWord, tailWord_940322, baseEnd_940322] using wordTrace_append hprefix tailTrace_940322
  have hstable : (prefixWord ++ tailWord_940322).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940322).length < 2 ^ (prefixWord ++ tailWord_940322).sum := by decide
  have hdescent : baseEnd_940322 < baseStart_940322 := by decide
  rcases family_descends (prefixWord ++ tailWord_940322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940353 : List Nat := [1, 2, 5, 2, 2, 1, 2, 1, 4]
def baseStart_940353 : Nat := 118140960795 + 940353 * 2 ^ 59
def prefixEnd_940353 : Nat := 4983230072969 + 3 ^ 40 * 940353 * 2
def baseEnd_940353 : Nat := 429202732353301865122579

theorem tailTrace_940353 : CollatzResearch.WordTrace tailWord_940353 prefixEnd_940353 429202732353301865122579 := by
  unfold tailWord_940353
  simp only [CollatzResearch.WordTrace]
  refine ⟨34297491562269155351529713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22864994374846103567686475 34297491562269155351529713)
  ·
    refine ⟨25723118671701866513647285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34297491562269155351529713 25723118671701866513647285)
    ·
      refine ⟨2411542375472049985654433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25723118671701866513647285 2411542375472049985654433)
      ·
        refine ⟨1808656781604037489240825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2411542375472049985654433 1808656781604037489240825)
        ·
          refine ⟨1356492586203028116930619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1808656781604037489240825 1356492586203028116930619)
          ·
            refine ⟨2034738879304542175395929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1356492586203028116930619 2034738879304542175395929)
            ·
              refine ⟨1526054159478406631546947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2034738879304542175395929 1526054159478406631546947)
              ·
                refine ⟨2289081239217609947320421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1526054159478406631546947 2289081239217609947320421)
                ·
                  refine ⟨429202732353301865122579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2289081239217609947320421 429202732353301865122579)
                  ·
                    rfl

theorem cell20_940353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 2, 1, 4].length) (baseStart_940353 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_940353 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_940353 prefixEnd_940353 := by exact prefixLift 940353
  have htrace : WordTrace (prefixWord ++ tailWord_940353) baseStart_940353 baseEnd_940353 := by
    simpa [prefixWord, tailWord_940353, baseEnd_940353] using wordTrace_append hprefix tailTrace_940353
  have hstable : (prefixWord ++ tailWord_940353).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940353).length < 2 ^ (prefixWord ++ tailWord_940353).sum := by decide
  have hdescent : baseEnd_940353 < baseStart_940353 := by decide
  rcases family_descends (prefixWord ++ tailWord_940353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940364 : List Nat := [2, 2, 1, 3, 2, 1, 2, 7]
def baseStart_940364 : Nat := 118140960795 + 940364 * 2 ^ 59
def prefixEnd_940364 : Nat := 4983230072969 + 3 ^ 40 * 940364 * 2
def baseEnd_940364 : Nat := 143069251017678238585289

theorem tailTrace_940364 : CollatzResearch.WordTrace tailWord_940364 prefixEnd_940364 143069251017678238585289 := by
  unfold tailWord_940364
  simp only [CollatzResearch.WordTrace]
  refine ⟨17148946382614652115090073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22865261843486202820120097 17148946382614652115090073)
  ·
    refine ⟨12861709786960989086317555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17148946382614652115090073 12861709786960989086317555)
    ·
      refine ⟨19292564680441483629476333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12861709786960989086317555 19292564680441483629476333)
      ·
        refine ⟨7234711755165556361053625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19292564680441483629476333 7234711755165556361053625)
        ·
          refine ⟨5426033816374167270790219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7234711755165556361053625 5426033816374167270790219)
          ·
            refine ⟨8139050724561250906185329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5426033816374167270790219 8139050724561250906185329)
            ·
              refine ⟨6104288043420938179638997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8139050724561250906185329 6104288043420938179638997)
              ·
                refine ⟨143069251017678238585289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6104288043420938179638997 143069251017678238585289)
                ·
                  rfl

theorem cell20_940364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 7].length) (baseStart_940364 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_940364 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_940364 prefixEnd_940364 := by exact prefixLift 940364
  have htrace : WordTrace (prefixWord ++ tailWord_940364) baseStart_940364 baseEnd_940364 := by
    simpa [prefixWord, tailWord_940364, baseEnd_940364] using wordTrace_append hprefix tailTrace_940364
  have hstable : (prefixWord ++ tailWord_940364).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940364).length < 2 ^ (prefixWord ++ tailWord_940364).sum := by decide
  have hdescent : baseEnd_940364 < baseStart_940364 := by decide
  rcases family_descends (prefixWord ++ tailWord_940364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940391 : List Nat := [1, 1, 5, 1, 3, 1, 3, 3, 2]
def baseStart_940391 : Nat := 118140960795 + 940391 * 2 ^ 59
def prefixEnd_940391 : Nat := 4983230072969 + 3 ^ 40 * 940391 * 2
def baseEnd_940391 : Nat := 429220076588742621855757

theorem tailTrace_940391 : CollatzResearch.WordTrace tailWord_940391 prefixEnd_940391 429220076588742621855757 := by
  unfold tailWord_940391
  simp only [CollatzResearch.WordTrace]
  refine ⟨34298877536131487841413027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22865918357420991894275351 34298877536131487841413027)
  ·
    refine ⟨51448316304197231762119541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34298877536131487841413027 51448316304197231762119541)
    ·
      refine ⟨4823279653518490477698707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51448316304197231762119541 4823279653518490477698707)
      ·
        refine ⟨7234919480277735716548061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4823279653518490477698707 7234919480277735716548061)
        ·
          refine ⟨2713094805104150893705523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7234919480277735716548061 2713094805104150893705523)
          ·
            refine ⟨4069642207656226340558285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2713094805104150893705523 4069642207656226340558285)
            ·
              refine ⟨1526115827871084877709357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4069642207656226340558285 1526115827871084877709357)
              ·
                refine ⟨572293435451656829141009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1526115827871084877709357 572293435451656829141009)
                ·
                  refine ⟨429220076588742621855757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 572293435451656829141009 429220076588742621855757)
                  ·
                    rfl

theorem cell20_940391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 3, 3, 2].length) (baseStart_940391 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_940391 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_940391 prefixEnd_940391 := by exact prefixLift 940391
  have htrace : WordTrace (prefixWord ++ tailWord_940391) baseStart_940391 baseEnd_940391 := by
    simpa [prefixWord, tailWord_940391, baseEnd_940391] using wordTrace_append hprefix tailTrace_940391
  have hstable : (prefixWord ++ tailWord_940391).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940391).length < 2 ^ (prefixWord ++ tailWord_940391).sum := by decide
  have hdescent : baseEnd_940391 < baseStart_940391 := by decide
  rcases family_descends (prefixWord ++ tailWord_940391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940402 : List Nat := [3, 2, 1, 2, 1, 3, 8]
def baseStart_940402 : Nat := 118140960795 + 940402 * 2 ^ 59
def prefixEnd_940402 : Nat := 4983230072969 + 3 ^ 40 * 940402 * 2
def baseEnd_940402 : Nat := 47691677476497274721005

theorem tailTrace_940402 : CollatzResearch.WordTrace tailWord_940402 prefixEnd_940402 47691677476497274721005 := by
  unfold tailWord_940402
  simp only [CollatzResearch.WordTrace]
  refine ⟨8574819684772909180015865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22866185826061091146708973 8574819684772909180015865)
  ·
    refine ⟨6431114763579681885011899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8574819684772909180015865 6431114763579681885011899)
    ·
      refine ⟨9646672145369522827517849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6431114763579681885011899 9646672145369522827517849)
      ·
        refine ⟨7235004109027142120638387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9646672145369522827517849 7235004109027142120638387)
        ·
          refine ⟨10852506163540713180957581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7235004109027142120638387 10852506163540713180957581)
          ·
            refine ⟨4069689811327767442859093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10852506163540713180957581 4069689811327767442859093)
            ·
              refine ⟨47691677476497274721005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4069689811327767442859093 47691677476497274721005)
              ·
                rfl

theorem cell20_940402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 8].length) (baseStart_940402 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_940402 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_940402 prefixEnd_940402 := by exact prefixLift 940402
  have htrace : WordTrace (prefixWord ++ tailWord_940402) baseStart_940402 baseEnd_940402 := by
    simpa [prefixWord, tailWord_940402, baseEnd_940402] using wordTrace_append hprefix tailTrace_940402
  have hstable : (prefixWord ++ tailWord_940402).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940402).length < 2 ^ (prefixWord ++ tailWord_940402).sum := by decide
  have hdescent : baseEnd_940402 < baseStart_940402 := by decide
  rcases family_descends (prefixWord ++ tailWord_940402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940418 : List Nat := [3, 4, 2, 1, 2, 2, 2, 1, 3]
def baseStart_940418 : Nat := 118140960795 + 940418 * 2 ^ 59
def prefixEnd_940418 : Nat := 4983230072969 + 3 ^ 40 * 940418 * 2
def baseEnd_940418 : Nat := 429232400124450527955647

theorem tailTrace_940418 : CollatzResearch.WordTrace tailWord_940418 prefixEnd_940418 429232400124450527955647 := by
  unfold tailWord_940418
  simp only [CollatzResearch.WordTrace]
  refine ⟨8574965576758417863161477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22866574871355780968430605 8574965576758417863161477)
  ·
    refine ⟨1607806045642203349342777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8574965576758417863161477 1607806045642203349342777)
    ·
      refine ⟨1205854534231652512007083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1607806045642203349342777 1205854534231652512007083)
      ·
        refine ⟨1808781801347478768010625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1205854534231652512007083 1808781801347478768010625)
        ·
          refine ⟨1356586351010609076007969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1808781801347478768010625 1356586351010609076007969)
          ·
            refine ⟨1017439763257956807005977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1356586351010609076007969 1017439763257956807005977)
            ·
              refine ⟨763079822443467605254483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1017439763257956807005977 763079822443467605254483)
              ·
                refine ⟨1144619733665201407881725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 763079822443467605254483 1144619733665201407881725)
                ·
                  refine ⟨429232400124450527955647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1144619733665201407881725 429232400124450527955647)
                  ·
                    rfl

theorem cell20_940418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_940418 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_940418 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_940418 prefixEnd_940418 := by exact prefixLift 940418
  have htrace : WordTrace (prefixWord ++ tailWord_940418) baseStart_940418 baseEnd_940418 := by
    simpa [prefixWord, tailWord_940418, baseEnd_940418] using wordTrace_append hprefix tailTrace_940418
  have hstable : (prefixWord ++ tailWord_940418).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940418).length < 2 ^ (prefixWord ++ tailWord_940418).sum := by decide
  have hdescent : baseEnd_940418 < baseStart_940418 := by decide
  rcases family_descends (prefixWord ++ tailWord_940418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940419 : List Nat := [1, 1, 1, 3, 6, 1, 2, 5]
def baseStart_940419 : Nat := 118140960795 + 940419 * 2 ^ 59
def prefixEnd_940419 : Nat := 4983230072969 + 3 ^ 40 * 940419 * 2
def baseEnd_940419 : Nat := 143077618850566322974103

theorem tailTrace_940419 : CollatzResearch.WordTrace tailWord_940419 prefixEnd_940419 143077618850566322974103 := by
  unfold tailWord_940419
  simp only [CollatzResearch.WordTrace]
  refine ⟨34299898780030048623432311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22866599186686699082288207 34299898780030048623432311)
  ·
    refine ⟨51449848170045072935148467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34299898780030048623432311 51449848170045072935148467)
    ·
      refine ⟨77174772255067609402722701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51449848170045072935148467 77174772255067609402722701)
      ·
        refine ⟨28940539595650353526021013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77174772255067609402722701 28940539595650353526021013)
        ·
          refine ⟨1356587793546110321532235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 28940539595650353526021013 1356587793546110321532235)
          ·
            refine ⟨2034881690319165482298353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1356587793546110321532235 2034881690319165482298353)
            ·
              refine ⟨1526161267739374111723765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2034881690319165482298353 1526161267739374111723765)
              ·
                refine ⟨143077618850566322974103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1526161267739374111723765 143077618850566322974103)
                ·
                  rfl

theorem cell20_940419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 2, 5].length) (baseStart_940419 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_940419 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_940419 prefixEnd_940419 := by exact prefixLift 940419
  have htrace : WordTrace (prefixWord ++ tailWord_940419) baseStart_940419 baseEnd_940419 := by
    simpa [prefixWord, tailWord_940419, baseEnd_940419] using wordTrace_append hprefix tailTrace_940419
  have hstable : (prefixWord ++ tailWord_940419).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940419).length < 2 ^ (prefixWord ++ tailWord_940419).sum := by decide
  have hdescent : baseEnd_940419 < baseStart_940419 := by decide
  rcases family_descends (prefixWord ++ tailWord_940419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940509 : List Nat := [1, 4, 3, 1, 1, 1, 1, 2, 6]
def baseStart_940509 : Nat := 118140960795 + 940509 * 2 ^ 59
def prefixEnd_940509 : Nat := 4983230072969 + 3 ^ 40 * 940509 * 2
def baseEnd_940509 : Nat := 429273935004058655921941

theorem tailTrace_940509 : CollatzResearch.WordTrace tailWord_940509 prefixEnd_940509 429273935004058655921941 := by
  unfold tailWord_940509
  simp only [CollatzResearch.WordTrace]
  refine ⟨34303181349703993994208581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22868787566469329329472387 34303181349703993994208581)
  ·
    refine ⟨6431846503069498873914109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34303181349703993994208581 6431846503069498873914109)
    ·
      refine ⟨2411942438651062077717791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6431846503069498873914109 2411942438651062077717791)
      ·
        refine ⟨3617913657976593116576687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2411942438651062077717791 3617913657976593116576687)
        ·
          refine ⟨5426870486964889674865031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3617913657976593116576687 5426870486964889674865031)
          ·
            refine ⟨8140305730447334512297547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5426870486964889674865031 8140305730447334512297547)
            ·
              refine ⟨12210458595671001768446321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8140305730447334512297547 12210458595671001768446321)
              ·
                refine ⟨9157843946753251326334741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12210458595671001768446321 9157843946753251326334741)
                ·
                  refine ⟨429273935004058655921941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9157843946753251326334741 429273935004058655921941)
                  ·
                    rfl

theorem cell20_940509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 2, 6].length) (baseStart_940509 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_940509 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_940509 prefixEnd_940509 := by exact prefixLift 940509
  have htrace : WordTrace (prefixWord ++ tailWord_940509) baseStart_940509 baseEnd_940509 := by
    simpa [prefixWord, tailWord_940509, baseEnd_940509] using wordTrace_append hprefix tailTrace_940509
  have hstable : (prefixWord ++ tailWord_940509).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940509).length < 2 ^ (prefixWord ++ tailWord_940509).sum := by decide
  have hdescent : baseEnd_940509 < baseStart_940509 := by decide
  rcases family_descends (prefixWord ++ tailWord_940509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940523 : List Nat := [1, 1, 1, 1, 2, 3, 5, 1, 5]
def baseStart_940523 : Nat := 118140960795 + 940523 * 2 ^ 59
def prefixEnd_940523 : Nat := 4983230072969 + 3 ^ 40 * 940523 * 2
def baseEnd_940523 : Nat := 429280324985536829455217

theorem tailTrace_940523 : CollatzResearch.WordTrace tailWord_940523 prefixEnd_940523 429280324985536829455217 := by
  unfold tailWord_940523
  simp only [CollatzResearch.WordTrace]
  refine ⟨34303691971653274385218223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22869127981102182923478815 34303691971653274385218223)
  ·
    refine ⟨51455537957479911577827335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34303691971653274385218223 51455537957479911577827335)
    ·
      refine ⟨77183306936219867366741003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51455537957479911577827335 77183306936219867366741003)
      ·
        refine ⟨115774960404329801050111505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77183306936219867366741003 115774960404329801050111505)
        ·
          refine ⟨86831220303247350787583629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115774960404329801050111505 86831220303247350787583629)
          ·
            refine ⟨32561707613717756545343861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86831220303247350787583629 32561707613717756545343861)
            ·
              refine ⟨3052660088786039676125987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32561707613717756545343861 3052660088786039676125987)
              ·
                refine ⟨4578990133179059514188981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3052660088786039676125987 4578990133179059514188981)
                ·
                  refine ⟨429280324985536829455217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4578990133179059514188981 429280324985536829455217)
                  ·
                    rfl

theorem cell20_940523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 1, 5].length) (baseStart_940523 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_940523 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_940523 prefixEnd_940523 := by exact prefixLift 940523
  have htrace : WordTrace (prefixWord ++ tailWord_940523) baseStart_940523 baseEnd_940523 := by
    simpa [prefixWord, tailWord_940523, baseEnd_940523] using wordTrace_append hprefix tailTrace_940523
  have hstable : (prefixWord ++ tailWord_940523).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940523).length < 2 ^ (prefixWord ++ tailWord_940523).sum := by decide
  have hdescent : baseEnd_940523 < baseStart_940523 := by decide
  rcases family_descends (prefixWord ++ tailWord_940523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940526 : List Nat := [4, 1, 2, 1, 2, 3, 2, 1, 4]
def baseStart_940526 : Nat := 118140960795 + 940526 * 2 ^ 59
def prefixEnd_940526 : Nat := 4983230072969 + 3 ^ 40 * 940526 * 2
def baseEnd_940526 : Nat := 429281694267282152355205

theorem tailTrace_940526 : CollatzResearch.WordTrace tailWord_940526 prefixEnd_940526 429281694267282152355205 := by
  unfold tailWord_940526
  simp only [CollatzResearch.WordTrace]
  refine ⟨4287975173830300737197179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22869200927094937265051621 4287975173830300737197179)
  ·
    refine ⟨6431962760745451105795769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4287975173830300737197179 6431962760745451105795769)
    ·
      refine ⟨4823972070559088329346827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6431962760745451105795769 4823972070559088329346827)
      ·
        refine ⟨7235958105838632494020241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4823972070559088329346827 7235958105838632494020241)
        ·
          refine ⟨5426968579378974370515181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7235958105838632494020241 5426968579378974370515181)
          ·
            refine ⟨2035113217267115388943193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5426968579378974370515181 2035113217267115388943193)
            ·
              refine ⟨1526334912950336541707395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2035113217267115388943193 1526334912950336541707395)
              ·
                refine ⟨2289502369425504812561093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1526334912950336541707395 2289502369425504812561093)
                ·
                  refine ⟨429281694267282152355205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2289502369425504812561093 429281694267282152355205)
                  ·
                    rfl

theorem cell20_940526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 2, 1, 4].length) (baseStart_940526 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_940526 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_940526 prefixEnd_940526 := by exact prefixLift 940526
  have htrace : WordTrace (prefixWord ++ tailWord_940526) baseStart_940526 baseEnd_940526 := by
    simpa [prefixWord, tailWord_940526, baseEnd_940526] using wordTrace_append hprefix tailTrace_940526
  have hstable : (prefixWord ++ tailWord_940526).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940526).length < 2 ^ (prefixWord ++ tailWord_940526).sum := by decide
  have hdescent : baseEnd_940526 < baseStart_940526 := by decide
  rcases family_descends (prefixWord ++ tailWord_940526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940546 : List Nat := [3, 4, 1, 2, 3, 1, 2, 4]
def baseStart_940546 : Nat := 118140960795 + 940546 * 2 ^ 59
def prefixEnd_940546 : Nat := 4983230072969 + 3 ^ 40 * 940546 * 2
def baseEnd_940546 : Nat := 143096940937416990562819

theorem tailTrace_940546 : CollatzResearch.WordTrace tailWord_940546 prefixEnd_940546 143096940937416990562819 := by
  unfold tailWord_940546
  simp only [CollatzResearch.WordTrace]
  refine ⟨8576132712642487328326373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22869687233713299542203661 8576132712642487328326373)
  ·
    refine ⟨1608024883620466374061195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8576132712642487328326373 1608024883620466374061195)
    ·
      refine ⟨2412037325430699561091793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1608024883620466374061195 2412037325430699561091793)
      ·
        refine ⟨1809027994073024670818845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2412037325430699561091793 1809027994073024670818845)
        ·
          refine ⟨678385497777384251557067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1809027994073024670818845 678385497777384251557067)
          ·
            refine ⟨1017578246666076377335601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 678385497777384251557067 1017578246666076377335601)
            ·
              refine ⟨763183684999557283001701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1017578246666076377335601 763183684999557283001701)
              ·
                refine ⟨143096940937416990562819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 763183684999557283001701 143096940937416990562819)
                ·
                  rfl

theorem cell20_940546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 2, 4].length) (baseStart_940546 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_940546 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_940546 prefixEnd_940546 := by exact prefixLift 940546
  have htrace : WordTrace (prefixWord ++ tailWord_940546) baseStart_940546 baseEnd_940546 := by
    simpa [prefixWord, tailWord_940546, baseEnd_940546] using wordTrace_append hprefix tailTrace_940546
  have hstable : (prefixWord ++ tailWord_940546).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940546).length < 2 ^ (prefixWord ++ tailWord_940546).sum := by decide
  have hdescent : baseEnd_940546 < baseStart_940546 := by decide
  rcases family_descends (prefixWord ++ tailWord_940546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940554 : List Nat := [3, 1, 2, 2, 2, 1, 3, 6]
def baseStart_940554 : Nat := 118140960795 + 940554 * 2 ^ 59
def prefixEnd_940554 : Nat := 4983230072969 + 3 ^ 40 * 940554 * 2
def baseEnd_940554 : Nat := 143098158076746166473919

theorem tailTrace_940554 : CollatzResearch.WordTrace tailWord_940554 prefixEnd_940554 143098158076746166473919 := by
  unfold tailWord_940554
  simp only [CollatzResearch.WordTrace]
  refine ⟨8576205658635241669899179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22869881756360644453064477 8576205658635241669899179)
  ·
    refine ⟨12864308487952862504848769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8576205658635241669899179 12864308487952862504848769)
    ·
      refine ⟨9648231365964646878636577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12864308487952862504848769 9648231365964646878636577)
      ·
        refine ⟨7236173524473485158977433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9648231365964646878636577 7236173524473485158977433)
        ·
          refine ⟨5427130143355113869233075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7236173524473485158977433 5427130143355113869233075)
          ·
            refine ⟨8140695215032670803849613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5427130143355113869233075 8140695215032670803849613)
            ·
              refine ⟨3052760705637251551443605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8140695215032670803849613 3052760705637251551443605)
              ·
                refine ⟨143098158076746166473919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3052760705637251551443605 143098158076746166473919)
                ·
                  rfl

theorem cell20_940554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 6].length) (baseStart_940554 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_940554 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_940554 prefixEnd_940554 := by exact prefixLift 940554
  have htrace : WordTrace (prefixWord ++ tailWord_940554) baseStart_940554 baseEnd_940554 := by
    simpa [prefixWord, tailWord_940554, baseEnd_940554] using wordTrace_append hprefix tailTrace_940554
  have hstable : (prefixWord ++ tailWord_940554).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940554).length < 2 ^ (prefixWord ++ tailWord_940554).sum := by decide
  have hdescent : baseEnd_940554 < baseStart_940554 := by decide
  rcases family_descends (prefixWord ++ tailWord_940554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940578 : List Nat := [3, 3, 1, 1, 1, 1, 1, 6, 3]
def baseStart_940578 : Nat := 118140960795 + 940578 * 2 ^ 59
def prefixEnd_940578 : Nat := 4983230072969 + 3 ^ 40 * 940578 * 2
def baseEnd_940578 : Nat := 429305428484201082621659

theorem tailTrace_940578 : CollatzResearch.WordTrace tailWord_940578 prefixEnd_940578 429305428484201082621659 := by
  unfold tailWord_940578
  simp only [CollatzResearch.WordTrace]
  refine ⟨8576424496613504694617597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22870465324302679185646925 8576424496613504694617597)
  ·
    refine ⟨3216159186230064260481599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8576424496613504694617597 3216159186230064260481599)
    ·
      refine ⟨4824238779345096390722399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3216159186230064260481599 4824238779345096390722399)
      ·
        refine ⟨7236358169017644586083599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4824238779345096390722399 7236358169017644586083599)
        ·
          refine ⟨10854537253526466879125399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7236358169017644586083599 10854537253526466879125399)
          ·
            refine ⟨16281805880289700318688099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10854537253526466879125399 16281805880289700318688099)
            ·
              refine ⟨24422708820434550478032149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16281805880289700318688099 24422708820434550478032149)
              ·
                refine ⟨1144814475957869553657757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 24422708820434550478032149 1144814475957869553657757)
                ·
                  refine ⟨429305428484201082621659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1144814475957869553657757 429305428484201082621659)
                  ·
                    rfl

theorem cell20_940578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 6, 3].length) (baseStart_940578 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_940578 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_940578 prefixEnd_940578 := by exact prefixLift 940578
  have htrace : WordTrace (prefixWord ++ tailWord_940578) baseStart_940578 baseEnd_940578 := by
    simpa [prefixWord, tailWord_940578, baseEnd_940578] using wordTrace_append hprefix tailTrace_940578
  have hstable : (prefixWord ++ tailWord_940578).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940578).length < 2 ^ (prefixWord ++ tailWord_940578).sum := by decide
  have hdescent : baseEnd_940578 < baseStart_940578 := by decide
  rcases family_descends (prefixWord ++ tailWord_940578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940651 : List Nat := [1, 1, 1, 1, 2, 2, 1, 11]
def baseStart_940651 : Nat := 118140960795 + 940651 * 2 ^ 59
def prefixEnd_940651 : Nat := 4983230072969 + 3 ^ 40 * 940651 * 2
def baseEnd_940651 : Nat := 143112915891112424396009

theorem tailTrace_940651 : CollatzResearch.WordTrace tailWord_940651 prefixEnd_940651 143112915891112424396009 := by
  unfold tailWord_940651
  simp only [CollatzResearch.WordTrace]
  refine ⟨34308360515189552245877807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22872240343459701497251871 34308360515189552245877807)
  ·
    refine ⟨51462540772784328368816711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34308360515189552245877807 51462540772784328368816711)
    ·
      refine ⟨77193811159176492553225067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51462540772784328368816711 77193811159176492553225067)
      ·
        refine ⟨115790716738764738829837601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77193811159176492553225067 115790716738764738829837601)
        ·
          refine ⟨86843037554073554122378201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115790716738764738829837601 86843037554073554122378201)
          ·
            refine ⟨65132278165555165591783651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86843037554073554122378201 65132278165555165591783651)
            ·
              refine ⟨97698417248332748387675477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65132278165555165591783651 97698417248332748387675477)
              ·
                refine ⟨143112915891112424396009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 97698417248332748387675477 143112915891112424396009)
                ·
                  rfl

theorem cell20_940651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 11].length) (baseStart_940651 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_940651 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_940651 prefixEnd_940651 := by exact prefixLift 940651
  have htrace : WordTrace (prefixWord ++ tailWord_940651) baseStart_940651 baseEnd_940651 := by
    simpa [prefixWord, tailWord_940651, baseEnd_940651] using wordTrace_append hprefix tailTrace_940651
  have hstable : (prefixWord ++ tailWord_940651).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940651).length < 2 ^ (prefixWord ++ tailWord_940651).sum := by decide
  have hdescent : baseEnd_940651 < baseStart_940651 := by decide
  rcases family_descends (prefixWord ++ tailWord_940651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940723 : List Nat := [1, 1, 1, 2, 3, 6, 2, 4]
def baseStart_940723 : Nat := 118140960795 + 940723 * 2 ^ 59
def prefixEnd_940723 : Nat := 4983230072969 + 3 ^ 40 * 940723 * 2
def baseEnd_940723 : Nat := 143123870145075007595911

theorem tailTrace_940723 : CollatzResearch.WordTrace tailWord_940723 prefixEnd_940723 143123870145075007595911 := by
  unfold tailWord_940723
  simp only [CollatzResearch.WordTrace]
  refine ⟨34310986570928708542498823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22873991047285805694999215 34310986570928708542498823)
  ·
    refine ⟨51466479856393062813748235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34310986570928708542498823 51466479856393062813748235)
    ·
      refine ⟨77199719784589594220622353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51466479856393062813748235 77199719784589594220622353)
      ·
        refine ⟨57899789838442195665466765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77199719784589594220622353 57899789838442195665466765)
        ·
          refine ⟨21712421189415823374550037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57899789838442195665466765 21712421189415823374550037)
          ·
            refine ⟨1017769743253866720682033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 21712421189415823374550037 1017769743253866720682033)
            ·
              refine ⟨763327307440400040511525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1017769743253866720682033 763327307440400040511525)
              ·
                refine ⟨143123870145075007595911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 763327307440400040511525 143123870145075007595911)
                ·
                  rfl

theorem cell20_940723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 2, 4].length) (baseStart_940723 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_940723 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_940723 prefixEnd_940723 := by exact prefixLift 940723
  have htrace : WordTrace (prefixWord ++ tailWord_940723) baseStart_940723 baseEnd_940723 := by
    simpa [prefixWord, tailWord_940723, baseEnd_940723] using wordTrace_append hprefix tailTrace_940723
  have hstable : (prefixWord ++ tailWord_940723).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940723).length < 2 ^ (prefixWord ++ tailWord_940723).sum := by decide
  have hdescent : baseEnd_940723 < baseStart_940723 := by decide
  rcases family_descends (prefixWord ++ tailWord_940723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940733 : List Nat := [1, 4, 1, 2, 1, 5, 1, 3, 2]
def baseStart_940733 : Nat := 118140960795 + 940733 * 2 ^ 59
def prefixEnd_940733 : Nat := 4983230072969 + 3 ^ 40 * 940733 * 2
def baseEnd_940733 : Nat := 429376174707709432454359

theorem tailTrace_940733 : CollatzResearch.WordTrace tailWord_940733 prefixEnd_940733 429376174707709432454359 := by
  unfold tailWord_940733
  simp only [CollatzResearch.WordTrace]
  refine ⟨34311351300892480250362853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22874234200594986833575235 34311351300892480250362853)
  ·
    refine ⟨6433378368917340046943035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34311351300892480250362853 6433378368917340046943035)
    ·
      refine ⟨9650067553376010070414553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6433378368917340046943035 9650067553376010070414553)
      ·
        refine ⟨7237550665032007552810915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9650067553376010070414553 7237550665032007552810915)
        ·
          refine ⟨10856325997548011329216373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7237550665032007552810915 10856325997548011329216373)
          ·
            refine ⟨1017780562270126062114035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10856325997548011329216373 1017780562270126062114035)
            ·
              refine ⟨1526670843405189093171053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1017780562270126062114035 1526670843405189093171053)
              ·
                refine ⟨572501566276945909939145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1526670843405189093171053 572501566276945909939145)
                ·
                  refine ⟨429376174707709432454359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 572501566276945909939145 429376174707709432454359)
                  ·
                    rfl

theorem cell20_940733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 1, 3, 2].length) (baseStart_940733 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_940733 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_940733 prefixEnd_940733 := by exact prefixLift 940733
  have htrace : WordTrace (prefixWord ++ tailWord_940733) baseStart_940733 baseEnd_940733 := by
    simpa [prefixWord, tailWord_940733, baseEnd_940733] using wordTrace_append hprefix tailTrace_940733
  have hstable : (prefixWord ++ tailWord_940733).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940733).length < 2 ^ (prefixWord ++ tailWord_940733).sum := by decide
  have hdescent : baseEnd_940733 < baseStart_940733 := by decide
  rcases family_descends (prefixWord ++ tailWord_940733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940744 : List Nat := [2, 1, 3, 1, 2, 5, 6]
def baseStart_940744 : Nat := 118140960795 + 940744 * 2 ^ 59
def prefixEnd_940744 : Nat := 4983230072969 + 3 ^ 40 * 940744 * 2
def baseEnd_940744 : Nat := 47709021711938031454183

theorem tailTrace_940744 : CollatzResearch.WordTrace tailWord_940744 prefixEnd_940744 47709021711938031454183 := by
  unfold tailWord_940744
  simp only [CollatzResearch.WordTrace]
  refine ⟨17155876251926314564506643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22874501669235086086008857 17155876251926314564506643)
  ·
    refine ⟨25733814377889471846759965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17155876251926314564506643 25733814377889471846759965)
    ·
      refine ⟨9650180391708551942534987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25733814377889471846759965 9650180391708551942534987)
      ·
        refine ⟨14475270587562827913802481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9650180391708551942534987 14475270587562827913802481)
        ·
          refine ⟨10856452940672120935351861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14475270587562827913802481 10856452940672120935351861)
          ·
            refine ⟨1017792463188011337689237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10856452940672120935351861 1017792463188011337689237)
            ·
              refine ⟨47709021711938031454183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1017792463188011337689237 47709021711938031454183)
              ·
                rfl

theorem cell20_940744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 6].length) (baseStart_940744 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_940744 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_940744 prefixEnd_940744 := by exact prefixLift 940744
  have htrace : WordTrace (prefixWord ++ tailWord_940744) baseStart_940744 baseEnd_940744 := by
    simpa [prefixWord, tailWord_940744, baseEnd_940744] using wordTrace_append hprefix tailTrace_940744
  have hstable : (prefixWord ++ tailWord_940744).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940744).length < 2 ^ (prefixWord ++ tailWord_940744).sum := by decide
  have hdescent : baseEnd_940744 < baseStart_940744 := by decide
  rcases family_descends (prefixWord ++ tailWord_940744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940764 : List Nat := [2, 2, 5, 1, 1, 1, 4, 1, 3]
def baseStart_940764 : Nat := 118140960795 + 940764 * 2 ^ 59
def prefixEnd_940764 : Nat := 4983230072969 + 3 ^ 40 * 940764 * 2
def baseEnd_940764 : Nat := 429390323952411102420899

theorem tailTrace_940764 : CollatzResearch.WordTrace tailWord_940764 prefixEnd_940764 429390323952411102420899 := by
  unfold tailWord_940764
  simp only [CollatzResearch.WordTrace]
  refine ⟨17156240981890086272370673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22874987975853448363160897 17156240981890086272370673)
  ·
    refine ⟨12867180736417564704278005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17156240981890086272370673 12867180736417564704278005)
    ·
      refine ⟨1206298194039146691026063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12867180736417564704278005 1206298194039146691026063)
      ·
        refine ⟨1809447291058720036539095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1206298194039146691026063 1809447291058720036539095)
        ·
          refine ⟨2714170936588080054808643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1809447291058720036539095 2714170936588080054808643)
          ·
            refine ⟨4071256404882120082212965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2714170936588080054808643 4071256404882120082212965)
            ·
              refine ⟨763360575915397515414931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4071256404882120082212965 763360575915397515414931)
              ·
                refine ⟨1145040863873096273122397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 763360575915397515414931 1145040863873096273122397)
                ·
                  refine ⟨429390323952411102420899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1145040863873096273122397 429390323952411102420899)
                  ·
                    rfl

theorem cell20_940764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 4, 1, 3].length) (baseStart_940764 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_940764 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_940764 prefixEnd_940764 := by exact prefixLift 940764
  have htrace : WordTrace (prefixWord ++ tailWord_940764) baseStart_940764 baseEnd_940764 := by
    simpa [prefixWord, tailWord_940764, baseEnd_940764] using wordTrace_append hprefix tailTrace_940764
  have hstable : (prefixWord ++ tailWord_940764).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940764).length < 2 ^ (prefixWord ++ tailWord_940764).sum := by decide
  have hdescent : baseEnd_940764 < baseStart_940764 := by decide
  rcases family_descends (prefixWord ++ tailWord_940764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940782 : List Nat := [4, 1, 2, 1, 1, 3, 2, 6]
def baseStart_940782 : Nat := 118140960795 + 940782 * 2 ^ 59
def prefixEnd_940782 : Nat := 4983230072969 + 3 ^ 40 * 940782 * 2
def baseEnd_940782 : Nat := 143132846547627679940275

theorem tailTrace_940782 : CollatzResearch.WordTrace tailWord_940782 prefixEnd_940782 143132846547627679940275 := by
  unfold tailWord_940782
  simp only [CollatzResearch.WordTrace]
  refine ⟨4289142309714370202362075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22875425651809974412597733 4289142309714370202362075)
  ·
    refine ⟨6433713464571555303543113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4289142309714370202362075 6433713464571555303543113)
    ·
      refine ⟨4825285098428666477657335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6433713464571555303543113 4825285098428666477657335)
      ·
        refine ⟨7237927647642999716486003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4825285098428666477657335 7237927647642999716486003)
        ·
          refine ⟨10856891471464499574729005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7237927647642999716486003 10856891471464499574729005)
          ·
            refine ⟨4071334301799187340523377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10856891471464499574729005 4071334301799187340523377)
            ·
              refine ⟨3053500726349390505392533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4071334301799187340523377 3053500726349390505392533)
              ·
                refine ⟨143132846547627679940275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3053500726349390505392533 143132846547627679940275)
                ·
                  rfl

theorem cell20_940782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 6].length) (baseStart_940782 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_940782 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_940782 prefixEnd_940782 := by exact prefixLift 940782
  have htrace : WordTrace (prefixWord ++ tailWord_940782) baseStart_940782 baseEnd_940782 := by
    simpa [prefixWord, tailWord_940782, baseEnd_940782] using wordTrace_append hprefix tailTrace_940782
  have hstable : (prefixWord ++ tailWord_940782).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940782).length < 2 ^ (prefixWord ++ tailWord_940782).sum := by decide
  have hdescent : baseEnd_940782 < baseStart_940782 := by decide
  rcases family_descends (prefixWord ++ tailWord_940782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940858 : List Nat := [3, 1, 1, 1, 6, 1, 7]
def baseStart_940858 : Nat := 118140960795 + 940858 * 2 ^ 59
def prefixEnd_940858 : Nat := 4983230072969 + 3 ^ 40 * 940858 * 2
def baseEnd_940858 : Nat := 47714803123751617031909

theorem tailTrace_940858 : CollatzResearch.WordTrace tailWord_940858 prefixEnd_940858 47714803123751617031909 := by
  unfold tailWord_940858
  simp only [CollatzResearch.WordTrace]
  refine ⟨8578977606359906649665807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22877273616959751065775485 8578977606359906649665807)
  ·
    refine ⟨12868466409539859974498711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8578977606359906649665807 12868466409539859974498711)
    ·
      refine ⟨19302699614309789961748067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12868466409539859974498711 19302699614309789961748067)
      ·
        refine ⟨28954049421464684942622101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19302699614309789961748067 28954049421464684942622101)
        ·
          refine ⟨1357221066631157106685411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 28954049421464684942622101 1357221066631157106685411)
          ·
            refine ⟨2035831599946735660028117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1357221066631157106685411 2035831599946735660028117)
            ·
              refine ⟨47714803123751617031909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2035831599946735660028117 47714803123751617031909)
              ·
                rfl

theorem cell20_940858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 7].length) (baseStart_940858 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_940858 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_940858 prefixEnd_940858 := by exact prefixLift 940858
  have htrace : WordTrace (prefixWord ++ tailWord_940858) baseStart_940858 baseEnd_940858 := by
    simpa [prefixWord, tailWord_940858, baseEnd_940858] using wordTrace_append hprefix tailTrace_940858
  have hstable : (prefixWord ++ tailWord_940858).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940858).length < 2 ^ (prefixWord ++ tailWord_940858).sum := by decide
  have hdescent : baseEnd_940858 < baseStart_940858 := by decide
  rcases family_descends (prefixWord ++ tailWord_940858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940892 : List Nat := [2, 2, 4, 2, 1, 3, 2, 4]
def baseStart_940892 : Nat := 118140960795 + 940892 * 2 ^ 59
def prefixEnd_940892 : Nat := 4983230072969 + 3 ^ 40 * 940892 * 2
def baseEnd_940892 : Nat := 143149582213403848717903

theorem tailTrace_940892 : CollatzResearch.WordTrace tailWord_940892 prefixEnd_940892 143149582213403848717903 := by
  unfold tailWord_940892
  simp only [CollatzResearch.WordTrace]
  refine ⟨17158575253658225202700465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22878100338210966936933953 17158575253658225202700465)
  ·
    refine ⟨12868931440243668902025349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17158575253658225202700465 12868931440243668902025349)
    ·
      refine ⟨2412924645045687919129753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12868931440243668902025349 2412924645045687919129753)
      ·
        refine ⟨1809693483784265939347315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2412924645045687919129753 1809693483784265939347315)
        ·
          refine ⟨2714540225676398909020973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1809693483784265939347315 2714540225676398909020973)
          ·
            refine ⟨1017952584628649590882865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2714540225676398909020973 1017952584628649590882865)
            ·
              refine ⟨763464438471487193162149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1017952584628649590882865 763464438471487193162149)
              ·
                refine ⟨143149582213403848717903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 763464438471487193162149 143149582213403848717903)
                ·
                  rfl

theorem cell20_940892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 2, 4].length) (baseStart_940892 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_940892 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_940892 prefixEnd_940892 := by exact prefixLift 940892
  have htrace : WordTrace (prefixWord ++ tailWord_940892) baseStart_940892 baseEnd_940892 := by
    simpa [prefixWord, tailWord_940892, baseEnd_940892] using wordTrace_append hprefix tailTrace_940892
  have hstable : (prefixWord ++ tailWord_940892).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940892).length < 2 ^ (prefixWord ++ tailWord_940892).sum := by decide
  have hdescent : baseEnd_940892 < baseStart_940892 := by decide
  rcases family_descends (prefixWord ++ tailWord_940892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940903 : List Nat := [1, 1, 5, 1, 2, 2, 1, 2, 5]
def baseStart_940903 : Nat := 118140960795 + 940903 * 2 ^ 59
def prefixEnd_940903 : Nat := 4983230072969 + 3 ^ 40 * 940903 * 2
def baseEnd_940903 : Nat := 429453767339944396786997

theorem tailTrace_940903 : CollatzResearch.WordTrace tailWord_940903 prefixEnd_940903 429453767339944396786997 := by
  unfold tailWord_940903
  simp only [CollatzResearch.WordTrace]
  refine ⟨34317551710276599284051363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22878367806851066189367575 34317551710276599284051363)
  ·
    refine ⟨51476327565414898926077045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34317551710276599284051363 51476327565414898926077045)
    ·
      refine ⟨4825905709257646774319723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51476327565414898926077045 4825905709257646774319723)
      ·
        refine ⟨7238858563886470161479585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4825905709257646774319723 7238858563886470161479585)
        ·
          refine ⟨5429143922914852621109689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7238858563886470161479585 5429143922914852621109689)
          ·
            refine ⟨4071857942186139465832267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5429143922914852621109689 4071857942186139465832267)
            ·
              refine ⟨6107786913279209198748401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4071857942186139465832267 6107786913279209198748401)
              ·
                refine ⟨4580840184959406899061301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6107786913279209198748401 4580840184959406899061301)
                ·
                  refine ⟨429453767339944396786997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4580840184959406899061301 429453767339944396786997)
                  ·
                    rfl

theorem cell20_940903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 2, 5].length) (baseStart_940903 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_940903 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_940903 prefixEnd_940903 := by exact prefixLift 940903
  have htrace : WordTrace (prefixWord ++ tailWord_940903) baseStart_940903 baseEnd_940903 := by
    simpa [prefixWord, tailWord_940903, baseEnd_940903] using wordTrace_append hprefix tailTrace_940903
  have hstable : (prefixWord ++ tailWord_940903).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940903).length < 2 ^ (prefixWord ++ tailWord_940903).sum := by decide
  have hdescent : baseEnd_940903 < baseStart_940903 := by decide
  rcases family_descends (prefixWord ++ tailWord_940903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940927 : List Nat := [1, 1, 2, 2, 1, 1, 4, 6, 2]
def baseStart_940927 : Nat := 118140960795 + 940927 * 2 ^ 59
def prefixEnd_940927 : Nat := 4983230072969 + 3 ^ 40 * 940927 * 2
def baseEnd_940927 : Nat := 429464721593906979986899

theorem tailTrace_940927 : CollatzResearch.WordTrace tailWord_940927 prefixEnd_940927 429464721593906979986899 := by
  unfold tailWord_940927
  simp only [CollatzResearch.WordTrace]
  refine ⟨34318427062189651382925035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22878951374793100921950023 34318427062189651382925035)
  ·
    refine ⟨51477640593284477074387553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34318427062189651382925035 51477640593284477074387553)
    ·
      refine ⟨38608230444963357805790665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51477640593284477074387553 38608230444963357805790665)
      ·
        refine ⟨28956172833722518354342999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38608230444963357805790665 28956172833722518354342999)
        ·
          refine ⟨43434259250583777531514499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28956172833722518354342999 43434259250583777531514499)
          ·
            refine ⟨65151388875875666297271749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43434259250583777531514499 65151388875875666297271749)
            ·
              refine ⟨12215885414226687430738453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65151388875875666297271749 12215885414226687430738453)
              ·
                refine ⟨572619628791875973315865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12215885414226687430738453 572619628791875973315865)
                ·
                  refine ⟨429464721593906979986899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 572619628791875973315865 429464721593906979986899)
                  ·
                    rfl

theorem cell20_940927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 6, 2].length) (baseStart_940927 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_940927 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_940927 prefixEnd_940927 := by exact prefixLift 940927
  have htrace : WordTrace (prefixWord ++ tailWord_940927) baseStart_940927 baseEnd_940927 := by
    simpa [prefixWord, tailWord_940927, baseEnd_940927] using wordTrace_append hprefix tailTrace_940927
  have hstable : (prefixWord ++ tailWord_940927).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940927).length < 2 ^ (prefixWord ++ tailWord_940927).sum := by decide
  have hdescent : baseEnd_940927 < baseStart_940927 := by decide
  rcases family_descends (prefixWord ++ tailWord_940927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940937 : List Nat := [1, 2, 1, 1, 5, 4, 2, 1, 3]
def baseStart_940937 : Nat := 118140960795 + 940937 * 2 ^ 59
def prefixEnd_940937 : Nat := 4983230072969 + 3 ^ 40 * 940937 * 2
def baseEnd_940937 : Nat := 429469285866391389653525

theorem tailTrace_940937 : CollatzResearch.WordTrace tailWord_940937 prefixEnd_940937 429469285866391389653525 := by
  unfold tailWord_940937
  simp only [CollatzResearch.WordTrace]
  refine ⟨34318791792153423090789065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22879194528102282060526043 34318791792153423090789065)
  ·
    refine ⟨25739093844115067318091799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34318791792153423090789065 25739093844115067318091799)
    ·
      refine ⟨38608640766172600977137699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25739093844115067318091799 38608640766172600977137699)
      ·
        refine ⟨57912961149258901465706549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38608640766172600977137699 57912961149258901465706549)
        ·
          refine ⟨5429340107743022012409989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 57912961149258901465706549 5429340107743022012409989)
          ·
            refine ⟨1018001270201816627326873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5429340107743022012409989 1018001270201816627326873)
            ·
              refine ⟨763500952651362470495155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1018001270201816627326873 763500952651362470495155)
              ·
                refine ⟨1145251428977043705742733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 763500952651362470495155 1145251428977043705742733)
                ·
                  refine ⟨429469285866391389653525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1145251428977043705742733 429469285866391389653525)
                  ·
                    rfl

theorem cell20_940937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 2, 1, 3].length) (baseStart_940937 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_940937 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_940937 prefixEnd_940937 := by exact prefixLift 940937
  have htrace : WordTrace (prefixWord ++ tailWord_940937) baseStart_940937 baseEnd_940937 := by
    simpa [prefixWord, tailWord_940937, baseEnd_940937] using wordTrace_append hprefix tailTrace_940937
  have hstable : (prefixWord ++ tailWord_940937).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940937).length < 2 ^ (prefixWord ++ tailWord_940937).sum := by decide
  have hdescent : baseEnd_940937 < baseStart_940937 := by decide
  rcases family_descends (prefixWord ++ tailWord_940937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940986 : List Nat := [3, 1, 1, 1, 2, 1, 4, 3, 4]
def baseStart_940986 : Nat := 118140960795 + 940986 * 2 ^ 59
def prefixEnd_940986 : Nat := 4983230072969 + 3 ^ 40 * 940986 * 2
def baseEnd_940986 : Nat := 429491650801564997019991

theorem tailTrace_940986 : CollatzResearch.WordTrace tailWord_940986 prefixEnd_940986 429491650801564997019991 := by
  unfold tailWord_940986
  simp only [CollatzResearch.WordTrace]
  refine ⟨8580144742243976114830703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22880385979317269639548541 8580144742243976114830703)
  ·
    refine ⟨12870217113365964172246055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8580144742243976114830703 12870217113365964172246055)
    ·
      refine ⟨19305325670048946258369083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12870217113365964172246055 19305325670048946258369083)
      ·
        refine ⟨28957988505073419387553625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19305325670048946258369083 28957988505073419387553625)
        ·
          refine ⟨21718491378805064540665219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28957988505073419387553625 21718491378805064540665219)
          ·
            refine ⟨32577737068207596810997829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21718491378805064540665219 32577737068207596810997829)
            ·
              refine ⟨6108325700288924402062093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32577737068207596810997829 6108325700288924402062093)
              ·
                refine ⟨2290622137608346650773285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6108325700288924402062093 2290622137608346650773285)
                ·
                  refine ⟨429491650801564997019991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2290622137608346650773285 429491650801564997019991)
                  ·
                    rfl

theorem cell20_940986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 3, 4].length) (baseStart_940986 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_940986 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_940986 prefixEnd_940986 := by exact prefixLift 940986
  have htrace : WordTrace (prefixWord ++ tailWord_940986) baseStart_940986 baseEnd_940986 := by
    simpa [prefixWord, tailWord_940986, baseEnd_940986] using wordTrace_append hprefix tailTrace_940986
  have hstable : (prefixWord ++ tailWord_940986).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940986).length < 2 ^ (prefixWord ++ tailWord_940986).sum := by decide
  have hdescent : baseEnd_940986 < baseStart_940986 := by decide
  rcases family_descends (prefixWord ++ tailWord_940986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_940989 : List Nat := [1, 4, 1, 2, 4, 2, 1, 5]
def baseStart_940989 : Nat := 118140960795 + 940989 * 2 ^ 59
def prefixEnd_940989 : Nat := 4983230072969 + 3 ^ 40 * 940989 * 2
def baseEnd_940989 : Nat := 143164340027770106639993

theorem tailTrace_940989 : CollatzResearch.WordTrace tailWord_940989 prefixEnd_940989 143164340027770106639993 := by
  unfold tailWord_940989
  simp only [CollatzResearch.WordTrace]
  refine ⟨34320688387965035971682021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22880458925310023981121347 34320688387965035971682021)
  ·
    refine ⟨6435129072743444244690379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34320688387965035971682021 6435129072743444244690379)
    ·
      refine ⟨9652693609115166367035569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6435129072743444244690379 9652693609115166367035569)
      ·
        refine ⟨7239520206836374775276677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9652693609115166367035569 7239520206836374775276677)
        ·
          refine ⟨1357410038781820270364377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7239520206836374775276677 1357410038781820270364377)
          ·
            refine ⟨1018057529086365202773283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1357410038781820270364377 1018057529086365202773283)
            ·
              refine ⟨1527086293629547804159925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1018057529086365202773283 1527086293629547804159925)
              ·
                refine ⟨143164340027770106639993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1527086293629547804159925 143164340027770106639993)
                ·
                  rfl

theorem cell20_940989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 1, 5].length) (baseStart_940989 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_940989 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_940989 prefixEnd_940989 := by exact prefixLift 940989
  have htrace : WordTrace (prefixWord ++ tailWord_940989) baseStart_940989 baseEnd_940989 := by
    simpa [prefixWord, tailWord_940989, baseEnd_940989] using wordTrace_append hprefix tailTrace_940989
  have hstable : (prefixWord ++ tailWord_940989).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_940989).length < 2 ^ (prefixWord ++ tailWord_940989).sum := by decide
  have hdescent : baseEnd_940989 < baseStart_940989 := by decide
  rcases family_descends (prefixWord ++ tailWord_940989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941034 : List Nat := [3, 1, 3, 1, 2, 2, 3, 2, 3]
def baseStart_941034 : Nat := 118140960795 + 941034 * 2 ^ 59
def prefixEnd_941034 : Nat := 4983230072969 + 3 ^ 40 * 941034 * 2
def baseEnd_941034 : Nat := 429513559309490163419795

theorem tailTrace_941034 : CollatzResearch.WordTrace tailWord_941034 prefixEnd_941034 429513559309490163419795 := by
  unfold tailWord_941034
  simp only [CollatzResearch.WordTrace]
  refine ⟨8580582418200502164267539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22881553115201339104713437 8580582418200502164267539)
  ·
    refine ⟨12870873627300753246401309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8580582418200502164267539 12870873627300753246401309)
    ·
      refine ⟨4826577610237782467400491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12870873627300753246401309 4826577610237782467400491)
      ·
        refine ⟨7239866415356673701100737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4826577610237782467400491 7239866415356673701100737)
        ·
          refine ⟨5429899811517505275825553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7239866415356673701100737 5429899811517505275825553)
          ·
            refine ⟨4072424858638128956869165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5429899811517505275825553 4072424858638128956869165)
            ·
              refine ⟨1527159321989298358825937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4072424858638128956869165 1527159321989298358825937)
              ·
                refine ⟨1145369491491973769119453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1527159321989298358825937 1145369491491973769119453)
                ·
                  refine ⟨429513559309490163419795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1145369491491973769119453 429513559309490163419795)
                  ·
                    rfl

theorem cell20_941034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 3, 2, 3].length) (baseStart_941034 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_941034 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_941034 prefixEnd_941034 := by exact prefixLift 941034
  have htrace : WordTrace (prefixWord ++ tailWord_941034) baseStart_941034 baseEnd_941034 := by
    simpa [prefixWord, tailWord_941034, baseEnd_941034] using wordTrace_append hprefix tailTrace_941034
  have hstable : (prefixWord ++ tailWord_941034).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941034).length < 2 ^ (prefixWord ++ tailWord_941034).sum := by decide
  have hdescent : baseEnd_941034 < baseStart_941034 := by decide
  rcases family_descends (prefixWord ++ tailWord_941034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941041 : List Nat := [1, 2, 2, 2, 4, 2, 2, 1, 4]
def baseStart_941041 : Nat := 118140960795 + 941041 * 2 ^ 59
def prefixEnd_941041 : Nat := 4983230072969 + 3 ^ 40 * 941041 * 2
def baseEnd_941041 : Nat := 429516754300229250186433

theorem tailTrace_941041 : CollatzResearch.WordTrace tailWord_941041 prefixEnd_941041 429516754300229250186433 := by
  unfold tailWord_941041
  simp only [CollatzResearch.WordTrace]
  refine ⟨34322584983776648852574977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22881723322517765901716651 34322584983776648852574977)
  ·
    refine ⟨25741938737832486639431233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34322584983776648852574977 25741938737832486639431233)
    ·
      refine ⟨19306454053374364979573425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25741938737832486639431233 19306454053374364979573425)
      ·
        refine ⟨14479840540030773734680069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19306454053374364979573425 14479840540030773734680069)
        ·
          refine ⟨2714970101255770075252513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14479840540030773734680069 2714970101255770075252513)
          ·
            refine ⟨2036227575941827556439385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2714970101255770075252513 2036227575941827556439385)
            ·
              refine ⟨1527170681956370667329539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2036227575941827556439385 1527170681956370667329539)
              ·
                refine ⟨2290756022934556000994309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1527170681956370667329539 2290756022934556000994309)
                ·
                  refine ⟨429516754300229250186433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2290756022934556000994309 429516754300229250186433)
                  ·
                    rfl

theorem cell20_941041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 2, 1, 4].length) (baseStart_941041 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_941041 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_941041 prefixEnd_941041 := by exact prefixLift 941041
  have htrace : WordTrace (prefixWord ++ tailWord_941041) baseStart_941041 baseEnd_941041 := by
    simpa [prefixWord, tailWord_941041, baseEnd_941041] using wordTrace_append hprefix tailTrace_941041
  have hstable : (prefixWord ++ tailWord_941041).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941041).length < 2 ^ (prefixWord ++ tailWord_941041).sum := by decide
  have hdescent : baseEnd_941041 < baseStart_941041 := by decide
  rcases family_descends (prefixWord ++ tailWord_941041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941093 : List Nat := [1, 3, 1, 2, 2, 2, 2, 4, 3]
def baseStart_941093 : Nat := 118140960795 + 941093 * 2 ^ 59
def prefixEnd_941093 : Nat := 4983230072969 + 3 ^ 40 * 941093 * 2
def baseEnd_941093 : Nat := 429540488517148180452887

theorem tailTrace_941093 : CollatzResearch.WordTrace tailWord_941093 prefixEnd_941093 429540488517148180452887 := by
  unfold tailWord_941093
  simp only [CollatzResearch.WordTrace]
  refine ⟨34324481579588261733467933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22882987719725507822311955 34324481579588261733467933)
  ·
    refine ⟨12871680592345598150050475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34324481579588261733467933 12871680592345598150050475)
    ·
      refine ⟨19307520888518397225075713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12871680592345598150050475 19307520888518397225075713)
      ·
        refine ⟨14480640666388797918806785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19307520888518397225075713 14480640666388797918806785)
        ·
          refine ⟨10860480499791598439105089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14480640666388797918806785 10860480499791598439105089)
          ·
            refine ⟨8145360374843698829328817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10860480499791598439105089 8145360374843698829328817)
            ·
              refine ⟨6109020281132774121996613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8145360374843698829328817 6109020281132774121996613)
              ·
                refine ⟨1145441302712395147874365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6109020281132774121996613 1145441302712395147874365)
                ·
                  refine ⟨429540488517148180452887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1145441302712395147874365 429540488517148180452887)
                  ·
                    rfl

theorem cell20_941093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 4, 3].length) (baseStart_941093 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_941093 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_941093 prefixEnd_941093 := by exact prefixLift 941093
  have htrace : WordTrace (prefixWord ++ tailWord_941093) baseStart_941093 baseEnd_941093 := by
    simpa [prefixWord, tailWord_941093, baseEnd_941093] using wordTrace_append hprefix tailTrace_941093
  have hstable : (prefixWord ++ tailWord_941093).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941093).length < 2 ^ (prefixWord ++ tailWord_941093).sum := by decide
  have hdescent : baseEnd_941093 < baseStart_941093 := by decide
  rcases family_descends (prefixWord ++ tailWord_941093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941148 : List Nat := [2, 2, 4, 1, 1, 1, 4, 2, 3]
def baseStart_941148 : Nat := 118140960795 + 941148 * 2 ^ 59
def prefixEnd_941148 : Nat := 4983230072969 + 3 ^ 40 * 941148 * 2
def baseEnd_941148 : Nat := 429565592015812433619329

theorem tailTrace_941148 : CollatzResearch.WordTrace tailWord_941148 prefixEnd_941148 429565592015812433619329 := by
  unfold tailWord_941148
  simp only [CollatzResearch.WordTrace]
  refine ⟨17163243797194503063360049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22884325062926004084480065 17163243797194503063360049)
  ·
    refine ⟨12872432847895877297520037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17163243797194503063360049 12872432847895877297520037)
    ·
      refine ⟨2413581158980476993285007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12872432847895877297520037 2413581158980476993285007)
      ·
        refine ⟨3620371738470715489927511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2413581158980476993285007 3620371738470715489927511)
        ·
          refine ⟨5430557607706073234891267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3620371738470715489927511 5430557607706073234891267)
          ·
            refine ⟨8145836411559109852336901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5430557607706073234891267 8145836411559109852336901)
            ·
              refine ⟨1527344327167333097313169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8145836411559109852336901 1527344327167333097313169)
              ·
                refine ⟨1145508245375499822984877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1527344327167333097313169 1145508245375499822984877)
                ·
                  refine ⟨429565592015812433619329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1145508245375499822984877 429565592015812433619329)
                  ·
                    rfl

theorem cell20_941148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 4, 2, 3].length) (baseStart_941148 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_941148 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_941148 prefixEnd_941148 := by exact prefixLift 941148
  have htrace : WordTrace (prefixWord ++ tailWord_941148) baseStart_941148 baseEnd_941148 := by
    simpa [prefixWord, tailWord_941148, baseEnd_941148] using wordTrace_append hprefix tailTrace_941148
  have hstable : (prefixWord ++ tailWord_941148).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941148).length < 2 ^ (prefixWord ++ tailWord_941148).sum := by decide
  have hdescent : baseEnd_941148 < baseStart_941148 := by decide
  rcases family_descends (prefixWord ++ tailWord_941148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941162 : List Nat := [3, 1, 3, 2, 2, 1, 3, 5]
def baseStart_941162 : Nat := 118140960795 + 941162 * 2 ^ 59
def prefixEnd_941162 : Nat := 4983230072969 + 3 ^ 40 * 941162 * 2
def baseEnd_941162 : Nat := 143190660665763535717535

theorem tailTrace_941162 : CollatzResearch.WordTrace tailWord_941162 prefixEnd_941162 143190660665763535717535 := by
  unfold tailWord_941162
  simp only [CollatzResearch.WordTrace]
  refine ⟨8581749554084571629432435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22884665477558857678486493 8581749554084571629432435)
  ·
    refine ⟨12872624331126857444148653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8581749554084571629432435 12872624331126857444148653)
    ·
      refine ⟨4827234124172571541555745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12872624331126857444148653 4827234124172571541555745)
      ·
        refine ⟨3620425593129428656166809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4827234124172571541555745 3620425593129428656166809)
        ·
          refine ⟨2715319194847071492125107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3620425593129428656166809 2715319194847071492125107)
          ·
            refine ⟨4072978792270607238187661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2715319194847071492125107 4072978792270607238187661)
            ·
              refine ⟨1527367047101477714320373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4072978792270607238187661 1527367047101477714320373)
              ·
                refine ⟨143190660665763535717535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1527367047101477714320373 143190660665763535717535)
                ·
                  rfl

theorem cell20_941162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 3, 5].length) (baseStart_941162 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_941162 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_941162 prefixEnd_941162 := by exact prefixLift 941162
  have htrace : WordTrace (prefixWord ++ tailWord_941162) baseStart_941162 baseEnd_941162 := by
    simpa [prefixWord, tailWord_941162, baseEnd_941162] using wordTrace_append hprefix tailTrace_941162
  have hstable : (prefixWord ++ tailWord_941162).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941162).length < 2 ^ (prefixWord ++ tailWord_941162).sum := by decide
  have hdescent : baseEnd_941162 < baseStart_941162 := by decide
  rcases family_descends (prefixWord ++ tailWord_941162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941193 : List Nat := [1, 2, 1, 1, 4, 3, 1, 5, 2]
def baseStart_941193 : Nat := 118140960795 + 941193 * 2 ^ 59
def prefixEnd_941193 : Nat := 4983230072969 + 3 ^ 40 * 941193 * 2
def baseEnd_941193 : Nat := 429586131241992277119145

theorem tailTrace_941193 : CollatzResearch.WordTrace tailWord_941193 prefixEnd_941193 429586131241992277119145 := by
  unfold tailWord_941193
  simp only [CollatzResearch.WordTrace]
  refine ⟨34328128879225978812108233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22885419252817319208072155 34328128879225978812108233)
  ·
    refine ⟨25746096659419484109081175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34328128879225978812108233 25746096659419484109081175)
    ·
      refine ⟨38619144989129226163621763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25746096659419484109081175 38619144989129226163621763)
      ·
        refine ⟨57928717483693839245432645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38619144989129226163621763 57928717483693839245432645)
        ·
          refine ⟨10861634528192594858518621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57928717483693839245432645 10861634528192594858518621)
          ·
            refine ⟨4073112948072223071944483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10861634528192594858518621 4073112948072223071944483)
            ·
              refine ⟨6109669422108334607916725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4073112948072223071944483 6109669422108334607916725)
              ·
                refine ⟨572781508322656369492193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6109669422108334607916725 572781508322656369492193)
                ·
                  refine ⟨429586131241992277119145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 572781508322656369492193 429586131241992277119145)
                  ·
                    rfl

theorem cell20_941193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 5, 2].length) (baseStart_941193 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_941193 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_941193 prefixEnd_941193 := by exact prefixLift 941193
  have htrace : WordTrace (prefixWord ++ tailWord_941193) baseStart_941193 baseEnd_941193 := by
    simpa [prefixWord, tailWord_941193, baseEnd_941193] using wordTrace_append hprefix tailTrace_941193
  have hstable : (prefixWord ++ tailWord_941193).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941193).length < 2 ^ (prefixWord ++ tailWord_941193).sum := by decide
  have hdescent : baseEnd_941193 < baseStart_941193 := by decide
  rcases family_descends (prefixWord ++ tailWord_941193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941207 : List Nat := [1, 1, 3, 3, 3, 2, 1, 1, 5]
def baseStart_941207 : Nat := 118140960795 + 941207 * 2 ^ 59
def prefixEnd_941207 : Nat := 4983230072969 + 3 ^ 40 * 941207 * 2
def baseEnd_941207 : Nat := 429592521223470450652421

theorem tailTrace_941207 : CollatzResearch.WordTrace tailWord_941207 prefixEnd_941207 429592521223470450652421 := by
  unfold tailWord_941207
  simp only [CollatzResearch.WordTrace]
  refine ⟨34328639501175259203117875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22885759667450172802078583 34328639501175259203117875)
  ·
    refine ⟨51492959251762888804676813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34328639501175259203117875 51492959251762888804676813)
    ·
      refine ⟨19309859719411083301753805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51492959251762888804676813 19309859719411083301753805)
      ·
        refine ⟨7241197394779156238157677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19309859719411083301753805 7241197394779156238157677)
        ·
          refine ⟨2715449023042183589309129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7241197394779156238157677 2715449023042183589309129)
          ·
            refine ⟨2036586767281637691981847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2715449023042183589309129 2036586767281637691981847)
            ·
              refine ⟨3054880150922456537972771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2036586767281637691981847 3054880150922456537972771)
              ·
                refine ⟨4582320226383684806959157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3054880150922456537972771 4582320226383684806959157)
                ·
                  refine ⟨429592521223470450652421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4582320226383684806959157 429592521223470450652421)
                  ·
                    rfl

theorem cell20_941207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 1, 5].length) (baseStart_941207 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_941207 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_941207 prefixEnd_941207 := by exact prefixLift 941207
  have htrace : WordTrace (prefixWord ++ tailWord_941207) baseStart_941207 baseEnd_941207 := by
    simpa [prefixWord, tailWord_941207, baseEnd_941207] using wordTrace_append hprefix tailTrace_941207
  have hstable : (prefixWord ++ tailWord_941207).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941207).length < 2 ^ (prefixWord ++ tailWord_941207).sum := by decide
  have hdescent : baseEnd_941207 < baseStart_941207 := by decide
  rcases family_descends (prefixWord ++ tailWord_941207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941210 : List Nat := [3, 1, 1, 5, 1, 1, 2, 4, 2]
def baseStart_941210 : Nat := 118140960795 + 941210 * 2 ^ 59
def prefixEnd_941210 : Nat := 4983230072969 + 3 ^ 40 * 941210 * 2
def baseEnd_941210 : Nat := 429593890505215773552409

theorem tailTrace_941210 : CollatzResearch.WordTrace tailWord_941210 prefixEnd_941210 429593890505215773552409 := by
  unfold tailWord_941210
  simp only [CollatzResearch.WordTrace]
  refine ⟨8582187230041097678869271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22885832613442927143651389 8582187230041097678869271)
  ·
    refine ⟨12873280845061646518303907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8582187230041097678869271 12873280845061646518303907)
    ·
      refine ⟨19309921267592469777455861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12873280845061646518303907 19309921267592469777455861)
      ·
        refine ⟨1810305118836794041636487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19309921267592469777455861 1810305118836794041636487)
        ·
          refine ⟨2715457678255191062454731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1810305118836794041636487 2715457678255191062454731)
          ·
            refine ⟨4073186517382786593682097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2715457678255191062454731 4073186517382786593682097)
            ·
              refine ⟨3054889888037089945261573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4073186517382786593682097 3054889888037089945261573)
              ·
                refine ⟨572791854006954364736545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3054889888037089945261573 572791854006954364736545)
                ·
                  refine ⟨429593890505215773552409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 572791854006954364736545 429593890505215773552409)
                  ·
                    rfl

theorem cell20_941210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 4, 2].length) (baseStart_941210 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_941210 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_941210 prefixEnd_941210 := by exact prefixLift 941210
  have htrace : WordTrace (prefixWord ++ tailWord_941210) baseStart_941210 baseEnd_941210 := by
    simpa [prefixWord, tailWord_941210, baseEnd_941210] using wordTrace_append hprefix tailTrace_941210
  have hstable : (prefixWord ++ tailWord_941210).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941210).length < 2 ^ (prefixWord ++ tailWord_941210).sum := by decide
  have hdescent : baseEnd_941210 < baseStart_941210 := by decide
  rcases family_descends (prefixWord ++ tailWord_941210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941261 : List Nat := [1, 6, 2, 2, 1, 1, 3, 2, 2]
def baseStart_941261 : Nat := 118140960795 + 941261 * 2 ^ 59
def prefixEnd_941261 : Nat := 4983230072969 + 3 ^ 40 * 941261 * 2
def baseEnd_941261 : Nat := 429617168294886262852201

theorem tailTrace_941261 : CollatzResearch.WordTrace tailWord_941261 prefixEnd_941261 429617168294886262852201 := by
  unfold tailWord_941261
  simp only [CollatzResearch.WordTrace]
  refine ⟨34330609042979626425583637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22887072695319750950389091 34330609042979626425583637)
  ·
    refine ⟨1609247298889669988699233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 34330609042979626425583637 1609247298889669988699233)
    ·
      refine ⟨1206935474167252491524425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1609247298889669988699233 1206935474167252491524425)
      ·
        refine ⟨905201605625439368643319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1206935474167252491524425 905201605625439368643319)
        ·
          refine ⟨1357802408438159052964979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 905201605625439368643319 1357802408438159052964979)
          ·
            refine ⟨2036703612657238579447469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1357802408438159052964979 2036703612657238579447469)
            ·
              refine ⟨763763854746464467292801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2036703612657238579447469 763763854746464467292801)
              ·
                refine ⟨572822891059848350469601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 763763854746464467292801 572822891059848350469601)
                ·
                  refine ⟨429617168294886262852201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 572822891059848350469601 429617168294886262852201)
                  ·
                    rfl

theorem cell20_941261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 3, 2, 2].length) (baseStart_941261 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_941261 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_941261 prefixEnd_941261 := by exact prefixLift 941261
  have htrace : WordTrace (prefixWord ++ tailWord_941261) baseStart_941261 baseEnd_941261 := by
    simpa [prefixWord, tailWord_941261, baseEnd_941261] using wordTrace_append hprefix tailTrace_941261
  have hstable : (prefixWord ++ tailWord_941261).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941261).length < 2 ^ (prefixWord ++ tailWord_941261).sum := by decide
  have hdescent : baseEnd_941261 < baseStart_941261 := by decide
  rcases family_descends (prefixWord ++ tailWord_941261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941269 : List Nat := [1, 3, 2, 4, 1, 1, 3, 1, 4]
def baseStart_941269 : Nat := 118140960795 + 941269 * 2 ^ 59
def prefixEnd_941269 : Nat := 4983230072969 + 3 ^ 40 * 941269 * 2
def baseEnd_941269 : Nat := 429620819712873790585501

theorem tailTrace_941269 : CollatzResearch.WordTrace tailWord_941269 prefixEnd_941269 429620819712873790585501 := by
  unfold tailWord_941269
  simp only [CollatzResearch.WordTrace]
  refine ⟨34330900826950643791874861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22887267217967095861249907 34330900826950643791874861)
  ·
    refine ⟨12874087810106491421953073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34330900826950643791874861 12874087810106491421953073)
    ·
      refine ⟨9655565857579868566464805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12874087810106491421953073 9655565857579868566464805)
      ·
        refine ⟨1810418598296225356212151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9655565857579868566464805 1810418598296225356212151)
        ·
          refine ⟨2715627897444338034318227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1810418598296225356212151 2715627897444338034318227)
          ·
            refine ⟨4073441846166507051477341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2715627897444338034318227 4073441846166507051477341)
            ·
              refine ⟨1527540692312440144304003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4073441846166507051477341 1527540692312440144304003)
              ·
                refine ⟨2291311038468660216456005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1527540692312440144304003 2291311038468660216456005)
                ·
                  refine ⟨429620819712873790585501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2291311038468660216456005 429620819712873790585501)
                  ·
                    rfl

theorem cell20_941269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 3, 1, 4].length) (baseStart_941269 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_941269 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_941269 prefixEnd_941269 := by exact prefixLift 941269
  have htrace : WordTrace (prefixWord ++ tailWord_941269) baseStart_941269 baseEnd_941269 := by
    simpa [prefixWord, tailWord_941269, baseEnd_941269] using wordTrace_append hprefix tailTrace_941269
  have hstable : (prefixWord ++ tailWord_941269).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941269).length < 2 ^ (prefixWord ++ tailWord_941269).sum := by decide
  have hdescent : baseEnd_941269 < baseStart_941269 := by decide
  rcases family_descends (prefixWord ++ tailWord_941269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941314 : List Nat := [3, 4, 1, 1, 3, 8]
def baseStart_941314 : Nat := 118140960795 + 941314 * 2 ^ 59
def prefixEnd_941314 : Nat := 4983230072969 + 3 ^ 40 * 941314 * 2
def baseEnd_941314 : Nat := 15912642923668653114271

theorem tailTrace_941314 : CollatzResearch.WordTrace tailWord_941314 prefixEnd_941314 15912642923668653114271 := by
  unfold tailWord_941314
  simp only [CollatzResearch.WordTrace]
  refine ⟨8583135527946904119315749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22888361407858410984841997 8583135527946904119315749)
  ·
    refine ⟨1609337911490044522371703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8583135527946904119315749 1609337911490044522371703)
    ·
      refine ⟨2414006867235066783557555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1609337911490044522371703 2414006867235066783557555)
      ·
        refine ⟨3621010300852600175336333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2414006867235066783557555 3621010300852600175336333)
        ·
          refine ⟨1357878862819725065751125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3621010300852600175336333 1357878862819725065751125)
          ·
            refine ⟨15912642923668653114271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1357878862819725065751125 15912642923668653114271)
            ·
              rfl

theorem cell20_941314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 8].length) (baseStart_941314 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_941314 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_941314 prefixEnd_941314 := by exact prefixLift 941314
  have htrace : WordTrace (prefixWord ++ tailWord_941314) baseStart_941314 baseEnd_941314 := by
    simpa [prefixWord, tailWord_941314, baseEnd_941314] using wordTrace_append hprefix tailTrace_941314
  have hstable : (prefixWord ++ tailWord_941314).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941314).length < 2 ^ (prefixWord ++ tailWord_941314).sum := by decide
  have hdescent : baseEnd_941314 < baseStart_941314 := by decide
  rcases family_descends (prefixWord ++ tailWord_941314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941320 : List Nat := [2, 1, 3, 2, 5, 1, 2, 2, 2]
def baseStart_941320 : Nat := 118140960795 + 941320 * 2 ^ 59
def prefixEnd_941320 : Nat := 4983230072969 + 3 ^ 40 * 941320 * 2
def baseEnd_941320 : Nat := 429644097502544279885293

theorem tailTrace_941320 : CollatzResearch.WordTrace tailWord_941320 prefixEnd_941320 429644097502544279885293 := by
  unfold tailWord_941320
  simp only [CollatzResearch.WordTrace]
  refine ⟨17166380474882939750990707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22888507299843919667987609 17166380474882939750990707)
  ·
    refine ⟨25749570712324409626486061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17166380474882939750990707 25749570712324409626486061)
    ·
      refine ⟨9656089017121653609932273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25749570712324409626486061 9656089017121653609932273)
      ·
        refine ⟨7242066762841240207449205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9656089017121653609932273 7242066762841240207449205)
        ·
          refine ⟨678943759016366269448363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7242066762841240207449205 678943759016366269448363)
          ·
            refine ⟨1018415638524549404172545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 678943759016366269448363 1018415638524549404172545)
            ·
              refine ⟨763811728893412053129409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1018415638524549404172545 763811728893412053129409)
              ·
                refine ⟨572858796670059039847057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 763811728893412053129409 572858796670059039847057)
                ·
                  refine ⟨429644097502544279885293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 572858796670059039847057 429644097502544279885293)
                  ·
                    rfl

theorem cell20_941320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 2, 2, 2].length) (baseStart_941320 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_941320 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_941320 prefixEnd_941320 := by exact prefixLift 941320
  have htrace : WordTrace (prefixWord ++ tailWord_941320) baseStart_941320 baseEnd_941320 := by
    simpa [prefixWord, tailWord_941320, baseEnd_941320] using wordTrace_append hprefix tailTrace_941320
  have hstable : (prefixWord ++ tailWord_941320).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941320).length < 2 ^ (prefixWord ++ tailWord_941320).sum := by decide
  have hdescent : baseEnd_941320 < baseStart_941320 := by decide
  rcases family_descends (prefixWord ++ tailWord_941320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941321 : List Nat := [1, 2, 1, 1, 3, 3, 4, 2, 3]
def baseStart_941321 : Nat := 118140960795 + 941321 * 2 ^ 59
def prefixEnd_941321 : Nat := 4983230072969 + 3 ^ 40 * 941321 * 2
def baseEnd_941321 : Nat := 429644553929792720851955

theorem tailTrace_941321 : CollatzResearch.WordTrace tailWord_941321 prefixEnd_941321 429644553929792720851955 := by
  unfold tailWord_941321
  simp only [CollatzResearch.WordTrace]
  refine ⟨34332797422762256672767817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22888531615174837781845211 34332797422762256672767817)
  ·
    refine ⟨25749598067071692504575863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34332797422762256672767817 25749598067071692504575863)
    ·
      refine ⟨38624397100607538756863795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25749598067071692504575863 38624397100607538756863795)
      ·
        refine ⟨57936595650911308135295693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38624397100607538756863795 57936595650911308135295693)
        ·
          refine ⟨21726223369091740550735885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57936595650911308135295693 21726223369091740550735885)
          ·
            refine ⟨8147333763409402706525957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21726223369091740550735885 8147333763409402706525957)
            ·
              refine ⟨1527625080639263007473617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8147333763409402706525957 1527625080639263007473617)
              ·
                refine ⟨1145718810479447255605213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1527625080639263007473617 1145718810479447255605213)
                ·
                  refine ⟨429644553929792720851955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1145718810479447255605213 429644553929792720851955)
                  ·
                    rfl

theorem cell20_941321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 4, 2, 3].length) (baseStart_941321 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_941321 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_941321 prefixEnd_941321 := by exact prefixLift 941321
  have htrace : WordTrace (prefixWord ++ tailWord_941321) baseStart_941321 baseEnd_941321 := by
    simpa [prefixWord, tailWord_941321, baseEnd_941321] using wordTrace_append hprefix tailTrace_941321
  have hstable : (prefixWord ++ tailWord_941321).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941321).length < 2 ^ (prefixWord ++ tailWord_941321).sum := by decide
  have hdescent : baseEnd_941321 < baseStart_941321 := by decide
  rcases family_descends (prefixWord ++ tailWord_941321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941324 : List Nat := [2, 2, 1, 2, 2, 3, 4, 2, 2]
def baseStart_941324 : Nat := 118140960795 + 941324 * 2 ^ 59
def prefixEnd_941324 : Nat := 4983230072969 + 3 ^ 40 * 941324 * 2
def baseEnd_941324 : Nat := 429645923211538043751943

theorem tailTrace_941324 : CollatzResearch.WordTrace tailWord_941324 prefixEnd_941324 429645923211538043751943 := by
  unfold tailWord_941324
  simp only [CollatzResearch.WordTrace]
  refine ⟨17166453420875694092563513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22888604561167592123418017 17166453420875694092563513)
  ·
    refine ⟨12874840065656770569422635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17166453420875694092563513 12874840065656770569422635)
    ·
      refine ⟨19312260098485155854133953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12874840065656770569422635 19312260098485155854133953)
      ·
        refine ⟨14484195073863866890600465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19312260098485155854133953 14484195073863866890600465)
        ·
          refine ⟨10863146305397900167950349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14484195073863866890600465 10863146305397900167950349)
          ·
            refine ⟨4073679864524212562981381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10863146305397900167950349 4073679864524212562981381)
            ·
              refine ⟨763814974598289855559009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4073679864524212562981381 763814974598289855559009)
              ·
                refine ⟨572861230948717391669257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 763814974598289855559009 572861230948717391669257)
                ·
                  refine ⟨429645923211538043751943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 572861230948717391669257 429645923211538043751943)
                  ·
                    rfl

theorem cell20_941324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 4, 2, 2].length) (baseStart_941324 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_941324 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_941324 prefixEnd_941324 := by exact prefixLift 941324
  have htrace : WordTrace (prefixWord ++ tailWord_941324) baseStart_941324 baseEnd_941324 := by
    simpa [prefixWord, tailWord_941324, baseEnd_941324] using wordTrace_append hprefix tailTrace_941324
  have hstable : (prefixWord ++ tailWord_941324).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941324).length < 2 ^ (prefixWord ++ tailWord_941324).sum := by decide
  have hdescent : baseEnd_941324 < baseStart_941324 := by decide
  rcases family_descends (prefixWord ++ tailWord_941324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941362 : List Nat := [3, 2, 1, 1, 4, 2, 2, 3, 2]
def baseStart_941362 : Nat := 118140960795 + 941362 * 2 ^ 59
def prefixEnd_941362 : Nat := 4983230072969 + 3 ^ 40 * 941362 * 2
def baseEnd_941362 : Nat := 429663267446978800485121

theorem tailTrace_941362 : CollatzResearch.WordTrace tailWord_941362 prefixEnd_941362 429663267446978800485121 := by
  unfold tailWord_941362
  simp only [CollatzResearch.WordTrace]
  refine ⟨8583573203903430168752585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22889528543742480450006893 8583573203903430168752585)
  ·
    refine ⟨6437679902927572626564439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8583573203903430168752585 6437679902927572626564439)
    ·
      refine ⟨9656519854391358939846659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6437679902927572626564439 9656519854391358939846659)
      ·
        refine ⟨14484779781587038409769989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9656519854391358939846659 14484779781587038409769989)
        ·
          refine ⟨2715896209047569701831873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14484779781587038409769989 2715896209047569701831873)
          ·
            refine ⟨2036922156785677276373905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2715896209047569701831873 2036922156785677276373905)
            ·
              refine ⟨1527691617589257957280429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2036922156785677276373905 1527691617589257957280429)
              ·
                refine ⟨572884356595971733980161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1527691617589257957280429 572884356595971733980161)
                ·
                  refine ⟨429663267446978800485121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 572884356595971733980161 429663267446978800485121)
                  ·
                    rfl

theorem cell20_941362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 2, 3, 2].length) (baseStart_941362 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_941362 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_941362 prefixEnd_941362 := by exact prefixLift 941362
  have htrace : WordTrace (prefixWord ++ tailWord_941362) baseStart_941362 baseEnd_941362 := by
    simpa [prefixWord, tailWord_941362, baseEnd_941362] using wordTrace_append hprefix tailTrace_941362
  have hstable : (prefixWord ++ tailWord_941362).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941362).length < 2 ^ (prefixWord ++ tailWord_941362).sum := by decide
  have hdescent : baseEnd_941362 < baseStart_941362 := by decide
  rcases family_descends (prefixWord ++ tailWord_941362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941383 : List Nat := [1, 1, 4, 1, 2, 3, 2, 4, 2]
def baseStart_941383 : Nat := 118140960795 + 941383 * 2 ^ 59
def prefixEnd_941383 : Nat := 4983230072969 + 3 ^ 40 * 941383 * 2
def baseEnd_941383 : Nat := 429672852419196060785035

theorem tailTrace_941383 : CollatzResearch.WordTrace tailWord_941383 prefixEnd_941383 429672852419196060785035 := by
  unfold tailWord_941383
  simp only [CollatzResearch.WordTrace]
  refine ⟨34335058748537641261524803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22890039165691760841016535 34335058748537641261524803)
  ·
    refine ⟨51502588122806461892287205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34335058748537641261524803 51502588122806461892287205)
    ·
      refine ⟨9656735273026211604803851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51502588122806461892287205 9656735273026211604803851)
      ·
        refine ⟨14485102909539317407205777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9656735273026211604803851 14485102909539317407205777)
        ·
          refine ⟨10863827182154488055404333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14485102909539317407205777 10863827182154488055404333)
          ·
            refine ⟨4073935193307933020776625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10863827182154488055404333 4073935193307933020776625)
            ·
              refine ⟨3055451394980949765582469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4073935193307933020776625 3055451394980949765582469)
              ·
                refine ⟨572897136558928081046713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3055451394980949765582469 572897136558928081046713)
                ·
                  refine ⟨429672852419196060785035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 572897136558928081046713 429672852419196060785035)
                  ·
                    rfl

theorem cell20_941383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 4, 2].length) (baseStart_941383 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_941383 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_941383 prefixEnd_941383 := by exact prefixLift 941383
  have htrace : WordTrace (prefixWord ++ tailWord_941383) baseStart_941383 baseEnd_941383 := by
    simpa [prefixWord, tailWord_941383, baseEnd_941383] using wordTrace_append hprefix tailTrace_941383
  have hstable : (prefixWord ++ tailWord_941383).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941383).length < 2 ^ (prefixWord ++ tailWord_941383).sum := by decide
  have hdescent : baseEnd_941383 < baseStart_941383 := by decide
  rcases family_descends (prefixWord ++ tailWord_941383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941411 : List Nat := [1, 1, 1, 5, 2, 3, 1, 6]
def baseStart_941411 : Nat := 118140960795 + 941411 * 2 ^ 59
def prefixEnd_941411 : Nat := 4983230072969 + 3 ^ 40 * 941411 * 2
def baseEnd_941411 : Nat := 143228544127384135950529

theorem tailTrace_941411 : CollatzResearch.WordTrace tailWord_941411 prefixEnd_941411 143228544127384135950529 := by
  unfold tailWord_941411
  simp only [CollatzResearch.WordTrace]
  refine ⟨34336079992436202043544087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22890719994957468029029391 34336079992436202043544087)
  ·
    refine ⟨51504119988654303065316131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34336079992436202043544087 51504119988654303065316131)
    ·
      refine ⟨77256179982981454597974197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51504119988654303065316131 77256179982981454597974197)
      ·
        refine ⟨7242766873404511368560081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 77256179982981454597974197 7242766873404511368560081)
        ·
          refine ⟨5432075155053383526420061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7242766873404511368560081 5432075155053383526420061)
          ·
            refine ⟨2037028183145018822407523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5432075155053383526420061 2037028183145018822407523)
            ·
              refine ⟨3055542274717528233611285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2037028183145018822407523 3055542274717528233611285)
              ·
                refine ⟨143228544127384135950529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3055542274717528233611285 143228544127384135950529)
                ·
                  rfl

theorem cell20_941411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 6].length) (baseStart_941411 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_941411 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_941411 prefixEnd_941411 := by exact prefixLift 941411
  have htrace : WordTrace (prefixWord ++ tailWord_941411) baseStart_941411 baseEnd_941411 := by
    simpa [prefixWord, tailWord_941411, baseEnd_941411] using wordTrace_append hprefix tailTrace_941411
  have hstable : (prefixWord ++ tailWord_941411).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941411).length < 2 ^ (prefixWord ++ tailWord_941411).sum := by decide
  have hdescent : baseEnd_941411 < baseStart_941411 := by decide
  rcases family_descends (prefixWord ++ tailWord_941411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941425 : List Nat := [1, 2, 2, 2, 1, 2, 2, 2, 6]
def baseStart_941425 : Nat := 118140960795 + 941425 * 2 ^ 59
def prefixEnd_941425 : Nat := 4983230072969 + 3 ^ 40 * 941425 * 2
def baseEnd_941425 : Nat := 429692022363630581384863

theorem tailTrace_941425 : CollatzResearch.WordTrace tailWord_941425 prefixEnd_941425 429692022363630581384863 := by
  unfold tailWord_941425
  simp only [CollatzResearch.WordTrace]
  refine ⟨34336590614385482434553729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22891060409590321623035819 34336590614385482434553729)
  ·
    refine ⟨25752442960789111825915297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34336590614385482434553729 25752442960789111825915297)
    ·
      refine ⟨19314332220591833869436473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25752442960789111825915297 19314332220591833869436473)
      ·
        refine ⟨14485749165443875402077355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19314332220591833869436473 14485749165443875402077355)
        ·
          refine ⟨21728623748165813103116033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14485749165443875402077355 21728623748165813103116033)
          ·
            refine ⟨16296467811124359827337025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21728623748165813103116033 16296467811124359827337025)
            ·
              refine ⟨12222350858343269870502769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16296467811124359827337025 12222350858343269870502769)
              ·
                refine ⟨9166763143757452402877077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12222350858343269870502769 9166763143757452402877077)
                ·
                  refine ⟨429692022363630581384863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9166763143757452402877077 429692022363630581384863)
                  ·
                    rfl

theorem cell20_941425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 6].length) (baseStart_941425 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_941425 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_941425 prefixEnd_941425 := by exact prefixLift 941425
  have htrace : WordTrace (prefixWord ++ tailWord_941425) baseStart_941425 baseEnd_941425 := by
    simpa [prefixWord, tailWord_941425, baseEnd_941425] using wordTrace_append hprefix tailTrace_941425
  have hstable : (prefixWord ++ tailWord_941425).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941425).length < 2 ^ (prefixWord ++ tailWord_941425).sum := by decide
  have hdescent : baseEnd_941425 < baseStart_941425 := by decide
  rcases family_descends (prefixWord ++ tailWord_941425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941463 : List Nat := [1, 1, 3, 3, 1, 1, 1, 3, 6]
def baseStart_941463 : Nat := 118140960795 + 941463 * 2 ^ 59
def prefixEnd_941463 : Nat := 4983230072969 + 3 ^ 40 * 941463 * 2
def baseEnd_941463 : Nat := 429709366599071338118041

theorem tailTrace_941463 : CollatzResearch.WordTrace tailWord_941463 prefixEnd_941463 429709366599071338118041 := by
  unfold tailWord_941463
  simp only [CollatzResearch.WordTrace]
  refine ⟨34337976588247814924437043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22891984392165209949624695 34337976588247814924437043)
  ·
    refine ⟨51506964882371722386655565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34337976588247814924437043 51506964882371722386655565)
    ·
      refine ⟨19315111830889395894995837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51506964882371722386655565 19315111830889395894995837)
      ·
        refine ⟨7243166936583523460623439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19315111830889395894995837 7243166936583523460623439)
        ·
          refine ⟨10864750404875285190935159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7243166936583523460623439 10864750404875285190935159)
          ·
            refine ⟨16297125607312927786402739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10864750404875285190935159 16297125607312927786402739)
            ·
              refine ⟨24445688410969391679604109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16297125607312927786402739 24445688410969391679604109)
              ·
                refine ⟨9167133154113521879851541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24445688410969391679604109 9167133154113521879851541)
                ·
                  refine ⟨429709366599071338118041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9167133154113521879851541 429709366599071338118041)
                  ·
                    rfl

theorem cell20_941463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 3, 6].length) (baseStart_941463 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_941463 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_941463 prefixEnd_941463 := by exact prefixLift 941463
  have htrace : WordTrace (prefixWord ++ tailWord_941463) baseStart_941463 baseEnd_941463 := by
    simpa [prefixWord, tailWord_941463, baseEnd_941463] using wordTrace_append hprefix tailTrace_941463
  have hstable : (prefixWord ++ tailWord_941463).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941463).length < 2 ^ (prefixWord ++ tailWord_941463).sum := by decide
  have hdescent : baseEnd_941463 < baseStart_941463 := by decide
  rcases family_descends (prefixWord ++ tailWord_941463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941493 : List Nat := [1, 3, 3, 2, 2, 3, 2, 2, 2]
def baseStart_941493 : Nat := 118140960795 + 941493 * 2 ^ 59
def prefixEnd_941493 : Nat := 4983230072969 + 3 ^ 40 * 941493 * 2
def baseEnd_941493 : Nat := 429723059416524567117919

theorem tailTrace_941493 : CollatzResearch.WordTrace tailWord_941493 prefixEnd_941493 429723059416524567117919 := by
  unfold tailWord_941493
  simp only [CollatzResearch.WordTrace]
  refine ⟨34339070778139130048029133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22892713852092753365352755 34339070778139130048029133)
  ·
    refine ⟨12877151541802173768010925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34339070778139130048029133 12877151541802173768010925)
    ·
      refine ⟨4828931828175815163004097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12877151541802173768010925 4828931828175815163004097)
      ·
        refine ⟨3621698871131861372253073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4828931828175815163004097 3621698871131861372253073)
        ·
          refine ⟨2716274153348896029189805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3621698871131861372253073 2716274153348896029189805)
          ·
            refine ⟨1018602807505836010946177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2716274153348896029189805 1018602807505836010946177)
            ·
              refine ⟨763952105629377008209633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1018602807505836010946177 763952105629377008209633)
              ·
                refine ⟨572964079222032756157225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 763952105629377008209633 572964079222032756157225)
                ·
                  refine ⟨429723059416524567117919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 572964079222032756157225 429723059416524567117919)
                  ·
                    rfl

theorem cell20_941493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 2, 2, 2].length) (baseStart_941493 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_941493 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_941493 prefixEnd_941493 := by exact prefixLift 941493
  have htrace : WordTrace (prefixWord ++ tailWord_941493) baseStart_941493 baseEnd_941493 := by
    simpa [prefixWord, tailWord_941493, baseEnd_941493] using wordTrace_append hprefix tailTrace_941493
  have hstable : (prefixWord ++ tailWord_941493).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941493).length < 2 ^ (prefixWord ++ tailWord_941493).sum := by decide
  have hdescent : baseEnd_941493 < baseStart_941493 := by decide
  rcases family_descends (prefixWord ++ tailWord_941493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941535 : List Nat := [1, 1, 2, 3, 3, 1, 4, 3, 2]
def baseStart_941535 : Nat := 118140960795 + 941535 * 2 ^ 59
def prefixEnd_941535 : Nat := 4983230072969 + 3 ^ 40 * 941535 * 2
def baseEnd_941535 : Nat := 429742229360959087717747

theorem tailTrace_941535 : CollatzResearch.WordTrace tailWord_941535 prefixEnd_941535 429742229360959087717747 := by
  unfold tailWord_941535
  simp only [CollatzResearch.WordTrace]
  refine ⟨34340602643986971221058059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22893735095991314147372039 34340602643986971221058059)
  ·
    refine ⟨51510903965980456831587089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34340602643986971221058059 51510903965980456831587089)
    ·
      refine ⟨38633177974485342623690317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51510903965980456831587089 38633177974485342623690317)
      ·
        refine ⟨14487441740432003483883869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38633177974485342623690317 14487441740432003483883869)
        ·
          refine ⟨5432790652662001306456451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14487441740432003483883869 5432790652662001306456451)
          ·
            refine ⟨8149185978993001959684677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5432790652662001306456451 8149185978993001959684677)
            ·
              refine ⟨1527972371061187867440877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8149185978993001959684677 1527972371061187867440877)
              ·
                refine ⟨572989639147945450290329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1527972371061187867440877 572989639147945450290329)
                ·
                  refine ⟨429742229360959087717747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 572989639147945450290329 429742229360959087717747)
                  ·
                    rfl

theorem cell20_941535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 4, 3, 2].length) (baseStart_941535 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_941535 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_941535 prefixEnd_941535 := by exact prefixLift 941535
  have htrace : WordTrace (prefixWord ++ tailWord_941535) baseStart_941535 baseEnd_941535 := by
    simpa [prefixWord, tailWord_941535, baseEnd_941535] using wordTrace_append hprefix tailTrace_941535
  have hstable : (prefixWord ++ tailWord_941535).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941535).length < 2 ^ (prefixWord ++ tailWord_941535).sum := by decide
  have hdescent : baseEnd_941535 < baseStart_941535 := by decide
  rcases family_descends (prefixWord ++ tailWord_941535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941577 : List Nat := [1, 2, 1, 1, 3, 1, 3, 4, 4]
def baseStart_941577 : Nat := 118140960795 + 941577 * 2 ^ 59
def prefixEnd_941577 : Nat := 4983230072969 + 3 ^ 40 * 941577 * 2
def baseEnd_941577 : Nat := 429761399305393608317575

theorem tailTrace_941577 : CollatzResearch.WordTrace tailWord_941577 prefixEnd_941577 429761399305393608317575 := by
  unfold tailWord_941577
  simp only [CollatzResearch.WordTrace]
  refine ⟨34342134509834812394086985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22894756339889874929391323 34342134509834812394086985)
  ·
    refine ⟨25756600882376109295565239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34342134509834812394086985 25756600882376109295565239)
    ·
      refine ⟨38634901323564163943347859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25756600882376109295565239 38634901323564163943347859)
      ·
        refine ⟨57952351985346245915021789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38634901323564163943347859 57952351985346245915021789)
        ·
          refine ⟨21732131994504842218133171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57952351985346245915021789 21732131994504842218133171)
          ·
            refine ⟨32598197991757263327199757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21732131994504842218133171 32598197991757263327199757)
            ·
              refine ⟨12224324246908973747699909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32598197991757263327199757 12224324246908973747699909)
              ·
                refine ⟨2292060796295432577693733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12224324246908973747699909 2292060796295432577693733)
                ·
                  refine ⟨429761399305393608317575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2292060796295432577693733 429761399305393608317575)
                  ·
                    rfl

theorem cell20_941577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 4, 4].length) (baseStart_941577 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_941577 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_941577 prefixEnd_941577 := by exact prefixLift 941577
  have htrace : WordTrace (prefixWord ++ tailWord_941577) baseStart_941577 baseEnd_941577 := by
    simpa [prefixWord, tailWord_941577, baseEnd_941577] using wordTrace_append hprefix tailTrace_941577
  have hstable : (prefixWord ++ tailWord_941577).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941577).length < 2 ^ (prefixWord ++ tailWord_941577).sum := by decide
  have hdescent : baseEnd_941577 < baseStart_941577 := by decide
  rcases family_descends (prefixWord ++ tailWord_941577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941601 : List Nat := [1, 2, 3, 2, 2, 4, 6]
def baseStart_941601 : Nat := 118140960795 + 941601 * 2 ^ 59
def prefixEnd_941601 : Nat := 4983230072969 + 3 ^ 40 * 941601 * 2
def baseEnd_941601 : Nat := 47752483728817354613053

theorem tailTrace_941601 : CollatzResearch.WordTrace tailWord_941601 prefixEnd_941601 47752483728817354613053 := by
  unfold tailWord_941601
  simp only [CollatzResearch.WordTrace]
  refine ⟨34343009861747864492960657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22895339907831909661973771 34343009861747864492960657)
  ·
    refine ⟨25757257396310898369720493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34343009861747864492960657 25757257396310898369720493)
    ·
      refine ⟨9658971523616586888645185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25757257396310898369720493 9658971523616586888645185)
      ·
        refine ⟨7244228642712440166483889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9658971523616586888645185 7244228642712440166483889)
        ·
          refine ⟨5433171482034330124862917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7244228642712440166483889 5433171482034330124862917)
          ·
            refine ⟨1018719652881436898411797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5433171482034330124862917 1018719652881436898411797)
            ·
              refine ⟨47752483728817354613053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1018719652881436898411797 47752483728817354613053)
              ·
                rfl

theorem cell20_941601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 6].length) (baseStart_941601 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_941601 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_941601 prefixEnd_941601 := by exact prefixLift 941601
  have htrace : WordTrace (prefixWord ++ tailWord_941601) baseStart_941601 baseEnd_941601 := by
    simpa [prefixWord, tailWord_941601, baseEnd_941601] using wordTrace_append hprefix tailTrace_941601
  have hstable : (prefixWord ++ tailWord_941601).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941601).length < 2 ^ (prefixWord ++ tailWord_941601).sum := by decide
  have hdescent : baseEnd_941601 < baseStart_941601 := by decide
  rcases family_descends (prefixWord ++ tailWord_941601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941625 : List Nat := [1, 2, 1, 5, 1, 3, 1, 3, 3]
def baseStart_941625 : Nat := 118140960795 + 941625 * 2 ^ 59
def prefixEnd_941625 : Nat := 4983230072969 + 3 ^ 40 * 941625 * 2
def baseEnd_941625 : Nat := 429783307813318774717379

theorem tailTrace_941625 : CollatzResearch.WordTrace tailWord_941625 prefixEnd_941625 429783307813318774717379 := by
  unfold tailWord_941625
  simp only [CollatzResearch.WordTrace]
  refine ⟨34343885213660916591834329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22895923475773944394556219 34343885213660916591834329)
  ·
    refine ⟨25757913910245687443875747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34343885213660916591834329 25757913910245687443875747)
    ·
      refine ⟨38636870865368531165813621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25757913910245687443875747 38636870865368531165813621)
      ·
        refine ⟨3622206643628299796795027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38636870865368531165813621 3622206643628299796795027)
        ·
          refine ⟨5433309965442449695192541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3622206643628299796795027 5433309965442449695192541)
          ·
            refine ⟨2037491237040918635697203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5433309965442449695192541 2037491237040918635697203)
            ·
              refine ⟨3056236855561377953545805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2037491237040918635697203 3056236855561377953545805)
              ·
                refine ⟨1146088820835516732579677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3056236855561377953545805 1146088820835516732579677)
                ·
                  refine ⟨429783307813318774717379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1146088820835516732579677 429783307813318774717379)
                  ·
                    rfl

theorem cell20_941625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 3, 3].length) (baseStart_941625 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_941625 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_941625 prefixEnd_941625 := by exact prefixLift 941625
  have htrace : WordTrace (prefixWord ++ tailWord_941625) baseStart_941625 baseEnd_941625 := by
    simpa [prefixWord, tailWord_941625, baseEnd_941625] using wordTrace_append hprefix tailTrace_941625
  have hstable : (prefixWord ++ tailWord_941625).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941625).length < 2 ^ (prefixWord ++ tailWord_941625).sum := by decide
  have hdescent : baseEnd_941625 < baseStart_941625 := by decide
  rcases family_descends (prefixWord ++ tailWord_941625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941691 : List Nat := [1, 1, 1, 1, 1, 4, 5, 2, 4]
def baseStart_941691 : Nat := 118140960795 + 941691 * 2 ^ 59
def prefixEnd_941691 : Nat := 4983230072969 + 3 ^ 40 * 941691 * 2
def baseEnd_941691 : Nat := 429813432011715878517109

theorem tailTrace_941691 : CollatzResearch.WordTrace tailWord_941691 prefixEnd_941691 429813432011715878517109 := by
  unfold tailWord_941691
  simp only [CollatzResearch.WordTrace]
  refine ⟨34346292431421809863736927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22897528287614539909157951 34346292431421809863736927)
  ·
    refine ⟨51519438647132714795605391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34346292431421809863736927 51519438647132714795605391)
    ·
      refine ⟨77279157970699072193408087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51519438647132714795605391 77279157970699072193408087)
      ·
        refine ⟨115918736956048608290112131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77279157970699072193408087 115918736956048608290112131)
        ·
          refine ⟨173878105434072912435168197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115918736956048608290112131 173878105434072912435168197)
          ·
            refine ⟨32602144768888671081594037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 173878105434072912435168197 32602144768888671081594037)
            ·
              refine ⟨3056451072083312913899441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32602144768888671081594037 3056451072083312913899441)
              ·
                refine ⟨2292338304062484685424581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3056451072083312913899441 2292338304062484685424581)
                ·
                  refine ⟨429813432011715878517109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2292338304062484685424581 429813432011715878517109)
                  ·
                    rfl

theorem cell20_941691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 2, 4].length) (baseStart_941691 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_941691 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_941691 prefixEnd_941691 := by exact prefixLift 941691
  have htrace : WordTrace (prefixWord ++ tailWord_941691) baseStart_941691 baseEnd_941691 := by
    simpa [prefixWord, tailWord_941691, baseEnd_941691] using wordTrace_append hprefix tailTrace_941691
  have hstable : (prefixWord ++ tailWord_941691).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941691).length < 2 ^ (prefixWord ++ tailWord_941691).sum := by decide
  have hdescent : baseEnd_941691 < baseStart_941691 := by decide
  rcases family_descends (prefixWord ++ tailWord_941691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941749 : List Nat := [1, 3, 3, 3, 2, 2, 2, 4]
def baseStart_941749 : Nat := 118140960795 + 941749 * 2 ^ 59
def prefixEnd_941749 : Nat := 4983230072969 + 3 ^ 40 * 941749 * 2
def baseEnd_941749 : Nat := 143279968264041818194513

theorem tailTrace_941749 : CollatzResearch.WordTrace tailWord_941749 prefixEnd_941749 143279968264041818194513 := by
  unfold tailWord_941749
  simp only [CollatzResearch.WordTrace]
  refine ⟨34348407865211685769348301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22898938576807790512898867 34348407865211685769348301)
  ·
    refine ⟨12880652949454382163505613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34348407865211685769348301 12880652949454382163505613)
    ·
      refine ⟨4830244856045393311314605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12880652949454382163505613 4830244856045393311314605)
      ·
        refine ⟨1811341821017022491742977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4830244856045393311314605 1811341821017022491742977)
        ·
          refine ⟨1358506365762766868807233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1811341821017022491742977 1358506365762766868807233)
          ·
            refine ⟨1018879774322075151605425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1358506365762766868807233 1018879774322075151605425)
            ·
              refine ⟨764159830741556363704069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1018879774322075151605425 764159830741556363704069)
              ·
                refine ⟨143279968264041818194513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 764159830741556363704069 143279968264041818194513)
                ·
                  rfl

theorem cell20_941749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 2, 4].length) (baseStart_941749 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_941749 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_941749 prefixEnd_941749 := by exact prefixLift 941749
  have htrace : WordTrace (prefixWord ++ tailWord_941749) baseStart_941749 baseEnd_941749 := by
    simpa [prefixWord, tailWord_941749, baseEnd_941749] using wordTrace_append hprefix tailTrace_941749
  have hstable : (prefixWord ++ tailWord_941749).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941749).length < 2 ^ (prefixWord ++ tailWord_941749).sum := by decide
  have hdescent : baseEnd_941749 < baseStart_941749 := by decide
  rcases family_descends (prefixWord ++ tailWord_941749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941753 : List Nat := [1, 2, 1, 4, 1, 1, 6, 4]
def baseStart_941753 : Nat := 118140960795 + 941753 * 2 ^ 59
def prefixEnd_941753 : Nat := 4983230072969 + 3 ^ 40 * 941753 * 2
def baseEnd_941753 : Nat := 143280576833706406150063

theorem tailTrace_941753 : CollatzResearch.WordTrace tailWord_941753 prefixEnd_941753 143280576833706406150063 := by
  unfold tailWord_941753
  simp only [CollatzResearch.WordTrace]
  refine ⟨34348553757197194452493913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22899035838131462968329275 34348553757197194452493913)
  ·
    refine ⟨25761415317897895839370435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34348553757197194452493913 25761415317897895839370435)
    ·
      refine ⟨38642122976846843759055653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25761415317897895839370435 38642122976846843759055653)
      ·
        refine ⟨7245398058158783204822935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38642122976846843759055653 7245398058158783204822935)
        ·
          refine ⟨10868097087238174807234403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7245398058158783204822935 10868097087238174807234403)
          ·
            refine ⟨16302145630857262210851605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10868097087238174807234403 16302145630857262210851605)
            ·
              refine ⟨764163076446434166133669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 16302145630857262210851605 764163076446434166133669)
              ·
                refine ⟨143280576833706406150063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 764163076446434166133669 143280576833706406150063)
                ·
                  rfl

theorem cell20_941753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 6, 4].length) (baseStart_941753 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_941753 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_941753 prefixEnd_941753 := by exact prefixLift 941753
  have htrace : WordTrace (prefixWord ++ tailWord_941753) baseStart_941753 baseEnd_941753 := by
    simpa [prefixWord, tailWord_941753, baseEnd_941753] using wordTrace_append hprefix tailTrace_941753
  have hstable : (prefixWord ++ tailWord_941753).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941753).length < 2 ^ (prefixWord ++ tailWord_941753).sum := by decide
  have hdescent : baseEnd_941753 < baseStart_941753 := by decide
  rcases family_descends (prefixWord ++ tailWord_941753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941770 : List Nat := [3, 1, 2, 1, 6, 1, 6]
def baseStart_941770 : Nat := 118140960795 + 941770 * 2 ^ 59
def prefixEnd_941770 : Nat := 4983230072969 + 3 ^ 40 * 941770 * 2
def baseEnd_941770 : Nat := 47761054418260301653717

theorem tailTrace_941770 : CollatzResearch.WordTrace tailWord_941770 prefixEnd_941770 47761054418260301653717 := by
  unfold tailWord_941770
  simp only [CollatzResearch.WordTrace]
  refine ⟨8587293449533901588965691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22899449198757070903908509 8587293449533901588965691)
  ·
    refine ⟨12880940174300852383448537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8587293449533901588965691 12880940174300852383448537)
    ·
      refine ⟨9660705130725639287586403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12880940174300852383448537 9660705130725639287586403)
      ·
        refine ⟨14491057696088458931379605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9660705130725639287586403 14491057696088458931379605)
        ·
          refine ⟨679268329504146512408419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 14491057696088458931379605 679268329504146512408419)
          ·
            refine ⟨1018902494256219768612629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 679268329504146512408419 1018902494256219768612629)
            ·
              refine ⟨47761054418260301653717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1018902494256219768612629 47761054418260301653717)
              ·
                rfl

theorem cell20_941770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 6].length) (baseStart_941770 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_941770 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_941770 prefixEnd_941770 := by exact prefixLift 941770
  have htrace : WordTrace (prefixWord ++ tailWord_941770) baseStart_941770 baseEnd_941770 := by
    simpa [prefixWord, tailWord_941770, baseEnd_941770] using wordTrace_append hprefix tailTrace_941770
  have hstable : (prefixWord ++ tailWord_941770).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941770).length < 2 ^ (prefixWord ++ tailWord_941770).sum := by decide
  have hdescent : baseEnd_941770 < baseStart_941770 := by decide
  rcases family_descends (prefixWord ++ tailWord_941770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941819 : List Nat := [1, 1, 1, 1, 1, 3, 1, 6, 5]
def baseStart_941819 : Nat := 118140960795 + 941819 * 2 ^ 59
def prefixEnd_941819 : Nat := 4983230072969 + 3 ^ 40 * 941819 * 2
def baseEnd_941819 : Nat := 429871854699516322249919

theorem tailTrace_941819 : CollatzResearch.WordTrace tailWord_941819 prefixEnd_941819 429871854699516322249919 := by
  unfold tailWord_941819
  simp only [CollatzResearch.WordTrace]
  refine ⟨34350960974958087724396511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22900640649972058482931007 34350960974958087724396511)
  ·
    refine ⟨51526441462437131586594767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34350960974958087724396511 51526441462437131586594767)
    ·
      refine ⟨77289662193655697379892151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51526441462437131586594767 77289662193655697379892151)
      ·
        refine ⟨115934493290483546069838227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77289662193655697379892151 115934493290483546069838227)
        ·
          refine ⟨173901739935725319104757341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115934493290483546069838227 173901739935725319104757341)
          ·
            refine ⟨65213152475896994664284003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 173901739935725319104757341 65213152475896994664284003)
            ·
              refine ⟨97819728713845491996426005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65213152475896994664284003 97819728713845491996426005)
              ·
                refine ⟨4585299783461507437332469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 97819728713845491996426005 4585299783461507437332469)
                ·
                  refine ⟨429871854699516322249919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4585299783461507437332469 429871854699516322249919)
                  ·
                    rfl

theorem cell20_941819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 6, 5].length) (baseStart_941819 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_941819 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_941819 prefixEnd_941819 := by exact prefixLift 941819
  have htrace : WordTrace (prefixWord ++ tailWord_941819) baseStart_941819 baseEnd_941819 := by
    simpa [prefixWord, tailWord_941819, baseEnd_941819] using wordTrace_append hprefix tailTrace_941819
  have hstable : (prefixWord ++ tailWord_941819).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941819).length < 2 ^ (prefixWord ++ tailWord_941819).sum := by decide
  have hdescent : baseEnd_941819 < baseStart_941819 := by decide
  rcases family_descends (prefixWord ++ tailWord_941819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941836 : List Nat := [2, 2, 1, 2, 2, 1, 3, 4, 3]
def baseStart_941836 : Nat := 118140960795 + 941836 * 2 ^ 59
def prefixEnd_941836 : Nat := 4983230072969 + 3 ^ 40 * 941836 * 2
def baseEnd_941836 : Nat := 429879613962739818683183

theorem tailTrace_941836 : CollatzResearch.WordTrace tailWord_941836 prefixEnd_941836 429879613962739818683183 := by
  unfold tailWord_941836
  simp only [CollatzResearch.WordTrace]
  refine ⟨17175790507948249813882681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22901054010597666418510241 17175790507948249813882681)
  ·
    refine ⟨12881842880961187360412011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17175790507948249813882681 12881842880961187360412011)
    ·
      refine ⟨19322764321441781040618017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12881842880961187360412011 19322764321441781040618017)
      ·
        refine ⟨14492073241081335780463513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19322764321441781040618017 14492073241081335780463513)
        ·
          refine ⟨10869054930811001835347635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14492073241081335780463513 10869054930811001835347635)
          ·
            refine ⟨16303582396216502753021453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10869054930811001835347635 16303582396216502753021453)
            ·
              refine ⟨6113843398581188532383045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16303582396216502753021453 6113843398581188532383045)
              ·
                refine ⟨1146345637233972849821821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6113843398581188532383045 1146345637233972849821821)
                ·
                  refine ⟨429879613962739818683183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1146345637233972849821821 429879613962739818683183)
                  ·
                    rfl

theorem cell20_941836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 4, 3].length) (baseStart_941836 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_941836 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_941836 prefixEnd_941836 := by exact prefixLift 941836
  have htrace : WordTrace (prefixWord ++ tailWord_941836) baseStart_941836 baseEnd_941836 := by
    simpa [prefixWord, tailWord_941836, baseEnd_941836] using wordTrace_append hprefix tailTrace_941836
  have hstable : (prefixWord ++ tailWord_941836).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941836).length < 2 ^ (prefixWord ++ tailWord_941836).sum := by decide
  have hdescent : baseEnd_941836 < baseStart_941836 := by decide
  rcases family_descends (prefixWord ++ tailWord_941836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941860 : List Nat := [2, 3, 1, 3, 2, 2, 1, 2, 4]
def baseStart_941860 : Nat := 118140960795 + 941860 * 2 ^ 59
def prefixEnd_941860 : Nat := 4983230072969 + 3 ^ 40 * 941860 * 2
def baseEnd_941860 : Nat := 429890568216702401883085

theorem tailTrace_941860 : CollatzResearch.WordTrace tailWord_941860 prefixEnd_941860 429890568216702401883085 := by
  unfold tailWord_941860
  simp only [CollatzResearch.WordTrace]
  refine ⟨17176228183904775863319517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22901637578539701151092689 17176228183904775863319517)
  ·
    refine ⟨6441085568964290948744819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17176228183904775863319517 6441085568964290948744819)
    ·
      refine ⟨9661628353446436423117229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6441085568964290948744819 9661628353446436423117229)
      ·
        refine ⟨3623110632542413658668961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9661628353446436423117229 3623110632542413658668961)
        ·
          refine ⟨2717332974406810244001721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3623110632542413658668961 2717332974406810244001721)
          ·
            refine ⟨2037999730805107683001291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2717332974406810244001721 2037999730805107683001291)
            ·
              refine ⟨3056999596207661524501937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2037999730805107683001291 3056999596207661524501937)
              ·
                refine ⟨2292749697155746143376453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3056999596207661524501937 2292749697155746143376453)
                ·
                  refine ⟨429890568216702401883085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2292749697155746143376453 429890568216702401883085)
                  ·
                    rfl

theorem cell20_941860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 2, 4].length) (baseStart_941860 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_941860 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_941860 prefixEnd_941860 := by exact prefixLift 941860
  have htrace : WordTrace (prefixWord ++ tailWord_941860) baseStart_941860 baseEnd_941860 := by
    simpa [prefixWord, tailWord_941860, baseEnd_941860] using wordTrace_append hprefix tailTrace_941860
  have hstable : (prefixWord ++ tailWord_941860).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941860).length < 2 ^ (prefixWord ++ tailWord_941860).sum := by decide
  have hdescent : baseEnd_941860 < baseStart_941860 := by decide
  rcases family_descends (prefixWord ++ tailWord_941860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941891 : List Nat := [1, 1, 1, 3, 1, 7, 1, 2, 3]
def baseStart_941891 : Nat := 118140960795 + 941891 * 2 ^ 59
def prefixEnd_941891 : Nat := 4983230072969 + 3 ^ 40 * 941891 * 2
def baseEnd_941891 : Nat := 429904717461404071849625

theorem tailTrace_941891 : CollatzResearch.WordTrace tailWord_941891 prefixEnd_941891 429904717461404071849625 := by
  unfold tailWord_941891
  simp only [CollatzResearch.WordTrace]
  refine ⟨34353587030697244021017527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22902391353798162680678351 34353587030697244021017527)
  ·
    refine ⟨51530380546045866031526291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34353587030697244021017527 51530380546045866031526291)
    ·
      refine ⟨77295570819068799047289437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51530380546045866031526291 77295570819068799047289437)
      ·
        refine ⟨28985839057150799642733539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77295570819068799047289437 28985839057150799642733539)
        ·
          refine ⟨43478758585726199464100309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28985839057150799642733539 43478758585726199464100309)
          ·
            refine ⟨1019033404352957799939851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 43478758585726199464100309 1019033404352957799939851)
            ·
              refine ⟨1528550106529436699909777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1019033404352957799939851 1528550106529436699909777)
              ·
                refine ⟨1146412579897077524932333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1528550106529436699909777 1146412579897077524932333)
                ·
                  refine ⟨429904717461404071849625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1146412579897077524932333 429904717461404071849625)
                  ·
                    rfl

theorem cell20_941891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 1, 2, 3].length) (baseStart_941891 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_941891 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_941891 prefixEnd_941891 := by exact prefixLift 941891
  have htrace : WordTrace (prefixWord ++ tailWord_941891) baseStart_941891 baseEnd_941891 := by
    simpa [prefixWord, tailWord_941891, baseEnd_941891] using wordTrace_append hprefix tailTrace_941891
  have hstable : (prefixWord ++ tailWord_941891).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941891).length < 2 ^ (prefixWord ++ tailWord_941891).sum := by decide
  have hdescent : baseEnd_941891 < baseStart_941891 := by decide
  rcases family_descends (prefixWord ++ tailWord_941891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941894 : List Nat := [6, 1, 1, 2, 1, 2, 2, 1, 4]
def baseStart_941894 : Nat := 118140960795 + 941894 * 2 ^ 59
def prefixEnd_941894 : Nat := 4983230072969 + 3 ^ 40 * 941894 * 2
def baseEnd_941894 : Nat := 429906086743149394749613

theorem tailTrace_941894 : CollatzResearch.WordTrace tailWord_941894 prefixEnd_941894 429906086743149394749613 := by
  unfold tailWord_941894
  simp only [CollatzResearch.WordTrace]
  refine ⟨1073553014052699235418023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 22902464299790917022251157 1073553014052699235418023)
  ·
    refine ⟨1610329521079048853127035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1073553014052699235418023 1610329521079048853127035)
    ·
      refine ⟨2415494281618573279690553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1610329521079048853127035 2415494281618573279690553)
      ·
        refine ⟨1811620711213929959767915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2415494281618573279690553 1811620711213929959767915)
        ·
          refine ⟨2717431066820894939651873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1811620711213929959767915 2717431066820894939651873)
          ·
            refine ⟨2038073300115671204738905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2717431066820894939651873 2038073300115671204738905)
            ·
              refine ⟨1528554975086753403554179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2038073300115671204738905 1528554975086753403554179)
              ·
                refine ⟨2292832462630130105331269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1528554975086753403554179 2292832462630130105331269)
                ·
                  refine ⟨429906086743149394749613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2292832462630130105331269 429906086743149394749613)
                  ·
                    rfl

theorem cell20_941894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_941894 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_941894 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_941894 prefixEnd_941894 := by exact prefixLift 941894
  have htrace : WordTrace (prefixWord ++ tailWord_941894) baseStart_941894 baseEnd_941894 := by
    simpa [prefixWord, tailWord_941894, baseEnd_941894] using wordTrace_append hprefix tailTrace_941894
  have hstable : (prefixWord ++ tailWord_941894).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941894).length < 2 ^ (prefixWord ++ tailWord_941894).sum := by decide
  have hdescent : baseEnd_941894 < baseStart_941894 := by decide
  rcases family_descends (prefixWord ++ tailWord_941894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941898 : List Nat := [3, 1, 2, 1, 1, 1, 3, 6, 2]
def baseStart_941898 : Nat := 118140960795 + 941898 * 2 ^ 59
def prefixEnd_941898 : Nat := 4983230072969 + 3 ^ 40 * 941898 * 2
def baseEnd_941898 : Nat := 429907912452143158616263

theorem tailTrace_941898 : CollatzResearch.WordTrace tailWord_941898 prefixEnd_941898 429907912452143158616263 := by
  unfold tailWord_941898
  simp only [CollatzResearch.WordTrace]
  refine ⟨8588460585417971054130587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22902561561114589477681565 8588460585417971054130587)
  ·
    refine ⟨12882690878126956581195881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8588460585417971054130587 12882690878126956581195881)
    ·
      refine ⟨9662018158595217435896911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12882690878126956581195881 9662018158595217435896911)
      ·
        refine ⟨14493027237892826153845367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9662018158595217435896911 14493027237892826153845367)
        ·
          refine ⟨21739540856839239230768051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14493027237892826153845367 21739540856839239230768051)
          ·
            refine ⟨32609311285258858846152077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21739540856839239230768051 32609311285258858846152077)
            ·
              refine ⟨12228491731972072067307029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32609311285258858846152077 12228491731972072067307029)
              ·
                refine ⟨573210549936190878155017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12228491731972072067307029 573210549936190878155017)
                ·
                  refine ⟨429907912452143158616263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 573210549936190878155017 429907912452143158616263)
                  ·
                    rfl

theorem cell20_941898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 6, 2].length) (baseStart_941898 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_941898 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_941898 prefixEnd_941898 := by exact prefixLift 941898
  have htrace : WordTrace (prefixWord ++ tailWord_941898) baseStart_941898 baseEnd_941898 := by
    simpa [prefixWord, tailWord_941898, baseEnd_941898] using wordTrace_append hprefix tailTrace_941898
  have hstable : (prefixWord ++ tailWord_941898).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941898).length < 2 ^ (prefixWord ++ tailWord_941898).sum := by decide
  have hdescent : baseEnd_941898 < baseStart_941898 := by decide
  rcases family_descends (prefixWord ++ tailWord_941898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941908 : List Nat := [2, 4, 1, 1, 3, 2, 3, 1, 3]
def baseStart_941908 : Nat := 118140960795 + 941908 * 2 ^ 59
def prefixEnd_941908 : Nat := 4983230072969 + 3 ^ 40 * 941908 * 2
def baseEnd_941908 : Nat := 429912476724627568282889

theorem tailTrace_941908 : CollatzResearch.WordTrace tailWord_941908 prefixEnd_941908 429912476724627568282889 := by
  unfold tailWord_941908
  simp only [CollatzResearch.WordTrace]
  refine ⟨17177103535817827962193189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22902804714423770616257585 17177103535817827962193189)
  ·
    refine ⟨3220706912965842742911223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17177103535817827962193189 3220706912965842742911223)
    ·
      refine ⟨4831060369448764114366835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3220706912965842742911223 4831060369448764114366835)
      ·
        refine ⟨7246590554173146171550253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4831060369448764114366835 7246590554173146171550253)
        ·
          refine ⟨2717471457814929814331345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7246590554173146171550253 2717471457814929814331345)
          ·
            refine ⟨2038103593361197360748509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2717471457814929814331345 2038103593361197360748509)
            ·
              refine ⟨764288847510449010280691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2038103593361197360748509 764288847510449010280691)
              ·
                refine ⟨1146433271265673515421037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 764288847510449010280691 1146433271265673515421037)
                ·
                  refine ⟨429912476724627568282889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1146433271265673515421037 429912476724627568282889)
                  ·
                    rfl

theorem cell20_941908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 3, 1, 3].length) (baseStart_941908 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_941908 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_941908 prefixEnd_941908 := by exact prefixLift 941908
  have htrace : WordTrace (prefixWord ++ tailWord_941908) baseStart_941908 baseEnd_941908 := by
    simpa [prefixWord, tailWord_941908, baseEnd_941908] using wordTrace_append hprefix tailTrace_941908
  have hstable : (prefixWord ++ tailWord_941908).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941908).length < 2 ^ (prefixWord ++ tailWord_941908).sum := by decide
  have hdescent : baseEnd_941908 < baseStart_941908 := by decide
  rcases family_descends (prefixWord ++ tailWord_941908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941919 : List Nat := [1, 1, 2, 3, 1, 4, 2, 2, 4]
def baseStart_941919 : Nat := 118140960795 + 941919 * 2 ^ 59
def prefixEnd_941919 : Nat := 4983230072969 + 3 ^ 40 * 941919 * 2
def baseEnd_941919 : Nat := 429917497424360418916177

theorem tailTrace_941919 : CollatzResearch.WordTrace tailWord_941919 prefixEnd_941919 429917497424360418916177 := by
  unfold tailWord_941919
  simp only [CollatzResearch.WordTrace]
  refine ⟨34354608274595804803036811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22903072183063869868691207 34354608274595804803036811)
  ·
    refine ⟨51531912411893707204555217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34354608274595804803036811 51531912411893707204555217)
    ·
      refine ⟨38648934308920280403416413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51531912411893707204555217 38648934308920280403416413)
      ·
        refine ⟨14493350365845105151281155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38648934308920280403416413 14493350365845105151281155)
        ·
          refine ⟨21740025548767657726921733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14493350365845105151281155 21740025548767657726921733)
          ·
            refine ⟨4076254790393935823797825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21740025548767657726921733 4076254790393935823797825)
            ·
              refine ⟨3057191092795451867848369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4076254790393935823797825 3057191092795451867848369)
              ·
                refine ⟨2292893319596588900886277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3057191092795451867848369 2292893319596588900886277)
                ·
                  refine ⟨429917497424360418916177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2292893319596588900886277 429917497424360418916177)
                  ·
                    rfl

theorem cell20_941919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 2, 4].length) (baseStart_941919 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_941919 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_941919 prefixEnd_941919 := by exact prefixLift 941919
  have htrace : WordTrace (prefixWord ++ tailWord_941919) baseStart_941919 baseEnd_941919 := by
    simpa [prefixWord, tailWord_941919, baseEnd_941919] using wordTrace_append hprefix tailTrace_941919
  have hstable : (prefixWord ++ tailWord_941919).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941919).length < 2 ^ (prefixWord ++ tailWord_941919).sum := by decide
  have hdescent : baseEnd_941919 < baseStart_941919 := by decide
  rcases family_descends (prefixWord ++ tailWord_941919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941922 : List Nat := [3, 3, 2, 1, 2, 1, 4, 4]
def baseStart_941922 : Nat := 118140960795 + 941922 * 2 ^ 59
def prefixEnd_941922 : Nat := 4983230072969 + 3 ^ 40 * 941922 * 2
def baseEnd_941922 : Nat := 143306288902035247272055

theorem tailTrace_941922 : CollatzResearch.WordTrace tailWord_941922 prefixEnd_941922 143306288902035247272055 := by
  unfold tailWord_941922
  simp only [CollatzResearch.WordTrace]
  refine ⟨8588679423396234078849005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22903145129056624210264013 8588679423396234078849005)
  ·
    refine ⟨3220754783773587779568377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8588679423396234078849005 3220754783773587779568377)
    ·
      refine ⟨2415566087830190834676283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3220754783773587779568377 2415566087830190834676283)
      ·
        refine ⟨3623349131745286252014425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2415566087830190834676283 3623349131745286252014425)
        ·
          refine ⟨2717511848808964689010819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3623349131745286252014425 2717511848808964689010819)
          ·
            refine ⟨4076267773213447033516229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2717511848808964689010819 4076267773213447033516229)
            ·
              refine ⟨764300207477521318784293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4076267773213447033516229 764300207477521318784293)
              ·
                refine ⟨143306288902035247272055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 764300207477521318784293 143306288902035247272055)
                ·
                  rfl

theorem cell20_941922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 4, 4].length) (baseStart_941922 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_941922 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_941922 prefixEnd_941922 := by exact prefixLift 941922
  have htrace : WordTrace (prefixWord ++ tailWord_941922) baseStart_941922 baseEnd_941922 := by
    simpa [prefixWord, tailWord_941922, baseEnd_941922] using wordTrace_append hprefix tailTrace_941922
  have hstable : (prefixWord ++ tailWord_941922).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941922).length < 2 ^ (prefixWord ++ tailWord_941922).sum := by decide
  have hdescent : baseEnd_941922 < baseStart_941922 := by decide
  rcases family_descends (prefixWord ++ tailWord_941922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_941998 : List Nat := [4, 1, 5, 1, 9]
def baseStart_941998 : Nat := 118140960795 + 941998 * 2 ^ 59
def prefixEnd_941998 : Nat := 4983230072969 + 3 ^ 40 * 941998 * 2
def baseEnd_941998 : Nat := 5308068582431941423241

theorem tailTrace_941998 : CollatzResearch.WordTrace tailWord_941998 prefixEnd_941998 5308068582431941423241 := by
  unfold tailWord_941998
  simp only [CollatzResearch.WordTrace]
  refine ⟨4294686205163700161895331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22904993094206400863441765 4294686205163700161895331)
  ·
    refine ⟨6442029307745550242842997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4294686205163700161895331 6442029307745550242842997)
    ·
      refine ⟨603940247601145335266531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6442029307745550242842997 603940247601145335266531)
      ·
        refine ⟨905910371401718002899797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 603940247601145335266531 905910371401718002899797)
        ·
          refine ⟨5308068582431941423241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 905910371401718002899797 5308068582431941423241)
          ·
            rfl

theorem cell20_941998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 9].length) (baseStart_941998 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_941998 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_941998 prefixEnd_941998 := by exact prefixLift 941998
  have htrace : WordTrace (prefixWord ++ tailWord_941998) baseStart_941998 baseEnd_941998 := by
    simpa [prefixWord, tailWord_941998, baseEnd_941998] using wordTrace_append hprefix tailTrace_941998
  have hstable : (prefixWord ++ tailWord_941998).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_941998).length < 2 ^ (prefixWord ++ tailWord_941998).sum := by decide
  have hdescent : baseEnd_941998 < baseStart_941998 := by decide
  rcases family_descends (prefixWord ++ tailWord_941998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942004 : List Nat := [2, 5, 2, 1, 2, 2, 2, 2, 2]
def baseStart_942004 : Nat := 118140960795 + 942004 * 2 ^ 59
def prefixEnd_942004 : Nat := 4983230072969 + 3 ^ 40 * 942004 * 2
def baseEnd_942004 : Nat := 429956293740477901082497

theorem tailTrace_942004 : CollatzResearch.WordTrace tailWord_942004 prefixEnd_942004 429956293740477901082497 := by
  unfold tailWord_942004
  simp only [CollatzResearch.WordTrace]
  refine ⟨17178854239643932159940533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22905138986191909546587377 17178854239643932159940533)
  ·
    refine ⟨1610517584966618639994425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17178854239643932159940533 1610517584966618639994425)
    ·
      refine ⟨1207888188724963979995819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1610517584966618639994425 1207888188724963979995819)
      ·
        refine ⟨1811832283087445969993729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1207888188724963979995819 1811832283087445969993729)
        ·
          refine ⟨1358874212315584477495297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1811832283087445969993729 1358874212315584477495297)
          ·
            refine ⟨1019155659236688358121473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1358874212315584477495297 1019155659236688358121473)
            ·
              refine ⟨764366744427516268591105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1019155659236688358121473 764366744427516268591105)
              ·
                refine ⟨573275058320637201443329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 764366744427516268591105 573275058320637201443329)
                ·
                  refine ⟨429956293740477901082497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 573275058320637201443329 429956293740477901082497)
                  ·
                    rfl

theorem cell20_942004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 2, 2, 2].length) (baseStart_942004 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_942004 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_942004 prefixEnd_942004 := by exact prefixLift 942004
  have htrace : WordTrace (prefixWord ++ tailWord_942004) baseStart_942004 baseEnd_942004 := by
    simpa [prefixWord, tailWord_942004, baseEnd_942004] using wordTrace_append hprefix tailTrace_942004
  have hstable : (prefixWord ++ tailWord_942004).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942004).length < 2 ^ (prefixWord ++ tailWord_942004).sum := by decide
  have hdescent : baseEnd_942004 < baseStart_942004 := by decide
  rcases family_descends (prefixWord ++ tailWord_942004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942005 : List Nat := [1, 3, 3, 2, 1, 3, 2, 2, 3]
def baseStart_942005 : Nat := 118140960795 + 942005 * 2 ^ 59
def prefixEnd_942005 : Nat := 4983230072969 + 3 ^ 40 * 942005 * 2
def baseEnd_942005 : Nat := 429956750167726342049159

theorem tailTrace_942005 : CollatzResearch.WordTrace tailWord_942005 prefixEnd_942005 429956750167726342049159 := by
  unfold tailWord_942005
  simp only [CollatzResearch.WordTrace]
  refine ⟨34357744952284241490667469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22905163301522827660444979 34357744952284241490667469)
  ·
    refine ⟨12884154357106590559000301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34357744952284241490667469 12884154357106590559000301)
    ·
      refine ⟨4831557883914971459625113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12884154357106590559000301 4831557883914971459625113)
      ·
        refine ⟨3623668412936228594718835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4831557883914971459625113 3623668412936228594718835)
        ·
          refine ⟨5435502619404342892078253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3623668412936228594718835 5435502619404342892078253)
          ·
            refine ⟨2038313482276628584529345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5435502619404342892078253 2038313482276628584529345)
            ·
              refine ⟨1528735111707471438397009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2038313482276628584529345 1528735111707471438397009)
              ·
                refine ⟨1146551333780603578797757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1528735111707471438397009 1146551333780603578797757)
                ·
                  refine ⟨429956750167726342049159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1146551333780603578797757 429956750167726342049159)
                  ·
                    rfl

theorem cell20_942005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 2, 2, 3].length) (baseStart_942005 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_942005 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_942005 prefixEnd_942005 := by exact prefixLift 942005
  have htrace : WordTrace (prefixWord ++ tailWord_942005) baseStart_942005 baseEnd_942005 := by
    simpa [prefixWord, tailWord_942005, baseEnd_942005] using wordTrace_append hprefix tailTrace_942005
  have hstable : (prefixWord ++ tailWord_942005).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942005).length < 2 ^ (prefixWord ++ tailWord_942005).sum := by decide
  have hdescent : baseEnd_942005 < baseStart_942005 := by decide
  rcases family_descends (prefixWord ++ tailWord_942005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942026 : List Nat := [3, 1, 2, 1, 2, 1, 4, 3, 3]
def baseStart_942026 : Nat := 118140960795 + 942026 * 2 ^ 59
def prefixEnd_942026 : Nat := 4983230072969 + 3 ^ 40 * 942026 * 2
def baseEnd_942026 : Nat := 429966335139943602349073

theorem tailTrace_942026 : CollatzResearch.WordTrace tailWord_942026 prefixEnd_942026 429966335139943602349073 := by
  unfold tailWord_942026
  simp only [CollatzResearch.WordTrace]
  refine ⟨8589627721302040519295483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22905673923472108051454621 8589627721302040519295483)
  ·
    refine ⟨12884441581953060778943225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8589627721302040519295483 12884441581953060778943225)
    ·
      refine ⟨9663331186464795584207419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12884441581953060778943225 9663331186464795584207419)
      ·
        refine ⟨14494996779697193376311129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9663331186464795584207419 14494996779697193376311129)
        ·
          refine ⟨10871247584772895032233347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14494996779697193376311129 10871247584772895032233347)
          ·
            refine ⟨16306871377159342548350021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10871247584772895032233347 16306871377159342548350021)
            ·
              refine ⟨3057538383217376727815629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16306871377159342548350021 3057538383217376727815629)
              ·
                refine ⟨1146576893706516272930861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3057538383217376727815629 1146576893706516272930861)
                ·
                  refine ⟨429966335139943602349073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1146576893706516272930861 429966335139943602349073)
                  ·
                    rfl

theorem cell20_942026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 3, 3].length) (baseStart_942026 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_942026 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_942026 prefixEnd_942026 := by exact prefixLift 942026
  have htrace : WordTrace (prefixWord ++ tailWord_942026) baseStart_942026 baseEnd_942026 := by
    simpa [prefixWord, tailWord_942026, baseEnd_942026] using wordTrace_append hprefix tailTrace_942026
  have hstable : (prefixWord ++ tailWord_942026).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942026).length < 2 ^ (prefixWord ++ tailWord_942026).sum := by decide
  have hdescent : baseEnd_942026 < baseStart_942026 := by decide
  rcases family_descends (prefixWord ++ tailWord_942026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942064 : List Nat := [2, 1, 1, 1, 3, 2, 5, 2, 3]
def baseStart_942064 : Nat := 118140960795 + 942064 * 2 ^ 59
def prefixEnd_942064 : Nat := 4983230072969 + 3 ^ 40 * 942064 * 2
def baseEnd_942064 : Nat := 429983679375384359082251

theorem tailTrace_942064 : CollatzResearch.WordTrace tailWord_942064 prefixEnd_942064 429983679375384359082251 := by
  unfold tailWord_942064
  simp only [CollatzResearch.WordTrace]
  refine ⟨17179948429535247283532623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22906597906046996378043497 17179948429535247283532623)
  ·
    refine ⟨25769922644302870925298935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17179948429535247283532623 25769922644302870925298935)
    ·
      refine ⟨38654883966454306387948403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25769922644302870925298935 38654883966454306387948403)
      ·
        refine ⟨57982325949681459581922605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38654883966454306387948403 57982325949681459581922605)
        ·
          refine ⟨21743372231130547343220977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57982325949681459581922605 21743372231130547343220977)
          ·
            refine ⟨16307529173347910507415733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21743372231130547343220977 16307529173347910507415733)
            ·
              refine ⟨1528830860001366610070225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16307529173347910507415733 1528830860001366610070225)
              ·
                refine ⟨1146623145001024957552669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1528830860001366610070225 1146623145001024957552669)
                ·
                  refine ⟨429983679375384359082251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1146623145001024957552669 429983679375384359082251)
                  ·
                    rfl

theorem cell20_942064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 5, 2, 3].length) (baseStart_942064 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_942064 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_942064 prefixEnd_942064 := by exact prefixLift 942064
  have htrace : WordTrace (prefixWord ++ tailWord_942064) baseStart_942064 baseEnd_942064 := by
    simpa [prefixWord, tailWord_942064, baseEnd_942064] using wordTrace_append hprefix tailTrace_942064
  have hstable : (prefixWord ++ tailWord_942064).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942064).length < 2 ^ (prefixWord ++ tailWord_942064).sum := by decide
  have hdescent : baseEnd_942064 < baseStart_942064 := by decide
  rcases family_descends (prefixWord ++ tailWord_942064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942081 : List Nat := [1, 2, 4, 1, 2, 1, 5, 1, 3]
def baseStart_942081 : Nat := 118140960795 + 942081 * 2 ^ 59
def prefixEnd_942081 : Nat := 4983230072969 + 3 ^ 40 * 942081 * 2
def baseEnd_942081 : Nat := 429991438638607855515515

theorem tailTrace_942081 : CollatzResearch.WordTrace tailWord_942081 prefixEnd_942081 429991438638607855515515 := by
  unfold tailWord_942081
  simp only [CollatzResearch.WordTrace]
  refine ⟨34360516900008906470434097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22907011266672604313622731 34360516900008906470434097)
  ·
    refine ⟨25770387675006679852825573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34360516900008906470434097 25770387675006679852825573)
    ·
      refine ⟨4831947689063752472404795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25770387675006679852825573 4831947689063752472404795)
      ·
        refine ⟨7247921533595628708607193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4831947689063752472404795 7247921533595628708607193)
        ·
          refine ⟨5435941150196721531455395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7247921533595628708607193 5435941150196721531455395)
          ·
            refine ⟨8153911725295082297183093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5435941150196721531455395 8153911725295082297183093)
            ·
              refine ⟨764429224246413965360915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8153911725295082297183093 764429224246413965360915)
              ·
                refine ⟨1146643836369620948041373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 764429224246413965360915 1146643836369620948041373)
                ·
                  refine ⟨429991438638607855515515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1146643836369620948041373 429991438638607855515515)
                  ·
                    rfl

theorem cell20_942081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 5, 1, 3].length) (baseStart_942081 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_942081 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_942081 prefixEnd_942081 := by exact prefixLift 942081
  have htrace : WordTrace (prefixWord ++ tailWord_942081) baseStart_942081 baseEnd_942081 := by
    simpa [prefixWord, tailWord_942081, baseEnd_942081] using wordTrace_append hprefix tailTrace_942081
  have hstable : (prefixWord ++ tailWord_942081).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942081).length < 2 ^ (prefixWord ++ tailWord_942081).sum := by decide
  have hdescent : baseEnd_942081 < baseStart_942081 := by decide
  rcases family_descends (prefixWord ++ tailWord_942081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942122 : List Nat := [3, 1, 4, 1, 2, 2, 3, 2, 2]
def baseStart_942122 : Nat := 118140960795 + 942122 * 2 ^ 59
def prefixEnd_942122 : Nat := 4983230072969 + 3 ^ 40 * 942122 * 2
def baseEnd_942122 : Nat := 430010152155793935148681

theorem tailTrace_942122 : CollatzResearch.WordTrace tailWord_942122 prefixEnd_942122 430010152155793935148681 := by
  unfold tailWord_942122
  simp only [CollatzResearch.WordTrace]
  refine ⟨8590503073215092618169155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22908008195240246981784413 8590503073215092618169155)
  ·
    refine ⟨12885754609822638927253733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8590503073215092618169155 12885754609822638927253733)
    ·
      refine ⟨2416078989341744798860075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12885754609822638927253733 2416078989341744798860075)
      ·
        refine ⟨3624118484012617198290113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2416078989341744798860075 3624118484012617198290113)
        ·
          refine ⟨2718088863009462898717585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3624118484012617198290113 2718088863009462898717585)
          ·
            refine ⟨2038566647257097174038189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2718088863009462898717585 2038566647257097174038189)
            ·
              refine ⟨764462492721411440264321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2038566647257097174038189 764462492721411440264321)
              ·
                refine ⟨573346869541058580198241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 764462492721411440264321 573346869541058580198241)
                ·
                  refine ⟨430010152155793935148681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 573346869541058580198241 430010152155793935148681)
                  ·
                    rfl

theorem cell20_942122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 3, 2, 2].length) (baseStart_942122 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_942122 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_942122 prefixEnd_942122 := by exact prefixLift 942122
  have htrace : WordTrace (prefixWord ++ tailWord_942122) baseStart_942122 baseEnd_942122 := by
    simpa [prefixWord, tailWord_942122, baseEnd_942122] using wordTrace_append hprefix tailTrace_942122
  have hstable : (prefixWord ++ tailWord_942122).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942122).length < 2 ^ (prefixWord ++ tailWord_942122).sum := by decide
  have hdescent : baseEnd_942122 < baseStart_942122 := by decide
  rcases family_descends (prefixWord ++ tailWord_942122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942126 : List Nat := [4, 1, 3, 1, 1, 2, 3, 1, 4]
def baseStart_942126 : Nat := 118140960795 + 942126 * 2 ^ 59
def prefixEnd_942126 : Nat := 4983230072969 + 3 ^ 40 * 942126 * 2
def baseEnd_942126 : Nat := 430011977864787699015331

theorem tailTrace_942126 : CollatzResearch.WordTrace tailWord_942126 prefixEnd_942126 430011977864787699015331 := by
  unfold tailWord_942126
  simp only [CollatzResearch.WordTrace]
  refine ⟨4295269773105734894477779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22908105456563919437214821 4295269773105734894477779)
  ·
    refine ⟨6442904659658602341716669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4295269773105734894477779 6442904659658602341716669)
    ·
      refine ⟨2416089247371975878143751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6442904659658602341716669 2416089247371975878143751)
      ·
        refine ⟨3624133871057963817215627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2416089247371975878143751 3624133871057963817215627)
        ·
          refine ⟨5436200806586945725823441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3624133871057963817215627 5436200806586945725823441)
          ·
            refine ⟨4077150604940209294367581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5436200806586945725823441 4077150604940209294367581)
            ·
              refine ⟨1528931476852578485387843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4077150604940209294367581 1528931476852578485387843)
              ·
                refine ⟨2293397215278867728081765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1528931476852578485387843 2293397215278867728081765)
                ·
                  refine ⟨430011977864787699015331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2293397215278867728081765 430011977864787699015331)
                  ·
                    rfl

theorem cell20_942126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 3, 1, 4].length) (baseStart_942126 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_942126 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_942126 prefixEnd_942126 := by exact prefixLift 942126
  have htrace : WordTrace (prefixWord ++ tailWord_942126) baseStart_942126 baseEnd_942126 := by
    simpa [prefixWord, tailWord_942126, baseEnd_942126] using wordTrace_append hprefix tailTrace_942126
  have hstable : (prefixWord ++ tailWord_942126).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942126).length < 2 ^ (prefixWord ++ tailWord_942126).sum := by decide
  have hdescent : baseEnd_942126 < baseStart_942126 := by decide
  rcases family_descends (prefixWord ++ tailWord_942126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942132 : List Nat := [2, 5, 1, 2, 3, 1, 2, 1, 3]
def baseStart_942132 : Nat := 118140960795 + 942132 * 2 ^ 59
def prefixEnd_942132 : Nat := 4983230072969 + 3 ^ 40 * 942132 * 2
def baseEnd_942132 : Nat := 430014716428278344815307

theorem tailTrace_942132 : CollatzResearch.WordTrace tailWord_942132 prefixEnd_942132 430014716428278344815307 := by
  unfold tailWord_942132
  simp only [CollatzResearch.WordTrace]
  refine ⟨17181188511412071090270325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22908251348549428120360433 17181188511412071090270325)
  ·
    refine ⟨1610736422944881664712843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17181188511412071090270325 1610736422944881664712843)
    ·
      refine ⟨2416104634417322497069265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1610736422944881664712843 2416104634417322497069265)
      ·
        refine ⟨1812078475812991872801949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2416104634417322497069265 1812078475812991872801949)
        ·
          refine ⟨679529428429871952300731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1812078475812991872801949 679529428429871952300731)
          ·
            refine ⟨1019294142644807928451097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 679529428429871952300731 1019294142644807928451097)
            ·
              refine ⟨764470606983605946338323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1019294142644807928451097 764470606983605946338323)
              ·
                refine ⟨1146705910475408919507485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 764470606983605946338323 1146705910475408919507485)
                ·
                  refine ⟨430014716428278344815307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1146705910475408919507485 430014716428278344815307)
                  ·
                    rfl

theorem cell20_942132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 2, 1, 3].length) (baseStart_942132 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_942132 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_942132 prefixEnd_942132 := by exact prefixLift 942132
  have htrace : WordTrace (prefixWord ++ tailWord_942132) baseStart_942132 baseEnd_942132 := by
    simpa [prefixWord, tailWord_942132, baseEnd_942132] using wordTrace_append hprefix tailTrace_942132
  have hstable : (prefixWord ++ tailWord_942132).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942132).length < 2 ^ (prefixWord ++ tailWord_942132).sum := by decide
  have hdescent : baseEnd_942132 < baseStart_942132 := by decide
  rcases family_descends (prefixWord ++ tailWord_942132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942136 : List Nat := [2, 1, 2, 1, 6, 2, 2, 1, 3]
def baseStart_942136 : Nat := 118140960795 + 942136 * 2 ^ 59
def prefixEnd_942136 : Nat := 4983230072969 + 3 ^ 40 * 942136 * 2
def baseEnd_942136 : Nat := 430016542137272108681957

theorem tailTrace_942136 : CollatzResearch.WordTrace tailWord_942136 prefixEnd_942136 430016542137272108681957 := by
  unfold tailWord_942136
  simp only [CollatzResearch.WordTrace]
  refine ⟨17181261457404825431843131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22908348609873100575790841 17181261457404825431843131)
  ·
    refine ⟨25771892186107238147764697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17181261457404825431843131 25771892186107238147764697)
    ·
      refine ⟨19328919139580428610823523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25771892186107238147764697 19328919139580428610823523)
      ·
        refine ⟨28993378709370642916235285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19328919139580428610823523 28993378709370642916235285)
        ·
          refine ⟨1359064627001748886698529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 28993378709370642916235285 1359064627001748886698529)
          ·
            refine ⟨1019298470251311665023897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1359064627001748886698529 1019298470251311665023897)
            ·
              refine ⟨764473852688483748767923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1019298470251311665023897 764473852688483748767923)
              ·
                refine ⟨1146710779032725623151885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 764473852688483748767923 1146710779032725623151885)
                ·
                  refine ⟨430016542137272108681957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1146710779032725623151885 430016542137272108681957)
                  ·
                    rfl

theorem cell20_942136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 2, 1, 3].length) (baseStart_942136 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_942136 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_942136 prefixEnd_942136 := by exact prefixLift 942136
  have htrace : WordTrace (prefixWord ++ tailWord_942136) baseStart_942136 baseEnd_942136 := by
    simpa [prefixWord, tailWord_942136, baseEnd_942136] using wordTrace_append hprefix tailTrace_942136
  have hstable : (prefixWord ++ tailWord_942136).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942136).length < 2 ^ (prefixWord ++ tailWord_942136).sum := by decide
  have hdescent : baseEnd_942136 < baseStart_942136 := by decide
  rcases family_descends (prefixWord ++ tailWord_942136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942140 : List Nat := [2, 2, 2, 2, 2, 1, 3, 3, 3]
def baseStart_942140 : Nat := 118140960795 + 942140 * 2 ^ 59
def prefixEnd_942140 : Nat := 4983230072969 + 3 ^ 40 * 942140 * 2
def baseEnd_942140 : Nat := 430018367846265872548607

theorem tailTrace_942140 : CollatzResearch.WordTrace tailWord_942140 prefixEnd_942140 430018367846265872548607 := by
  unfold tailWord_942140
  simp only [CollatzResearch.WordTrace]
  refine ⟨17181334403397579773415937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22908445871196773031221249 17181334403397579773415937)
  ·
    refine ⟨12886000802548184830061953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17181334403397579773415937 12886000802548184830061953)
    ·
      refine ⟨9664500601911138622546465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12886000802548184830061953 9664500601911138622546465)
      ·
        refine ⟨7248375451433353966909849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9664500601911138622546465 7248375451433353966909849)
        ·
          refine ⟨5436281588575015475182387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7248375451433353966909849 5436281588575015475182387)
          ·
            refine ⟨8154422382862523212773581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5436281588575015475182387 8154422382862523212773581)
            ·
              refine ⟨3057908393573446204790093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8154422382862523212773581 3057908393573446204790093)
              ·
                refine ⟨1146715647590042326796285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3057908393573446204790093 1146715647590042326796285)
                ·
                  refine ⟨430018367846265872548607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1146715647590042326796285 430018367846265872548607)
                  ·
                    rfl

theorem cell20_942140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 3, 3].length) (baseStart_942140 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_942140 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_942140 prefixEnd_942140 := by exact prefixLift 942140
  have htrace : WordTrace (prefixWord ++ tailWord_942140) baseStart_942140 baseEnd_942140 := by
    simpa [prefixWord, tailWord_942140, baseEnd_942140] using wordTrace_append hprefix tailTrace_942140
  have hstable : (prefixWord ++ tailWord_942140).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942140).length < 2 ^ (prefixWord ++ tailWord_942140).sum := by decide
  have hdescent : baseEnd_942140 < baseStart_942140 := by decide
  rcases family_descends (prefixWord ++ tailWord_942140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942164 : List Nat := [2, 4, 1, 1, 1, 1, 1, 7, 2]
def baseStart_942164 : Nat := 118140960795 + 942164 * 2 ^ 59
def prefixEnd_942164 : Nat := 4983230072969 + 3 ^ 40 * 942164 * 2
def baseEnd_942164 : Nat := 430029322100228455748509

theorem tailTrace_942164 : CollatzResearch.WordTrace tailWord_942164 prefixEnd_942164 430029322100228455748509 := by
  unfold tailWord_942164
  simp only [CollatzResearch.WordTrace]
  refine ⟨17181772079354105822852773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22909029439138807763803697 17181772079354105822852773)
  ·
    refine ⟨3221582264878894841784895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17181772079354105822852773 3221582264878894841784895)
    ·
      refine ⟨4832373397318342262677343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3221582264878894841784895 4832373397318342262677343)
      ·
        refine ⟨7248560095977513394016015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4832373397318342262677343 7248560095977513394016015)
        ·
          refine ⟨10872840143966270091024023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7248560095977513394016015 10872840143966270091024023)
          ·
            refine ⟨16309260215949405136536035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10872840143966270091024023 16309260215949405136536035)
            ·
              refine ⟨24463890323924107704804053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16309260215949405136536035 24463890323924107704804053)
              ·
                refine ⟨573372429466971274331345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 24463890323924107704804053 573372429466971274331345)
                ·
                  refine ⟨430029322100228455748509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 573372429466971274331345 430029322100228455748509)
                  ·
                    rfl

theorem cell20_942164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 7, 2].length) (baseStart_942164 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_942164 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_942164 prefixEnd_942164 := by exact prefixLift 942164
  have htrace : WordTrace (prefixWord ++ tailWord_942164) baseStart_942164 baseEnd_942164 := by
    simpa [prefixWord, tailWord_942164, baseEnd_942164] using wordTrace_append hprefix tailTrace_942164
  have hstable : (prefixWord ++ tailWord_942164).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942164).length < 2 ^ (prefixWord ++ tailWord_942164).sum := by decide
  have hdescent : baseEnd_942164 < baseStart_942164 := by decide
  rcases family_descends (prefixWord ++ tailWord_942164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942181 : List Nat := [1, 3, 1, 3, 2, 2, 4, 2, 2]
def baseStart_942181 : Nat := 118140960795 + 942181 * 2 ^ 59
def prefixEnd_942181 : Nat := 4983230072969 + 3 ^ 40 * 942181 * 2
def baseEnd_942181 : Nat := 430037081363451952181773

theorem tailTrace_942181 : CollatzResearch.WordTrace tailWord_942181 prefixEnd_942181 430037081363451952181773 := by
  unfold tailWord_942181
  simp only [CollatzResearch.WordTrace]
  refine ⟨34364164199646623549074397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22909442799764415699382931 34364164199646623549074397)
  ·
    refine ⟨12886561574867483830902899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34364164199646623549074397 12886561574867483830902899)
    ·
      refine ⟨19329842362301225746354349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12886561574867483830902899 19329842362301225746354349)
      ·
        refine ⟨7248690885862959654882881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19329842362301225746354349 7248690885862959654882881)
        ·
          refine ⟨5436518164397219741162161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7248690885862959654882881 5436518164397219741162161)
          ·
            refine ⟨4077388623297914805871621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5436518164397219741162161 4077388623297914805871621)
            ·
              refine ⟨764510366868359026100929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4077388623297914805871621 764510366868359026100929)
              ·
                refine ⟨573382775151269269575697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 764510366868359026100929 573382775151269269575697)
                ·
                  refine ⟨430037081363451952181773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 573382775151269269575697 430037081363451952181773)
                  ·
                    rfl

theorem cell20_942181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 4, 2, 2].length) (baseStart_942181 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_942181 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_942181 prefixEnd_942181 := by exact prefixLift 942181
  have htrace : WordTrace (prefixWord ++ tailWord_942181) baseStart_942181 baseEnd_942181 := by
    simpa [prefixWord, tailWord_942181, baseEnd_942181] using wordTrace_append hprefix tailTrace_942181
  have hstable : (prefixWord ++ tailWord_942181).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942181).length < 2 ^ (prefixWord ++ tailWord_942181).sum := by decide
  have hdescent : baseEnd_942181 < baseStart_942181 := by decide
  rcases family_descends (prefixWord ++ tailWord_942181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942192 : List Nat := [2, 1, 1, 1, 5, 2, 3, 5]
def baseStart_942192 : Nat := 118140960795 + 942192 * 2 ^ 59
def prefixEnd_942192 : Nat := 4983230072969 + 3 ^ 40 * 942192 * 2
def baseEnd_942192 : Nat := 143347367354394934271687

theorem tailTrace_942192 : CollatzResearch.WordTrace tailWord_942192 prefixEnd_942192 143347367354394934271687 := by
  unfold tailWord_942192
  simp only [CollatzResearch.WordTrace]
  refine ⟨17182282701303386213862415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22909710268404514951816553 17182282701303386213862415)
  ·
    refine ⟨25773424051955079320793623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17182282701303386213862415 25773424051955079320793623)
    ·
      refine ⟨38660136077932618981190435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25773424051955079320793623 38660136077932618981190435)
      ·
        refine ⟨57990204116898928471785653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38660136077932618981190435 57990204116898928471785653)
        ·
          refine ⟨5436581635959274544229905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 57990204116898928471785653 5436581635959274544229905)
          ·
            refine ⟨4077436226969455908172429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5436581635959274544229905 4077436226969455908172429)
            ·
              refine ⟨1529038585113545965564661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4077436226969455908172429 1529038585113545965564661)
              ·
                refine ⟨143347367354394934271687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1529038585113545965564661 143347367354394934271687)
                ·
                  rfl

theorem cell20_942192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 3, 5].length) (baseStart_942192 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_942192 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_942192 prefixEnd_942192 := by exact prefixLift 942192
  have htrace : WordTrace (prefixWord ++ tailWord_942192) baseStart_942192 baseEnd_942192 := by
    simpa [prefixWord, tailWord_942192, baseEnd_942192] using wordTrace_append hprefix tailTrace_942192
  have hstable : (prefixWord ++ tailWord_942192).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942192).length < 2 ^ (prefixWord ++ tailWord_942192).sum := by decide
  have hdescent : baseEnd_942192 < baseStart_942192 := by decide
  rcases family_descends (prefixWord ++ tailWord_942192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942240 : List Nat := [2, 1, 1, 4, 2, 2, 2, 4, 2]
def baseStart_942240 : Nat := 118140960795 + 942240 * 2 ^ 59
def prefixEnd_942240 : Nat := 4983230072969 + 3 ^ 40 * 942240 * 2
def baseEnd_942240 : Nat := 430064010571109969214865

theorem tailTrace_942240 : CollatzResearch.WordTrace tailWord_942240 prefixEnd_942240 430064010571109969214865 := by
  unfold tailWord_942240
  simp only [CollatzResearch.WordTrace]
  refine ⟨17183158053216438312736087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22910877404288584416981449 17183158053216438312736087)
  ·
    refine ⟨25774737079824657469104131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17183158053216438312736087 25774737079824657469104131)
    ·
      refine ⟨38662105619736986203656197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25774737079824657469104131 38662105619736986203656197)
      ·
        refine ⟨7249144803700684913185537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38662105619736986203656197 7249144803700684913185537)
        ·
          refine ⟨5436858602775513684889153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7249144803700684913185537 5436858602775513684889153)
          ·
            refine ⟨4077643952081635263666865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5436858602775513684889153 4077643952081635263666865)
            ·
              refine ⟨3058232964061226447750149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4077643952081635263666865 3058232964061226447750149)
              ·
                refine ⟨573418680761479958953153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3058232964061226447750149 573418680761479958953153)
                ·
                  refine ⟨430064010571109969214865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 573418680761479958953153 430064010571109969214865)
                  ·
                    rfl

theorem cell20_942240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 4, 2].length) (baseStart_942240 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_942240 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_942240 prefixEnd_942240 := by exact prefixLift 942240
  have htrace : WordTrace (prefixWord ++ tailWord_942240) baseStart_942240 baseEnd_942240 := by
    simpa [prefixWord, tailWord_942240, baseEnd_942240] using wordTrace_append hprefix tailTrace_942240
  have hstable : (prefixWord ++ tailWord_942240).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942240).length < 2 ^ (prefixWord ++ tailWord_942240).sum := by decide
  have hdescent : baseEnd_942240 < baseStart_942240 := by decide
  rcases family_descends (prefixWord ++ tailWord_942240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942289 : List Nat := [1, 2, 2, 1, 2, 2, 10]
def baseStart_942289 : Nat := 118140960795 + 942289 * 2 ^ 59
def prefixEnd_942289 : Nat := 4983230072969 + 3 ^ 40 * 942289 * 2
def baseEnd_942289 : Nat := 47787375056253730731259

theorem tailTrace_942289 : CollatzResearch.WordTrace tailWord_942289 prefixEnd_942289 47787375056253730731259 := by
  unfold tailWord_942289
  simp only [CollatzResearch.WordTrace]
  refine ⟨34368103283255357994005921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22912068855503571996003947 34368103283255357994005921)
  ·
    refine ⟨25776077462441518495504441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34368103283255357994005921 25776077462441518495504441)
    ·
      refine ⟨19332058096831138871628331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25776077462441518495504441 19332058096831138871628331)
      ·
        refine ⟨28998087145246708307442497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19332058096831138871628331 28998087145246708307442497)
        ·
          refine ⟨21748565358935031230581873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28998087145246708307442497 21748565358935031230581873)
          ·
            refine ⟨16311424019201273422936405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21748565358935031230581873 16311424019201273422936405)
            ·
              refine ⟨47787375056253730731259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 16311424019201273422936405 47787375056253730731259)
              ·
                rfl

theorem cell20_942289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 10].length) (baseStart_942289 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_942289 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_942289 prefixEnd_942289 := by exact prefixLift 942289
  have htrace : WordTrace (prefixWord ++ tailWord_942289) baseStart_942289 baseEnd_942289 := by
    simpa [prefixWord, tailWord_942289, baseEnd_942289] using wordTrace_append hprefix tailTrace_942289
  have hstable : (prefixWord ++ tailWord_942289).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942289).length < 2 ^ (prefixWord ++ tailWord_942289).sum := by decide
  have hdescent : baseEnd_942289 < baseStart_942289 := by decide
  rcases family_descends (prefixWord ++ tailWord_942289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942309 : List Nat := [1, 3, 1, 4, 2, 1, 4, 1, 3]
def baseStart_942309 : Nat := 118140960795 + 942309 * 2 ^ 59
def prefixEnd_942309 : Nat := 4983230072969 + 3 ^ 40 * 942309 * 2
def baseEnd_942309 : Nat := 430095504051252395914583

theorem tailTrace_942309 : CollatzResearch.WordTrace tailWord_942309 prefixEnd_942309 430095504051252395914583 := by
  unfold tailWord_942309
  simp only [CollatzResearch.WordTrace]
  refine ⟨34368832743182901409733981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22912555162121934273155987 34368832743182901409733981)
  ·
    refine ⟨12888312278693588028650243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34368832743182901409733981 12888312278693588028650243)
    ·
      refine ⟨19332468418040382042975365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12888312278693588028650243 19332468418040382042975365)
      ·
        refine ⟨3624837828382571633057881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19332468418040382042975365 3624837828382571633057881)
        ·
          refine ⟨2718628371286928724793411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3624837828382571633057881 2718628371286928724793411)
          ·
            refine ⟨4077942556930393087190117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2718628371286928724793411 4077942556930393087190117)
            ·
              refine ⟨764614229424448703848147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4077942556930393087190117 764614229424448703848147)
              ·
                refine ⟨1146921344136673055772221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 764614229424448703848147 1146921344136673055772221)
                ·
                  refine ⟨430095504051252395914583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1146921344136673055772221 430095504051252395914583)
                  ·
                    rfl

theorem cell20_942309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 4, 1, 3].length) (baseStart_942309 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_942309 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_942309 prefixEnd_942309 := by exact prefixLift 942309
  have htrace : WordTrace (prefixWord ++ tailWord_942309) baseStart_942309 baseEnd_942309 := by
    simpa [prefixWord, tailWord_942309, baseEnd_942309] using wordTrace_append hprefix tailTrace_942309
  have hstable : (prefixWord ++ tailWord_942309).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942309).length < 2 ^ (prefixWord ++ tailWord_942309).sum := by decide
  have hdescent : baseEnd_942309 < baseStart_942309 := by decide
  rcases family_descends (prefixWord ++ tailWord_942309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942313 : List Nat := [1, 2, 1, 1, 1, 2, 2, 7, 3]
def baseStart_942313 : Nat := 118140960795 + 942313 * 2 ^ 59
def prefixEnd_942313 : Nat := 4983230072969 + 3 ^ 40 * 942313 * 2
def baseEnd_942313 : Nat := 430097329760246159781233

theorem tailTrace_942313 : CollatzResearch.WordTrace tailWord_942313 prefixEnd_942313 430097329760246159781233 := by
  unfold tailWord_942313
  simp only [CollatzResearch.WordTrace]
  refine ⟨34368978635168410092879593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22912652423445606728586395 34368978635168410092879593)
  ·
    refine ⟨25776733976376307569659695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34368978635168410092879593 25776733976376307569659695)
    ·
      refine ⟨38665100964564461354489543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25776733976376307569659695 38665100964564461354489543)
      ·
        refine ⟨57997651446846692031734315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38665100964564461354489543 57997651446846692031734315)
        ·
          refine ⟨86996477170270038047601473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57997651446846692031734315 86996477170270038047601473)
          ·
            refine ⟨65247357877702528535701105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86996477170270038047601473 65247357877702528535701105)
            ·
              refine ⟨48935518408276896401775829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65247357877702528535701105 48935518408276896401775829)
              ·
                refine ⟨1146926212693989759416621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 48935518408276896401775829 1146926212693989759416621)
                ·
                  refine ⟨430097329760246159781233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1146926212693989759416621 430097329760246159781233)
                  ·
                    rfl

theorem cell20_942313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 7, 3].length) (baseStart_942313 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_942313 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_942313 prefixEnd_942313 := by exact prefixLift 942313
  have htrace : WordTrace (prefixWord ++ tailWord_942313) baseStart_942313 baseEnd_942313 := by
    simpa [prefixWord, tailWord_942313, baseEnd_942313] using wordTrace_append hprefix tailTrace_942313
  have hstable : (prefixWord ++ tailWord_942313).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942313).length < 2 ^ (prefixWord ++ tailWord_942313).sum := by decide
  have hdescent : baseEnd_942313 < baseStart_942313 := by decide
  rcases family_descends (prefixWord ++ tailWord_942313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942320 : List Nat := [2, 1, 1, 1, 3, 1, 1, 6, 4]
def baseStart_942320 : Nat := 118140960795 + 942320 * 2 ^ 59
def prefixEnd_942320 : Nat := 4983230072969 + 3 ^ 40 * 942320 * 2
def baseEnd_942320 : Nat := 430100524750985246547871

theorem tailTrace_942320 : CollatzResearch.WordTrace tailWord_942320 prefixEnd_942320 430100524750985246547871 := by
  unfold tailWord_942320
  simp only [CollatzResearch.WordTrace]
  refine ⟨17184616973071525144192207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22912822630762033525589609 17184616973071525144192207)
  ·
    refine ⟨25776925459607287716288311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17184616973071525144192207 25776925459607287716288311)
    ·
      refine ⟨38665388189410931574432467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25776925459607287716288311 38665388189410931574432467)
      ·
        refine ⟨57998082284116397361648701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38665388189410931574432467 57998082284116397361648701)
        ·
          refine ⟨21749280856543649010618263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57998082284116397361648701 21749280856543649010618263)
          ·
            refine ⟨32623921284815473515927395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21749280856543649010618263 32623921284815473515927395)
            ·
              refine ⟨48935881927223210273891093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32623921284815473515927395 48935881927223210273891093)
              ·
                refine ⟨2293869465338587981588645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 48935881927223210273891093 2293869465338587981588645)
                ·
                  refine ⟨430100524750985246547871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2293869465338587981588645 430100524750985246547871)
                  ·
                    rfl

theorem cell20_942320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 6, 4].length) (baseStart_942320 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_942320 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_942320 prefixEnd_942320 := by exact prefixLift 942320
  have htrace : WordTrace (prefixWord ++ tailWord_942320) baseStart_942320 baseEnd_942320 := by
    simpa [prefixWord, tailWord_942320, baseEnd_942320] using wordTrace_append hprefix tailTrace_942320
  have hstable : (prefixWord ++ tailWord_942320).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942320).length < 2 ^ (prefixWord ++ tailWord_942320).sum := by decide
  have hdescent : baseEnd_942320 < baseStart_942320 := by decide
  rcases family_descends (prefixWord ++ tailWord_942320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942368 : List Nat := [2, 1, 1, 5, 2, 1, 2, 3, 3]
def baseStart_942368 : Nat := 118140960795 + 942368 * 2 ^ 59
def prefixEnd_942368 : Nat := 4983230072969 + 3 ^ 40 * 942368 * 2
def baseEnd_942368 : Nat := 430122433258910412947675

theorem tailTrace_942368 : CollatzResearch.WordTrace tailWord_942368 prefixEnd_942368 430122433258910412947675 := by
  unfold tailWord_942368
  simp only [CollatzResearch.WordTrace]
  refine ⟨17185492324984577243065879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22913989766646102990754505 17185492324984577243065879)
  ·
    refine ⟨25778238487476865864598819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17185492324984577243065879 25778238487476865864598819)
    ·
      refine ⟨38667357731215298796898229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25778238487476865864598819 38667357731215298796898229)
      ·
        refine ⟨3625064787301434262209209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38667357731215298796898229 3625064787301434262209209)
        ·
          refine ⟨2718798590476075696656907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3625064787301434262209209 2718798590476075696656907)
          ·
            refine ⟨4078197885714113544985361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2718798590476075696656907 4078197885714113544985361)
            ·
              refine ⟨3058648414285585158739021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4078197885714113544985361 3058648414285585158739021)
              ·
                refine ⟨1146993155357094434527133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3058648414285585158739021 1146993155357094434527133)
                ·
                  refine ⟨430122433258910412947675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1146993155357094434527133 430122433258910412947675)
                  ·
                    rfl

theorem cell20_942368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 3, 3].length) (baseStart_942368 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_942368 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_942368 prefixEnd_942368 := by exact prefixLift 942368
  have htrace : WordTrace (prefixWord ++ tailWord_942368) baseStart_942368 baseEnd_942368 := by
    simpa [prefixWord, tailWord_942368, baseEnd_942368] using wordTrace_append hprefix tailTrace_942368
  have hstable : (prefixWord ++ tailWord_942368).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942368).length < 2 ^ (prefixWord ++ tailWord_942368).sum := by decide
  have hdescent : baseEnd_942368 < baseStart_942368 := by decide
  rcases family_descends (prefixWord ++ tailWord_942368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942378 : List Nat := [3, 1, 4, 2, 2, 1, 3, 4]
def baseStart_942378 : Nat := 118140960795 + 942378 * 2 ^ 59
def prefixEnd_942378 : Nat := 4983230072969 + 3 ^ 40 * 942378 * 2
def baseEnd_942378 : Nat := 143375665843798274204767

theorem tailTrace_942378 : CollatzResearch.WordTrace tailWord_942378 prefixEnd_942378 143375665843798274204767 := by
  unfold tailWord_942378
  simp only [CollatzResearch.WordTrace]
  refine ⟨8592837344983231548498947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22914232919955284129330525 8592837344983231548498947)
  ·
    refine ⟨12889256017474847322748421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8592837344983231548498947 12889256017474847322748421)
    ·
      refine ⟨2416735503276533873015329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12889256017474847322748421 2416735503276533873015329)
      ·
        refine ⟨1812551627457400404761497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2416735503276533873015329 1812551627457400404761497)
        ·
          refine ⟨1359413720593050303571123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1812551627457400404761497 1359413720593050303571123)
          ·
            refine ⟨2039120580889575455356685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1359413720593050303571123 2039120580889575455356685)
            ·
              refine ⟨764670217833590795758757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2039120580889575455356685 764670217833590795758757)
              ·
                refine ⟨143375665843798274204767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 764670217833590795758757 143375665843798274204767)
                ·
                  rfl

theorem cell20_942378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 3, 4].length) (baseStart_942378 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_942378 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_942378 prefixEnd_942378 := by exact prefixLift 942378
  have htrace : WordTrace (prefixWord ++ tailWord_942378) baseStart_942378 baseEnd_942378 := by
    simpa [prefixWord, tailWord_942378, baseEnd_942378] using wordTrace_append hprefix tailTrace_942378
  have hstable : (prefixWord ++ tailWord_942378).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942378).length < 2 ^ (prefixWord ++ tailWord_942378).sum := by decide
  have hdescent : baseEnd_942378 < baseStart_942378 := by decide
  rcases family_descends (prefixWord ++ tailWord_942378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942389 : List Nat := [1, 3, 3, 1, 2, 1, 2, 2, 5]
def baseStart_942389 : Nat := 118140960795 + 942389 * 2 ^ 59
def prefixEnd_942389 : Nat := 4983230072969 + 3 ^ 40 * 942389 * 2
def baseEnd_942389 : Nat := 430132018231127673247589

theorem tailTrace_942389 : CollatzResearch.WordTrace tailWord_942389 prefixEnd_942389 430132018231127673247589 := by
  unfold tailWord_942389
  simp only [CollatzResearch.WordTrace]
  refine ⟨34371750582893075072646221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22914500388595383381764147 34371750582893075072646221)
  ·
    refine ⟨12889406468584903152242333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34371750582893075072646221 12889406468584903152242333)
    ·
      refine ⟨4833527425719338682090875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12889406468584903152242333 4833527425719338682090875)
      ·
        refine ⟨7250291138579008023136313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4833527425719338682090875 7250291138579008023136313)
        ·
          refine ⟨5437718353934256017352235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7250291138579008023136313 5437718353934256017352235)
          ·
            refine ⟨8156577530901384026028353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5437718353934256017352235 8156577530901384026028353)
            ·
              refine ⟨6117433148176038019521265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8156577530901384026028353 6117433148176038019521265)
              ·
                refine ⟨4588074861132028514640949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6117433148176038019521265 4588074861132028514640949)
                ·
                  refine ⟨430132018231127673247589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4588074861132028514640949 430132018231127673247589)
                  ·
                    rfl

theorem cell20_942389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 2, 5].length) (baseStart_942389 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_942389 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_942389 prefixEnd_942389 := by exact prefixLift 942389
  have htrace : WordTrace (prefixWord ++ tailWord_942389) baseStart_942389 baseEnd_942389 := by
    simpa [prefixWord, tailWord_942389, baseEnd_942389] using wordTrace_append hprefix tailTrace_942389
  have hstable : (prefixWord ++ tailWord_942389).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942389).length < 2 ^ (prefixWord ++ tailWord_942389).sum := by decide
  have hdescent : baseEnd_942389 < baseStart_942389 := by decide
  rcases family_descends (prefixWord ++ tailWord_942389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942396 : List Nat := [2, 2, 2, 2, 1, 2, 1, 2, 6]
def baseStart_942396 : Nat := 118140960795 + 942396 * 2 ^ 59
def prefixEnd_942396 : Nat := 4983230072969 + 3 ^ 40 * 942396 * 2
def baseEnd_942396 : Nat := 430135213221866760014227

theorem tailTrace_942396 : CollatzResearch.WordTrace tailWord_942396 prefixEnd_942396 430135213221866760014227 := by
  unfold tailWord_942396
  simp only [CollatzResearch.WordTrace]
  refine ⟨17186002946933857634075521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22914670595911810178767361 17186002946933857634075521)
  ·
    refine ⟨12889502210200393225556641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17186002946933857634075521 12889502210200393225556641)
    ·
      refine ⟨9667126657650294919167481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12889502210200393225556641 9667126657650294919167481)
      ·
        refine ⟨7250344993237721189375611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9667126657650294919167481 7250344993237721189375611)
        ·
          refine ⟨10875517489856581784063417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7250344993237721189375611 10875517489856581784063417)
          ·
            refine ⟨8156638117392436338047563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10875517489856581784063417 8156638117392436338047563)
            ·
              refine ⟨12234957176088654507071345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8156638117392436338047563 12234957176088654507071345)
              ·
                refine ⟨9176217882066490880303509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12234957176088654507071345 9176217882066490880303509)
                ·
                  refine ⟨430135213221866760014227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9176217882066490880303509 430135213221866760014227)
                  ·
                    rfl

theorem cell20_942396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 2, 6].length) (baseStart_942396 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_942396 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_942396 prefixEnd_942396 := by exact prefixLift 942396
  have htrace : WordTrace (prefixWord ++ tailWord_942396) baseStart_942396 baseEnd_942396 := by
    simpa [prefixWord, tailWord_942396, baseEnd_942396] using wordTrace_append hprefix tailTrace_942396
  have hstable : (prefixWord ++ tailWord_942396).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942396).length < 2 ^ (prefixWord ++ tailWord_942396).sum := by decide
  have hdescent : baseEnd_942396 < baseStart_942396 := by decide
  rcases family_descends (prefixWord ++ tailWord_942396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942437 : List Nat := [1, 3, 1, 3, 1, 5, 2, 4]
def baseStart_942437 : Nat := 118140960795 + 942437 * 2 ^ 59
def prefixEnd_942437 : Nat := 4983230072969 + 3 ^ 40 * 942437 * 2
def baseEnd_942437 : Nat := 143384642246350946549131

theorem tailTrace_942437 : CollatzResearch.WordTrace tailWord_942437 prefixEnd_942437 143384642246350946549131 := by
  unfold tailWord_942437
  simp only [CollatzResearch.WordTrace]
  refine ⟨34373501286719179270393565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22915667524479452846929043 34373501286719179270393565)
  ·
    refine ⟨12890062982519692226397587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34373501286719179270393565 12890062982519692226397587)
    ·
      refine ⟨19335094473779538339596381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12890062982519692226397587 19335094473779538339596381)
      ·
        refine ⟨7250660427667326877348643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19335094473779538339596381 7250660427667326877348643)
        ·
          refine ⟨10875990641500990316022965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7250660427667326877348643 10875990641500990316022965)
          ·
            refine ⟨1019624122640717842127153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10875990641500990316022965 1019624122640717842127153)
            ·
              refine ⟨764718091980538381595365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1019624122640717842127153 764718091980538381595365)
              ·
                refine ⟨143384642246350946549131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 764718091980538381595365 143384642246350946549131)
                ·
                  rfl

theorem cell20_942437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 2, 4].length) (baseStart_942437 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_942437 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_942437 prefixEnd_942437 := by exact prefixLift 942437
  have htrace : WordTrace (prefixWord ++ tailWord_942437) baseStart_942437 baseEnd_942437 := by
    simpa [prefixWord, tailWord_942437, baseEnd_942437] using wordTrace_append hprefix tailTrace_942437
  have hstable : (prefixWord ++ tailWord_942437).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942437).length < 2 ^ (prefixWord ++ tailWord_942437).sum := by decide
  have hdescent : baseEnd_942437 < baseStart_942437 := by decide
  rcases family_descends (prefixWord ++ tailWord_942437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942441 : List Nat := [1, 2, 1, 1, 1, 3, 5, 6]
def baseStart_942441 : Nat := 118140960795 + 942441 * 2 ^ 59
def prefixEnd_942441 : Nat := 4983230072969 + 3 ^ 40 * 942441 * 2
def baseEnd_942441 : Nat := 143385250816015534504681

theorem tailTrace_942441 : CollatzResearch.WordTrace tailWord_942441 prefixEnd_942441 143385250816015534504681 := by
  unfold tailWord_942441
  simp only [CollatzResearch.WordTrace]
  refine ⟨34373647178704687953539177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22915764785803125302359451 34373647178704687953539177)
  ·
    refine ⟨25780235384028515965154383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34373647178704687953539177 25780235384028515965154383)
    ·
      refine ⟨38670353076042773947731575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25780235384028515965154383 38670353076042773947731575)
      ·
        refine ⟨58005529614064160921597363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38670353076042773947731575 58005529614064160921597363)
        ·
          refine ⟨87008294421096241382396045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58005529614064160921597363 87008294421096241382396045)
          ·
            refine ⟨32628110407911090518398517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87008294421096241382396045 32628110407911090518398517)
            ·
              refine ⟨3058885350741664736099861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32628110407911090518398517 3058885350741664736099861)
              ·
                refine ⟨143385250816015534504681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3058885350741664736099861 143385250816015534504681)
                ·
                  rfl

theorem cell20_942441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 6].length) (baseStart_942441 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_942441 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_942441 prefixEnd_942441 := by exact prefixLift 942441
  have htrace : WordTrace (prefixWord ++ tailWord_942441) baseStart_942441 baseEnd_942441 := by
    simpa [prefixWord, tailWord_942441, baseEnd_942441] using wordTrace_append hprefix tailTrace_942441
  have hstable : (prefixWord ++ tailWord_942441).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942441).length < 2 ^ (prefixWord ++ tailWord_942441).sum := by decide
  have hdescent : baseEnd_942441 < baseStart_942441 := by decide
  rcases family_descends (prefixWord ++ tailWord_942441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942454 : List Nat := [5, 1, 1, 4, 1, 2, 6]
def baseStart_942454 : Nat := 118140960795 + 942454 * 2 ^ 59
def prefixEnd_942454 : Nat := 4983230072969 + 3 ^ 40 * 942454 * 2
def baseEnd_942454 : Nat := 47795742889141815120073

theorem tailTrace_942454 : CollatzResearch.WordTrace tailWord_942454 prefixEnd_942454 47795742889141815120073 := by
  unfold tailWord_942454
  simp only [CollatzResearch.WordTrace]
  refine ⟨2148382582978599448360151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22916080885105060782508277 2148382582978599448360151)
  ·
    refine ⟨3222573874467899172540227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2148382582978599448360151 3222573874467899172540227)
    ·
      refine ⟨4833860811701848758810341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3222573874467899172540227 4833860811701848758810341)
      ·
        refine ⟨906348902194096642276939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4833860811701848758810341 906348902194096642276939)
        ·
          refine ⟨1359523353291144963415409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 906348902194096642276939 1359523353291144963415409)
          ·
            refine ⟨1019642514968358722561557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1359523353291144963415409 1019642514968358722561557)
            ·
              refine ⟨47795742889141815120073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1019642514968358722561557 47795742889141815120073)
              ·
                rfl

theorem cell20_942454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 6].length) (baseStart_942454 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_942454 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_942454 prefixEnd_942454 := by exact prefixLift 942454
  have htrace : WordTrace (prefixWord ++ tailWord_942454) baseStart_942454 baseEnd_942454 := by
    simpa [prefixWord, tailWord_942454, baseEnd_942454] using wordTrace_append hprefix tailTrace_942454
  have hstable : (prefixWord ++ tailWord_942454).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942454).length < 2 ^ (prefixWord ++ tailWord_942454).sum := by decide
  have hdescent : baseEnd_942454 < baseStart_942454 := by decide
  rcases family_descends (prefixWord ++ tailWord_942454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942478 : List Nat := [4, 1, 1, 4, 1, 3, 2, 1, 3]
def baseStart_942478 : Nat := 118140960795 + 942478 * 2 ^ 59
def prefixEnd_942478 : Nat := 4983230072969 + 3 ^ 40 * 942478 * 2
def baseEnd_942478 : Nat := 430172640256238919280559

theorem tailTrace_942478 : CollatzResearch.WordTrace tailWord_942478 prefixEnd_942478 430172640256238919280559 := by
  unfold tailWord_942478
  simp only [CollatzResearch.WordTrace]
  refine ⟨4296874584946330409079511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22916664453047095515090725 4296874584946330409079511)
  ·
    refine ⟨6445311877419495613619267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4296874584946330409079511 6445311877419495613619267)
    ·
      refine ⟨9667967816129243420428901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6445311877419495613619267 9667967816129243420428901)
      ·
        refine ⟨1812743965524233141330419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9667967816129243420428901 1812743965524233141330419)
        ·
          refine ⟨2719115948286349711995629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1812743965524233141330419 2719115948286349711995629)
          ·
            refine ⟨1019668480607381141998361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2719115948286349711995629 1019668480607381141998361)
            ·
              refine ⟨764751360455535856498771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1019668480607381141998361 764751360455535856498771)
              ·
                refine ⟨1147127040683303784748157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 764751360455535856498771 1147127040683303784748157)
                ·
                  refine ⟨430172640256238919280559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1147127040683303784748157 430172640256238919280559)
                  ·
                    rfl

theorem cell20_942478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 2, 1, 3].length) (baseStart_942478 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_942478 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_942478 prefixEnd_942478 := by exact prefixLift 942478
  have htrace : WordTrace (prefixWord ++ tailWord_942478) baseStart_942478 baseEnd_942478 := by
    simpa [prefixWord, tailWord_942478, baseEnd_942478] using wordTrace_append hprefix tailTrace_942478
  have hstable : (prefixWord ++ tailWord_942478).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942478).length < 2 ^ (prefixWord ++ tailWord_942478).sum := by decide
  have hdescent : baseEnd_942478 < baseStart_942478 := by decide
  rcases family_descends (prefixWord ++ tailWord_942478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942517 : List Nat := [1, 3, 3, 2, 11]
def baseStart_942517 : Nat := 118140960795 + 942517 * 2 ^ 59
def prefixEnd_942517 : Nat := 4983230072969 + 3 ^ 40 * 942517 * 2
def baseEnd_942517 : Nat := 5310993097764544654079

theorem tailTrace_942517 : CollatzResearch.WordTrace tailWord_942517 prefixEnd_942517 5310993097764544654079 := by
  unfold tailWord_942517
  simp only [CollatzResearch.WordTrace]
  refine ⟨34376419126429352933305805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22917612750952901955537203 34376419126429352933305805)
  ·
    refine ⟨12891157172411007349989677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34376419126429352933305805 12891157172411007349989677)
    ·
      refine ⟨4834183939654127756246129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12891157172411007349989677 4834183939654127756246129)
      ·
        refine ⟨3625637954740595817184597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4834183939654127756246129 3625637954740595817184597)
        ·
          refine ⟨5310993097764544654079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 3625637954740595817184597 5310993097764544654079)
          ·
            rfl

theorem cell20_942517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 11].length) (baseStart_942517 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_942517 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_942517 prefixEnd_942517 := by exact prefixLift 942517
  have htrace : WordTrace (prefixWord ++ tailWord_942517) baseStart_942517 baseEnd_942517 := by
    simpa [prefixWord, tailWord_942517, baseEnd_942517] using wordTrace_append hprefix tailTrace_942517
  have hstable : (prefixWord ++ tailWord_942517).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942517).length < 2 ^ (prefixWord ++ tailWord_942517).sum := by decide
  have hdescent : baseEnd_942517 < baseStart_942517 := by decide
  rcases family_descends (prefixWord ++ tailWord_942517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942582 : List Nat := [5, 1, 1, 1, 2, 1, 1, 6, 2]
def baseStart_942582 : Nat := 118140960795 + 942582 * 2 ^ 59
def prefixEnd_942582 : Nat := 4983230072969 + 3 ^ 40 * 942582 * 2
def baseEnd_942582 : Nat := 430220108690076779813467

theorem tailTrace_942582 : CollatzResearch.WordTrace tailWord_942582 prefixEnd_942582 430220108690076779813467 := by
  unfold tailWord_942582
  simp only [CollatzResearch.WordTrace]
  refine ⟨2148674366949616814651375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22919193247462579356281333 2148674366949616814651375)
  ·
    refine ⟨3223011550424425221977063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2148674366949616814651375 3223011550424425221977063)
    ·
      refine ⟨4834517325636637832965595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3223011550424425221977063 4834517325636637832965595)
      ·
        refine ⟨7251775988454956749448393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4834517325636637832965595 7251775988454956749448393)
        ·
          refine ⟨5438831991341217562086295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7251775988454956749448393 5438831991341217562086295)
          ·
            refine ⟨8158247987011826343129443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5438831991341217562086295 8158247987011826343129443)
            ·
              refine ⟨12237371980517739514694165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8158247987011826343129443 12237371980517739514694165)
              ·
                refine ⟨573626811586769039751289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12237371980517739514694165 573626811586769039751289)
                ·
                  refine ⟨430220108690076779813467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 573626811586769039751289 430220108690076779813467)
                  ·
                    rfl

theorem cell20_942582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 6, 2].length) (baseStart_942582 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_942582 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_942582 prefixEnd_942582 := by exact prefixLift 942582
  have htrace : WordTrace (prefixWord ++ tailWord_942582) baseStart_942582 baseEnd_942582 := by
    simpa [prefixWord, tailWord_942582, baseEnd_942582] using wordTrace_append hprefix tailTrace_942582
  have hstable : (prefixWord ++ tailWord_942582).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942582).length < 2 ^ (prefixWord ++ tailWord_942582).sum := by decide
  have hdescent : baseEnd_942582 < baseStart_942582 := by decide
  rcases family_descends (prefixWord ++ tailWord_942582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942620 : List Nat := [2, 2, 3, 1, 2, 2, 3, 3, 2]
def baseStart_942620 : Nat := 118140960795 + 942620 * 2 ^ 59
def prefixEnd_942620 : Nat := 4983230072969 + 3 ^ 40 * 942620 * 2
def baseEnd_942620 : Nat := 430237452925517536546645

theorem tailTrace_942620 : CollatzResearch.WordTrace tailWord_942620 prefixEnd_942620 430237452925517536546645 := by
  unfold tailWord_942620
  simp only [CollatzResearch.WordTrace]
  refine ⟨17190087922528100762152657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22920117230037467682870209 17190087922528100762152657)
  ·
    refine ⟨12892565941896075571614493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17190087922528100762152657 12892565941896075571614493)
    ·
      refine ⟨4834712228211028339355435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12892565941896075571614493 4834712228211028339355435)
      ·
        refine ⟨7252068342316542509033153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4834712228211028339355435 7252068342316542509033153)
        ·
          refine ⟨5439051256737406881774865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7252068342316542509033153 5439051256737406881774865)
          ·
            refine ⟨4079288442553055161331149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5439051256737406881774865 4079288442553055161331149)
            ·
              refine ⟨1529733165957395685499181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4079288442553055161331149 1529733165957395685499181)
              ·
                refine ⟨573649937234023382062193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1529733165957395685499181 573649937234023382062193)
                ·
                  refine ⟨430237452925517536546645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 573649937234023382062193 430237452925517536546645)
                  ·
                    rfl

theorem cell20_942620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 3, 3, 2].length) (baseStart_942620 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_942620 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_942620 prefixEnd_942620 := by exact prefixLift 942620
  have htrace : WordTrace (prefixWord ++ tailWord_942620) baseStart_942620 baseEnd_942620 := by
    simpa [prefixWord, tailWord_942620, baseEnd_942620] using wordTrace_append hprefix tailTrace_942620
  have hstable : (prefixWord ++ tailWord_942620).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942620).length < 2 ^ (prefixWord ++ tailWord_942620).sum := by decide
  have hdescent : baseEnd_942620 < baseStart_942620 := by decide
  rcases family_descends (prefixWord ++ tailWord_942620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942641 : List Nat := [1, 2, 2, 3, 1, 1, 2, 6, 2]
def baseStart_942641 : Nat := 118140960795 + 942641 * 2 ^ 59
def prefixEnd_942641 : Nat := 4983230072969 + 3 ^ 40 * 942641 * 2
def baseEnd_942641 : Nat := 430247037897734796846559

theorem tailTrace_942641 : CollatzResearch.WordTrace tailWord_942641 prefixEnd_942641 430247037897734796846559 := by
  unfold tailWord_942641
  simp only [CollatzResearch.WordTrace]
  refine ⟨34380941777980122110819777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22920627851986748073879851 34380941777980122110819777)
  ·
    refine ⟨25785706333485091583114833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34380941777980122110819777 25785706333485091583114833)
    ·
      refine ⟨19339279750113818687336125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25785706333485091583114833 19339279750113818687336125)
      ·
        refine ⟨7252229906292682007751047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19339279750113818687336125 7252229906292682007751047)
        ·
          refine ⟨10878344859439023011626571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7252229906292682007751047 10878344859439023011626571)
          ·
            refine ⟨16317517289158534517439857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10878344859439023011626571 16317517289158534517439857)
            ·
              refine ⟨12238137966868900888079893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16317517289158534517439857 12238137966868900888079893)
              ·
                refine ⟨573662717196979729128745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12238137966868900888079893 573662717196979729128745)
                ·
                  refine ⟨430247037897734796846559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 573662717196979729128745 430247037897734796846559)
                  ·
                    rfl

theorem cell20_942641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 6, 2].length) (baseStart_942641 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_942641 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_942641 prefixEnd_942641 := by exact prefixLift 942641
  have htrace : WordTrace (prefixWord ++ tailWord_942641) baseStart_942641 baseEnd_942641 := by
    simpa [prefixWord, tailWord_942641, baseEnd_942641] using wordTrace_append hprefix tailTrace_942641
  have hstable : (prefixWord ++ tailWord_942641).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942641).length < 2 ^ (prefixWord ++ tailWord_942641).sum := by decide
  have hdescent : baseEnd_942641 < baseStart_942641 := by decide
  rcases family_descends (prefixWord ++ tailWord_942641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942644 : List Nat := [2, 5, 1, 3, 1, 1, 2, 5]
def baseStart_942644 : Nat := 118140960795 + 942644 * 2 ^ 59
def prefixEnd_942644 : Nat := 4983230072969 + 3 ^ 40 * 942644 * 2
def baseEnd_942644 : Nat := 143416135726493373248849

theorem tailTrace_942644 : CollatzResearch.WordTrace tailWord_942644 prefixEnd_942644 143416135726493373248849 := by
  unfold tailWord_942644
  simp only [CollatzResearch.WordTrace]
  refine ⟨17190525598484626811589493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22920700797979502415452657 17190525598484626811589493)
  ·
    refine ⟨1611611774857933763586515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17190525598484626811589493 1611611774857933763586515)
    ·
      refine ⟨2417417662286900645379773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1611611774857933763586515 2417417662286900645379773)
      ·
        refine ⟨906531623357587742017415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2417417662286900645379773 906531623357587742017415)
        ·
          refine ⟨1359797435036381613026123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 906531623357587742017415 1359797435036381613026123)
          ·
            refine ⟨2039696152554572419539185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1359797435036381613026123 2039696152554572419539185)
            ·
              refine ⟨1529772114415929314654389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2039696152554572419539185 1529772114415929314654389)
              ·
                refine ⟨143416135726493373248849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1529772114415929314654389 143416135726493373248849)
                ·
                  rfl

theorem cell20_942644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 2, 5].length) (baseStart_942644 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_942644 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_942644 prefixEnd_942644 := by exact prefixLift 942644
  have htrace : WordTrace (prefixWord ++ tailWord_942644) baseStart_942644 baseEnd_942644 := by
    simpa [prefixWord, tailWord_942644, baseEnd_942644] using wordTrace_append hprefix tailTrace_942644
  have hstable : (prefixWord ++ tailWord_942644).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942644).length < 2 ^ (prefixWord ++ tailWord_942644).sum := by decide
  have hdescent : baseEnd_942644 < baseStart_942644 := by decide
  rcases family_descends (prefixWord ++ tailWord_942644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942655 : List Nat := [1, 1, 2, 2, 3, 2, 3, 3, 3]
def baseStart_942655 : Nat := 118140960795 + 942655 * 2 ^ 59
def prefixEnd_942655 : Nat := 4983230072969 + 3 ^ 40 * 942655 * 2
def baseEnd_942655 : Nat := 430253427879212970379835

theorem tailTrace_942655 : CollatzResearch.WordTrace tailWord_942655 prefixEnd_942655 430253427879212970379835 := by
  unfold tailWord_942655
  simp only [CollatzResearch.WordTrace]
  refine ⟨34381452399929402501829419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22920968266619601667886279 34381452399929402501829419)
  ·
    refine ⟨51572178599894103752744129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34381452399929402501829419 51572178599894103752744129)
    ·
      refine ⟨38679133949920577814558097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51572178599894103752744129 38679133949920577814558097)
      ·
        refine ⟨29009350462440433360918573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38679133949920577814558097 29009350462440433360918573)
        ·
          refine ⟨10878506423415162510344465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29009350462440433360918573 10878506423415162510344465)
          ·
            refine ⟨8158879817561371882758349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10878506423415162510344465 8158879817561371882758349)
            ·
              refine ⟨3059579931585514456034381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8158879817561371882758349 3059579931585514456034381)
              ·
                refine ⟨1147342474344567921012893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3059579931585514456034381 1147342474344567921012893)
                ·
                  refine ⟨430253427879212970379835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1147342474344567921012893 430253427879212970379835)
                  ·
                    rfl

theorem cell20_942655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 3, 3].length) (baseStart_942655 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_942655 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_942655 prefixEnd_942655 := by exact prefixLift 942655
  have htrace : WordTrace (prefixWord ++ tailWord_942655) baseStart_942655 baseEnd_942655 := by
    simpa [prefixWord, tailWord_942655, baseEnd_942655] using wordTrace_append hprefix tailTrace_942655
  have hstable : (prefixWord ++ tailWord_942655).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942655).length < 2 ^ (prefixWord ++ tailWord_942655).sum := by decide
  have hdescent : baseEnd_942655 < baseStart_942655 := by decide
  rcases family_descends (prefixWord ++ tailWord_942655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942679 : List Nat := [1, 1, 3, 2, 2, 2, 2, 5, 2]
def baseStart_942679 : Nat := 118140960795 + 942679 * 2 ^ 59
def prefixEnd_942679 : Nat := 4983230072969 + 3 ^ 40 * 942679 * 2
def baseEnd_942679 : Nat := 430264382133175553579737

theorem tailTrace_942679 : CollatzResearch.WordTrace tailWord_942679 prefixEnd_942679 430264382133175553579737 := by
  unfold tailWord_942679
  simp only [CollatzResearch.WordTrace]
  refine ⟨34382327751842454600703091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22921551834561636400468727 34382327751842454600703091)
  ·
    refine ⟨51573491627763681901054637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34382327751842454600703091 51573491627763681901054637)
    ·
      refine ⟨19340059360411380712895489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51573491627763681901054637 19340059360411380712895489)
      ·
        refine ⟨14505044520308535534671617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19340059360411380712895489 14505044520308535534671617)
        ·
          refine ⟨10878783390231401651003713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14505044520308535534671617 10878783390231401651003713)
          ·
            refine ⟨8159087542673551238252785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10878783390231401651003713 8159087542673551238252785)
            ·
              refine ⟨6119315657005163428689589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8159087542673551238252785 6119315657005163428689589)
              ·
                refine ⟨573685842844234071439649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6119315657005163428689589 573685842844234071439649)
                ·
                  refine ⟨430264382133175553579737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 573685842844234071439649 430264382133175553579737)
                  ·
                    rfl

theorem cell20_942679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 5, 2].length) (baseStart_942679 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_942679 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_942679 prefixEnd_942679 := by exact prefixLift 942679
  have htrace : WordTrace (prefixWord ++ tailWord_942679) baseStart_942679 baseEnd_942679 := by
    simpa [prefixWord, tailWord_942679, baseEnd_942679] using wordTrace_append hprefix tailTrace_942679
  have hstable : (prefixWord ++ tailWord_942679).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942679).length < 2 ^ (prefixWord ++ tailWord_942679).sum := by decide
  have hdescent : baseEnd_942679 < baseStart_942679 := by decide
  rcases family_descends (prefixWord ++ tailWord_942679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942717 : List Nat := [1, 4, 1, 1, 5, 1, 1, 2, 4]
def baseStart_942717 : Nat := 118140960795 + 942717 * 2 ^ 59
def prefixEnd_942717 : Nat := 4983230072969 + 3 ^ 40 * 942717 * 2
def baseEnd_942717 : Nat := 430281726368616310312915

theorem tailTrace_942717 : CollatzResearch.WordTrace tailWord_942717 prefixEnd_942717 430281726368616310312915 := by
  unfold tailWord_942717
  simp only [CollatzResearch.WordTrace]
  refine ⟨34383713725704787090586405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22922475817136524727057603 34383713725704787090586405)
  ·
    refine ⟨6446946323569647579484951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34383713725704787090586405 6446946323569647579484951)
    ·
      refine ⟨9670419485354471369227427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6446946323569647579484951 9670419485354471369227427)
      ·
        refine ⟨14505629228031707053841141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9670419485354471369227427 14505629228031707053841141)
        ·
          refine ⟨1359902740127972536297607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14505629228031707053841141 1359902740127972536297607)
          ·
            refine ⟨2039854110191958804446411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1359902740127972536297607 2039854110191958804446411)
            ·
              refine ⟨3059781165287938206669617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2039854110191958804446411 3059781165287938206669617)
              ·
                refine ⟨2294835873965953655002213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3059781165287938206669617 2294835873965953655002213)
                ·
                  refine ⟨430281726368616310312915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2294835873965953655002213 430281726368616310312915)
                  ·
                    rfl

theorem cell20_942717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 2, 4].length) (baseStart_942717 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_942717 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_942717 prefixEnd_942717 := by exact prefixLift 942717
  have htrace : WordTrace (prefixWord ++ tailWord_942717) baseStart_942717 baseEnd_942717 := by
    simpa [prefixWord, tailWord_942717, baseEnd_942717] using wordTrace_append hprefix tailTrace_942717
  have hstable : (prefixWord ++ tailWord_942717).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942717).length < 2 ^ (prefixWord ++ tailWord_942717).sum := by decide
  have hdescent : baseEnd_942717 < baseStart_942717 := by decide
  rcases family_descends (prefixWord ++ tailWord_942717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942734 : List Nat := [4, 1, 1, 3, 1, 1, 4, 3, 2]
def baseStart_942734 : Nat := 118140960795 + 942734 * 2 ^ 59
def prefixEnd_942734 : Nat := 4983230072969 + 3 ^ 40 * 942734 * 2
def baseEnd_942734 : Nat := 430289485631839806746179

theorem tailTrace_942734 : CollatzResearch.WordTrace tailWord_942734 prefixEnd_942734 430289485631839806746179 := by
  unfold tailWord_942734
  simp only [CollatzResearch.WordTrace]
  refine ⟨4298041720830399874244407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22922889177762132662636837 4298041720830399874244407)
  ·
    refine ⟨6447062581245599811366611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4298041720830399874244407 6447062581245599811366611)
    ·
      refine ⟨9670593871868399717049917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6447062581245599811366611 9670593871868399717049917)
      ·
        refine ⟨3626472701950649893893719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9670593871868399717049917 3626472701950649893893719)
        ·
          refine ⟨5439709052925974840840579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3626472701950649893893719 5439709052925974840840579)
          ·
            refine ⟨8159563579388962261260869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5439709052925974840840579 8159563579388962261260869)
            ·
              refine ⟨1529918171135430423986413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8159563579388962261260869 1529918171135430423986413)
              ·
                refine ⟨573719314175786408994905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1529918171135430423986413 573719314175786408994905)
                ·
                  refine ⟨430289485631839806746179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 573719314175786408994905 430289485631839806746179)
                  ·
                    rfl

theorem cell20_942734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 4, 3, 2].length) (baseStart_942734 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_942734 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_942734 prefixEnd_942734 := by exact prefixLift 942734
  have htrace : WordTrace (prefixWord ++ tailWord_942734) baseStart_942734 baseEnd_942734 := by
    simpa [prefixWord, tailWord_942734, baseEnd_942734] using wordTrace_append hprefix tailTrace_942734
  have hstable : (prefixWord ++ tailWord_942734).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942734).length < 2 ^ (prefixWord ++ tailWord_942734).sum := by decide
  have hdescent : baseEnd_942734 < baseStart_942734 := by decide
  rcases family_descends (prefixWord ++ tailWord_942734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942748 : List Nat := [2, 2, 3, 2, 2, 1, 3, 2, 3]
def baseStart_942748 : Nat := 118140960795 + 942748 * 2 ^ 59
def prefixEnd_942748 : Nat := 4983230072969 + 3 ^ 40 * 942748 * 2
def baseEnd_942748 : Nat := 430295875613317980279455

theorem tailTrace_942748 : CollatzResearch.WordTrace tailWord_942748 prefixEnd_942748 430295875613317980279455 := by
  unfold tailWord_942748
  simp only [CollatzResearch.WordTrace]
  refine ⟨17192422194296239692482449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22923229592394986256643265 17192422194296239692482449)
  ·
    refine ⟨12894316645722179769361837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17192422194296239692482449 12894316645722179769361837)
    ·
      refine ⟨4835368742145817413510689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12894316645722179769361837 4835368742145817413510689)
      ·
        refine ⟨3626526556609363060133017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4835368742145817413510689 3626526556609363060133017)
        ·
          refine ⟨2719894917457022295099763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3626526556609363060133017 2719894917457022295099763)
          ·
            refine ⟨4079842376185533442649645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2719894917457022295099763 4079842376185533442649645)
            ·
              refine ⟨1529940891069575040993617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4079842376185533442649645 1529940891069575040993617)
              ·
                refine ⟨1147455668302181280745213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1529940891069575040993617 1147455668302181280745213)
                ·
                  refine ⟨430295875613317980279455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1147455668302181280745213 430295875613317980279455)
                  ·
                    rfl

theorem cell20_942748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 3, 2, 3].length) (baseStart_942748 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_942748 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_942748 prefixEnd_942748 := by exact prefixLift 942748
  have htrace : WordTrace (prefixWord ++ tailWord_942748) baseStart_942748 baseEnd_942748 := by
    simpa [prefixWord, tailWord_942748, baseEnd_942748] using wordTrace_append hprefix tailTrace_942748
  have hstable : (prefixWord ++ tailWord_942748).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942748).length < 2 ^ (prefixWord ++ tailWord_942748).sum := by decide
  have hdescent : baseEnd_942748 < baseStart_942748 := by decide
  rcases family_descends (prefixWord ++ tailWord_942748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942765 : List Nat := [1, 5, 2, 1, 1, 3, 3, 1, 3]
def baseStart_942765 : Nat := 118140960795 + 942765 * 2 ^ 59
def prefixEnd_942765 : Nat := 4983230072969 + 3 ^ 40 * 942765 * 2
def baseEnd_942765 : Nat := 430303634876541476712719

theorem tailTrace_942765 : CollatzResearch.WordTrace tailWord_942765 prefixEnd_942765 430303634876541476712719 := by
  unfold tailWord_942765
  simp only [CollatzResearch.WordTrace]
  refine ⟨34385464429530891288333749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22923642953020594192222499 34385464429530891288333749)
  ·
    refine ⟨3223637290268521058281289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34385464429530891288333749 3223637290268521058281289)
    ·
      refine ⟨2417727967701390793710967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3223637290268521058281289 2417727967701390793710967)
      ·
        refine ⟨3626591951552086190566451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2417727967701390793710967 3626591951552086190566451)
        ·
          refine ⟨5439887927328129285849677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3626591951552086190566451 5439887927328129285849677)
          ·
            refine ⟨2039957972748048482193629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5439887927328129285849677 2039957972748048482193629)
            ·
              refine ⟨764984239780518180822611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2039957972748048482193629 764984239780518180822611)
              ·
                refine ⟨1147476359670777271233917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 764984239780518180822611 1147476359670777271233917)
                ·
                  refine ⟨430303634876541476712719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1147476359670777271233917 430303634876541476712719)
                  ·
                    rfl

theorem cell20_942765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 3, 1, 3].length) (baseStart_942765 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_942765 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_942765 prefixEnd_942765 := by exact prefixLift 942765
  have htrace : WordTrace (prefixWord ++ tailWord_942765) baseStart_942765 baseEnd_942765 := by
    simpa [prefixWord, tailWord_942765, baseEnd_942765] using wordTrace_append hprefix tailTrace_942765
  have hstable : (prefixWord ++ tailWord_942765).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942765).length < 2 ^ (prefixWord ++ tailWord_942765).sum := by decide
  have hdescent : baseEnd_942765 < baseStart_942765 := by decide
  rcases family_descends (prefixWord ++ tailWord_942765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942783 : List Nat := [1, 1, 2, 2, 2, 5, 1, 6]
def baseStart_942783 : Nat := 118140960795 + 942783 * 2 ^ 59
def prefixEnd_942783 : Nat := 4983230072969 + 3 ^ 40 * 942783 * 2
def baseEnd_942783 : Nat := 143437283522337804704215

theorem tailTrace_942783 : CollatzResearch.WordTrace tailWord_942783 prefixEnd_942783 143437283522337804704215 := by
  unfold tailWord_942783
  simp only [CollatzResearch.WordTrace]
  refine ⟨34386120943465680362489003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22924080628977120241659335 34386120943465680362489003)
  ·
    refine ⟨51579181415198520543733505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34386120943465680362489003 51579181415198520543733505)
    ·
      refine ⟨38684386061398890407800129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51579181415198520543733505 38684386061398890407800129)
      ·
        refine ⟨29013289546049167805850097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38684386061398890407800129 29013289546049167805850097)
        ·
          refine ⟨21759967159536875854387573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29013289546049167805850097 21759967159536875854387573)
          ·
            refine ⟨2039996921206582111348835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21759967159536875854387573 2039996921206582111348835)
            ·
              refine ⟨3059995381809873167023253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2039996921206582111348835 3059995381809873167023253)
              ·
                refine ⟨143437283522337804704215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3059995381809873167023253 143437283522337804704215)
                ·
                  rfl

theorem cell20_942783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 6].length) (baseStart_942783 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_942783 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_942783 prefixEnd_942783 := by exact prefixLift 942783
  have htrace : WordTrace (prefixWord ++ tailWord_942783) baseStart_942783 baseEnd_942783 := by
    simpa [prefixWord, tailWord_942783, baseEnd_942783] using wordTrace_append hprefix tailTrace_942783
  have hstable : (prefixWord ++ tailWord_942783).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942783).length < 2 ^ (prefixWord ++ tailWord_942783).sum := by decide
  have hdescent : baseEnd_942783 < baseStart_942783 := by decide
  rcases family_descends (prefixWord ++ tailWord_942783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942785 : List Nat := [1, 2, 6, 2, 2, 1, 1, 3, 2]
def baseStart_942785 : Nat := 118140960795 + 942785 * 2 ^ 59
def prefixEnd_942785 : Nat := 4983230072969 + 3 ^ 40 * 942785 * 2
def baseEnd_942785 : Nat := 430312763421510296045971

theorem tailTrace_942785 : CollatzResearch.WordTrace tailWord_942785 prefixEnd_942785 430312763421510296045971 := by
  unfold tailWord_942785
  simp only [CollatzResearch.WordTrace]
  refine ⟨34386193889458434704061809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22924129259638956469374539 34386193889458434704061809)
  ·
    refine ⟨25789645417093826028046357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34386193889458434704061809 25789645417093826028046357)
    ·
      refine ⟨1208889628926273095064673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 25789645417093826028046357 1208889628926273095064673)
      ·
        refine ⟨906667221694704821298505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1208889628926273095064673 906667221694704821298505)
        ·
          refine ⟨680000416271028615973879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 906667221694704821298505 680000416271028615973879)
          ·
            refine ⟨1020000624406542923960819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 680000416271028615973879 1020000624406542923960819)
            ·
              refine ⟨1530000936609814385941229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1020000624406542923960819 1530000936609814385941229)
              ·
                refine ⟨573750351228680394727961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1530000936609814385941229 573750351228680394727961)
                ·
                  refine ⟨430312763421510296045971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 573750351228680394727961 430312763421510296045971)
                  ·
                    rfl

theorem cell20_942785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 1, 3, 2].length) (baseStart_942785 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_942785 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_942785 prefixEnd_942785 := by exact prefixLift 942785
  have htrace : WordTrace (prefixWord ++ tailWord_942785) baseStart_942785 baseEnd_942785 := by
    simpa [prefixWord, tailWord_942785, baseEnd_942785] using wordTrace_append hprefix tailTrace_942785
  have hstable : (prefixWord ++ tailWord_942785).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942785).length < 2 ^ (prefixWord ++ tailWord_942785).sum := by decide
  have hdescent : baseEnd_942785 < baseStart_942785 := by decide
  rcases family_descends (prefixWord ++ tailWord_942785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942810 : List Nat := [3, 1, 1, 2, 2, 2, 5, 2, 2]
def baseStart_942810 : Nat := 118140960795 + 942810 * 2 ^ 59
def prefixEnd_942810 : Nat := 4983230072969 + 3 ^ 40 * 942810 * 2
def baseEnd_942810 : Nat := 430324174102721320212535

theorem tailTrace_942810 : CollatzResearch.WordTrace tailWord_942810 prefixEnd_942810 430324174102721320212535 := by
  unfold tailWord_942810
  simp only [CollatzResearch.WordTrace]
  refine ⟨8596776428591965993430471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22924737142911909315814589 8596776428591965993430471)
  ·
    refine ⟨12895164642887948990145707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8596776428591965993430471 12895164642887948990145707)
    ·
      refine ⟨19342746964331923485218561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12895164642887948990145707 19342746964331923485218561)
      ·
        refine ⟨14507060223248942613913921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19342746964331923485218561 14507060223248942613913921)
        ·
          refine ⟨10880295167436706960435441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14507060223248942613913921 10880295167436706960435441)
          ·
            refine ⟨8160221375577530220326581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10880295167436706960435441 8160221375577530220326581)
            ·
              refine ⟨765020753960393458155617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8160221375577530220326581 765020753960393458155617)
              ·
                refine ⟨573765565470295093616713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 765020753960393458155617 573765565470295093616713)
                ·
                  refine ⟨430324174102721320212535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 573765565470295093616713 430324174102721320212535)
                  ·
                    rfl

theorem cell20_942810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 5, 2, 2].length) (baseStart_942810 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_942810 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_942810 prefixEnd_942810 := by exact prefixLift 942810
  have htrace : WordTrace (prefixWord ++ tailWord_942810) baseStart_942810 baseEnd_942810 := by
    simpa [prefixWord, tailWord_942810, baseEnd_942810] using wordTrace_append hprefix tailTrace_942810
  have hstable : (prefixWord ++ tailWord_942810).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942810).length < 2 ^ (prefixWord ++ tailWord_942810).sum := by decide
  have hdescent : baseEnd_942810 < baseStart_942810 := by decide
  rcases family_descends (prefixWord ++ tailWord_942810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942821 : List Nat := [1, 3, 1, 4, 1, 2, 1, 7]
def baseStart_942821 : Nat := 118140960795 + 942821 * 2 ^ 59
def prefixEnd_942821 : Nat := 4983230072969 + 3 ^ 40 * 942821 * 2
def baseEnd_942821 : Nat := 143443064934151390281941

theorem tailTrace_942821 : CollatzResearch.WordTrace tailWord_942821 prefixEnd_942821 143443064934151390281941 := by
  unfold tailWord_942821
  simp only [CollatzResearch.WordTrace]
  refine ⟨34387506917328012852372317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22925004611552008568248211 34387506917328012852372317)
  ·
    refine ⟨12895315093998004819639619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34387506917328012852372317 12895315093998004819639619)
    ·
      refine ⟨19342972640997007229459429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12895315093998004819639619 19342972640997007229459429)
      ·
        refine ⟨3626807370186938855523643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19342972640997007229459429 3626807370186938855523643)
        ·
          refine ⟨5440211055280408283285465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3626807370186938855523643 5440211055280408283285465)
          ·
            refine ⟨4080158291460306212464099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5440211055280408283285465 4080158291460306212464099)
            ·
              refine ⟨6120237437190459318696149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4080158291460306212464099 6120237437190459318696149)
              ·
                refine ⟨143443064934151390281941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6120237437190459318696149 143443064934151390281941)
                ·
                  rfl

theorem cell20_942821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 7].length) (baseStart_942821 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_942821 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_942821 prefixEnd_942821 := by exact prefixLift 942821
  have htrace : WordTrace (prefixWord ++ tailWord_942821) baseStart_942821 baseEnd_942821 := by
    simpa [prefixWord, tailWord_942821, baseEnd_942821] using wordTrace_append hprefix tailTrace_942821
  have hstable : (prefixWord ++ tailWord_942821).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942821).length < 2 ^ (prefixWord ++ tailWord_942821).sum := by decide
  have hdescent : baseEnd_942821 < baseStart_942821 := by decide
  rcases family_descends (prefixWord ++ tailWord_942821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942824 : List Nat := [2, 1, 4, 1, 4, 1, 1, 3, 3]
def baseStart_942824 : Nat := 118140960795 + 942824 * 2 ^ 59
def prefixEnd_942824 : Nat := 4983230072969 + 3 ^ 40 * 942824 * 2
def baseEnd_942824 : Nat := 430330564084199493745811

theorem tailTrace_942824 : CollatzResearch.WordTrace tailWord_942824 prefixEnd_942824 430330564084199493745811 := by
  unfold tailWord_942824
  simp only [CollatzResearch.WordTrace]
  refine ⟨17193808168158572182365763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22925077557544762909821017 17193808168158572182365763)
  ·
    refine ⟨25790712252237858273548645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17193808168158572182365763 25790712252237858273548645)
    ·
      refine ⟨4835758547294598426290371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25790712252237858273548645 4835758547294598426290371)
      ·
        refine ⟨7253637820941897639435557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4835758547294598426290371 7253637820941897639435557)
        ·
          refine ⟨1360057091426605807394167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7253637820941897639435557 1360057091426605807394167)
          ·
            refine ⟨2040085637139908711091251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1360057091426605807394167 2040085637139908711091251)
            ·
              refine ⟨3060128455709863066636877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2040085637139908711091251 3060128455709863066636877)
              ·
                refine ⟨1147548170891198649988829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3060128455709863066636877 1147548170891198649988829)
                ·
                  refine ⟨430330564084199493745811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1147548170891198649988829 430330564084199493745811)
                  ·
                    rfl

theorem cell20_942824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 3, 3].length) (baseStart_942824 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_942824 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_942824 prefixEnd_942824 := by exact prefixLift 942824
  have htrace : WordTrace (prefixWord ++ tailWord_942824) baseStart_942824 baseEnd_942824 := by
    simpa [prefixWord, tailWord_942824, baseEnd_942824] using wordTrace_append hprefix tailTrace_942824
  have hstable : (prefixWord ++ tailWord_942824).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942824).length < 2 ^ (prefixWord ++ tailWord_942824).sum := by decide
  have hdescent : baseEnd_942824 < baseStart_942824 := by decide
  rcases family_descends (prefixWord ++ tailWord_942824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942835 : List Nat := [1, 1, 1, 2, 2, 3, 1, 3, 6]
def baseStart_942835 : Nat := 118140960795 + 942835 * 2 ^ 59
def prefixEnd_942835 : Nat := 4983230072969 + 3 ^ 40 * 942835 * 2
def baseEnd_942835 : Nat := 430335584783932344379099

theorem tailTrace_942835 : CollatzResearch.WordTrace tailWord_942835 prefixEnd_942835 430335584783932344379099 := by
  unfold tailWord_942835
  simp only [CollatzResearch.WordTrace]
  refine ⟨34388017539277293243381959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22925345026184862162254639 34388017539277293243381959)
  ·
    refine ⟨51582026308915939865072939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34388017539277293243381959 51582026308915939865072939)
    ·
      refine ⟨77373039463373909797609409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51582026308915939865072939 77373039463373909797609409)
      ·
        refine ⟨58029779597530432348207057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77373039463373909797609409 58029779597530432348207057)
        ·
          refine ⟨43522334698147824261155293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58029779597530432348207057 43522334698147824261155293)
          ·
            refine ⟨16320875511805434097933235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43522334698147824261155293 16320875511805434097933235)
            ·
              refine ⟨24481313267708151146899853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16320875511805434097933235 24481313267708151146899853)
              ·
                refine ⟨9180492475390556680087445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24481313267708151146899853 9180492475390556680087445)
                ·
                  refine ⟨430335584783932344379099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9180492475390556680087445 430335584783932344379099)
                  ·
                    rfl

theorem cell20_942835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 3, 6].length) (baseStart_942835 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_942835 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_942835 prefixEnd_942835 := by exact prefixLift 942835
  have htrace : WordTrace (prefixWord ++ tailWord_942835) baseStart_942835 baseEnd_942835 := by
    simpa [prefixWord, tailWord_942835, baseEnd_942835] using wordTrace_append hprefix tailTrace_942835
  have hstable : (prefixWord ++ tailWord_942835).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942835).length < 2 ^ (prefixWord ++ tailWord_942835).sum := by decide
  have hdescent : baseEnd_942835 < baseStart_942835 := by decide
  rcases family_descends (prefixWord ++ tailWord_942835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942869 : List Nat := [1, 3, 2, 1, 2, 2, 3, 4, 2]
def baseStart_942869 : Nat := 118140960795 + 942869 * 2 ^ 59
def prefixEnd_942869 : Nat := 4983230072969 + 3 ^ 40 * 942869 * 2
def baseEnd_942869 : Nat := 430351103310379337245627

theorem tailTrace_942869 : CollatzResearch.WordTrace tailWord_942869 prefixEnd_942869 430351103310379337245627 := by
  unfold tailWord_942869
  simp only [CollatzResearch.WordTrace]
  refine ⟨34389257621154117050119661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22926171747436078033413107 34389257621154117050119661)
  ·
    refine ⟨12895971607932793893794873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34389257621154117050119661 12895971607932793893794873)
    ·
      refine ⟨9671978705949595420346155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12895971607932793893794873 9671978705949595420346155)
      ·
        refine ⟨14507968058924393130519233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9671978705949595420346155 14507968058924393130519233)
        ·
          refine ⟨10880976044193294847889425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14507968058924393130519233 10880976044193294847889425)
          ·
            refine ⟨8160732033144971135917069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10880976044193294847889425 8160732033144971135917069)
            ·
              refine ⟨3060274512429364175968901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8160732033144971135917069 3060274512429364175968901)
              ·
                refine ⟨573801471080505782994169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3060274512429364175968901 573801471080505782994169)
                ·
                  refine ⟨430351103310379337245627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 573801471080505782994169 430351103310379337245627)
                  ·
                    rfl

theorem cell20_942869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 4, 2].length) (baseStart_942869 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_942869 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_942869 prefixEnd_942869 := by exact prefixLift 942869
  have htrace : WordTrace (prefixWord ++ tailWord_942869) baseStart_942869 baseEnd_942869 := by
    simpa [prefixWord, tailWord_942869, baseEnd_942869] using wordTrace_append hprefix tailTrace_942869
  have hstable : (prefixWord ++ tailWord_942869).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942869).length < 2 ^ (prefixWord ++ tailWord_942869).sum := by decide
  have hdescent : baseEnd_942869 < baseStart_942869 := by decide
  rcases family_descends (prefixWord ++ tailWord_942869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942876 : List Nat := [2, 2, 3, 1, 1, 5, 1, 5]
def baseStart_942876 : Nat := 118140960795 + 942876 * 2 ^ 59
def prefixEnd_942876 : Nat := 4983230072969 + 3 ^ 40 * 942876 * 2
def baseEnd_942876 : Nat := 143451432767039474670755

theorem tailTrace_942876 : CollatzResearch.WordTrace tailWord_942876 prefixEnd_942876 143451432767039474670755 := by
  unfold tailWord_942876
  simp only [CollatzResearch.WordTrace]
  refine ⟨17194756466064378622812241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22926341954752504830416321 17194756466064378622812241)
  ·
    refine ⟨12896067349548283967109181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17194756466064378622812241 12896067349548283967109181)
    ·
      refine ⟨4836025256080606487665943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12896067349548283967109181 4836025256080606487665943)
      ·
        refine ⟨7254037884120909731498915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4836025256080606487665943 7254037884120909731498915)
        ·
          refine ⟨10881056826181364597248373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7254037884120909731498915 10881056826181364597248373)
          ·
            refine ⟨1020099077454502930992035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10881056826181364597248373 1020099077454502930992035)
            ·
              refine ⟨1530148616181754396488053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1020099077454502930992035 1530148616181754396488053)
              ·
                refine ⟨143451432767039474670755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1530148616181754396488053 143451432767039474670755)
                ·
                  rfl

theorem cell20_942876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 1, 5].length) (baseStart_942876 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_942876 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_942876 prefixEnd_942876 := by exact prefixLift 942876
  have htrace : WordTrace (prefixWord ++ tailWord_942876) baseStart_942876 baseEnd_942876 := by
    simpa [prefixWord, tailWord_942876, baseEnd_942876] using wordTrace_append hprefix tailTrace_942876
  have hstable : (prefixWord ++ tailWord_942876).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942876).length < 2 ^ (prefixWord ++ tailWord_942876).sum := by decide
  have hdescent : baseEnd_942876 < baseStart_942876 := by decide
  rcases family_descends (prefixWord ++ tailWord_942876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942904 : List Nat := [2, 1, 2, 1, 3, 2, 2, 2, 5]
def baseStart_942904 : Nat := 118140960795 + 942904 * 2 ^ 59
def prefixEnd_942904 : Nat := 4983230072969 + 3 ^ 40 * 942904 * 2
def baseEnd_942904 : Nat := 430367078264074771078817

theorem tailTrace_942904 : CollatzResearch.WordTrace tailWord_942904 prefixEnd_942904 430367078264074771078817 := by
  unfold tailWord_942904
  simp only [CollatzResearch.WordTrace]
  refine ⟨17195267088013659013821883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22927022784018212018429177 17195267088013659013821883)
  ·
    refine ⟨25792900632020488520732825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17195267088013659013821883 25792900632020488520732825)
    ·
      refine ⟨19344675474015366390549619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25792900632020488520732825 19344675474015366390549619)
      ·
        refine ⟨29017013211023049585824429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19344675474015366390549619 29017013211023049585824429)
        ·
          refine ⟨10881379954133643594684161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29017013211023049585824429 10881379954133643594684161)
          ·
            refine ⟨8161034965600232696013121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10881379954133643594684161 8161034965600232696013121)
            ·
              refine ⟨6120776224200174522009841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8161034965600232696013121 6120776224200174522009841)
              ·
                refine ⟨4590582168150130891507381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6120776224200174522009841 4590582168150130891507381)
                ·
                  refine ⟨430367078264074771078817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4590582168150130891507381 430367078264074771078817)
                  ·
                    rfl

theorem cell20_942904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 2, 5].length) (baseStart_942904 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_942904 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_942904 prefixEnd_942904 := by exact prefixLift 942904
  have htrace : WordTrace (prefixWord ++ tailWord_942904) baseStart_942904 baseEnd_942904 := by
    simpa [prefixWord, tailWord_942904, baseEnd_942904] using wordTrace_append hprefix tailTrace_942904
  have hstable : (prefixWord ++ tailWord_942904).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942904).length < 2 ^ (prefixWord ++ tailWord_942904).sum := by decide
  have hdescent : baseEnd_942904 < baseStart_942904 := by decide
  rcases family_descends (prefixWord ++ tailWord_942904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942921 : List Nat := [1, 2, 1, 1, 2, 5, 3, 2, 3]
def baseStart_942921 : Nat := 118140960795 + 942921 * 2 ^ 59
def prefixEnd_942921 : Nat := 4983230072969 + 3 ^ 40 * 942921 * 2
def baseEnd_942921 : Nat := 430374837527298267512081

theorem tailTrace_942921 : CollatzResearch.WordTrace tailWord_942921 prefixEnd_942921 430374837527298267512081 := by
  unfold tailWord_942921
  simp only [CollatzResearch.WordTrace]
  refine ⟨34391154216965729931012617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22927436144643819954008411 34391154216965729931012617)
  ·
    refine ⟨25793365662724297448259463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34391154216965729931012617 25793365662724297448259463)
    ·
      refine ⟨38690048494086446172389195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25793365662724297448259463 38690048494086446172389195)
      ·
        refine ⟨58035072741129669258583793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38690048494086446172389195 58035072741129669258583793)
        ·
          refine ⟨43526304555847251943937845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58035072741129669258583793 43526304555847251943937845)
          ·
            refine ⟨4080591052110679869744173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43526304555847251943937845 4080591052110679869744173)
            ·
              refine ⟨1530221644541504951154065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4080591052110679869744173 1530221644541504951154065)
              ·
                refine ⟨1147666233406128713365549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1530221644541504951154065 1147666233406128713365549)
                ·
                  refine ⟨430374837527298267512081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1147666233406128713365549 430374837527298267512081)
                  ·
                    rfl

theorem cell20_942921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 3, 2, 3].length) (baseStart_942921 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_942921 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_942921 prefixEnd_942921 := by exact prefixLift 942921
  have htrace : WordTrace (prefixWord ++ tailWord_942921) baseStart_942921 baseEnd_942921 := by
    simpa [prefixWord, tailWord_942921, baseEnd_942921] using wordTrace_append hprefix tailTrace_942921
  have hstable : (prefixWord ++ tailWord_942921).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942921).length < 2 ^ (prefixWord ++ tailWord_942921).sum := by decide
  have hdescent : baseEnd_942921 < baseStart_942921 := by decide
  rcases family_descends (prefixWord ++ tailWord_942921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942938 : List Nat := [3, 1, 1, 2, 1, 5, 3, 1, 3]
def baseStart_942938 : Nat := 118140960795 + 942938 * 2 ^ 59
def prefixEnd_942938 : Nat := 4983230072969 + 3 ^ 40 * 942938 * 2
def baseEnd_942938 : Nat := 430382596790521763945345

theorem tailTrace_942938 : CollatzResearch.WordTrace tailWord_942938 prefixEnd_942938 430382596790521763945345 := by
  unfold tailWord_942938
  simp only [CollatzResearch.WordTrace]
  refine ⟨8597943564476035458595367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22927849505269427889587645 8597943564476035458595367)
  ·
    refine ⟨12896915346714053187893051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8597943564476035458595367 12896915346714053187893051)
    ·
      refine ⟨19345373020071079781839577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12896915346714053187893051 19345373020071079781839577)
      ·
        refine ⟨14509029765053309836379683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19345373020071079781839577 14509029765053309836379683)
        ·
          refine ⟨21763544647579964754569525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14509029765053309836379683 21763544647579964754569525)
          ·
            refine ⟨2040332310710621695740893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21763544647579964754569525 2040332310710621695740893)
            ·
              refine ⟨765124616516483135902835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2040332310710621695740893 765124616516483135902835)
              ·
                refine ⟨1147686924774724703854253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 765124616516483135902835 1147686924774724703854253)
                ·
                  refine ⟨430382596790521763945345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1147686924774724703854253 430382596790521763945345)
                  ·
                    rfl

theorem cell20_942938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 3, 1, 3].length) (baseStart_942938 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_942938 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_942938 prefixEnd_942938 := by exact prefixLift 942938
  have htrace : WordTrace (prefixWord ++ tailWord_942938) baseStart_942938 baseEnd_942938 := by
    simpa [prefixWord, tailWord_942938, baseEnd_942938] using wordTrace_append hprefix tailTrace_942938
  have hstable : (prefixWord ++ tailWord_942938).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942938).length < 2 ^ (prefixWord ++ tailWord_942938).sum := by decide
  have hdescent : baseEnd_942938 < baseStart_942938 := by decide
  rcases family_descends (prefixWord ++ tailWord_942938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942952 : List Nat := [2, 1, 4, 2, 1, 2, 4, 4]
def baseStart_942952 : Nat := 118140960795 + 942952 * 2 ^ 59
def prefixEnd_942952 : Nat := 4983230072969 + 3 ^ 40 * 942952 * 2
def baseEnd_942952 : Nat := 143462995590666645826207

theorem tailTrace_942952 : CollatzResearch.WordTrace tailWord_942952 prefixEnd_942952 143462995590666645826207 := by
  unfold tailWord_942952
  simp only [CollatzResearch.WordTrace]
  refine ⟨17196142439926711112695555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22928189919902281483594073 17196142439926711112695555)
  ·
    refine ⟨25794213659890066669043333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17196142439926711112695555 25794213659890066669043333)
    ·
      refine ⟨4836415061229387500445625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25794213659890066669043333 4836415061229387500445625)
      ·
        refine ⟨3627311295922040625334219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4836415061229387500445625 3627311295922040625334219)
        ·
          refine ⟨5440966943883060938001329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3627311295922040625334219 5440966943883060938001329)
          ·
            refine ⟨4080725207912295703500997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5440966943883060938001329 4080725207912295703500997)
            ·
              refine ⟨765135976483555444406437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4080725207912295703500997 765135976483555444406437)
              ·
                refine ⟨143462995590666645826207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 765135976483555444406437 143462995590666645826207)
                ·
                  rfl

theorem cell20_942952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 4, 4].length) (baseStart_942952 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_942952 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_942952 prefixEnd_942952 := by exact prefixLift 942952
  have htrace : WordTrace (prefixWord ++ tailWord_942952) baseStart_942952 baseEnd_942952 := by
    simpa [prefixWord, tailWord_942952, baseEnd_942952] using wordTrace_append hprefix tailTrace_942952
  have hstable : (prefixWord ++ tailWord_942952).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942952).length < 2 ^ (prefixWord ++ tailWord_942952).sum := by decide
  have hdescent : baseEnd_942952 < baseStart_942952 := by decide
  rcases family_descends (prefixWord ++ tailWord_942952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942958 : List Nat := [4, 1, 2, 3, 3, 1, 1, 3, 2]
def baseStart_942958 : Nat := 118140960795 + 942958 * 2 ^ 59
def prefixEnd_942958 : Nat := 4983230072969 + 3 ^ 40 * 942958 * 2
def baseEnd_942958 : Nat := 430391725335490583278597

theorem tailTrace_942958 : CollatzResearch.WordTrace tailWord_942958 prefixEnd_942958 430391725335490583278597 := by
  unfold tailWord_942958
  simp only [CollatzResearch.WordTrace]
  refine ⟨4299062964728960656263691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22928335811887790166739685 4299062964728960656263691)
  ·
    refine ⟨6448594447093440984395537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4299062964728960656263691 6448594447093440984395537)
    ·
      refine ⟨4836445835320080738296653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6448594447093440984395537 4836445835320080738296653)
      ·
        refine ⟨1813667188245030276861245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4836445835320080738296653 1813667188245030276861245)
        ·
          refine ⟨680125195591886353822967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1813667188245030276861245 680125195591886353822967)
          ·
            refine ⟨1020187793387829530734451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 680125195591886353822967 1020187793387829530734451)
            ·
              refine ⟨1530281690081744296101677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1020187793387829530734451 1530281690081744296101677)
              ·
                refine ⟨573855633780654111038129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1530281690081744296101677 573855633780654111038129)
                ·
                  refine ⟨430391725335490583278597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 573855633780654111038129 430391725335490583278597)
                  ·
                    rfl

theorem cell20_942958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 1, 3, 2].length) (baseStart_942958 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_942958 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_942958 prefixEnd_942958 := by exact prefixLift 942958
  have htrace : WordTrace (prefixWord ++ tailWord_942958) baseStart_942958 baseEnd_942958 := by
    simpa [prefixWord, tailWord_942958, baseEnd_942958] using wordTrace_append hprefix tailTrace_942958
  have hstable : (prefixWord ++ tailWord_942958).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942958).length < 2 ^ (prefixWord ++ tailWord_942958).sum := by decide
  have hdescent : baseEnd_942958 < baseStart_942958 := by decide
  rcases family_descends (prefixWord ++ tailWord_942958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942983 : List Nat := [1, 1, 4, 2, 3, 3, 1, 1, 4]
def baseStart_942983 : Nat := 118140960795 + 942983 * 2 ^ 59
def prefixEnd_942983 : Nat := 4983230072969 + 3 ^ 40 * 942983 * 2
def baseEnd_942983 : Nat := 430403136016701607445161

theorem tailTrace_942983 : CollatzResearch.WordTrace tailWord_942983 prefixEnd_942983 430403136016701607445161 := by
  unfold tailWord_942983
  simp only [CollatzResearch.WordTrace]
  refine ⟨34393415542741114519769603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22928943695160743013179735 34393415542741114519769603)
  ·
    refine ⟨51590123314111671779654405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34393415542741114519769603 51590123314111671779654405)
    ·
      refine ⟨9673148121395938458685201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51590123314111671779654405 9673148121395938458685201)
      ·
        refine ⟨7254861091046953844013901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9673148121395938458685201 7254861091046953844013901)
        ·
          refine ⟨2720572909142607691505213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7254861091046953844013901 2720572909142607691505213)
          ·
            refine ⟨1020214840928477884314455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2720572909142607691505213 1020214840928477884314455)
            ·
              refine ⟨1530322261392716826471683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1020214840928477884314455 1530322261392716826471683)
              ·
                refine ⟨2295483392089075239707525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1530322261392716826471683 2295483392089075239707525)
                ·
                  refine ⟨430403136016701607445161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2295483392089075239707525 430403136016701607445161)
                  ·
                    rfl

theorem cell20_942983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 1, 1, 4].length) (baseStart_942983 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_942983 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_942983 prefixEnd_942983 := by exact prefixLift 942983
  have htrace : WordTrace (prefixWord ++ tailWord_942983) baseStart_942983 baseEnd_942983 := by
    simpa [prefixWord, tailWord_942983, baseEnd_942983] using wordTrace_append hprefix tailTrace_942983
  have hstable : (prefixWord ++ tailWord_942983).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942983).length < 2 ^ (prefixWord ++ tailWord_942983).sum := by decide
  have hdescent : baseEnd_942983 < baseStart_942983 := by decide
  rcases family_descends (prefixWord ++ tailWord_942983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_942997 : List Nat := [1, 3, 2, 1, 1, 5, 1, 3, 3]
def baseStart_942997 : Nat := 118140960795 + 942997 * 2 ^ 59
def prefixEnd_942997 : Nat := 4983230072969 + 3 ^ 40 * 942997 * 2
def baseEnd_942997 : Nat := 430409525998179780978437

theorem tailTrace_942997 : CollatzResearch.WordTrace tailWord_942997 prefixEnd_942997 430409525998179780978437 := by
  unfold tailWord_942997
  simp only [CollatzResearch.WordTrace]
  refine ⟨34393926164690394910779245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22929284109793596607186163 34393926164690394910779245)
  ·
    refine ⟨12897722311758898091542217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34393926164690394910779245 12897722311758898091542217)
    ·
      refine ⟨9673291733819173568656663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12897722311758898091542217 9673291733819173568656663)
      ·
        refine ⟨14509937600728760352984995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9673291733819173568656663 14509937600728760352984995)
        ·
          refine ⟨21764906401093140529477493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14509937600728760352984995 21764906401093140529477493)
          ·
            refine ⟨2040459975102481924638515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21764906401093140529477493 2040459975102481924638515)
            ·
              refine ⟨3060689962653722886957773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2040459975102481924638515 3060689962653722886957773)
              ·
                refine ⟨1147758735995146082609165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3060689962653722886957773 1147758735995146082609165)
                ·
                  refine ⟨430409525998179780978437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1147758735995146082609165 430409525998179780978437)
                  ·
                    rfl

theorem cell20_942997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 3, 3].length) (baseStart_942997 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_942997 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_942997 prefixEnd_942997 := by exact prefixLift 942997
  have htrace : WordTrace (prefixWord ++ tailWord_942997) baseStart_942997 baseEnd_942997 := by
    simpa [prefixWord, tailWord_942997, baseEnd_942997] using wordTrace_append hprefix tailTrace_942997
  have hstable : (prefixWord ++ tailWord_942997).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_942997).length < 2 ^ (prefixWord ++ tailWord_942997).sum := by decide
  have hdescent : baseEnd_942997 < baseStart_942997 := by decide
  rcases family_descends (prefixWord ++ tailWord_942997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943028 : List Nat := [2, 5, 2, 1, 1, 9]
def baseStart_943028 : Nat := 118140960795 + 943028 * 2 ^ 59
def prefixEnd_943028 : Nat := 4983230072969 + 3 ^ 40 * 943028 * 2
def baseEnd_943028 : Nat := 15941617601588201886851

theorem tailTrace_943028 : CollatzResearch.WordTrace tailWord_943028 prefixEnd_943028 15941617601588201886851 := by
  unfold tailWord_943028
  simp only [CollatzResearch.WordTrace]
  refine ⟨17197528413789043602578869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22930037885052058136771825 17197528413789043602578869)
  ·
    refine ⟨1612268288792722837741769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17197528413789043602578869 1612268288792722837741769)
    ·
      refine ⟨1209201216594542128306327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1612268288792722837741769 1209201216594542128306327)
      ·
        refine ⟨1813801824891813192459491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1209201216594542128306327 1813801824891813192459491)
        ·
          refine ⟨2720702737337719788689237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1813801824891813192459491 2720702737337719788689237)
          ·
            refine ⟨15941617601588201886851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2720702737337719788689237 15941617601588201886851)
            ·
              rfl

theorem cell20_943028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 9].length) (baseStart_943028 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_943028 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_943028 prefixEnd_943028 := by exact prefixLift 943028
  have htrace : WordTrace (prefixWord ++ tailWord_943028) baseStart_943028 baseEnd_943028 := by
    simpa [prefixWord, tailWord_943028, baseEnd_943028] using wordTrace_append hprefix tailTrace_943028
  have hstable : (prefixWord ++ tailWord_943028).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943028).length < 2 ^ (prefixWord ++ tailWord_943028).sum := by decide
  have hdescent : baseEnd_943028 < baseStart_943028 := by decide
  rcases family_descends (prefixWord ++ tailWord_943028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943030 : List Nat := [5, 1, 4, 1, 1, 2, 2, 2, 2]
def baseStart_943030 : Nat := 118140960795 + 943030 * 2 ^ 59
def prefixEnd_943030 : Nat := 4983230072969 + 3 ^ 40 * 943030 * 2
def baseEnd_943030 : Nat := 430424588097378332878303

theorem tailTrace_943030 : CollatzResearch.WordTrace tailWord_943030 prefixEnd_943030 430424588097378332878303 := by
  unfold tailWord_943030
  simp only [CollatzResearch.WordTrace]
  refine ⟨2149695610848177596670659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22930086515713894364487029 2149695610848177596670659)
  ·
    refine ⟨3224543416272266395005989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2149695610848177596670659 3224543416272266395005989)
    ·
      refine ⟨604601890551049949063623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3224543416272266395005989 604601890551049949063623)
      ·
        refine ⟨906902835826574923595435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 604601890551049949063623 906902835826574923595435)
        ·
          refine ⟨1360354253739862385393153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 906902835826574923595435 1360354253739862385393153)
          ·
            refine ⟨1020265690304896789044865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1360354253739862385393153 1020265690304896789044865)
            ·
              refine ⟨765199267728672591783649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1020265690304896789044865 765199267728672591783649)
              ·
                refine ⟨573899450796504443837737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 765199267728672591783649 573899450796504443837737)
                ·
                  refine ⟨430424588097378332878303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 573899450796504443837737 430424588097378332878303)
                  ·
                    rfl

theorem cell20_943030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 2, 2, 2].length) (baseStart_943030 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_943030 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_943030 prefixEnd_943030 := by exact prefixLift 943030
  have htrace : WordTrace (prefixWord ++ tailWord_943030) baseStart_943030 baseEnd_943030 := by
    simpa [prefixWord, tailWord_943030, baseEnd_943030] using wordTrace_append hprefix tailTrace_943030
  have hstable : (prefixWord ++ tailWord_943030).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943030).length < 2 ^ (prefixWord ++ tailWord_943030).sum := by decide
  have hdescent : baseEnd_943030 < baseStart_943030 := by decide
  rcases family_descends (prefixWord ++ tailWord_943030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943032 : List Nat := [2, 1, 2, 1, 2, 12]
def baseStart_943032 : Nat := 118140960795 + 943032 * 2 ^ 59
def prefixEnd_943032 : Nat := 4983230072969 + 3 ^ 40 * 943032 * 2
def baseEnd_943032 : Nat := 15941685220439822770801

theorem tailTrace_943032 : CollatzResearch.WordTrace tailWord_943032 prefixEnd_943032 15941685220439822770801 := by
  unfold tailWord_943032
  simp only [CollatzResearch.WordTrace]
  refine ⟨17197601359781797944151675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22930135146375730592202233 17197601359781797944151675)
  ·
    refine ⟨25796402039672696916227513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17197601359781797944151675 25796402039672696916227513)
    ·
      refine ⟨19347301529754522687170635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25796402039672696916227513 19347301529754522687170635)
      ·
        refine ⟨29020952294631784030755953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19347301529754522687170635 29020952294631784030755953)
        ·
          refine ⟨21765714220973838023066965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29020952294631784030755953 21765714220973838023066965)
          ·
            refine ⟨15941685220439822770801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 21765714220973838023066965 15941685220439822770801)
            ·
              rfl

theorem cell20_943032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 12].length) (baseStart_943032 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_943032 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_943032 prefixEnd_943032 := by exact prefixLift 943032
  have htrace : WordTrace (prefixWord ++ tailWord_943032) baseStart_943032 baseEnd_943032 := by
    simpa [prefixWord, tailWord_943032, baseEnd_943032] using wordTrace_append hprefix tailTrace_943032
  have hstable : (prefixWord ++ tailWord_943032).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943032).length < 2 ^ (prefixWord ++ tailWord_943032).sum := by decide
  have hdescent : baseEnd_943032 < baseStart_943032 := by decide
  rcases family_descends (prefixWord ++ tailWord_943032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943066 : List Nat := [3, 1, 1, 2, 4, 2, 3, 4]
def baseStart_943066 : Nat := 118140960795 + 943066 * 2 ^ 59
def prefixEnd_943066 : Nat := 4983230072969 + 3 ^ 40 * 943066 * 2
def baseEnd_943066 : Nat := 143480339826107402559385

theorem tailTrace_943066 : CollatzResearch.WordTrace tailWord_943066 prefixEnd_943066 143480339826107402559385 := by
  unfold tailWord_943066
  simp only [CollatzResearch.WordTrace]
  refine ⟨8599110700360104923760263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22930961867626946463360701 8599110700360104923760263)
  ·
    refine ⟨12898666050540157385640395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8599110700360104923760263 12898666050540157385640395)
    ·
      refine ⟨19347999075810236078460593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12898666050540157385640395 19347999075810236078460593)
      ·
        refine ⟨14510999306857677058845445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19347999075810236078460593 14510999306857677058845445)
        ·
          refine ⟨2720812370035814448533521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14510999306857677058845445 2720812370035814448533521)
          ·
            refine ⟨2040609277526860836400141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2720812370035814448533521 2040609277526860836400141)
            ·
              refine ⟨765228479072572813650053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2040609277526860836400141 765228479072572813650053)
              ·
                refine ⟨143480339826107402559385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 765228479072572813650053 143480339826107402559385)
                ·
                  rfl

theorem cell20_943066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 3, 4].length) (baseStart_943066 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_943066 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_943066 prefixEnd_943066 := by exact prefixLift 943066
  have htrace : WordTrace (prefixWord ++ tailWord_943066) baseStart_943066 baseEnd_943066 := by
    simpa [prefixWord, tailWord_943066, baseEnd_943066] using wordTrace_append hprefix tailTrace_943066
  have hstable : (prefixWord ++ tailWord_943066).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943066).length < 2 ^ (prefixWord ++ tailWord_943066).sum := by decide
  have hdescent : baseEnd_943066 < baseStart_943066 := by decide
  rcases family_descends (prefixWord ++ tailWord_943066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943090 : List Nat := [3, 2, 1, 5, 1, 1, 1, 1, 5]
def baseStart_943090 : Nat := 118140960795 + 943090 * 2 ^ 59
def prefixEnd_943090 : Nat := 4983230072969 + 3 ^ 40 * 943090 * 2
def baseEnd_943090 : Nat := 430451973732284790878057

theorem tailTrace_943090 : CollatzResearch.WordTrace tailWord_943090 prefixEnd_943090 430451973732284790878057 := by
  unfold tailWord_943090
  simp only [CollatzResearch.WordTrace]
  refine ⟨8599329538338367948478681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22931545435568981195943149 8599329538338367948478681)
  ·
    refine ⟨6449497153753775961359011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8599329538338367948478681 6449497153753775961359011)
    ·
      refine ⟨9674245730630663942038517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6449497153753775961359011 9674245730630663942038517)
      ·
        refine ⟨906960537246624744566111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9674245730630663942038517 906960537246624744566111)
        ·
          refine ⟨1360440805869937116849167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 906960537246624744566111 1360440805869937116849167)
          ·
            refine ⟨2040661208804905675273751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1360440805869937116849167 2040661208804905675273751)
            ·
              refine ⟨3060991813207358512910627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2040661208804905675273751 3060991813207358512910627)
              ·
                refine ⟨4591487719811037769365941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3060991813207358512910627 4591487719811037769365941)
                ·
                  refine ⟨430451973732284790878057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4591487719811037769365941 430451973732284790878057)
                  ·
                    rfl

theorem cell20_943090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 1, 5].length) (baseStart_943090 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_943090 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_943090 prefixEnd_943090 := by exact prefixLift 943090
  have htrace : WordTrace (prefixWord ++ tailWord_943090) baseStart_943090 baseEnd_943090 := by
    simpa [prefixWord, tailWord_943090, baseEnd_943090] using wordTrace_append hprefix tailTrace_943090
  have hstable : (prefixWord ++ tailWord_943090).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943090).length < 2 ^ (prefixWord ++ tailWord_943090).sum := by decide
  have hdescent : baseEnd_943090 < baseStart_943090 := by decide
  rcases family_descends (prefixWord ++ tailWord_943090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943118 : List Nat := [4, 1, 1, 2, 2, 2, 2, 2, 4]
def baseStart_943118 : Nat := 118140960795 + 943118 * 2 ^ 59
def prefixEnd_943118 : Nat := 4983230072969 + 3 ^ 40 * 943118 * 2
def baseEnd_943118 : Nat := 430464753695241137944609

theorem tailTrace_943118 : CollatzResearch.WordTrace tailWord_943118 prefixEnd_943118 430464753695241137944609 := by
  unfold tailWord_943118
  simp only [CollatzResearch.WordTrace]
  refine ⟨4299792424656504071991751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22932226264834688383956005 4299792424656504071991751)
  ·
    refine ⟨6449688636984756107987627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4299792424656504071991751 6449688636984756107987627)
    ·
      refine ⟨9674532955477134161981441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6449688636984756107987627 9674532955477134161981441)
      ·
        refine ⟨7255899716607850621486081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9674532955477134161981441 7255899716607850621486081)
        ·
          refine ⟨5441924787455887966114561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7255899716607850621486081 5441924787455887966114561)
          ·
            refine ⟨4081443590591915974585921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5441924787455887966114561 4081443590591915974585921)
            ·
              refine ⟨3061082692943936980939441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4081443590591915974585921 3061082692943936980939441)
              ·
                refine ⟨2295812019707952735704581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3061082692943936980939441 2295812019707952735704581)
                ·
                  refine ⟨430464753695241137944609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2295812019707952735704581 430464753695241137944609)
                  ·
                    rfl

theorem cell20_943118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 2, 4].length) (baseStart_943118 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_943118 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_943118 prefixEnd_943118 := by exact prefixLift 943118
  have htrace : WordTrace (prefixWord ++ tailWord_943118) baseStart_943118 baseEnd_943118 := by
    simpa [prefixWord, tailWord_943118, baseEnd_943118] using wordTrace_append hprefix tailTrace_943118
  have hstable : (prefixWord ++ tailWord_943118).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943118).length < 2 ^ (prefixWord ++ tailWord_943118).sum := by decide
  have hdescent : baseEnd_943118 < baseStart_943118 := by decide
  rcases family_descends (prefixWord ++ tailWord_943118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943125 : List Nat := [1, 3, 2, 1, 4, 2, 1, 6]
def baseStart_943125 : Nat := 118140960795 + 943125 * 2 ^ 59
def prefixEnd_943125 : Nat := 4983230072969 + 3 ^ 40 * 943125 * 2
def baseEnd_943125 : Nat := 143489316228660074903749

theorem tailTrace_943125 : CollatzResearch.WordTrace tailWord_943125 prefixEnd_943125 143489316228660074903749 := by
  unfold tailWord_943125
  simp only [CollatzResearch.WordTrace]
  refine ⟨34398594708226672771438829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22932396472151115180959219 34398594708226672771438829)
  ·
    refine ⟨12899473015585002289289561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34398594708226672771438829 12899473015585002289289561)
    ·
      refine ⟨9674604761688751716967171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12899473015585002289289561 9674604761688751716967171)
      ·
        refine ⟨14511907142533127575450757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9674604761688751716967171 14511907142533127575450757)
        ·
          refine ⟨2720982589224961420397017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14511907142533127575450757 2720982589224961420397017)
          ·
            refine ⟨2040736941918721065297763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2720982589224961420397017 2040736941918721065297763)
            ·
              refine ⟨3061105412878081597946645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2040736941918721065297763 3061105412878081597946645)
              ·
                refine ⟨143489316228660074903749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3061105412878081597946645 143489316228660074903749)
                ·
                  rfl

theorem cell20_943125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 6].length) (baseStart_943125 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_943125 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_943125 prefixEnd_943125 := by exact prefixLift 943125
  have htrace : WordTrace (prefixWord ++ tailWord_943125) baseStart_943125 baseEnd_943125 := by
    simpa [prefixWord, tailWord_943125, baseEnd_943125] using wordTrace_append hprefix tailTrace_943125
  have hstable : (prefixWord ++ tailWord_943125).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943125).length < 2 ^ (prefixWord ++ tailWord_943125).sum := by decide
  have hdescent : baseEnd_943125 < baseStart_943125 := by decide
  rcases family_descends (prefixWord ++ tailWord_943125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943135 : List Nat := [1, 1, 2, 4, 1, 3, 3, 3, 2]
def baseStart_943135 : Nat := 118140960795 + 943135 * 2 ^ 59
def prefixEnd_943135 : Nat := 4983230072969 + 3 ^ 40 * 943135 * 2
def baseEnd_943135 : Nat := 430472512958464634377873

theorem tailTrace_943135 : CollatzResearch.WordTrace tailWord_943135 prefixEnd_943135 430472512958464634377873 := by
  unfold tailWord_943135
  simp only [CollatzResearch.WordTrace]
  refine ⟨34398959438190444479302859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22932639625460296319535239 34398959438190444479302859)
  ·
    refine ⟨51598439157285666718954289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34398959438190444479302859 51598439157285666718954289)
    ·
      refine ⟨38698829367964250039215717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51598439157285666718954289 38698829367964250039215717)
      ·
        refine ⟨7256030506493296882352947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38698829367964250039215717 7256030506493296882352947)
        ·
          refine ⟨10884045759739945323529421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7256030506493296882352947 10884045759739945323529421)
          ·
            refine ⟨4081517159902479496323533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10884045759739945323529421 4081517159902479496323533)
            ·
              refine ⟨1530568934963429811121325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4081517159902479496323533 1530568934963429811121325)
              ·
                refine ⟨573963350611286179170497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1530568934963429811121325 573963350611286179170497)
                ·
                  refine ⟨430472512958464634377873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 573963350611286179170497 430472512958464634377873)
                  ·
                    rfl

theorem cell20_943135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 3, 3, 2].length) (baseStart_943135 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_943135 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_943135 prefixEnd_943135 := by exact prefixLift 943135
  have htrace : WordTrace (prefixWord ++ tailWord_943135) baseStart_943135 baseEnd_943135 := by
    simpa [prefixWord, tailWord_943135, baseEnd_943135] using wordTrace_append hprefix tailTrace_943135
  have hstable : (prefixWord ++ tailWord_943135).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943135).length < 2 ^ (prefixWord ++ tailWord_943135).sum := by decide
  have hdescent : baseEnd_943135 < baseStart_943135 := by decide
  rcases family_descends (prefixWord ++ tailWord_943135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943166 : List Nat := [4, 2, 1, 3, 1, 2, 1, 3, 3]
def baseStart_943166 : Nat := 118140960795 + 943166 * 2 ^ 59
def prefixEnd_943166 : Nat := 4983230072969 + 3 ^ 40 * 943166 * 2
def baseEnd_943166 : Nat := 430486662203166304344413

theorem tailTrace_943166 : CollatzResearch.WordTrace tailWord_943166 prefixEnd_943166 430486662203166304344413 := by
  unfold tailWord_943166
  simp only [CollatzResearch.WordTrace]
  refine ⟨4300011262634767096710169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22933393400718757849120901 4300011262634767096710169)
  ·
    refine ⟨3225008446976075322532627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4300011262634767096710169 3225008446976075322532627)
    ·
      refine ⟨4837512670464112983798941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3225008446976075322532627 4837512670464112983798941)
      ·
        refine ⟨1814067251424042368924603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4837512670464112983798941 1814067251424042368924603)
        ·
          refine ⟨2721100877136063553386905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1814067251424042368924603 2721100877136063553386905)
          ·
            refine ⟨2040825657852047665040179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2721100877136063553386905 2040825657852047665040179)
            ·
              refine ⟨3061238486778071497560269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2040825657852047665040179 3061238486778071497560269)
              ·
                refine ⟨1147964432541776811585101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3061238486778071497560269 1147964432541776811585101)
                ·
                  refine ⟨430486662203166304344413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1147964432541776811585101 430486662203166304344413)
                  ·
                    rfl

theorem cell20_943166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 3, 3].length) (baseStart_943166 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_943166 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_943166 prefixEnd_943166 := by exact prefixLift 943166
  have htrace : WordTrace (prefixWord ++ tailWord_943166) baseStart_943166 baseEnd_943166 := by
    simpa [prefixWord, tailWord_943166, baseEnd_943166] using wordTrace_append hprefix tailTrace_943166
  have hstable : (prefixWord ++ tailWord_943166).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943166).length < 2 ^ (prefixWord ++ tailWord_943166).sum := by decide
  have hdescent : baseEnd_943166 < baseStart_943166 := by decide
  rcases family_descends (prefixWord ++ tailWord_943166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943215 : List Nat := [1, 1, 2, 1, 3, 3, 2, 3, 4]
def baseStart_943215 : Nat := 118140960795 + 943215 * 2 ^ 59
def prefixEnd_943215 : Nat := 4983230072969 + 3 ^ 40 * 943215 * 2
def baseEnd_943215 : Nat := 430509027138339911710879

theorem tailTrace_943215 : CollatzResearch.WordTrace tailWord_943215 prefixEnd_943215 430509027138339911710879 := by
  unfold tailWord_943215
  simp only [CollatzResearch.WordTrace]
  refine ⟨34401877277900618142215099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22934584851933745428143399 34401877277900618142215099)
  ·
    refine ⟨51602815916850927213322649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34401877277900618142215099 51602815916850927213322649)
    ·
      refine ⟨38702111937638195409991987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51602815916850927213322649 38702111937638195409991987)
      ·
        refine ⟨58053167906457293114987981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38702111937638195409991987 58053167906457293114987981)
        ·
          refine ⟨21769937964921484918120493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 58053167906457293114987981 21769937964921484918120493)
          ·
            refine ⟨8163726736845556844295185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21769937964921484918120493 8163726736845556844295185)
            ·
              refine ⟨6122795052634167633221389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8163726736845556844295185 6122795052634167633221389)
              ·
                refine ⟨2296048144737812862458021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6122795052634167633221389 2296048144737812862458021)
                ·
                  refine ⟨430509027138339911710879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2296048144737812862458021 430509027138339911710879)
                  ·
                    rfl

theorem cell20_943215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 3, 4].length) (baseStart_943215 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_943215 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_943215 prefixEnd_943215 := by exact prefixLift 943215
  have htrace : WordTrace (prefixWord ++ tailWord_943215) baseStart_943215 baseEnd_943215 := by
    simpa [prefixWord, tailWord_943215, baseEnd_943215] using wordTrace_append hprefix tailTrace_943215
  have hstable : (prefixWord ++ tailWord_943215).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943215).length < 2 ^ (prefixWord ++ tailWord_943215).sum := by decide
  have hdescent : baseEnd_943215 < baseStart_943215 := by decide
  rcases family_descends (prefixWord ++ tailWord_943215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943263 : List Nat := [1, 1, 2, 6, 2, 1, 1, 1, 5]
def baseStart_943263 : Nat := 118140960795 + 943263 * 2 ^ 59
def prefixEnd_943263 : Nat := 4983230072969 + 3 ^ 40 * 943263 * 2
def baseEnd_943263 : Nat := 430530935646265078110683

theorem tailTrace_943263 : CollatzResearch.WordTrace tailWord_943263 prefixEnd_943263 430530935646265078110683 := by
  unfold tailWord_943263
  simp only [CollatzResearch.WordTrace]
  refine ⟨34403627981726722339962443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22935751987817814893308295 34403627981726722339962443)
  ·
    refine ⟨51605441972590083509943665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34403627981726722339962443 51605441972590083509943665)
    ·
      refine ⟨38704081479442562632457749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51605441972590083509943665 38704081479442562632457749)
      ·
        refine ⟨1814253819348870123396457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 38704081479442562632457749 1814253819348870123396457)
        ·
          refine ⟨1360690364511652592547343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1814253819348870123396457 1360690364511652592547343)
          ·
            refine ⟨2041035546767478888821015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1360690364511652592547343 2041035546767478888821015)
            ·
              refine ⟨3061553320151218333231523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2041035546767478888821015 3061553320151218333231523)
              ·
                refine ⟨4592329980226827499847285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3061553320151218333231523 4592329980226827499847285)
                ·
                  refine ⟨430530935646265078110683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4592329980226827499847285 430530935646265078110683)
                  ·
                    rfl

theorem cell20_943263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 1, 5].length) (baseStart_943263 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_943263 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_943263 prefixEnd_943263 := by exact prefixLift 943263
  have htrace : WordTrace (prefixWord ++ tailWord_943263) baseStart_943263 baseEnd_943263 := by
    simpa [prefixWord, tailWord_943263, baseEnd_943263] using wordTrace_append hprefix tailTrace_943263
  have hstable : (prefixWord ++ tailWord_943263).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943263).length < 2 ^ (prefixWord ++ tailWord_943263).sum := by decide
  have hdescent : baseEnd_943263 < baseStart_943263 := by decide
  rcases family_descends (prefixWord ++ tailWord_943263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943294 : List Nat := [4, 2, 1, 1, 3, 1, 4, 4]
def baseStart_943294 : Nat := 118140960795 + 943294 * 2 ^ 59
def prefixEnd_943294 : Nat := 4983230072969 + 3 ^ 40 * 943294 * 2
def baseEnd_943294 : Nat := 143515028296988916025741

theorem tailTrace_943294 : CollatzResearch.WordTrace tailWord_943294 prefixEnd_943294 143515028296988916025741 := by
  unfold tailWord_943294
  simp only [CollatzResearch.WordTrace]
  refine ⟨4300594830576801829292617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22936505763076276422893957 4300594830576801829292617)
  ·
    refine ⟨3225446122932601371969463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4300594830576801829292617 3225446122932601371969463)
    ·
      refine ⟨4838169184398902057954195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3225446122932601371969463 4838169184398902057954195)
      ·
        refine ⟨7257253776598353086931293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4838169184398902057954195 7257253776598353086931293)
        ·
          refine ⟨2721470166224382407599235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7257253776598353086931293 2721470166224382407599235)
          ·
            refine ⟨4082205249336573611398853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2721470166224382407599235 4082205249336573611398853)
            ·
              refine ⟨765413484250607552137285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4082205249336573611398853 765413484250607552137285)
              ·
                refine ⟨143515028296988916025741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 765413484250607552137285 143515028296988916025741)
                ·
                  rfl

theorem cell20_943294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 4, 4].length) (baseStart_943294 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_943294 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_943294 prefixEnd_943294 := by exact prefixLift 943294
  have htrace : WordTrace (prefixWord ++ tailWord_943294) baseStart_943294 baseEnd_943294 := by
    simpa [prefixWord, tailWord_943294, baseEnd_943294] using wordTrace_append hprefix tailTrace_943294
  have hstable : (prefixWord ++ tailWord_943294).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943294).length < 2 ^ (prefixWord ++ tailWord_943294).sum := by decide
  have hdescent : baseEnd_943294 < baseStart_943294 := by decide
  rcases family_descends (prefixWord ++ tailWord_943294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943322 : List Nat := [3, 1, 1, 2, 2, 1, 1, 6, 3]
def baseStart_943322 : Nat := 118140960795 + 943322 * 2 ^ 59
def prefixEnd_943322 : Nat := 4983230072969 + 3 ^ 40 * 943322 * 2
def baseEnd_943322 : Nat := 430557864853923095143775

theorem tailTrace_943322 : CollatzResearch.WordTrace tailWord_943322 prefixEnd_943322 430557864853923095143775 := by
  unfold tailWord_943322
  simp only [CollatzResearch.WordTrace]
  refine ⟨8601444972128243854090055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22937186592341983610906813 8601444972128243854090055)
  ·
    refine ⟨12902167458192365781135083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8601444972128243854090055 12902167458192365781135083)
    ·
      refine ⟨19353251187288548671702625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12902167458192365781135083 19353251187288548671702625)
      ·
        refine ⟨14514938390466411503776969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19353251187288548671702625 14514938390466411503776969)
        ·
          refine ⟨10886203792849808627832727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14514938390466411503776969 10886203792849808627832727)
          ·
            refine ⟨16329305689274712941749091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10886203792849808627832727 16329305689274712941749091)
            ·
              refine ⟨24493958533912069412623637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16329305689274712941749091 24493958533912069412623637)
              ·
                refine ⟨1148154306277128253716733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 24493958533912069412623637 1148154306277128253716733)
                ·
                  refine ⟨430557864853923095143775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1148154306277128253716733 430557864853923095143775)
                  ·
                    rfl

theorem cell20_943322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 6, 3].length) (baseStart_943322 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_943322 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_943322 prefixEnd_943322 := by exact prefixLift 943322
  have htrace : WordTrace (prefixWord ++ tailWord_943322) baseStart_943322 baseEnd_943322 := by
    simpa [prefixWord, tailWord_943322, baseEnd_943322] using wordTrace_append hprefix tailTrace_943322
  have hstable : (prefixWord ++ tailWord_943322).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943322).length < 2 ^ (prefixWord ++ tailWord_943322).sum := by decide
  have hdescent : baseEnd_943322 < baseStart_943322 := by decide
  rcases family_descends (prefixWord ++ tailWord_943322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943335 : List Nat := [1, 1, 5, 3, 2, 2, 2, 1, 3]
def baseStart_943335 : Nat := 118140960795 + 943335 * 2 ^ 59
def prefixEnd_943335 : Nat := 4983230072969 + 3 ^ 40 * 943335 * 2
def baseEnd_943335 : Nat := 430563798408152827710389

theorem tailTrace_943335 : CollatzResearch.WordTrace tailWord_943335 prefixEnd_943335 430563798408152827710389 := by
  unfold tailWord_943335
  simp only [CollatzResearch.WordTrace]
  refine ⟨34406254037465878636583459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22937502691643919091055639 34406254037465878636583459)
  ·
    refine ⟨51609381056198817954875189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34406254037465878636583459 51609381056198817954875189)
    ·
      refine ⟨4838379474018639183269549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51609381056198817954875189 4838379474018639183269549)
      ·
        refine ⟨1814392302756989693726081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4838379474018639183269549 1814392302756989693726081)
        ·
          refine ⟨1360794227067742270294561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1814392302756989693726081 1360794227067742270294561)
          ·
            refine ⟨1020595670300806702720921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1360794227067742270294561 1020595670300806702720921)
            ·
              refine ⟨765446752725605027040691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1020595670300806702720921 765446752725605027040691)
              ·
                refine ⟨1148170129088407540561037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 765446752725605027040691 1148170129088407540561037)
                ·
                  refine ⟨430563798408152827710389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1148170129088407540561037 430563798408152827710389)
                  ·
                    rfl

theorem cell20_943335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 2, 1, 3].length) (baseStart_943335 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_943335 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_943335 prefixEnd_943335 := by exact prefixLift 943335
  have htrace : WordTrace (prefixWord ++ tailWord_943335) baseStart_943335 baseEnd_943335 := by
    simpa [prefixWord, tailWord_943335, baseEnd_943335] using wordTrace_append hprefix tailTrace_943335
  have hstable : (prefixWord ++ tailWord_943335).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943335).length < 2 ^ (prefixWord ++ tailWord_943335).sum := by decide
  have hdescent : baseEnd_943335 < baseStart_943335 := by decide
  rcases family_descends (prefixWord ++ tailWord_943335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943339 : List Nat := [1, 1, 1, 1, 2, 6, 4, 1, 3]
def baseStart_943339 : Nat := 118140960795 + 943339 * 2 ^ 59
def prefixEnd_943339 : Nat := 4983230072969 + 3 ^ 40 * 943339 * 2
def baseEnd_943339 : Nat := 430565624117146591577039

theorem tailTrace_943339 : CollatzResearch.WordTrace tailWord_943339 prefixEnd_943339 430565624117146591577039 := by
  unfold tailWord_943339
  simp only [CollatzResearch.WordTrace]
  refine ⟨34406399929451387319729071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22937599952967591546486047 34406399929451387319729071)
  ·
    refine ⟨51609599894177080979593607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34406399929451387319729071 51609599894177080979593607)
    ·
      refine ⟨77414399841265621469390411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51609599894177080979593607 77414399841265621469390411)
      ·
        refine ⟨116121599761898432204085617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77414399841265621469390411 116121599761898432204085617)
        ·
          refine ⟨87091199821423824153064213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 116121599761898432204085617 87091199821423824153064213)
          ·
            refine ⟨4082399991629241757174885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 87091199821423824153064213 4082399991629241757174885)
            ·
              refine ⟨765449998430482829470291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4082399991629241757174885 765449998430482829470291)
              ·
                refine ⟨1148174997645724244205437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 765449998430482829470291 1148174997645724244205437)
                ·
                  refine ⟨430565624117146591577039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1148174997645724244205437 430565624117146591577039)
                  ·
                    rfl

theorem cell20_943339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 4, 1, 3].length) (baseStart_943339 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_943339 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_943339 prefixEnd_943339 := by exact prefixLift 943339
  have htrace : WordTrace (prefixWord ++ tailWord_943339) baseStart_943339 baseEnd_943339 := by
    simpa [prefixWord, tailWord_943339, baseEnd_943339] using wordTrace_append hprefix tailTrace_943339
  have hstable : (prefixWord ++ tailWord_943339).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943339).length < 2 ^ (prefixWord ++ tailWord_943339).sum := by decide
  have hdescent : baseEnd_943339 < baseStart_943339 := by decide
  rcases family_descends (prefixWord ++ tailWord_943339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943374 : List Nat := [4, 1, 1, 2, 1, 11]
def baseStart_943374 : Nat := 118140960795 + 943374 * 2 ^ 59
def prefixEnd_943374 : Nat := 4983230072969 + 3 ^ 40 * 943374 * 2
def baseEnd_943374 : Nat := 15947466632253408348527

theorem tailTrace_943374 : CollatzResearch.WordTrace tailWord_943374 prefixEnd_943374 15947466632253408348527 := by
  unfold tailWord_943374
  simp only [CollatzResearch.WordTrace]
  refine ⟨4300959560540573537156647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22938450989549725531502117 4300959560540573537156647)
  ·
    refine ⟨6451439340810860305734971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4300959560540573537156647 6451439340810860305734971)
    ·
      refine ⟨9677159011216290458602457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6451439340810860305734971 9677159011216290458602457)
      ·
        refine ⟨7257869258412217843951843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9677159011216290458602457 7257869258412217843951843)
        ·
          refine ⟨10886803887618326765927765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7257869258412217843951843 10886803887618326765927765)
          ·
            refine ⟨15947466632253408348527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 10886803887618326765927765 15947466632253408348527)
            ·
              rfl

theorem cell20_943374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 11].length) (baseStart_943374 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_943374 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_943374 prefixEnd_943374 := by exact prefixLift 943374
  have htrace : WordTrace (prefixWord ++ tailWord_943374) baseStart_943374 baseEnd_943374 := by
    simpa [prefixWord, tailWord_943374, baseEnd_943374] using wordTrace_append hprefix tailTrace_943374
  have hstable : (prefixWord ++ tailWord_943374).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943374).length < 2 ^ (prefixWord ++ tailWord_943374).sum := by decide
  have hdescent : baseEnd_943374 < baseStart_943374 := by decide
  rcases family_descends (prefixWord ++ tailWord_943374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943436 : List Nat := [2, 2, 1, 3, 2, 3, 1, 1, 5]
def baseStart_943436 : Nat := 118140960795 + 943436 * 2 ^ 59
def prefixEnd_943436 : Nat := 4983230072969 + 3 ^ 40 * 943436 * 2
def baseEnd_943436 : Nat := 430609897560245365343309

theorem tailTrace_943436 : CollatzResearch.WordTrace tailWord_943436 prefixEnd_943436 430609897560245365343309 := by
  unfold tailWord_943436
  simp only [CollatzResearch.WordTrace]
  refine ⟨17204968905049986443005081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22939958540066648590673441 17204968905049986443005081)
  ·
    refine ⟨12903726678787489832253811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17204968905049986443005081 12903726678787489832253811)
    ·
      refine ⟨19355590018181234748380717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12903726678787489832253811 19355590018181234748380717)
      ·
        refine ⟨7258346256817963030642769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19355590018181234748380717 7258346256817963030642769)
        ·
          refine ⟨5443759692613472272982077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7258346256817963030642769 5443759692613472272982077)
          ·
            refine ⟨2041409884730052102368279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5443759692613472272982077 2041409884730052102368279)
            ·
              refine ⟨3062114827095078153552419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2041409884730052102368279 3062114827095078153552419)
              ·
                refine ⟨4593172240642617230328629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3062114827095078153552419 4593172240642617230328629)
                ·
                  refine ⟨430609897560245365343309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4593172240642617230328629 430609897560245365343309)
                  ·
                    rfl

theorem cell20_943436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 1, 5].length) (baseStart_943436 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_943436 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_943436 prefixEnd_943436 := by exact prefixLift 943436
  have htrace : WordTrace (prefixWord ++ tailWord_943436) baseStart_943436 baseEnd_943436 := by
    simpa [prefixWord, tailWord_943436, baseEnd_943436] using wordTrace_append hprefix tailTrace_943436
  have hstable : (prefixWord ++ tailWord_943436).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943436).length < 2 ^ (prefixWord ++ tailWord_943436).sum := by decide
  have hdescent : baseEnd_943436 < baseStart_943436 := by decide
  rcases family_descends (prefixWord ++ tailWord_943436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943443 : List Nat := [1, 1, 1, 2, 1, 1, 8, 1, 4]
def baseStart_943443 : Nat := 118140960795 + 943443 * 2 ^ 59
def prefixEnd_943443 : Nat := 4983230072969 + 3 ^ 40 * 943443 * 2
def baseEnd_943443 : Nat := 430613092550984452109947

theorem tailTrace_943443 : CollatzResearch.WordTrace tailWord_943443 prefixEnd_943443 430613092550984452109947 := by
  unfold tailWord_943443
  simp only [CollatzResearch.WordTrace]
  refine ⟨34410193121074613081514983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22940128747383075387676655 34410193121074613081514983)
  ·
    refine ⟨51615289681611919622272475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34410193121074613081514983 51615289681611919622272475)
    ·
      refine ⟨77422934522417879433408713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51615289681611919622272475 77422934522417879433408713)
      ·
        refine ⟨58067200891813409575056535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77422934522417879433408713 58067200891813409575056535)
        ·
          refine ⟨87100801337720114362584803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58067200891813409575056535 87100801337720114362584803)
          ·
            refine ⟨130651202006580171543877205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87100801337720114362584803 130651202006580171543877205)
            ·
              refine ⟨1531068773514611385279811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 130651202006580171543877205 1531068773514611385279811)
              ·
                refine ⟨2296603160271917077919717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1531068773514611385279811 2296603160271917077919717)
                ·
                  refine ⟨430613092550984452109947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2296603160271917077919717 430613092550984452109947)
                  ·
                    rfl

theorem cell20_943443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 8, 1, 4].length) (baseStart_943443 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_943443 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_943443 prefixEnd_943443 := by exact prefixLift 943443
  have htrace : WordTrace (prefixWord ++ tailWord_943443) baseStart_943443 baseEnd_943443 := by
    simpa [prefixWord, tailWord_943443, baseEnd_943443] using wordTrace_append hprefix tailTrace_943443
  have hstable : (prefixWord ++ tailWord_943443).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943443).length < 2 ^ (prefixWord ++ tailWord_943443).sum := by decide
  have hdescent : baseEnd_943443 < baseStart_943443 := by decide
  rcases family_descends (prefixWord ++ tailWord_943443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943463 : List Nat := [1, 1, 5, 1, 5, 1, 2, 4]
def baseStart_943463 : Nat := 118140960795 + 943463 * 2 ^ 59
def prefixEnd_943463 : Nat := 4983230072969 + 3 ^ 40 * 943463 * 2
def baseEnd_943463 : Nat := 143540740365317757147733

theorem tailTrace_943463 : CollatzResearch.WordTrace tailWord_943463 prefixEnd_943463 143540740365317757147733 := by
  unfold tailWord_943463
  simp only [CollatzResearch.WordTrace]
  refine ⟨34410922581002156497243043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22940615054001437664828695 34410922581002156497243043)
  ·
    refine ⟨51616383871503234745864565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34410922581002156497243043 51616383871503234745864565)
    ·
      refine ⟨4839035987953428257424803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51616383871503234745864565 4839035987953428257424803)
      ·
        refine ⟨7258553981930142386137205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4839035987953428257424803 7258553981930142386137205)
        ·
          refine ⟨680489435805950848700363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7258553981930142386137205 680489435805950848700363)
          ·
            refine ⟨1020734153708926273050545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 680489435805950848700363 1020734153708926273050545)
            ·
              refine ⟨765550615281694704787909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1020734153708926273050545 765550615281694704787909)
              ·
                refine ⟨143540740365317757147733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 765550615281694704787909 143540740365317757147733)
                ·
                  rfl

theorem cell20_943463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 2, 4].length) (baseStart_943463 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_943463 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_943463 prefixEnd_943463 := by exact prefixLift 943463
  have htrace : WordTrace (prefixWord ++ tailWord_943463) baseStart_943463 baseEnd_943463 := by
    simpa [prefixWord, tailWord_943463, baseEnd_943463] using wordTrace_append hprefix tailTrace_943463
  have hstable : (prefixWord ++ tailWord_943463).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943463).length < 2 ^ (prefixWord ++ tailWord_943463).sum := by decide
  have hdescent : baseEnd_943463 < baseStart_943463 := by decide
  rcases family_descends (prefixWord ++ tailWord_943463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943508 : List Nat := [2, 4, 2, 1, 2, 1, 4, 1, 3]
def baseStart_943508 : Nat := 118140960795 + 943508 * 2 ^ 59
def prefixEnd_943508 : Nat := 4983230072969 + 3 ^ 40 * 943508 * 2
def baseEnd_943508 : Nat := 430642760322133114943015

theorem tailTrace_943508 : CollatzResearch.WordTrace tailWord_943508 prefixEnd_943508 430642760322133114943015 := by
  unfold tailWord_943508
  simp only [CollatzResearch.WordTrace]
  refine ⟨17206281932919564591315589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22941709243892752788420785 17206281932919564591315589)
  ·
    refine ⟨3226177862422418360871673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17206281932919564591315589 3226177862422418360871673)
    ·
      refine ⟨2419633396816813770653755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3226177862422418360871673 2419633396816813770653755)
      ·
        refine ⟨3629450095225220655980633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2419633396816813770653755 3629450095225220655980633)
        ·
          refine ⟨2722087571418915491985475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3629450095225220655980633 2722087571418915491985475)
          ·
            refine ⟨4083131357128373237978213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2722087571418915491985475 4083131357128373237978213)
            ·
              refine ⟨765587129461569982120915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4083131357128373237978213 765587129461569982120915)
              ·
                refine ⟨1148380694192354973181373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 765587129461569982120915 1148380694192354973181373)
                ·
                  refine ⟨430642760322133114943015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1148380694192354973181373 430642760322133114943015)
                  ·
                    rfl

theorem cell20_943508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 4, 1, 3].length) (baseStart_943508 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_943508 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_943508 prefixEnd_943508 := by exact prefixLift 943508
  have htrace : WordTrace (prefixWord ++ tailWord_943508) baseStart_943508 baseEnd_943508 := by
    simpa [prefixWord, tailWord_943508, baseEnd_943508] using wordTrace_append hprefix tailTrace_943508
  have hstable : (prefixWord ++ tailWord_943508).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943508).length < 2 ^ (prefixWord ++ tailWord_943508).sum := by decide
  have hdescent : baseEnd_943508 < baseStart_943508 := by decide
  rcases family_descends (prefixWord ++ tailWord_943508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943574 : List Nat := [5, 2, 1, 1, 1, 2, 1, 1, 6]
def baseStart_943574 : Nat := 118140960795 + 943574 * 2 ^ 59
def prefixEnd_943574 : Nat := 4983230072969 + 3 ^ 40 * 943574 * 2
def baseEnd_943574 : Nat := 430672884520530218742745

theorem tailTrace_943574 : CollatzResearch.WordTrace tailWord_943574 prefixEnd_943574 430672884520530218742745 := by
  unfold tailWord_943574
  simp only [CollatzResearch.WordTrace]
  refine ⟨2150935692725001403408361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22943314055733348303022517 2150935692725001403408361)
  ·
    refine ⟨1613201769543751052556271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2150935692725001403408361 1613201769543751052556271)
    ·
      refine ⟨2419802654315626578834407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1613201769543751052556271 2419802654315626578834407)
      ·
        refine ⟨3629703981473439868251611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2419802654315626578834407 3629703981473439868251611)
        ·
          refine ⟨5444555972210159802377417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3629703981473439868251611 5444555972210159802377417)
          ·
            refine ⟨4083416979157619851783063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5444555972210159802377417 4083416979157619851783063)
            ·
              refine ⟨6125125468736429777674595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4083416979157619851783063 6125125468736429777674595)
              ·
                refine ⟨9187688203104644666511893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6125125468736429777674595 9187688203104644666511893)
                ·
                  refine ⟨430672884520530218742745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9187688203104644666511893 430672884520530218742745)
                  ·
                    rfl

theorem cell20_943574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_943574 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_943574 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_943574 prefixEnd_943574 := by exact prefixLift 943574
  have htrace : WordTrace (prefixWord ++ tailWord_943574) baseStart_943574 baseEnd_943574 := by
    simpa [prefixWord, tailWord_943574, baseEnd_943574] using wordTrace_append hprefix tailTrace_943574
  have hstable : (prefixWord ++ tailWord_943574).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943574).length < 2 ^ (prefixWord ++ tailWord_943574).sum := by decide
  have hdescent : baseEnd_943574 < baseStart_943574 := by decide
  rcases family_descends (prefixWord ++ tailWord_943574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943591 : List Nat := [1, 1, 5, 2, 1, 3, 2, 3, 2]
def baseStart_943591 : Nat := 118140960795 + 943591 * 2 ^ 59
def prefixEnd_943591 : Nat := 4983230072969 + 3 ^ 40 * 943591 * 2
def baseEnd_943591 : Nat := 430680643783753715176009

theorem tailTrace_943591 : CollatzResearch.WordTrace tailWord_943591 prefixEnd_943591 430680643783753715176009 := by
  unfold tailWord_943591
  simp only [CollatzResearch.WordTrace]
  refine ⟨34415591124538434357902627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22943727416358956238601751 34415591124538434357902627)
  ·
    refine ⟨51623386686807651536853941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34415591124538434357902627 51623386686807651536853941)
    ·
      refine ⟨4839692501888217331580057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51623386686807651536853941 4839692501888217331580057)
      ·
        refine ⟨3629769376416162998685043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4839692501888217331580057 3629769376416162998685043)
        ·
          refine ⟨5444654064624244498027565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3629769376416162998685043 5444654064624244498027565)
          ·
            refine ⟨2041745274234091686760337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5444654064624244498027565 2041745274234091686760337)
            ·
              refine ⟨1531308955675568765070253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2041745274234091686760337 1531308955675568765070253)
              ·
                refine ⟨574240858378338286901345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1531308955675568765070253 574240858378338286901345)
                ·
                  refine ⟨430680643783753715176009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 574240858378338286901345 430680643783753715176009)
                  ·
                    rfl

theorem cell20_943591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 2, 3, 2].length) (baseStart_943591 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_943591 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_943591 prefixEnd_943591 := by exact prefixLift 943591
  have htrace : WordTrace (prefixWord ++ tailWord_943591) baseStart_943591 baseEnd_943591 := by
    simpa [prefixWord, tailWord_943591, baseEnd_943591] using wordTrace_append hprefix tailTrace_943591
  have hstable : (prefixWord ++ tailWord_943591).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943591).length < 2 ^ (prefixWord ++ tailWord_943591).sum := by decide
  have hdescent : baseEnd_943591 < baseStart_943591 := by decide
  rcases family_descends (prefixWord ++ tailWord_943591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943605 : List Nat := [1, 3, 5, 1, 1, 2, 1, 1, 5]
def baseStart_943605 : Nat := 118140960795 + 943605 * 2 ^ 59
def prefixEnd_943605 : Nat := 4983230072969 + 3 ^ 40 * 943605 * 2
def baseEnd_943605 : Nat := 430687033765231888709285

theorem tailTrace_943605 : CollatzResearch.WordTrace tailWord_943605 prefixEnd_943605 430687033765231888709285 := by
  unfold tailWord_943605
  simp only [CollatzResearch.WordTrace]
  refine ⟨34416101746487714748912269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22944067830991809832608179 34416101746487714748912269)
  ·
    refine ⟨12906038154932893030842101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34416101746487714748912269 12906038154932893030842101)
    ·
      refine ⟨1209941077024958721641447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12906038154932893030842101 1209941077024958721641447)
      ·
        refine ⟨1814911615537438082462171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1209941077024958721641447 1814911615537438082462171)
        ·
          refine ⟨2722367423306157123693257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1814911615537438082462171 2722367423306157123693257)
          ·
            refine ⟨2041775567479617842769943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2722367423306157123693257 2041775567479617842769943)
            ·
              refine ⟨3062663351219426764154915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2041775567479617842769943 3062663351219426764154915)
              ·
                refine ⟨4593995026829140146232373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3062663351219426764154915 4593995026829140146232373)
                ·
                  refine ⟨430687033765231888709285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4593995026829140146232373 430687033765231888709285)
                  ·
                    rfl

theorem cell20_943605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 1, 5].length) (baseStart_943605 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_943605 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_943605 prefixEnd_943605 := by exact prefixLift 943605
  have htrace : WordTrace (prefixWord ++ tailWord_943605) baseStart_943605 baseEnd_943605 := by
    simpa [prefixWord, tailWord_943605, baseEnd_943605] using wordTrace_append hprefix tailTrace_943605
  have hstable : (prefixWord ++ tailWord_943605).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943605).length < 2 ^ (prefixWord ++ tailWord_943605).sum := by decide
  have hdescent : baseEnd_943605 < baseStart_943605 := by decide
  rcases family_descends (prefixWord ++ tailWord_943605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943612 : List Nat := [2, 2, 2, 1, 2, 1, 4, 4, 2]
def baseStart_943612 : Nat := 118140960795 + 943612 * 2 ^ 59
def prefixEnd_943612 : Nat := 4983230072969 + 3 ^ 40 * 943612 * 2
def baseEnd_943612 : Nat := 430690228755970975475923

theorem tailTrace_943612 : CollatzResearch.WordTrace tailWord_943612 prefixEnd_943612 430690228755970975475923 := by
  unfold tailWord_943612
  simp only [CollatzResearch.WordTrace]
  refine ⟨17208178528731177472208545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22944238038308236629611393 17208178528731177472208545)
  ·
    refine ⟨12906133896548383104156409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17208178528731177472208545 12906133896548383104156409)
    ·
      refine ⟨9679600422411287328117307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12906133896548383104156409 9679600422411287328117307)
      ·
        refine ⟨14519400633616930992175961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9679600422411287328117307 14519400633616930992175961)
        ·
          refine ⟨10889550475212698244131971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14519400633616930992175961 10889550475212698244131971)
          ·
            refine ⟨16334325712819047366197957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10889550475212698244131971 16334325712819047366197957)
            ·
              refine ⟨3062686071153571381162117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16334325712819047366197957 3062686071153571381162117)
              ·
                refine ⟨574253638341294633967897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3062686071153571381162117 574253638341294633967897)
                ·
                  refine ⟨430690228755970975475923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 574253638341294633967897 430690228755970975475923)
                  ·
                    rfl

theorem cell20_943612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 4, 2].length) (baseStart_943612 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_943612 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_943612 prefixEnd_943612 := by exact prefixLift 943612
  have htrace : WordTrace (prefixWord ++ tailWord_943612) baseStart_943612 baseEnd_943612 := by
    simpa [prefixWord, tailWord_943612, baseEnd_943612] using wordTrace_append hprefix tailTrace_943612
  have hstable : (prefixWord ++ tailWord_943612).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943612).length < 2 ^ (prefixWord ++ tailWord_943612).sum := by decide
  have hdescent : baseEnd_943612 < baseStart_943612 := by decide
  rcases family_descends (prefixWord ++ tailWord_943612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943636 : List Nat := [2, 4, 3, 1, 2, 1, 1, 6]
def baseStart_943636 : Nat := 118140960795 + 943636 * 2 ^ 59
def prefixEnd_943636 : Nat := 4983230072969 + 3 ^ 40 * 943636 * 2
def baseEnd_943636 : Nat := 143567061003311186225275

theorem tailTrace_943636 : CollatzResearch.WordTrace tailWord_943636 prefixEnd_943636 143567061003311186225275 := by
  unfold tailWord_943636
  simp only [CollatzResearch.WordTrace]
  refine ⟨17208616204687703521645381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22944821606250271362193841 17208616204687703521645381)
  ·
    refine ⟨3226615538378944410308509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17208616204687703521645381 3226615538378944410308509)
    ·
      refine ⟨1209980826892104153865691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3226615538378944410308509 1209980826892104153865691)
      ·
        refine ⟨1814971240338156230798537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1209980826892104153865691 1814971240338156230798537)
        ·
          refine ⟨1361228430253617173098903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1814971240338156230798537 1361228430253617173098903)
          ·
            refine ⟨2041842645380425759648355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1361228430253617173098903 2041842645380425759648355)
            ·
              refine ⟨3062763968070638639472533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2041842645380425759648355 3062763968070638639472533)
              ·
                refine ⟨143567061003311186225275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3062763968070638639472533 143567061003311186225275)
                ·
                  rfl

theorem cell20_943636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 1, 6].length) (baseStart_943636 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_943636 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_943636 prefixEnd_943636 := by exact prefixLift 943636
  have htrace : WordTrace (prefixWord ++ tailWord_943636) baseStart_943636 baseEnd_943636 := by
    simpa [prefixWord, tailWord_943636, baseEnd_943636] using wordTrace_append hprefix tailTrace_943636
  have hstable : (prefixWord ++ tailWord_943636).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943636).length < 2 ^ (prefixWord ++ tailWord_943636).sum := by decide
  have hdescent : baseEnd_943636 < baseStart_943636 := by decide
  rcases family_descends (prefixWord ++ tailWord_943636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943647 : List Nat := [1, 1, 2, 4, 1, 1, 3, 2, 5]
def baseStart_943647 : Nat := 118140960795 + 943647 * 2 ^ 59
def prefixEnd_943647 : Nat := 4983230072969 + 3 ^ 40 * 943647 * 2
def baseEnd_943647 : Nat := 430706203709666409309113

theorem tailTrace_943647 : CollatzResearch.WordTrace tailWord_943647 prefixEnd_943647 430706203709666409309113 := by
  unfold tailWord_943647
  simp only [CollatzResearch.WordTrace]
  refine ⟨34417633612335555921941195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22945089074890370614627463 34417633612335555921941195)
  ·
    refine ⟨51626450418503333882911793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34417633612335555921941195 51626450418503333882911793)
    ·
      refine ⟨38719837813877500412183845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51626450418503333882911793 38719837813877500412183845)
      ·
        refine ⟨7259969590102031327284471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38719837813877500412183845 7259969590102031327284471)
        ·
          refine ⟨10889954385153046990926707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7259969590102031327284471 10889954385153046990926707)
          ·
            refine ⟨16334931577729570486390061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10889954385153046990926707 16334931577729570486390061)
            ·
              refine ⟨6125599341648588932396273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16334931577729570486390061 6125599341648588932396273)
              ·
                refine ⟨4594199506236441699297205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6125599341648588932396273 4594199506236441699297205)
                ·
                  refine ⟨430706203709666409309113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4594199506236441699297205 430706203709666409309113)
                  ·
                    rfl

theorem cell20_943647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 2, 5].length) (baseStart_943647 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_943647 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_943647 prefixEnd_943647 := by exact prefixLift 943647
  have htrace : WordTrace (prefixWord ++ tailWord_943647) baseStart_943647 baseEnd_943647 := by
    simpa [prefixWord, tailWord_943647, baseEnd_943647] using wordTrace_append hprefix tailTrace_943647
  have hstable : (prefixWord ++ tailWord_943647).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943647).length < 2 ^ (prefixWord ++ tailWord_943647).sum := by decide
  have hdescent : baseEnd_943647 < baseStart_943647 := by decide
  rcases family_descends (prefixWord ++ tailWord_943647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943667 : List Nat := [1, 1, 1, 2, 4, 4, 3, 2, 2]
def baseStart_943667 : Nat := 118140960795 + 943667 * 2 ^ 59
def prefixEnd_943667 : Nat := 4983230072969 + 3 ^ 40 * 943667 * 2
def baseEnd_943667 : Nat := 430715332254635228642365

theorem tailTrace_943667 : CollatzResearch.WordTrace tailWord_943667 prefixEnd_943667 430715332254635228642365 := by
  unfold tailWord_943667
  simp only [CollatzResearch.WordTrace]
  refine ⟨34418363072263099337669255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22945575381508732891779503 34418363072263099337669255)
  ·
    refine ⟨51627544608394649006503883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34418363072263099337669255 51627544608394649006503883)
    ·
      refine ⟨77441316912591973509755825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51627544608394649006503883 77441316912591973509755825)
      ·
        refine ⟨58080987684443980132316869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77441316912591973509755825 58080987684443980132316869)
        ·
          refine ⟨10890185190833246274809413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 58080987684443980132316869 10890185190833246274809413)
          ·
            refine ⟨2041909723281233676526765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10890185190833246274809413 2041909723281233676526765)
            ·
              refine ⟨765716146230462628697537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2041909723281233676526765 765716146230462628697537)
              ·
                refine ⟨574287109672846971523153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 765716146230462628697537 574287109672846971523153)
                ·
                  refine ⟨430715332254635228642365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 574287109672846971523153 430715332254635228642365)
                  ·
                    rfl

theorem cell20_943667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 3, 2, 2].length) (baseStart_943667 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_943667 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_943667 prefixEnd_943667 := by exact prefixLift 943667
  have htrace : WordTrace (prefixWord ++ tailWord_943667) baseStart_943667 baseEnd_943667 := by
    simpa [prefixWord, tailWord_943667, baseEnd_943667] using wordTrace_append hprefix tailTrace_943667
  have hstable : (prefixWord ++ tailWord_943667).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943667).length < 2 ^ (prefixWord ++ tailWord_943667).sum := by decide
  have hdescent : baseEnd_943667 < baseStart_943667 := by decide
  rcases family_descends (prefixWord ++ tailWord_943667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943671 : List Nat := [1, 1, 3, 1, 2, 4, 3, 1, 4]
def baseStart_943671 : Nat := 118140960795 + 943671 * 2 ^ 59
def prefixEnd_943671 : Nat := 4983230072969 + 3 ^ 40 * 943671 * 2
def baseEnd_943671 : Nat := 430717157963628992509015

theorem tailTrace_943671 : CollatzResearch.WordTrace tailWord_943671 prefixEnd_943671 430717157963628992509015 := by
  unfold tailWord_943671
  simp only [CollatzResearch.WordTrace]
  refine ⟨34418508964248608020814867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22945672642832405347209911 34418508964248608020814867)
  ·
    refine ⟨51627763446372912031222301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34418508964248608020814867 51627763446372912031222301)
    ·
      refine ⟨19360411292389842011708363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51627763446372912031222301 19360411292389842011708363)
      ·
        refine ⟨29040616938584763017562545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19360411292389842011708363 29040616938584763017562545)
        ·
          refine ⟨21780462703938572263171909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29040616938584763017562545 21780462703938572263171909)
          ·
            refine ⟨4083836756988482299344733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21780462703938572263171909 4083836756988482299344733)
            ·
              refine ⟨1531438783870680862254275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4083836756988482299344733 1531438783870680862254275)
              ·
                refine ⟨2297158175806021293381413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1531438783870680862254275 2297158175806021293381413)
                ·
                  refine ⟨430717157963628992509015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2297158175806021293381413 430717157963628992509015)
                  ·
                    rfl

theorem cell20_943671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 3, 1, 4].length) (baseStart_943671 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_943671 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_943671 prefixEnd_943671 := by exact prefixLift 943671
  have htrace : WordTrace (prefixWord ++ tailWord_943671) baseStart_943671 baseEnd_943671 := by
    simpa [prefixWord, tailWord_943671, baseEnd_943671] using wordTrace_append hprefix tailTrace_943671
  have hstable : (prefixWord ++ tailWord_943671).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943671).length < 2 ^ (prefixWord ++ tailWord_943671).sum := by decide
  have hdescent : baseEnd_943671 < baseStart_943671 := by decide
  rcases family_descends (prefixWord ++ tailWord_943671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_943677 : List Nat := [1, 4, 1, 3, 4, 1, 2, 1, 3]
def baseStart_943677 : Nat := 118140960795 + 943677 * 2 ^ 59
def prefixEnd_943677 : Nat := 4983230072969 + 3 ^ 40 * 943677 * 2
def baseEnd_943677 : Nat := 430719896527119638308991

theorem tailTrace_943677 : CollatzResearch.WordTrace tailWord_943677 prefixEnd_943677 430719896527119638308991 := by
  unfold tailWord_943677
  simp only [CollatzResearch.WordTrace]
  refine ⟨34418727802226871045533285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22945818534817914030355523 34418727802226871045533285)
  ·
    refine ⟨6453511462917538321037491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34418727802226871045533285 6453511462917538321037491)
    ·
      refine ⟨9680267194376307481556237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6453511462917538321037491 9680267194376307481556237)
      ·
        refine ⟨3630100197891115305583589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9680267194376307481556237 3630100197891115305583589)
        ·
          refine ⟨680643787104584119796923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3630100197891115305583589 680643787104584119796923)
          ·
            refine ⟨1020965680656876179695385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 680643787104584119796923 1020965680656876179695385)
            ·
              refine ⟨765724260492657134771539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1020965680656876179695385 765724260492657134771539)
              ·
                refine ⟨1148586390738985702157309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 765724260492657134771539 1148586390738985702157309)
                ·
                  refine ⟨430719896527119638308991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1148586390738985702157309 430719896527119638308991)
                  ·
                    rfl

theorem cell20_943677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 2, 1, 3].length) (baseStart_943677 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_943677 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_943677 prefixEnd_943677 := by exact prefixLift 943677
  have htrace : WordTrace (prefixWord ++ tailWord_943677) baseStart_943677 baseEnd_943677 := by
    simpa [prefixWord, tailWord_943677, baseEnd_943677] using wordTrace_append hprefix tailTrace_943677
  have hstable : (prefixWord ++ tailWord_943677).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_943677).length < 2 ^ (prefixWord ++ tailWord_943677).sum := by decide
  have hdescent : baseEnd_943677 < baseStart_943677 := by decide
  rcases family_descends (prefixWord ++ tailWord_943677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
