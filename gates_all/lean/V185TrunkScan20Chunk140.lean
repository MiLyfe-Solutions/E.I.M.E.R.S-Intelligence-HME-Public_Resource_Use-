import V185TrunkScan20Chunk139

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_851236 : List Nat := [2, 3, 1, 3, 1, 1, 1, 1, 7]
def baseStart_851236 : Nat := 118140960795 + 851236 * 2 ^ 59
def prefixEnd_851236 : Nat := 4983230072969 + 3 ^ 40 * 851236 * 2
def baseEnd_851236 : Nat := 388527305253988239053549

theorem tailTrace_851236 : CollatzResearch.WordTrace tailWord_851236 prefixEnd_851236 388527305253988239053549 := by
  unfold tailWord_851236
  simp only [CollatzResearch.WordTrace]
  refine ⟨15523563772062413189826781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20698085029416550919769041 15523563772062413189826781)
  ·
    refine ⟨5821336414523404946185043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15523563772062413189826781 5821336414523404946185043)
    ·
      refine ⟨8732004621785107419277565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5821336414523404946185043 8732004621785107419277565)
      ·
        refine ⟨3274501733169415282229087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8732004621785107419277565 3274501733169415282229087)
        ·
          refine ⟨4911752599754122923343631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3274501733169415282229087 4911752599754122923343631)
          ·
            refine ⟨7367628899631184385015447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4911752599754122923343631 7367628899631184385015447)
            ·
              refine ⟨11051443349446776577523171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7367628899631184385015447 11051443349446776577523171)
              ·
                refine ⟨16577165024170164866284757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11051443349446776577523171 16577165024170164866284757)
                ·
                  refine ⟨388527305253988239053549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16577165024170164866284757 388527305253988239053549)
                  ·
                    rfl

theorem cell20_851236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 7].length) (baseStart_851236 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_851236 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_851236 prefixEnd_851236 := by exact prefixLift 851236
  have htrace : WordTrace (prefixWord ++ tailWord_851236) baseStart_851236 baseEnd_851236 := by
    simpa [prefixWord, tailWord_851236, baseEnd_851236] using wordTrace_append hprefix tailTrace_851236
  have hstable : (prefixWord ++ tailWord_851236).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851236).length < 2 ^ (prefixWord ++ tailWord_851236).sum := by decide
  have hdescent : baseEnd_851236 < baseStart_851236 := by decide
  rcases family_descends (prefixWord ++ tailWord_851236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851260 : List Nat := [2, 2, 2, 2, 1, 3, 3, 1, 4]
def baseStart_851260 : Nat := 118140960795 + 851260 * 2 ^ 59
def prefixEnd_851260 : Nat := 4983230072969 + 3 ^ 40 * 851260 * 2
def baseEnd_851260 : Nat := 388538259507950822253451

theorem tailTrace_851260 : CollatzResearch.WordTrace tailWord_851260 prefixEnd_851260 388538259507950822253451 := by
  unfold tailWord_851260
  simp only [CollatzResearch.WordTrace]
  refine ⟨15524001448018939239263617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20698668597358585652351489 15524001448018939239263617)
  ·
    refine ⟨11643001086014204429447713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15524001448018939239263617 11643001086014204429447713)
    ·
      refine ⟨8732250814510653322085785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11643001086014204429447713 8732250814510653322085785)
      ·
        refine ⟨6549188110882989991564339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8732250814510653322085785 6549188110882989991564339)
        ·
          refine ⟨9823782166324484987346509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6549188110882989991564339 9823782166324484987346509)
          ·
            refine ⟨3683918312371681870254941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9823782166324484987346509 3683918312371681870254941)
            ·
              refine ⟨1381469367139380701345603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3683918312371681870254941 1381469367139380701345603)
              ·
                refine ⟨2072204050709071052018405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1381469367139380701345603 2072204050709071052018405)
                ·
                  refine ⟨388538259507950822253451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2072204050709071052018405 388538259507950822253451)
                  ·
                    rfl

theorem cell20_851260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 3, 1, 4].length) (baseStart_851260 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_851260 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_851260 prefixEnd_851260 := by exact prefixLift 851260
  have htrace : WordTrace (prefixWord ++ tailWord_851260) baseStart_851260 baseEnd_851260 := by
    simpa [prefixWord, tailWord_851260, baseEnd_851260] using wordTrace_append hprefix tailTrace_851260
  have hstable : (prefixWord ++ tailWord_851260).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851260).length < 2 ^ (prefixWord ++ tailWord_851260).sum := by decide
  have hdescent : baseEnd_851260 < baseStart_851260 := by decide
  rcases family_descends (prefixWord ++ tailWord_851260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851281 : List Nat := [1, 2, 2, 1, 4, 1, 2, 1, 6]
def baseStart_851281 : Nat := 118140960795 + 851281 * 2 ^ 59
def prefixEnd_851281 : Nat := 4983230072969 + 3 ^ 40 * 851281 * 2
def baseEnd_851281 : Nat := 388547844480168082553365

theorem tailTrace_851281 : CollatzResearch.WordTrace tailWord_851281 prefixEnd_851281 388547844480168082553365 := by
  unfold tailWord_851281
  simp only [CollatzResearch.WordTrace]
  refine ⟨31048768828961799065041697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20699179219307866043361131 31048768828961799065041697)
  ·
    refine ⟨23286576621721349298781273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31048768828961799065041697 23286576621721349298781273)
    ·
      refine ⟨17464932466291011974085955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23286576621721349298781273 17464932466291011974085955)
      ·
        refine ⟨26197398699436517961128933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17464932466291011974085955 26197398699436517961128933)
        ·
          refine ⟨4912012256144347117711675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26197398699436517961128933 4912012256144347117711675)
          ·
            refine ⟨7368018384216520676567513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4912012256144347117711675 7368018384216520676567513)
            ·
              refine ⟨5526013788162390507425635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7368018384216520676567513 5526013788162390507425635)
              ·
                refine ⟨8289020682243585761138453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5526013788162390507425635 8289020682243585761138453)
                ·
                  refine ⟨388547844480168082553365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8289020682243585761138453 388547844480168082553365)
                  ·
                    rfl

theorem cell20_851281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 1, 6].length) (baseStart_851281 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_851281 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_851281 prefixEnd_851281 := by exact prefixLift 851281
  have htrace : WordTrace (prefixWord ++ tailWord_851281) baseStart_851281 baseEnd_851281 := by
    simpa [prefixWord, tailWord_851281, baseEnd_851281] using wordTrace_append hprefix tailTrace_851281
  have hstable : (prefixWord ++ tailWord_851281).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851281).length < 2 ^ (prefixWord ++ tailWord_851281).sum := by decide
  have hdescent : baseEnd_851281 < baseStart_851281 := by decide
  rcases family_descends (prefixWord ++ tailWord_851281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851288 : List Nat := [2, 1, 2, 2, 1, 1, 3, 8]
def baseStart_851288 : Nat := 118140960795 + 851288 * 2 ^ 59
def prefixEnd_851288 : Nat := 4983230072969 + 3 ^ 40 * 851288 * 2
def baseEnd_851288 : Nat := 129517013156969056440001

theorem tailTrace_851288 : CollatzResearch.WordTrace tailWord_851288 prefixEnd_851288 129517013156969056440001 := by
  unfold tailWord_851288
  simp only [CollatzResearch.WordTrace]
  refine ⟨15524512069968219630273259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20699349426624292840364345 15524512069968219630273259)
  ·
    refine ⟨23286768104952329445409889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15524512069968219630273259 23286768104952329445409889)
    ·
      refine ⟨17465076078714247084057417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23286768104952329445409889 17465076078714247084057417)
      ·
        refine ⟨13098807059035685313043063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17465076078714247084057417 13098807059035685313043063)
        ·
          refine ⟨19648210588553527969564595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13098807059035685313043063 19648210588553527969564595)
          ·
            refine ⟨29472315882830291954346893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19648210588553527969564595 29472315882830291954346893)
            ·
              refine ⟨11052118456061359482880085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29472315882830291954346893 11052118456061359482880085)
              ·
                refine ⟨129517013156969056440001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11052118456061359482880085 129517013156969056440001)
                ·
                  rfl

theorem cell20_851288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 8].length) (baseStart_851288 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_851288 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_851288 prefixEnd_851288 := by exact prefixLift 851288
  have htrace : WordTrace (prefixWord ++ tailWord_851288) baseStart_851288 baseEnd_851288 := by
    simpa [prefixWord, tailWord_851288, baseEnd_851288] using wordTrace_append hprefix tailTrace_851288
  have hstable : (prefixWord ++ tailWord_851288).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851288).length < 2 ^ (prefixWord ++ tailWord_851288).sum := by decide
  have hdescent : baseEnd_851288 < baseStart_851288 := by decide
  rcases family_descends (prefixWord ++ tailWord_851288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851319 : List Nat := [1, 1, 3, 1, 1, 2, 4, 3, 4]
def baseStart_851319 : Nat := 118140960795 + 851319 * 2 ^ 59
def prefixEnd_851319 : Nat := 4983230072969 + 3 ^ 40 * 851319 * 2
def baseEnd_851319 : Nat := 388565188715608839286543

theorem tailTrace_851319 : CollatzResearch.WordTrace tailWord_851319 prefixEnd_851319 388565188715608839286543 := by
  unfold tailWord_851319
  simp only [CollatzResearch.WordTrace]
  refine ⟨31050154802824131554925011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20700103201882754369950007 31050154802824131554925011)
  ·
    refine ⟨46575232204236197332387517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31050154802824131554925011 46575232204236197332387517)
    ·
      refine ⟨17465712076588573999645319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46575232204236197332387517 17465712076588573999645319)
      ·
        refine ⟨26198568114882860999467979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17465712076588573999645319 26198568114882860999467979)
        ·
          refine ⟨39297852172324291499201969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26198568114882860999467979 39297852172324291499201969)
          ·
            refine ⟨29473389129243218624401477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39297852172324291499201969 29473389129243218624401477)
            ·
              refine ⟨5526260461733103492075277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29473389129243218624401477 5526260461733103492075277)
              ·
                refine ⟨2072347673149913809528229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5526260461733103492075277 2072347673149913809528229)
                ·
                  refine ⟨388565188715608839286543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2072347673149913809528229 388565188715608839286543)
                  ·
                    rfl

theorem cell20_851319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 4].length) (baseStart_851319 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_851319 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_851319 prefixEnd_851319 := by exact prefixLift 851319
  have htrace : WordTrace (prefixWord ++ tailWord_851319) baseStart_851319 baseEnd_851319 := by
    simpa [prefixWord, tailWord_851319, baseEnd_851319] using wordTrace_append hprefix tailTrace_851319
  have hstable : (prefixWord ++ tailWord_851319).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851319).length < 2 ^ (prefixWord ++ tailWord_851319).sum := by decide
  have hdescent : baseEnd_851319 < baseStart_851319 := by decide
  rcases family_descends (prefixWord ++ tailWord_851319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851336 : List Nat := [2, 1, 3, 3, 1, 3, 1, 2, 4]
def baseStart_851336 : Nat := 118140960795 + 851336 * 2 ^ 59
def prefixEnd_851336 : Nat := 4983230072969 + 3 ^ 40 * 851336 * 2
def baseEnd_851336 : Nat := 388572947978832335719807

theorem tailTrace_851336 : CollatzResearch.WordTrace tailWord_851336 prefixEnd_851336 388572947978832335719807 := by
  unfold tailWord_851336
  simp only [CollatzResearch.WordTrace]
  refine ⟨15525387421881271729146931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20700516562508362305529241 15525387421881271729146931)
  ·
    refine ⟨23288081132821907593720397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15525387421881271729146931 23288081132821907593720397)
    ·
      refine ⟨8733030424808215347645149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23288081132821907593720397 8733030424808215347645149)
      ·
        refine ⟨3274886409303080755366931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8733030424808215347645149 3274886409303080755366931)
        ·
          refine ⟨4912329613954621133050397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3274886409303080755366931 4912329613954621133050397)
          ·
            refine ⟨1842123605232982924893899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4912329613954621133050397 1842123605232982924893899)
            ·
              refine ⟨2763185407849474387340849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1842123605232982924893899 2763185407849474387340849)
              ·
                refine ⟨2072389055887105790505637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2763185407849474387340849 2072389055887105790505637)
                ·
                  refine ⟨388572947978832335719807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2072389055887105790505637 388572947978832335719807)
                  ·
                    rfl

theorem cell20_851336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 2, 4].length) (baseStart_851336 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_851336 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_851336 prefixEnd_851336 := by exact prefixLift 851336
  have htrace : WordTrace (prefixWord ++ tailWord_851336) baseStart_851336 baseEnd_851336 := by
    simpa [prefixWord, tailWord_851336, baseEnd_851336] using wordTrace_append hprefix tailTrace_851336
  have hstable : (prefixWord ++ tailWord_851336).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851336).length < 2 ^ (prefixWord ++ tailWord_851336).sum := by decide
  have hdescent : baseEnd_851336 < baseStart_851336 := by decide
  rcases family_descends (prefixWord ++ tailWord_851336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851353 : List Nat := [1, 2, 1, 2, 1, 6, 2, 3, 2]
def baseStart_851353 : Nat := 118140960795 + 851353 * 2 ^ 59
def prefixEnd_851353 : Nat := 4983230072969 + 3 ^ 40 * 851353 * 2
def baseEnd_851353 : Nat := 388580707242055832153071

theorem tailTrace_851353 : CollatzResearch.WordTrace tailWord_851353 prefixEnd_851353 388580707242055832153071 := by
  unfold tailWord_851353
  simp only [CollatzResearch.WordTrace]
  refine ⟨31051394884700955361662713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20700929923133970241108475 31051394884700955361662713)
  ·
    refine ⟨23288546163525716521247035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31051394884700955361662713 23288546163525716521247035)
    ·
      refine ⟨34932819245288574781870553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23288546163525716521247035 34932819245288574781870553)
      ·
        refine ⟨26199614433966431086402915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34932819245288574781870553 26199614433966431086402915)
        ·
          refine ⟨39299421650949646629604373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26199614433966431086402915 39299421650949646629604373)
          ·
            refine ⟨1842160389888264685762705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 39299421650949646629604373 1842160389888264685762705)
            ·
              refine ⟨1381620292416198514322029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1842160389888264685762705 1381620292416198514322029)
              ·
                refine ⟨518107609656074442870761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1381620292416198514322029 518107609656074442870761)
                ·
                  refine ⟨388580707242055832153071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 518107609656074442870761 388580707242055832153071)
                  ·
                    rfl

theorem cell20_851353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 2, 3, 2].length) (baseStart_851353 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_851353 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_851353 prefixEnd_851353 := by exact prefixLift 851353
  have htrace : WordTrace (prefixWord ++ tailWord_851353) baseStart_851353 baseEnd_851353 := by
    simpa [prefixWord, tailWord_851353, baseEnd_851353] using wordTrace_append hprefix tailTrace_851353
  have hstable : (prefixWord ++ tailWord_851353).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851353).length < 2 ^ (prefixWord ++ tailWord_851353).sum := by decide
  have hdescent : baseEnd_851353 < baseStart_851353 := by decide
  rcases family_descends (prefixWord ++ tailWord_851353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851395 : List Nat := [1, 1, 1, 3, 1, 1, 6, 2, 4]
def baseStart_851395 : Nat := 118140960795 + 851395 * 2 ^ 59
def prefixEnd_851395 : Nat := 4983230072969 + 3 ^ 40 * 851395 * 2
def baseEnd_851395 : Nat := 388599877186490352752899

theorem tailTrace_851395 : CollatzResearch.WordTrace tailWord_851395 prefixEnd_851395 388599877186490352752899 := by
  unfold tailWord_851395
  simp only [CollatzResearch.WordTrace]
  refine ⟨31052926750548796534691639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20701951167032531023127759 31052926750548796534691639)
  ·
    refine ⟨46579390125823194802037459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31052926750548796534691639 46579390125823194802037459)
    ·
      refine ⟨69869085188734792203056189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46579390125823194802037459 69869085188734792203056189)
      ·
        refine ⟨26200906945775547076146071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69869085188734792203056189 26200906945775547076146071)
        ·
          refine ⟨39301360418663320614219107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26200906945775547076146071 39301360418663320614219107)
          ·
            refine ⟨58952040627994980921328661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39301360418663320614219107 58952040627994980921328661)
            ·
              refine ⟨2763376904437264730687281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 58952040627994980921328661 2763376904437264730687281)
              ·
                refine ⟨2072532678327948548015461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2763376904437264730687281 2072532678327948548015461)
                ·
                  refine ⟨388599877186490352752899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2072532678327948548015461 388599877186490352752899)
                  ·
                    rfl

theorem cell20_851395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 2, 4].length) (baseStart_851395 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_851395 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_851395 prefixEnd_851395 := by exact prefixLift 851395
  have htrace : WordTrace (prefixWord ++ tailWord_851395) baseStart_851395 baseEnd_851395 := by
    simpa [prefixWord, tailWord_851395, baseEnd_851395] using wordTrace_append hprefix tailTrace_851395
  have hstable : (prefixWord ++ tailWord_851395).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851395).length < 2 ^ (prefixWord ++ tailWord_851395).sum := by decide
  have hdescent : baseEnd_851395 < baseStart_851395 := by decide
  rcases family_descends (prefixWord ++ tailWord_851395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851429 : List Nat := [1, 3, 1, 5, 1, 3, 1, 1, 4]
def baseStart_851429 : Nat := 118140960795 + 851429 * 2 ^ 59
def prefixEnd_851429 : Nat := 4983230072969 + 3 ^ 40 * 851429 * 2
def baseEnd_851429 : Nat := 388615395712937345619427

theorem tailTrace_851429 : CollatzResearch.WordTrace tailWord_851429 prefixEnd_851429 388615395712937345619427 := by
  unfold tailWord_851429
  simp only [CollatzResearch.WordTrace]
  refine ⟨31054166832425620341429341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20702777888283746894286227 31054166832425620341429341)
  ·
    refine ⟨11645312562159607628036003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31054166832425620341429341 11645312562159607628036003)
    ·
      refine ⟨17467968843239411442054005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11645312562159607628036003 17467968843239411442054005)
      ·
        refine ⟨1637622079053694822692563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17467968843239411442054005 1637622079053694822692563)
        ·
          refine ⟨2456433118580542234038845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1637622079053694822692563 2456433118580542234038845)
          ·
            refine ⟨921162419467703337764567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2456433118580542234038845 921162419467703337764567)
            ·
              refine ⟨1381743629201555006646851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 921162419467703337764567 1381743629201555006646851)
              ·
                refine ⟨2072615443802332509970277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1381743629201555006646851 2072615443802332509970277)
                ·
                  refine ⟨388615395712937345619427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2072615443802332509970277 388615395712937345619427)
                  ·
                    rfl

theorem cell20_851429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 1, 1, 4].length) (baseStart_851429 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_851429 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_851429 prefixEnd_851429 := by exact prefixLift 851429
  have htrace : WordTrace (prefixWord ++ tailWord_851429) baseStart_851429 baseEnd_851429 := by
    simpa [prefixWord, tailWord_851429, baseEnd_851429] using wordTrace_append hprefix tailTrace_851429
  have hstable : (prefixWord ++ tailWord_851429).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851429).length < 2 ^ (prefixWord ++ tailWord_851429).sum := by decide
  have hdescent : baseEnd_851429 < baseStart_851429 := by decide
  rcases family_descends (prefixWord ++ tailWord_851429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851440 : List Nat := [2, 1, 1, 1, 3, 4, 1, 7]
def baseStart_851440 : Nat := 118140960795 + 851440 * 2 ^ 59
def prefixEnd_851440 : Nat := 4983230072969 + 3 ^ 40 * 851440 * 2
def baseEnd_851440 : Nat := 129540138804223398750905

theorem tailTrace_851440 : CollatzResearch.WordTrace tailWord_851440 prefixEnd_851440 129540138804223398750905 := by
  unfold tailWord_851440
  simp only [CollatzResearch.WordTrace]
  refine ⟨15527284017692884610039887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20703045356923846146719849 15527284017692884610039887)
  ·
    refine ⟨23290926026539326915059831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15527284017692884610039887 23290926026539326915059831)
    ·
      refine ⟨34936389039808990372589747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23290926026539326915059831 34936389039808990372589747)
      ·
        refine ⟨52404583559713485558884621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34936389039808990372589747 52404583559713485558884621)
        ·
          refine ⟨19651718834892557084581733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52404583559713485558884621 19651718834892557084581733)
          ·
            refine ⟨3684697281542354453359075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19651718834892557084581733 3684697281542354453359075)
            ·
              refine ⟨5527045922313531680038613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3684697281542354453359075 5527045922313531680038613)
              ·
                refine ⟨129540138804223398750905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5527045922313531680038613 129540138804223398750905)
                ·
                  rfl

theorem cell20_851440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 7].length) (baseStart_851440 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_851440 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_851440 prefixEnd_851440 := by exact prefixLift 851440
  have htrace : WordTrace (prefixWord ++ tailWord_851440) baseStart_851440 baseEnd_851440 := by
    simpa [prefixWord, tailWord_851440, baseEnd_851440] using wordTrace_append hprefix tailTrace_851440
  have hstable : (prefixWord ++ tailWord_851440).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851440).length < 2 ^ (prefixWord ++ tailWord_851440).sum := by decide
  have hdescent : baseEnd_851440 < baseStart_851440 := by decide
  rcases family_descends (prefixWord ++ tailWord_851440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851447 : List Nat := [1, 1, 3, 1, 1, 1, 1, 4, 7]
def baseStart_851447 : Nat := 118140960795 + 851447 * 2 ^ 59
def prefixEnd_851447 : Nat := 4983230072969 + 3 ^ 40 * 851447 * 2
def baseEnd_851447 : Nat := 388623611403409283019353

theorem tailTrace_851447 : CollatzResearch.WordTrace tailWord_851447 prefixEnd_851447 388623611403409283019353 := by
  unfold tailWord_851447
  simp only [CollatzResearch.WordTrace]
  refine ⟨31054823346360409415584595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20703215564240272943723063 31054823346360409415584595)
  ·
    refine ⟨46582235019540614123376893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31054823346360409415584595 46582235019540614123376893)
    ·
      refine ⟨17468338132327730296266335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46582235019540614123376893 17468338132327730296266335)
      ·
        refine ⟨26202507198491595444399503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17468338132327730296266335 26202507198491595444399503)
        ·
          refine ⟨39303760797737393166599255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26202507198491595444399503 39303760797737393166599255)
          ·
            refine ⟨58955641196606089749898883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39303760797737393166599255 58955641196606089749898883)
            ·
              refine ⟨88433461794909134624848325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58955641196606089749898883 88433461794909134624848325)
              ·
                refine ⟨16581274086545462742159061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88433461794909134624848325 16581274086545462742159061)
                ·
                  refine ⟨388623611403409283019353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16581274086545462742159061 388623611403409283019353)
                  ·
                    rfl

theorem cell20_851447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 7].length) (baseStart_851447 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_851447 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_851447 prefixEnd_851447 := by exact prefixLift 851447
  have htrace : WordTrace (prefixWord ++ tailWord_851447) baseStart_851447 baseEnd_851447 := by
    simpa [prefixWord, tailWord_851447, baseEnd_851447] using wordTrace_append hprefix tailTrace_851447
  have hstable : (prefixWord ++ tailWord_851447).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851447).length < 2 ^ (prefixWord ++ tailWord_851447).sum := by decide
  have hdescent : baseEnd_851447 < baseStart_851447 := by decide
  rcases family_descends (prefixWord ++ tailWord_851447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851509 : List Nat := [1, 3, 3, 1, 1, 3, 1, 1, 6]
def baseStart_851509 : Nat := 118140960795 + 851509 * 2 ^ 59
def prefixEnd_851509 : Nat := 4983230072969 + 3 ^ 40 * 851509 * 2
def baseEnd_851509 : Nat := 388651909892812622952433

theorem tailTrace_851509 : CollatzResearch.WordTrace tailWord_851509 prefixEnd_851509 388651909892812622952433 := by
  unfold tailWord_851509
  simp only [CollatzResearch.WordTrace]
  refine ⟨31057084672135794004341581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20704723114757196002894387 31057084672135794004341581)
  ·
    refine ⟨11646406752050922751628093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31057084672135794004341581 11646406752050922751628093)
    ·
      refine ⟨4367402532019096031860535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11646406752050922751628093 4367402532019096031860535)
      ·
        refine ⟨6551103798028644047790803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4367402532019096031860535 6551103798028644047790803)
        ·
          refine ⟨9826655697042966071686205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6551103798028644047790803 9826655697042966071686205)
          ·
            refine ⟨3684995886391112276882327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9826655697042966071686205 3684995886391112276882327)
            ·
              refine ⟨5527493829586668415323491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3684995886391112276882327 5527493829586668415323491)
              ·
                refine ⟨8291240744380002622985237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5527493829586668415323491 8291240744380002622985237)
                ·
                  refine ⟨388651909892812622952433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8291240744380002622985237 388651909892812622952433)
                  ·
                    rfl

theorem cell20_851509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 1, 6].length) (baseStart_851509 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_851509 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_851509 prefixEnd_851509 := by exact prefixLift 851509
  have htrace : WordTrace (prefixWord ++ tailWord_851509) baseStart_851509 baseEnd_851509 := by
    simpa [prefixWord, tailWord_851509, baseEnd_851509] using wordTrace_append hprefix tailTrace_851509
  have hstable : (prefixWord ++ tailWord_851509).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851509).length < 2 ^ (prefixWord ++ tailWord_851509).sum := by decide
  have hdescent : baseEnd_851509 < baseStart_851509 := by decide
  rcases family_descends (prefixWord ++ tailWord_851509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851540 : List Nat := [2, 4, 1, 1, 1, 2, 3, 1, 5]
def baseStart_851540 : Nat := 118140960795 + 851540 * 2 ^ 59
def prefixEnd_851540 : Nat := 4983230072969 + 3 ^ 40 * 851540 * 2
def baseEnd_851540 : Nat := 388666059137514292918973

theorem tailTrace_851540 : CollatzResearch.WordTrace tailWord_851540 prefixEnd_851540 388666059137514292918973 := by
  unfold tailWord_851540
  simp only [CollatzResearch.WordTrace]
  refine ⟨15529107667511743149360037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20705476890015657532480049 15529107667511743149360037)
  ·
    refine ⟨2911707687658451840505007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15529107667511743149360037 2911707687658451840505007)
    ·
      refine ⟨4367561531487677760757511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2911707687658451840505007 4367561531487677760757511)
      ·
        refine ⟨6551342297231516641136267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4367561531487677760757511 6551342297231516641136267)
        ·
          refine ⟨9827013445847274961704401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6551342297231516641136267 9827013445847274961704401)
          ·
            refine ⟨7370260084385456221278301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9827013445847274961704401 7370260084385456221278301)
            ·
              refine ⟨2763847531644546082979363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7370260084385456221278301 2763847531644546082979363)
              ·
                refine ⟨4145771297466819124469045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2763847531644546082979363 4145771297466819124469045)
                ·
                  refine ⟨388666059137514292918973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4145771297466819124469045 388666059137514292918973)
                  ·
                    rfl

theorem cell20_851540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_851540 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_851540 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_851540 prefixEnd_851540 := by exact prefixLift 851540
  have htrace : WordTrace (prefixWord ++ tailWord_851540) baseStart_851540 baseEnd_851540 := by
    simpa [prefixWord, tailWord_851540, baseEnd_851540] using wordTrace_append hprefix tailTrace_851540
  have hstable : (prefixWord ++ tailWord_851540).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851540).length < 2 ^ (prefixWord ++ tailWord_851540).sum := by decide
  have hdescent : baseEnd_851540 < baseStart_851540 := by decide
  rcases family_descends (prefixWord ++ tailWord_851540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851581 : List Nat := [1, 4, 1, 1, 4, 1, 3, 3, 2]
def baseStart_851581 : Nat := 118140960795 + 851581 * 2 ^ 59
def prefixEnd_851581 : Nat := 4983230072969 + 3 ^ 40 * 851581 * 2
def baseEnd_851581 : Nat := 388684772654700372552139

theorem tailTrace_851581 : CollatzResearch.WordTrace tailWord_851581 prefixEnd_851581 388684772654700372552139 := by
  unfold tailWord_851581
  simp only [CollatzResearch.WordTrace]
  refine ⟨31059710727874950300962597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20706473818583300200641731 31059710727874950300962597)
  ·
    refine ⟨5823695761476553181430487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31059710727874950300962597 5823695761476553181430487)
    ·
      refine ⟨8735543642214829772145731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5823695761476553181430487 8735543642214829772145731)
      ·
        refine ⟨13103315463322244658218597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8735543642214829772145731 13103315463322244658218597)
        ·
          refine ⟨2456871649372920873415987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13103315463322244658218597 2456871649372920873415987)
          ·
            refine ⟨3685307474059381310123981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2456871649372920873415987 3685307474059381310123981)
            ·
              refine ⟨1381990302772267991296493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3685307474059381310123981 1381990302772267991296493)
              ·
                refine ⟨518246363539600496736185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1381990302772267991296493 518246363539600496736185)
                ·
                  refine ⟨388684772654700372552139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 518246363539600496736185 388684772654700372552139)
                  ·
                    rfl

theorem cell20_851581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 3, 3, 2].length) (baseStart_851581 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_851581 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_851581 prefixEnd_851581 := by exact prefixLift 851581
  have htrace : WordTrace (prefixWord ++ tailWord_851581) baseStart_851581 baseEnd_851581 := by
    simpa [prefixWord, tailWord_851581, baseEnd_851581] using wordTrace_append hprefix tailTrace_851581
  have hstable : (prefixWord ++ tailWord_851581).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851581).length < 2 ^ (prefixWord ++ tailWord_851581).sum := by decide
  have hdescent : baseEnd_851581 < baseStart_851581 := by decide
  rcases family_descends (prefixWord ++ tailWord_851581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851588 : List Nat := [2, 3, 2, 1, 5, 1, 6]
def baseStart_851588 : Nat := 118140960795 + 851588 * 2 ^ 59
def prefixEnd_851588 : Nat := 4983230072969 + 3 ^ 40 * 851588 * 2
def baseEnd_851588 : Nat := 43187551960604384368753

theorem tailTrace_851588 : CollatzResearch.WordTrace tailWord_851588 prefixEnd_851588 43187551960604384368753 := by
  unfold tailWord_851588
  simp only [CollatzResearch.WordTrace]
  refine ⟨15529983019424795248233709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20706644025899726997644945 15529983019424795248233709)
  ·
    refine ⟨5823743632284298218087641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15529983019424795248233709 5823743632284298218087641)
    ·
      refine ⟨4367807724213223663565731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5823743632284298218087641 4367807724213223663565731)
      ·
        refine ⟨6551711586319835495348597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4367807724213223663565731 6551711586319835495348597)
        ·
          refine ⟨614222961217484577688931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6551711586319835495348597 614222961217484577688931)
          ·
            refine ⟨921334441826226866533397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 614222961217484577688931 921334441826226866533397)
            ·
              refine ⟨43187551960604384368753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 921334441826226866533397 43187551960604384368753)
              ·
                rfl

theorem cell20_851588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 6].length) (baseStart_851588 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_851588 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_851588 prefixEnd_851588 := by exact prefixLift 851588
  have htrace : WordTrace (prefixWord ++ tailWord_851588) baseStart_851588 baseEnd_851588 := by
    simpa [prefixWord, tailWord_851588, baseEnd_851588] using wordTrace_append hprefix tailTrace_851588
  have hstable : (prefixWord ++ tailWord_851588).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851588).length < 2 ^ (prefixWord ++ tailWord_851588).sum := by decide
  have hdescent : baseEnd_851588 < baseStart_851588 := by decide
  rcases family_descends (prefixWord ++ tailWord_851588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851598 : List Nat := [4, 1, 1, 3, 1, 3, 3, 2, 2]
def baseStart_851598 : Nat := 118140960795 + 851598 * 2 ^ 59
def prefixEnd_851598 : Nat := 4983230072969 + 3 ^ 40 * 851598 * 2
def baseEnd_851598 : Nat := 388692531917923868985403

theorem tailTrace_851598 : CollatzResearch.WordTrace tailWord_851598 prefixEnd_851598 388692531917923868985403 := by
  unfold tailWord_851598
  simp only [CollatzResearch.WordTrace]
  refine ⟨3882541346101670275541431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20706887179208908136220965 3882541346101670275541431)
  ·
    refine ⟨5823812019152505413312147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3882541346101670275541431 5823812019152505413312147)
    ·
      refine ⟨8735718028728758119968221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5823812019152505413312147 8735718028728758119968221)
      ·
        refine ⟨3275894260773284294988083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8735718028728758119968221 3275894260773284294988083)
        ·
          refine ⟨4913841391159926442482125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3275894260773284294988083 4913841391159926442482125)
          ·
            refine ⟨1842690521684972415930797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4913841391159926442482125 1842690521684972415930797)
            ·
              refine ⟨691008945631864655974049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1842690521684972415930797 691008945631864655974049)
              ·
                refine ⟨518256709223898491980537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 691008945631864655974049 518256709223898491980537)
                ·
                  refine ⟨388692531917923868985403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 518256709223898491980537 388692531917923868985403)
                  ·
                    rfl

theorem cell20_851598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 3, 2, 2].length) (baseStart_851598 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_851598 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_851598 prefixEnd_851598 := by exact prefixLift 851598
  have htrace : WordTrace (prefixWord ++ tailWord_851598) baseStart_851598 baseEnd_851598 := by
    simpa [prefixWord, tailWord_851598, baseEnd_851598] using wordTrace_append hprefix tailTrace_851598
  have hstable : (prefixWord ++ tailWord_851598).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851598).length < 2 ^ (prefixWord ++ tailWord_851598).sum := by decide
  have hdescent : baseEnd_851598 < baseStart_851598 := by decide
  rcases family_descends (prefixWord ++ tailWord_851598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851685 : List Nat := [1, 3, 1, 4, 1, 1, 5, 4]
def baseStart_851685 : Nat := 118140960795 + 851685 * 2 ^ 59
def prefixEnd_851685 : Nat := 4983230072969 + 3 ^ 40 * 851685 * 2
def baseEnd_851685 : Nat := 129577413696179411028349

theorem tailTrace_851685 : CollatzResearch.WordTrace tailWord_851685 prefixEnd_851685 129577413696179411028349 := by
  unfold tailWord_851685
  simp only [CollatzResearch.WordTrace]
  refine ⟨31063503919498176062748509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20709002612998784041832339 31063503919498176062748509)
  ·
    refine ⟨11648813969811816023530691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31063503919498176062748509 11648813969811816023530691)
    ·
      refine ⟨17473220954717724035296037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11648813969811816023530691 17473220954717724035296037)
      ·
        refine ⟨3276228929009573256618007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17473220954717724035296037 3276228929009573256618007)
        ·
          refine ⟨4914343393514359884927011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3276228929009573256618007 4914343393514359884927011)
          ·
            refine ⟨7371515090271539827390517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4914343393514359884927011 7371515090271539827390517)
            ·
              refine ⟨691079539712956858817861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7371515090271539827390517 691079539712956858817861)
              ·
                refine ⟨129577413696179411028349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 691079539712956858817861 129577413696179411028349)
                ·
                  rfl

theorem cell20_851685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 5, 4].length) (baseStart_851685 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_851685 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_851685 prefixEnd_851685 := by exact prefixLift 851685
  have htrace : WordTrace (prefixWord ++ tailWord_851685) baseStart_851685 baseEnd_851685 := by
    simpa [prefixWord, tailWord_851685, baseEnd_851685] using wordTrace_append hprefix tailTrace_851685
  have hstable : (prefixWord ++ tailWord_851685).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851685).length < 2 ^ (prefixWord ++ tailWord_851685).sum := by decide
  have hdescent : baseEnd_851685 < baseStart_851685 := by decide
  rcases family_descends (prefixWord ++ tailWord_851685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851716 : List Nat := [2, 3, 2, 2, 1, 3, 2, 1, 4]
def baseStart_851716 : Nat := 118140960795 + 851716 * 2 ^ 59
def prefixEnd_851716 : Nat := 4983230072969 + 3 ^ 40 * 851716 * 2
def baseEnd_851716 : Nat := 388746390333239903051587

theorem tailTrace_851716 : CollatzResearch.WordTrace tailWord_851716 prefixEnd_851716 388746390333239903051587 := by
  unfold tailWord_851716
  simp only [CollatzResearch.WordTrace]
  refine ⟨15532317291192934178563501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20709756388257245571418001 15532317291192934178563501)
  ·
    refine ⟨5824618984197350316961313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15532317291192934178563501 5824618984197350316961313)
    ·
      refine ⟨4368464238148012737720985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5824618984197350316961313 4368464238148012737720985)
      ·
        refine ⟨3276348178611009553290739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4368464238148012737720985 3276348178611009553290739)
        ·
          refine ⟨4914522267916514329936109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3276348178611009553290739 4914522267916514329936109)
          ·
            refine ⟨1842945850468692873726041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4914522267916514329936109 1842945850468692873726041)
            ·
              refine ⟨1382209387851519655294531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1842945850468692873726041 1382209387851519655294531)
              ·
                refine ⟨2073314081777279482941797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1382209387851519655294531 2073314081777279482941797)
                ·
                  refine ⟨388746390333239903051587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2073314081777279482941797 388746390333239903051587)
                  ·
                    rfl

theorem cell20_851716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 2, 1, 4].length) (baseStart_851716 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_851716 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_851716 prefixEnd_851716 := by exact prefixLift 851716
  have htrace : WordTrace (prefixWord ++ tailWord_851716) baseStart_851716 baseEnd_851716 := by
    simpa [prefixWord, tailWord_851716, baseEnd_851716] using wordTrace_append hprefix tailTrace_851716
  have hstable : (prefixWord ++ tailWord_851716).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851716).length < 2 ^ (prefixWord ++ tailWord_851716).sum := by decide
  have hdescent : baseEnd_851716 < baseStart_851716 := by decide
  rcases family_descends (prefixWord ++ tailWord_851716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851718 : List Nat := [6, 2, 2, 1, 1, 1, 3, 1, 3]
def baseStart_851718 : Nat := 118140960795 + 851718 * 2 ^ 59
def prefixEnd_851718 : Nat := 4983230072969 + 3 ^ 40 * 851718 * 2
def baseEnd_851718 : Nat := 388747303187736784984913

theorem tailTrace_851718 : CollatzResearch.WordTrace tailWord_851718 prefixEnd_851718 388747303187736784984913 := by
  unfold tailWord_851718
  simp only [CollatzResearch.WordTrace]
  refine ⟨970772110261831959334369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 20709805018919081799133205 970772110261831959334369)
  ·
    refine ⟨728079082696373969500777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 970772110261831959334369 728079082696373969500777)
    ·
      refine ⟨546059312022280477125583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 728079082696373969500777 546059312022280477125583)
      ·
        refine ⟨819088968033420715688375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 546059312022280477125583 819088968033420715688375)
        ·
          refine ⟨1228633452050131073532563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 819088968033420715688375 1228633452050131073532563)
          ·
            refine ⟨1842950178075196610298845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1228633452050131073532563 1842950178075196610298845)
            ·
              refine ⟨691106316778198728862067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1842950178075196610298845 691106316778198728862067)
              ·
                refine ⟨1036659475167298093293101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 691106316778198728862067 1036659475167298093293101)
                ·
                  refine ⟨388747303187736784984913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1036659475167298093293101 388747303187736784984913)
                  ·
                    rfl

theorem cell20_851718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_851718 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_851718 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_851718 prefixEnd_851718 := by exact prefixLift 851718
  have htrace : WordTrace (prefixWord ++ tailWord_851718) baseStart_851718 baseEnd_851718 := by
    simpa [prefixWord, tailWord_851718, baseEnd_851718] using wordTrace_append hprefix tailTrace_851718
  have hstable : (prefixWord ++ tailWord_851718).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851718).length < 2 ^ (prefixWord ++ tailWord_851718).sum := by decide
  have hdescent : baseEnd_851718 < baseStart_851718 := by decide
  rcases family_descends (prefixWord ++ tailWord_851718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851744 : List Nat := [2, 1, 1, 5, 1, 1, 3, 6]
def baseStart_851744 : Nat := 118140960795 + 851744 * 2 ^ 59
def prefixEnd_851744 : Nat := 4983230072969 + 3 ^ 40 * 851744 * 2
def baseEnd_851744 : Nat := 129586390098732083372713

theorem tailTrace_851744 : CollatzResearch.WordTrace tailWord_851744 prefixEnd_851744 129586390098732083372713 := by
  unfold tailWord_851744
  simp only [CollatzResearch.WordTrace]
  refine ⟨15532827913142214569573143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20710437217522952759430857 15532827913142214569573143)
  ·
    refine ⟨23299241869713321854359715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15532827913142214569573143 23299241869713321854359715)
    ·
      refine ⟨34948862804569982781539573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23299241869713321854359715 34948862804569982781539573)
      ·
        refine ⟨3276455887928435885769335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34948862804569982781539573 3276455887928435885769335)
        ·
          refine ⟨4914683831892653828654003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3276455887928435885769335 4914683831892653828654003)
          ·
            refine ⟨7372025747838980742981005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4914683831892653828654003 7372025747838980742981005)
            ·
              refine ⟨2764509655439617778617877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7372025747838980742981005 2764509655439617778617877)
              ·
                refine ⟨129586390098732083372713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2764509655439617778617877 129586390098732083372713)
                ·
                  rfl

theorem cell20_851744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 6].length) (baseStart_851744 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_851744 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_851744 prefixEnd_851744 := by exact prefixLift 851744
  have htrace : WordTrace (prefixWord ++ tailWord_851744) baseStart_851744 baseEnd_851744 := by
    simpa [prefixWord, tailWord_851744, baseEnd_851744] using wordTrace_append hprefix tailTrace_851744
  have hstable : (prefixWord ++ tailWord_851744).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851744).length < 2 ^ (prefixWord ++ tailWord_851744).sum := by decide
  have hdescent : baseEnd_851744 < baseStart_851744 := by decide
  rcases family_descends (prefixWord ++ tailWord_851744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851844 : List Nat := [2, 3, 2, 1, 1, 1, 4, 3, 3]
def baseStart_851844 : Nat := 118140960795 + 851844 * 2 ^ 59
def prefixEnd_851844 : Nat := 4983230072969 + 3 ^ 40 * 851844 * 2
def baseEnd_851844 : Nat := 388804813021040346784397

theorem tailTrace_851844 : CollatzResearch.WordTrace tailWord_851844 prefixEnd_851844 388804813021040346784397 := by
  unfold tailWord_851844
  simp only [CollatzResearch.WordTrace]
  refine ⟨15534651562961073108893293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20712868750614764145191057 15534651562961073108893293)
  ·
    refine ⟨5825494336110402415834985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15534651562961073108893293 5825494336110402415834985)
    ·
      refine ⟨4369120752082801811876239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5825494336110402415834985 4369120752082801811876239)
      ·
        refine ⟨6553681128124202717814359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4369120752082801811876239 6553681128124202717814359)
        ·
          refine ⟨9830521692186304076721539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6553681128124202717814359 9830521692186304076721539)
          ·
            refine ⟨14745782538279456115082309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9830521692186304076721539 14745782538279456115082309)
            ·
              refine ⟨2764834225927398021577933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14745782538279456115082309 2764834225927398021577933)
              ·
                refine ⟨1036812834722774258091725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2764834225927398021577933 1036812834722774258091725)
                ·
                  refine ⟨388804813021040346784397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1036812834722774258091725 388804813021040346784397)
                  ·
                    rfl

theorem cell20_851844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 3, 3].length) (baseStart_851844 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_851844 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_851844 prefixEnd_851844 := by exact prefixLift 851844
  have htrace : WordTrace (prefixWord ++ tailWord_851844) baseStart_851844 baseEnd_851844 := by
    simpa [prefixWord, tailWord_851844, baseEnd_851844] using wordTrace_append hprefix tailTrace_851844
  have hstable : (prefixWord ++ tailWord_851844).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851844).length < 2 ^ (prefixWord ++ tailWord_851844).sum := by decide
  have hdescent : baseEnd_851844 < baseStart_851844 := by decide
  rcases family_descends (prefixWord ++ tailWord_851844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851864 : List Nat := [2, 1, 2, 6, 1, 1, 2, 3, 2]
def baseStart_851864 : Nat := 118140960795 + 851864 * 2 ^ 59
def prefixEnd_851864 : Nat := 4983230072969 + 3 ^ 40 * 851864 * 2
def baseEnd_851864 : Nat := 388813941566009166117649

theorem tailTrace_851864 : CollatzResearch.WordTrace tailWord_851864 prefixEnd_851864 388813941566009166117649 := by
  unfold tailWord_851864
  simp only [CollatzResearch.WordTrace]
  refine ⟨15535016292924844816757323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20713355057233126422343097 15535016292924844816757323)
  ·
    refine ⟨23302524439387267225135985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15535016292924844816757323 23302524439387267225135985)
    ·
      refine ⟨17476893329540450418851989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23302524439387267225135985 17476893329540450418851989)
      ·
        refine ⟨819229374822208613383687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 17476893329540450418851989 819229374822208613383687)
        ·
          refine ⟨1228844062233312920075531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 819229374822208613383687 1228844062233312920075531)
          ·
            refine ⟨1843266093349969380113297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1228844062233312920075531 1843266093349969380113297)
            ·
              refine ⟨1382449570012477035084973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1843266093349969380113297 1382449570012477035084973)
              ·
                refine ⟨518418588754678888156865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1382449570012477035084973 518418588754678888156865)
                ·
                  refine ⟨388813941566009166117649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 518418588754678888156865 388813941566009166117649)
                  ·
                    rfl

theorem cell20_851864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 2, 3, 2].length) (baseStart_851864 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_851864 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_851864 prefixEnd_851864 := by exact prefixLift 851864
  have htrace : WordTrace (prefixWord ++ tailWord_851864) baseStart_851864 baseEnd_851864 := by
    simpa [prefixWord, tailWord_851864, baseEnd_851864] using wordTrace_append hprefix tailTrace_851864
  have hstable : (prefixWord ++ tailWord_851864).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851864).length < 2 ^ (prefixWord ++ tailWord_851864).sum := by decide
  have hdescent : baseEnd_851864 < baseStart_851864 := by decide
  rcases family_descends (prefixWord ++ tailWord_851864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851872 : List Nat := [2, 1, 1, 4, 1, 1, 1, 1, 8]
def baseStart_851872 : Nat := 118140960795 + 851872 * 2 ^ 59
def prefixEnd_851872 : Nat := 4983230072969 + 3 ^ 40 * 851872 * 2
def baseEnd_851872 : Nat := 388817592983996693850949

theorem tailTrace_851872 : CollatzResearch.WordTrace tailWord_851872 prefixEnd_851872 388817592983996693850949 := by
  unfold tailWord_851872
  simp only [CollatzResearch.WordTrace]
  refine ⟨15535162184910353499902935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20713549579880471333203913 15535162184910353499902935)
  ·
    refine ⟨23302743277365530249854403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15535162184910353499902935 23302743277365530249854403)
    ·
      refine ⟨34954114916048295374781605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23302743277365530249854403 34954114916048295374781605)
      ·
        refine ⟨6553896546759055382771551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34954114916048295374781605 6553896546759055382771551)
        ·
          refine ⟨9830844820138583074157327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6553896546759055382771551 9830844820138583074157327)
          ·
            refine ⟨14746267230207874611235991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9830844820138583074157327 14746267230207874611235991)
            ·
              refine ⟨22119400845311811916853987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14746267230207874611235991 22119400845311811916853987)
              ·
                refine ⟨33179101267967717875280981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22119400845311811916853987 33179101267967717875280981)
                ·
                  refine ⟨388817592983996693850949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33179101267967717875280981 388817592983996693850949)
                  ·
                    rfl

theorem cell20_851872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 8].length) (baseStart_851872 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_851872 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_851872 prefixEnd_851872 := by exact prefixLift 851872
  have htrace : WordTrace (prefixWord ++ tailWord_851872) baseStart_851872 baseEnd_851872 := by
    simpa [prefixWord, tailWord_851872, baseEnd_851872] using wordTrace_append hprefix tailTrace_851872
  have hstable : (prefixWord ++ tailWord_851872).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851872).length < 2 ^ (prefixWord ++ tailWord_851872).sum := by decide
  have hdescent : baseEnd_851872 < baseStart_851872 := by decide
  rcases family_descends (prefixWord ++ tailWord_851872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851889 : List Nat := [1, 2, 2, 4, 2, 1, 1, 3, 4]
def baseStart_851889 : Nat := 118140960795 + 851889 * 2 ^ 59
def prefixEnd_851889 : Nat := 4983230072969 + 3 ^ 40 * 851889 * 2
def baseEnd_851889 : Nat := 388825352247220190284213

theorem tailTrace_851889 : CollatzResearch.WordTrace tailWord_851889 prefixEnd_851889 388825352247220190284213 := by
  unfold tailWord_851889
  simp only [CollatzResearch.WordTrace]
  refine ⟨31070944410759118903174721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20713962940506079268783147 31070944410759118903174721)
  ·
    refine ⟨23303208308069339177381041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31070944410759118903174721 23303208308069339177381041)
    ·
      refine ⟨17477406231052004383035781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23303208308069339177381041 17477406231052004383035781)
      ·
        refine ⟨3277013668322250821819209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17477406231052004383035781 3277013668322250821819209)
        ·
          refine ⟨2457760251241688116364407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3277013668322250821819209 2457760251241688116364407)
          ·
            refine ⟨3686640376862532174546611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2457760251241688116364407 3686640376862532174546611)
            ·
              refine ⟨5529960565293798261819917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3686640376862532174546611 5529960565293798261819917)
              ·
                refine ⟨2073735211985174348182469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5529960565293798261819917 2073735211985174348182469)
                ·
                  refine ⟨388825352247220190284213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2073735211985174348182469 388825352247220190284213)
                  ·
                    rfl

theorem cell20_851889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 3, 4].length) (baseStart_851889 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_851889 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_851889 prefixEnd_851889 := by exact prefixLift 851889
  have htrace : WordTrace (prefixWord ++ tailWord_851889) baseStart_851889 baseEnd_851889 := by
    simpa [prefixWord, tailWord_851889, baseEnd_851889] using wordTrace_append hprefix tailTrace_851889
  have hstable : (prefixWord ++ tailWord_851889).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851889).length < 2 ^ (prefixWord ++ tailWord_851889).sum := by decide
  have hdescent : baseEnd_851889 < baseStart_851889 := by decide
  rcases family_descends (prefixWord ++ tailWord_851889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851982 : List Nat := [4, 1, 1, 2, 2, 1, 2, 5, 2]
def baseStart_851982 : Nat := 118140960795 + 851982 * 2 ^ 59
def prefixEnd_851982 : Nat := 4983230072969 + 3 ^ 40 * 851982 * 2
def baseEnd_851982 : Nat := 388867799981325200183833

theorem tailTrace_851982 : CollatzResearch.WordTrace tailWord_851982 prefixEnd_851982 388867799981325200183833 := by
  unfold tailWord_851982
  simp only [CollatzResearch.WordTrace]
  refine ⟨3884292049927774473288775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20716224266281463857540133 3884292049927774473288775)
  ·
    refine ⟨5826438074891661709933163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3884292049927774473288775 5826438074891661709933163)
    ·
      refine ⟨8739657112337492564899745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5826438074891661709933163 8739657112337492564899745)
      ·
        refine ⟨6554742834253119423674809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8739657112337492564899745 6554742834253119423674809)
        ·
          refine ⟨4916057125689839567756107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6554742834253119423674809 4916057125689839567756107)
          ·
            refine ⟨7374085688534759351634161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4916057125689839567756107 7374085688534759351634161)
            ·
              refine ⟨5530564266401069513725621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7374085688534759351634161 5530564266401069513725621)
              ·
                refine ⟨518490399975100266911777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5530564266401069513725621 518490399975100266911777)
                ·
                  refine ⟨388867799981325200183833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 518490399975100266911777 388867799981325200183833)
                  ·
                    rfl

theorem cell20_851982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 5, 2].length) (baseStart_851982 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_851982 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_851982 prefixEnd_851982 := by exact prefixLift 851982
  have htrace : WordTrace (prefixWord ++ tailWord_851982) baseStart_851982 baseEnd_851982 := by
    simpa [prefixWord, tailWord_851982, baseEnd_851982] using wordTrace_append hprefix tailTrace_851982
  have hstable : (prefixWord ++ tailWord_851982).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851982).length < 2 ^ (prefixWord ++ tailWord_851982).sum := by decide
  have hdescent : baseEnd_851982 < baseStart_851982 := by decide
  rcases family_descends (prefixWord ++ tailWord_851982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_851996 : List Nat := [2, 2, 3, 1, 3, 1, 1, 4, 3]
def baseStart_851996 : Nat := 118140960795 + 851996 * 2 ^ 59
def prefixEnd_851996 : Nat := 4983230072969 + 3 ^ 40 * 851996 * 2
def baseEnd_851996 : Nat := 388874189962803373717109

theorem tailTrace_851996 : CollatzResearch.WordTrace tailWord_851996 prefixEnd_851996 388874189962803373717109 := by
  unfold tailWord_851996
  simp only [CollatzResearch.WordTrace]
  refine ⟨15537423510685738088659921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20716564680914317451546561 15537423510685738088659921)
  ·
    refine ⟨11653067633014303566494941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15537423510685738088659921 11653067633014303566494941)
    ·
      refine ⟨4369900362380363837435603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11653067633014303566494941 4369900362380363837435603)
      ·
        refine ⟨6554850543570545756153405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4369900362380363837435603 6554850543570545756153405)
        ·
          refine ⟨2458068953838954658557527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6554850543570545756153405 2458068953838954658557527)
          ·
            refine ⟨3687103430758431987836291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2458068953838954658557527 3687103430758431987836291)
            ·
              refine ⟨5530655146137647981754437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3687103430758431987836291 5530655146137647981754437)
              ·
                refine ⟨1036997839900808996578957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5530655146137647981754437 1036997839900808996578957)
                ·
                  refine ⟨388874189962803373717109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1036997839900808996578957 388874189962803373717109)
                  ·
                    rfl

theorem cell20_851996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 4, 3].length) (baseStart_851996 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_851996 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_851996 prefixEnd_851996 := by exact prefixLift 851996
  have htrace : WordTrace (prefixWord ++ tailWord_851996) baseStart_851996 baseEnd_851996 := by
    simpa [prefixWord, tailWord_851996, baseEnd_851996] using wordTrace_append hprefix tailTrace_851996
  have hstable : (prefixWord ++ tailWord_851996).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_851996).length < 2 ^ (prefixWord ++ tailWord_851996).sum := by decide
  have hdescent : baseEnd_851996 < baseStart_851996 := by decide
  rcases family_descends (prefixWord ++ tailWord_851996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852031 : List Nat := [1, 1, 2, 2, 3, 1, 2, 8]
def baseStart_852031 : Nat := 118140960795 + 852031 * 2 ^ 59
def prefixEnd_852031 : Nat := 4983230072969 + 3 ^ 40 * 852031 * 2
def baseEnd_852031 : Nat := 129630054972166269183433

theorem tailTrace_852031 : CollatzResearch.WordTrace tailWord_852031 prefixEnd_852031 129630054972166269183433 := by
  unfold tailWord_852031
  simp only [CollatzResearch.WordTrace]
  refine ⟨31076123576244677154843947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20717415717496451436562631 31076123576244677154843947)
  ·
    refine ⟨46614185364367015732265921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31076123576244677154843947 46614185364367015732265921)
    ·
      refine ⟨34960639023275261799199441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46614185364367015732265921 34960639023275261799199441)
      ·
        refine ⟨26220479267456446349399581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34960639023275261799199441 26220479267456446349399581)
        ·
          refine ⟨9832679725296167381024843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26220479267456446349399581 9832679725296167381024843)
          ·
            refine ⟨14749019587944251071537265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9832679725296167381024843 14749019587944251071537265)
            ·
              refine ⟨11061764690958188303652949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14749019587944251071537265 11061764690958188303652949)
              ·
                refine ⟨129630054972166269183433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11061764690958188303652949 129630054972166269183433)
                ·
                  rfl

theorem cell20_852031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 8].length) (baseStart_852031 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_852031 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_852031 prefixEnd_852031 := by exact prefixLift 852031
  have htrace : WordTrace (prefixWord ++ tailWord_852031) baseStart_852031 baseEnd_852031 := by
    simpa [prefixWord, tailWord_852031, baseEnd_852031] using wordTrace_append hprefix tailTrace_852031
  have hstable : (prefixWord ++ tailWord_852031).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852031).length < 2 ^ (prefixWord ++ tailWord_852031).sum := by decide
  have hdescent : baseEnd_852031 < baseStart_852031 := by decide
  rcases family_descends (prefixWord ++ tailWord_852031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852054 : List Nat := [5, 2, 2, 1, 1, 1, 2, 4, 2]
def baseStart_852054 : Nat := 118140960795 + 852054 * 2 ^ 59
def prefixEnd_852054 : Nat := 4983230072969 + 3 ^ 40 * 852054 * 2
def baseEnd_852054 : Nat := 388900662743212949783539

theorem tailTrace_852054 : CollatzResearch.WordTrace tailWord_852054 prefixEnd_852054 388900662743212949783539 := by
  unfold tailWord_852054
  simp only [CollatzResearch.WordTrace]
  refine ⟨1942310153447584505183201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20717974970107568055287477 1942310153447584505183201)
  ·
    refine ⟨1456732615085688378887401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1942310153447584505183201 1456732615085688378887401)
    ·
      refine ⟨1092549461314266284165551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1456732615085688378887401 1092549461314266284165551)
      ·
        refine ⟨1638824191971399426248327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1092549461314266284165551 1638824191971399426248327)
        ·
          refine ⟨2458236287957099139372491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1638824191971399426248327 2458236287957099139372491)
          ·
            refine ⟨3687354431935648709058737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2458236287957099139372491 3687354431935648709058737)
            ·
              refine ⟨2765515823951736531794053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3687354431935648709058737 2765515823951736531794053)
              ·
                refine ⟨518534216990950599711385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2765515823951736531794053 518534216990950599711385)
                ·
                  refine ⟨388900662743212949783539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 518534216990950599711385 388900662743212949783539)
                  ·
                    rfl

theorem cell20_852054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 4, 2].length) (baseStart_852054 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_852054 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_852054 prefixEnd_852054 := by exact prefixLift 852054
  have htrace : WordTrace (prefixWord ++ tailWord_852054) baseStart_852054 baseEnd_852054 := by
    simpa [prefixWord, tailWord_852054, baseEnd_852054] using wordTrace_append hprefix tailTrace_852054
  have hstable : (prefixWord ++ tailWord_852054).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852054).length < 2 ^ (prefixWord ++ tailWord_852054).sum := by decide
  have hdescent : baseEnd_852054 < baseStart_852054 := by decide
  rcases family_descends (prefixWord ++ tailWord_852054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852093 : List Nat := [1, 4, 1, 1, 3, 2, 1, 2, 5]
def baseStart_852093 : Nat := 118140960795 + 852093 * 2 ^ 59
def prefixEnd_852093 : Nat := 4983230072969 + 3 ^ 40 * 852093 * 2
def baseEnd_852093 : Nat := 388918463405902147483379

theorem tailTrace_852093 : CollatzResearch.WordTrace tailWord_852093 prefixEnd_852093 388918463405902147483379 := by
  unfold tailWord_852093
  simp only [CollatzResearch.WordTrace]
  refine ⟨31078384902020061743600933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20718923268013374495733955 31078384902020061743600933)
  ·
    refine ⟨5827197169128761576925175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31078384902020061743600933 5827197169128761576925175)
    ·
      refine ⟨8740795753693142365387763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5827197169128761576925175 8740795753693142365387763)
      ·
        refine ⟨13111193630539713548081645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8740795753693142365387763 13111193630539713548081645)
        ·
          refine ⟨4916697611452392580530617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13111193630539713548081645 4916697611452392580530617)
          ·
            refine ⟨3687523208589294435397963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4916697611452392580530617 3687523208589294435397963)
            ·
              refine ⟨5531284812883941653096945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3687523208589294435397963 5531284812883941653096945)
              ·
                refine ⟨4148463609662956239822709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5531284812883941653096945 4148463609662956239822709)
                ·
                  refine ⟨388918463405902147483379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4148463609662956239822709 388918463405902147483379)
                  ·
                    rfl

theorem cell20_852093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 2, 5].length) (baseStart_852093 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_852093 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_852093 prefixEnd_852093 := by exact prefixLift 852093
  have htrace : WordTrace (prefixWord ++ tailWord_852093) baseStart_852093 baseEnd_852093 := by
    simpa [prefixWord, tailWord_852093, baseEnd_852093] using wordTrace_append hprefix tailTrace_852093
  have hstable : (prefixWord ++ tailWord_852093).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852093).length < 2 ^ (prefixWord ++ tailWord_852093).sum := by decide
  have hdescent : baseEnd_852093 < baseStart_852093 := by decide
  rcases family_descends (prefixWord ++ tailWord_852093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852124 : List Nat := [2, 2, 3, 2, 1, 1, 4, 5]
def baseStart_852124 : Nat := 118140960795 + 852124 * 2 ^ 59
def prefixEnd_852124 : Nat := 4983230072969 + 3 ^ 40 * 852124 * 2
def baseEnd_852124 : Nat := 129644204216867939149973

theorem tailTrace_852124 : CollatzResearch.WordTrace tailWord_852124 prefixEnd_852124 129644204216867939149973 := by
  unfold tailWord_852124
  simp only [CollatzResearch.WordTrace]
  refine ⟨15539757782453877018989713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20719677043271836025319617 15539757782453877018989713)
  ·
    refine ⟨11654818336840407764242285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15539757782453877018989713 11654818336840407764242285)
    ·
      refine ⟨4370556876315152911590857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11654818336840407764242285 4370556876315152911590857)
      ·
        refine ⟨3277917657236364683693143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4370556876315152911590857 3277917657236364683693143)
        ·
          refine ⟨4916876485854547025539715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3277917657236364683693143 4916876485854547025539715)
          ·
            refine ⟨7375314728781820538309573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4916876485854547025539715 7375314728781820538309573)
            ·
              refine ⟨1382871511646591350933045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7375314728781820538309573 1382871511646591350933045)
              ·
                refine ⟨129644204216867939149973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1382871511646591350933045 129644204216867939149973)
                ·
                  rfl

theorem cell20_852124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 4, 5].length) (baseStart_852124 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_852124 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_852124 prefixEnd_852124 := by exact prefixLift 852124
  have htrace : WordTrace (prefixWord ++ tailWord_852124) baseStart_852124 baseEnd_852124 := by
    simpa [prefixWord, tailWord_852124, baseEnd_852124] using wordTrace_append hprefix tailTrace_852124
  have hstable : (prefixWord ++ tailWord_852124).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852124).length < 2 ^ (prefixWord ++ tailWord_852124).sum := by decide
  have hdescent : baseEnd_852124 < baseStart_852124 := by decide
  rcases family_descends (prefixWord ++ tailWord_852124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852127 : List Nat := [1, 1, 2, 6, 1, 1, 4, 1, 3]
def baseStart_852127 : Nat := 118140960795 + 852127 * 2 ^ 59
def prefixEnd_852127 : Nat := 4983230072969 + 3 ^ 40 * 852127 * 2
def baseEnd_852127 : Nat := 388933981932349140349907

theorem tailTrace_852127 : CollatzResearch.WordTrace tailWord_852127 prefixEnd_852127 388933981932349140349907 := by
  unfold tailWord_852127
  simp only [CollatzResearch.WordTrace]
  refine ⟨31079624983896885550338635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20719749989264590366892423 31079624983896885550338635)
  ·
    refine ⟨46619437475845328325507953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31079624983896885550338635 46619437475845328325507953)
    ·
      refine ⟨34964578106883996244130965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46619437475845328325507953 34964578106883996244130965)
      ·
        refine ⟨1638964598760187323943639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 34964578106883996244130965 1638964598760187323943639)
        ·
          refine ⟨2458446898140280985915459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1638964598760187323943639 2458446898140280985915459)
          ·
            refine ⟨3687670347210421478873189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2458446898140280985915459 3687670347210421478873189)
            ·
              refine ⟨691438190101954027288723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3687670347210421478873189 691438190101954027288723)
              ·
                refine ⟨1037157285152931040933085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 691438190101954027288723 1037157285152931040933085)
                ·
                  refine ⟨388933981932349140349907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1037157285152931040933085 388933981932349140349907)
                  ·
                    rfl

theorem cell20_852127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 4, 1, 3].length) (baseStart_852127 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_852127 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_852127 prefixEnd_852127 := by exact prefixLift 852127
  have htrace : WordTrace (prefixWord ++ tailWord_852127) baseStart_852127 baseEnd_852127 := by
    simpa [prefixWord, tailWord_852127, baseEnd_852127] using wordTrace_append hprefix tailTrace_852127
  have hstable : (prefixWord ++ tailWord_852127).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852127).length < 2 ^ (prefixWord ++ tailWord_852127).sum := by decide
  have hdescent : baseEnd_852127 < baseStart_852127 := by decide
  rcases family_descends (prefixWord ++ tailWord_852127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852155 : List Nat := [1, 1, 1, 1, 1, 2, 6, 5, 2]
def baseStart_852155 : Nat := 118140960795 + 852155 * 2 ^ 59
def prefixEnd_852155 : Nat := 4983230072969 + 3 ^ 40 * 852155 * 2
def baseEnd_852155 : Nat := 388946761895305487416459

theorem tailTrace_852155 : CollatzResearch.WordTrace tailWord_852155 prefixEnd_852155 388946761895305487416459 := by
  unfold tailWord_852155
  simp only [CollatzResearch.WordTrace]
  refine ⟨31080646227795446332357919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20720430818530297554905279 31080646227795446332357919)
  ·
    refine ⟨46620969341693169498536879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31080646227795446332357919 46620969341693169498536879)
    ·
      refine ⟨69931454012539754247805319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46620969341693169498536879 69931454012539754247805319)
      ·
        refine ⟨104897181018809631371707979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69931454012539754247805319 104897181018809631371707979)
        ·
          refine ⟨157345771528214447057561969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104897181018809631371707979 157345771528214447057561969)
          ·
            refine ⟨118009328646160835293171477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157345771528214447057561969 118009328646160835293171477)
            ·
              refine ⟨5531687280288789154367413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 118009328646160835293171477 5531687280288789154367413)
              ·
                refine ⟨518595682527073983221945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5531687280288789154367413 518595682527073983221945)
                ·
                  refine ⟨388946761895305487416459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 518595682527073983221945 388946761895305487416459)
                  ·
                    rfl

theorem cell20_852155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 5, 2].length) (baseStart_852155 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_852155 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_852155 prefixEnd_852155 := by exact prefixLift 852155
  have htrace : WordTrace (prefixWord ++ tailWord_852155) baseStart_852155 baseEnd_852155 := by
    simpa [prefixWord, tailWord_852155, baseEnd_852155] using wordTrace_append hprefix tailTrace_852155
  have hstable : (prefixWord ++ tailWord_852155).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852155).length < 2 ^ (prefixWord ++ tailWord_852155).sum := by decide
  have hdescent : baseEnd_852155 < baseStart_852155 := by decide
  rcases family_descends (prefixWord ++ tailWord_852155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852210 : List Nat := [3, 2, 1, 3, 2, 1, 1, 5, 2]
def baseStart_852210 : Nat := 118140960795 + 852210 * 2 ^ 59
def prefixEnd_852210 : Nat := 4983230072969 + 3 ^ 40 * 852210 * 2
def baseEnd_852210 : Nat := 388971865393969740582901

theorem tailTrace_852210 : CollatzResearch.WordTrace tailWord_852210 prefixEnd_852210 388971865393969740582901 := by
  unfold tailWord_852210
  simp only [CollatzResearch.WordTrace]
  refine ⟨7770663060649047681402521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20721768161730793817073389 7770663060649047681402521)
  ·
    refine ⟨5827997295486785761051891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7770663060649047681402521 5827997295486785761051891)
    ·
      refine ⟨8741995943230178641577837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5827997295486785761051891 8741995943230178641577837)
      ·
        refine ⟨3278248478711316990591689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8741995943230178641577837 3278248478711316990591689)
        ·
          refine ⟨2458686359033487742943767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3278248478711316990591689 2458686359033487742943767)
          ·
            refine ⟨3688029538550231614415651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2458686359033487742943767 3688029538550231614415651)
            ·
              refine ⟨5532044307825347421623477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3688029538550231614415651 5532044307825347421623477)
              ·
                refine ⟨518629153858626320777201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5532044307825347421623477 518629153858626320777201)
                ·
                  refine ⟨388971865393969740582901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 518629153858626320777201 388971865393969740582901)
                  ·
                    rfl

theorem cell20_852210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 5, 2].length) (baseStart_852210 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_852210 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_852210 prefixEnd_852210 := by exact prefixLift 852210
  have htrace : WordTrace (prefixWord ++ tailWord_852210) baseStart_852210 baseEnd_852210 := by
    simpa [prefixWord, tailWord_852210, baseEnd_852210] using wordTrace_append hprefix tailTrace_852210
  have hstable : (prefixWord ++ tailWord_852210).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852210).length < 2 ^ (prefixWord ++ tailWord_852210).sum := by decide
  have hdescent : baseEnd_852210 < baseStart_852210 := by decide
  rcases family_descends (prefixWord ++ tailWord_852210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852245 : List Nat := [1, 3, 2, 1, 2, 1, 2, 5, 3]
def baseStart_852245 : Nat := 118140960795 + 852245 * 2 ^ 59
def prefixEnd_852245 : Nat := 4983230072969 + 3 ^ 40 * 852245 * 2
def baseEnd_852245 : Nat := 388987840347665174416091

theorem tailTrace_852245 : CollatzResearch.WordTrace tailWord_852245 prefixEnd_852245 388987840347665174416091 := by
  unfold tailWord_852245
  simp only [CollatzResearch.WordTrace]
  refine ⟨31083928797469391703134189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20722619198312927802089459 31083928797469391703134189)
  ·
    refine ⟨11656473299051021888675321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31083928797469391703134189 11656473299051021888675321)
    ·
      refine ⟨8742354974288266416506491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11656473299051021888675321 8742354974288266416506491)
      ·
        refine ⟨13113532461432399624759737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8742354974288266416506491 13113532461432399624759737)
        ·
          refine ⟨9835149346074299718569803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13113532461432399624759737 9835149346074299718569803)
          ·
            refine ⟨14752724019111449577854705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9835149346074299718569803 14752724019111449577854705)
            ·
              refine ⟨11064543014333587183391029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14752724019111449577854705 11064543014333587183391029)
              ·
                refine ⟨1037300907593773798442909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11064543014333587183391029 1037300907593773798442909)
                ·
                  refine ⟨388987840347665174416091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1037300907593773798442909 388987840347665174416091)
                  ·
                    rfl

theorem cell20_852245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 5, 3].length) (baseStart_852245 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_852245 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_852245 prefixEnd_852245 := by exact prefixLift 852245
  have htrace : WordTrace (prefixWord ++ tailWord_852245) baseStart_852245 baseEnd_852245 := by
    simpa [prefixWord, tailWord_852245, baseEnd_852245] using wordTrace_append hprefix tailTrace_852245
  have hstable : (prefixWord ++ tailWord_852245).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852245).length < 2 ^ (prefixWord ++ tailWord_852245).sum := by decide
  have hdescent : baseEnd_852245 < baseStart_852245 := by decide
  rcases family_descends (prefixWord ++ tailWord_852245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852255 : List Nat := [1, 1, 2, 4, 3, 3, 2, 4]
def baseStart_852255 : Nat := 118140960795 + 852255 * 2 ^ 59
def prefixEnd_852255 : Nat := 4983230072969 + 3 ^ 40 * 852255 * 2
def baseEnd_852255 : Nat := 129664134873383194694239

theorem tailTrace_852255 : CollatzResearch.WordTrace tailWord_852255 prefixEnd_852255 129664134873383194694239 := by
  unfold tailWord_852255
  simp only [CollatzResearch.WordTrace]
  refine ⟨31084293527433163410998219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20722862351622108940665479 31084293527433163410998219)
  ·
    refine ⟨46626440291149745116497329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31084293527433163410998219 46626440291149745116497329)
    ·
      refine ⟨34969830218362308837372997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46626440291149745116497329 34969830218362308837372997)
      ·
        refine ⟨6556843165942932907007437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34969830218362308837372997 6556843165942932907007437)
        ·
          refine ⟨2458816187228599840127789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6556843165942932907007437 2458816187228599840127789)
          ·
            refine ⟨922056070210724940047921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2458816187228599840127789 922056070210724940047921)
            ·
              refine ⟨691542052658043705035941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 922056070210724940047921 691542052658043705035941)
              ·
                refine ⟨129664134873383194694239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 691542052658043705035941 129664134873383194694239)
                ·
                  rfl

theorem cell20_852255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 2, 4].length) (baseStart_852255 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_852255 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_852255 prefixEnd_852255 := by exact prefixLift 852255
  have htrace : WordTrace (prefixWord ++ tailWord_852255) baseStart_852255 baseEnd_852255 := by
    simpa [prefixWord, tailWord_852255, baseEnd_852255] using wordTrace_append hprefix tailTrace_852255
  have hstable : (prefixWord ++ tailWord_852255).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852255).length < 2 ^ (prefixWord ++ tailWord_852255).sum := by decide
  have hdescent : baseEnd_852255 < baseStart_852255 := by decide
  rcases family_descends (prefixWord ++ tailWord_852255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852259 : List Nat := [1, 1, 1, 4, 2, 2, 3, 6]
def baseStart_852259 : Nat := 118140960795 + 852259 * 2 ^ 59
def prefixEnd_852259 : Nat := 4983230072969 + 3 ^ 40 * 852259 * 2
def baseEnd_852259 : Nat := 129664743443047782649789

theorem tailTrace_852259 : CollatzResearch.WordTrace tailWord_852259 prefixEnd_852259 129664743443047782649789 := by
  unfold tailWord_852259
  simp only [CollatzResearch.WordTrace]
  refine ⟨31084439419418672094143831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20722959612945781396095887 31084439419418672094143831)
  ·
    refine ⟨46626659129128008141215747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31084439419418672094143831 46626659129128008141215747)
    ·
      refine ⟨69939988693692012211823621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46626659129128008141215747 69939988693692012211823621)
      ·
        refine ⟨13113747880067252289716929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69939988693692012211823621 13113747880067252289716929)
        ·
          refine ⟨9835310910050439217287697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13113747880067252289716929 9835310910050439217287697)
          ·
            refine ⟨7376483182537829412965773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9835310910050439217287697 7376483182537829412965773)
            ·
              refine ⟨2766181193451686029862165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7376483182537829412965773 2766181193451686029862165)
              ·
                refine ⟨129664743443047782649789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2766181193451686029862165 129664743443047782649789)
                ·
                  rfl

theorem cell20_852259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 6].length) (baseStart_852259 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_852259 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_852259 prefixEnd_852259 := by exact prefixLift 852259
  have htrace : WordTrace (prefixWord ++ tailWord_852259) baseStart_852259 baseEnd_852259 := by
    simpa [prefixWord, tailWord_852259, baseEnd_852259] using wordTrace_append hprefix tailTrace_852259
  have hstable : (prefixWord ++ tailWord_852259).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852259).length < 2 ^ (prefixWord ++ tailWord_852259).sum := by decide
  have hdescent : baseEnd_852259 < baseStart_852259 := by decide
  rcases family_descends (prefixWord ++ tailWord_852259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852276 : List Nat := [2, 5, 1, 1, 1, 2, 8]
def baseStart_852276 : Nat := 118140960795 + 852276 * 2 ^ 59
def prefixEnd_852276 : Nat := 4983230072969 + 3 ^ 40 * 852276 * 2
def baseEnd_852276 : Nat := 43222443288040760486959

theorem tailTrace_852276 : CollatzResearch.WordTrace tailWord_852276 prefixEnd_852276 43222443288040760486959 := by
  unfold tailWord_852276
  simp only [CollatzResearch.WordTrace]
  refine ⟨15542529730178541998756341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20723372973571389331675121 15542529730178541998756341)
  ·
    refine ⟨1457112162204238312383407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15542529730178541998756341 1457112162204238312383407)
    ·
      refine ⟨2185668243306357468575111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1457112162204238312383407 2185668243306357468575111)
      ·
        refine ⟨3278502364959536202862667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2185668243306357468575111 3278502364959536202862667)
        ·
          refine ⟨4917753547439304304294001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3278502364959536202862667 4917753547439304304294001)
          ·
            refine ⟨3688315160579478228220501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4917753547439304304294001 3688315160579478228220501)
            ·
              refine ⟨43222443288040760486959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3688315160579478228220501 43222443288040760486959)
              ·
                rfl

theorem cell20_852276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 8].length) (baseStart_852276 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_852276 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_852276 prefixEnd_852276 := by exact prefixLift 852276
  have htrace : WordTrace (prefixWord ++ tailWord_852276) baseStart_852276 baseEnd_852276 := by
    simpa [prefixWord, tailWord_852276, baseEnd_852276] using wordTrace_append hprefix tailTrace_852276
  have hstable : (prefixWord ++ tailWord_852276).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852276).length < 2 ^ (prefixWord ++ tailWord_852276).sum := by decide
  have hdescent : baseEnd_852276 < baseStart_852276 := by decide
  rcases family_descends (prefixWord ++ tailWord_852276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852286 : List Nat := [4, 2, 1, 2, 1, 4, 1, 1, 4]
def baseStart_852286 : Nat := 118140960795 + 852286 * 2 ^ 59
def prefixEnd_852286 : Nat := 4983230072969 + 3 ^ 40 * 852286 * 2
def baseEnd_852286 : Nat := 389006553864851254049257

theorem tailTrace_852286 : CollatzResearch.WordTrace tailWord_852286 prefixEnd_852286 389006553864851254049257 := by
  unfold tailWord_852286
  simp only [CollatzResearch.WordTrace]
  refine ⟨3885678023790106963172089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20723616126880570470251141 3885678023790106963172089)
  ·
    refine ⟨2914258517842580222379067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3885678023790106963172089 2914258517842580222379067)
    ·
      refine ⟨4371387776763870333568601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2914258517842580222379067 4371387776763870333568601)
      ·
        refine ⟨3278540832572902750176451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4371387776763870333568601 3278540832572902750176451)
        ·
          refine ⟨4917811248859354125264677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3278540832572902750176451 4917811248859354125264677)
          ·
            refine ⟨922089609161128898487127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4917811248859354125264677 922089609161128898487127)
            ·
              refine ⟨1383134413741693347730691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 922089609161128898487127 1383134413741693347730691)
              ·
                refine ⟨2074701620612540021596037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1383134413741693347730691 2074701620612540021596037)
                ·
                  refine ⟨389006553864851254049257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2074701620612540021596037 389006553864851254049257)
                  ·
                    rfl

theorem cell20_852286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 1, 1, 4].length) (baseStart_852286 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_852286 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_852286 prefixEnd_852286 := by exact prefixLift 852286
  have htrace : WordTrace (prefixWord ++ tailWord_852286) baseStart_852286 baseEnd_852286 := by
    simpa [prefixWord, tailWord_852286, baseEnd_852286] using wordTrace_append hprefix tailTrace_852286
  have hstable : (prefixWord ++ tailWord_852286).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852286).length < 2 ^ (prefixWord ++ tailWord_852286).sum := by decide
  have hdescent : baseEnd_852286 < baseStart_852286 := by decide
  rcases family_descends (prefixWord ++ tailWord_852286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852338 : List Nat := [3, 2, 1, 2, 1, 4, 2, 2, 3]
def baseStart_852338 : Nat := 118140960795 + 852338 * 2 ^ 59
def prefixEnd_852338 : Nat := 4983230072969 + 3 ^ 40 * 852338 * 2
def baseEnd_852338 : Nat := 389030288081770184315711

theorem tailTrace_852338 : CollatzResearch.WordTrace tailWord_852338 prefixEnd_852338 389030288081770184315711 := by
  unfold tailWord_852338
  simp only [CollatzResearch.WordTrace]
  refine ⟨7771830196533117146567417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20724880524088312390846445 7771830196533117146567417)
  ·
    refine ⟨5828872647399837859925563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7771830196533117146567417 5828872647399837859925563)
    ·
      refine ⟨8743308971099756789888345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5828872647399837859925563 8743308971099756789888345)
      ·
        refine ⟨6557481728324817592416259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8743308971099756789888345 6557481728324817592416259)
        ·
          refine ⟨9836222592487226388624389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6557481728324817592416259 9836222592487226388624389)
          ·
            refine ⟨1844291736091354947867073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9836222592487226388624389 1844291736091354947867073)
            ·
              refine ⟨1383218802068516210900305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1844291736091354947867073 1383218802068516210900305)
              ·
                refine ⟨1037414101551387158175229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1383218802068516210900305 1037414101551387158175229)
                ·
                  refine ⟨389030288081770184315711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1037414101551387158175229 389030288081770184315711)
                  ·
                    rfl

theorem cell20_852338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 2, 2, 3].length) (baseStart_852338 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_852338 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_852338 prefixEnd_852338 := by exact prefixLift 852338
  have htrace : WordTrace (prefixWord ++ tailWord_852338) baseStart_852338 baseEnd_852338 := by
    simpa [prefixWord, tailWord_852338, baseEnd_852338] using wordTrace_append hprefix tailTrace_852338
  have hstable : (prefixWord ++ tailWord_852338).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852338).length < 2 ^ (prefixWord ++ tailWord_852338).sum := by decide
  have hdescent : baseEnd_852338 < baseStart_852338 := by decide
  rcases family_descends (prefixWord ++ tailWord_852338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852341 : List Nat := [1, 3, 4, 1, 2, 1, 4, 2, 2]
def baseStart_852341 : Nat := 118140960795 + 852341 * 2 ^ 59
def prefixEnd_852341 : Nat := 4983230072969 + 3 ^ 40 * 852341 * 2
def baseEnd_852341 : Nat := 389031657363515507215699

theorem tailTrace_852341 : CollatzResearch.WordTrace tailWord_852341 prefixEnd_852341 389031657363515507215699 := by
  unfold tailWord_852341
  simp only [CollatzResearch.WordTrace]
  refine ⟨31087430205121600098628877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20724953470081066732419251 31087430205121600098628877)
  ·
    refine ⟨11657786326920600036985829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31087430205121600098628877 11657786326920600036985829)
    ·
      refine ⟨2185834936297612506934843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11657786326920600036985829 2185834936297612506934843)
      ·
        refine ⟨3278752404446418760402265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2185834936297612506934843 3278752404446418760402265)
        ·
          refine ⟨2459064303334814070301699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3278752404446418760402265 2459064303334814070301699)
          ·
            refine ⟨3688596455002221105452549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2459064303334814070301699 3688596455002221105452549)
            ·
              refine ⟨691611835312916457272353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3688596455002221105452549 691611835312916457272353)
              ·
                refine ⟨518708876484687342954265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 691611835312916457272353 518708876484687342954265)
                ·
                  refine ⟨389031657363515507215699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 518708876484687342954265 389031657363515507215699)
                  ·
                    rfl

theorem cell20_852341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 4, 2, 2].length) (baseStart_852341 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_852341 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_852341 prefixEnd_852341 := by exact prefixLift 852341
  have htrace : WordTrace (prefixWord ++ tailWord_852341) baseStart_852341 baseEnd_852341 := by
    simpa [prefixWord, tailWord_852341, baseEnd_852341] using wordTrace_append hprefix tailTrace_852341
  have hstable : (prefixWord ++ tailWord_852341).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852341).length < 2 ^ (prefixWord ++ tailWord_852341).sum := by decide
  have hdescent : baseEnd_852341 < baseStart_852341 := by decide
  rcases family_descends (prefixWord ++ tailWord_852341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852359 : List Nat := [1, 1, 4, 2, 2, 1, 1, 5, 3]
def baseStart_852359 : Nat := 118140960795 + 852359 * 2 ^ 59
def prefixEnd_852359 : Nat := 4983230072969 + 3 ^ 40 * 852359 * 2
def baseEnd_852359 : Nat := 389039873053987444615625

theorem tailTrace_852359 : CollatzResearch.WordTrace tailWord_852359 prefixEnd_852359 389039873053987444615625 := by
  unfold tailWord_852359
  simp only [CollatzResearch.WordTrace]
  refine ⟨31088086719056389172784131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20725391146037592781856087 31088086719056389172784131)
  ·
    refine ⟨46632130078584583759176197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31088086719056389172784131 46632130078584583759176197)
    ·
      refine ⟨8743524389734609454845537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46632130078584583759176197 8743524389734609454845537)
      ·
        refine ⟨6557643292300957091134153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8743524389734609454845537 6557643292300957091134153)
        ·
          refine ⟨4918232469225717818350615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6557643292300957091134153 4918232469225717818350615)
          ·
            refine ⟨7377348703838576727525923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4918232469225717818350615 7377348703838576727525923)
            ·
              refine ⟨11066023055757865091288885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7377348703838576727525923 11066023055757865091288885)
              ·
                refine ⟨1037439661477299852308333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11066023055757865091288885 1037439661477299852308333)
                ·
                  refine ⟨389039873053987444615625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1037439661477299852308333 389039873053987444615625)
                  ·
                    rfl

theorem cell20_852359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 5, 3].length) (baseStart_852359 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_852359 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_852359 prefixEnd_852359 := by exact prefixLift 852359
  have htrace : WordTrace (prefixWord ++ tailWord_852359) baseStart_852359 baseEnd_852359 := by
    simpa [prefixWord, tailWord_852359, baseEnd_852359] using wordTrace_append hprefix tailTrace_852359
  have hstable : (prefixWord ++ tailWord_852359).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852359).length < 2 ^ (prefixWord ++ tailWord_852359).sum := by decide
  have hdescent : baseEnd_852359 < baseStart_852359 := by decide
  rcases family_descends (prefixWord ++ tailWord_852359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852362 : List Nat := [3, 1, 2, 5, 1, 1, 1, 2, 4]
def baseStart_852362 : Nat := 118140960795 + 852362 * 2 ^ 59
def prefixEnd_852362 : Nat := 4983230072969 + 3 ^ 40 * 852362 * 2
def baseEnd_852362 : Nat := 389041242335732767515613

theorem tailTrace_852362 : CollatzResearch.WordTrace tailWord_852362 prefixEnd_852362 389041242335732767515613 := by
  unfold tailWord_852362
  simp only [CollatzResearch.WordTrace]
  refine ⟨7772049034511380171285835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20725464092030347123428893 7772049034511380171285835)
  ·
    refine ⟨11658073551767070256928753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7772049034511380171285835 11658073551767070256928753)
    ·
      refine ⟨8743555163825302692696565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11658073551767070256928753 8743555163825302692696565)
      ·
        refine ⟨819708296608622127440303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8743555163825302692696565 819708296608622127440303)
        ·
          refine ⟨1229562444912933191160455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 819708296608622127440303 1229562444912933191160455)
          ·
            refine ⟨1844343667369399786740683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1229562444912933191160455 1844343667369399786740683)
            ·
              refine ⟨2766515501054099680111025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1844343667369399786740683 2766515501054099680111025)
              ·
                refine ⟨2074886625790574760083269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2766515501054099680111025 2074886625790574760083269)
                ·
                  refine ⟨389041242335732767515613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2074886625790574760083269 389041242335732767515613)
                  ·
                    rfl

theorem cell20_852362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 2, 4].length) (baseStart_852362 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_852362 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_852362 prefixEnd_852362 := by exact prefixLift 852362
  have htrace : WordTrace (prefixWord ++ tailWord_852362) baseStart_852362 baseEnd_852362 := by
    simpa [prefixWord, tailWord_852362, baseEnd_852362] using wordTrace_append hprefix tailTrace_852362
  have hstable : (prefixWord ++ tailWord_852362).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852362).length < 2 ^ (prefixWord ++ tailWord_852362).sum := by decide
  have hdescent : baseEnd_852362 < baseStart_852362 := by decide
  rcases family_descends (prefixWord ++ tailWord_852362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852428 : List Nat := [2, 2, 1, 4, 3, 1, 1, 6]
def baseStart_852428 : Nat := 118140960795 + 852428 * 2 ^ 59
def prefixEnd_852428 : Nat := 4983230072969 + 3 ^ 40 * 852428 * 2
def baseEnd_852428 : Nat := 129690455511376623771781

theorem tailTrace_852428 : CollatzResearch.WordTrace tailWord_852428 prefixEnd_852428 129690455511376623771781 := by
  unfold tailWord_852428
  simp only [CollatzResearch.WordTrace]
  refine ⟨15545301677903206978522969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20727068903870942638030625 15545301677903206978522969)
  ·
    refine ⟨11658976258427405233892227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15545301677903206978522969 11658976258427405233892227)
    ·
      refine ⟨17488464387641107850838341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11658976258427405233892227 17488464387641107850838341)
      ·
        refine ⟨3279087072682707722032189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17488464387641107850838341 3279087072682707722032189)
        ·
          refine ⟨1229657652256015395762071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3279087072682707722032189 1229657652256015395762071)
          ·
            refine ⟨1844486478384023093643107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1229657652256015395762071 1844486478384023093643107)
            ·
              refine ⟨2766729717576034640464661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1844486478384023093643107 2766729717576034640464661)
              ·
                refine ⟨129690455511376623771781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2766729717576034640464661 129690455511376623771781)
                ·
                  rfl

theorem cell20_852428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 6].length) (baseStart_852428 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_852428 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_852428 prefixEnd_852428 := by exact prefixLift 852428
  have htrace : WordTrace (prefixWord ++ tailWord_852428) baseStart_852428 baseEnd_852428 := by
    simpa [prefixWord, tailWord_852428, baseEnd_852428] using wordTrace_append hprefix tailTrace_852428
  have hstable : (prefixWord ++ tailWord_852428).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852428).length < 2 ^ (prefixWord ++ tailWord_852428).sum := by decide
  have hdescent : baseEnd_852428 < baseStart_852428 := by decide
  rcases family_descends (prefixWord ++ tailWord_852428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852434 : List Nat := [3, 2, 2, 4, 1, 2, 1, 3, 2]
def baseStart_852434 : Nat := 118140960795 + 852434 * 2 ^ 59
def prefixEnd_852434 : Nat := 4983230072969 + 3 ^ 40 * 852434 * 2
def baseEnd_852434 : Nat := 389074105097620517115319

theorem tailTrace_852434 : CollatzResearch.WordTrace tailWord_852434 prefixEnd_852434 389074105097620517115319 := by
  unfold tailWord_852434
  simp only [CollatzResearch.WordTrace]
  refine ⟨7772705548446169245441089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20727214795856451321176237 7772705548446169245441089)
  ·
    refine ⟨5829529161334626934080817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7772705548446169245441089 5829529161334626934080817)
    ·
      refine ⟨4372146871000970200560613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5829529161334626934080817 4372146871000970200560613)
      ·
        refine ⟨819777538312681912605115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4372146871000970200560613 819777538312681912605115)
        ·
          refine ⟨1229666307469022868907673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 819777538312681912605115 1229666307469022868907673)
          ·
            refine ⟨922249730601767151680755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1229666307469022868907673 922249730601767151680755)
            ·
              refine ⟨1383374595902650727521133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 922249730601767151680755 1383374595902650727521133)
              ·
                refine ⟨518765473463494022820425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1383374595902650727521133 518765473463494022820425)
                ·
                  refine ⟨389074105097620517115319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 518765473463494022820425 389074105097620517115319)
                  ·
                    rfl

theorem cell20_852434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 1, 3, 2].length) (baseStart_852434 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_852434 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_852434 prefixEnd_852434 := by exact prefixLift 852434
  have htrace : WordTrace (prefixWord ++ tailWord_852434) baseStart_852434 baseEnd_852434 := by
    simpa [prefixWord, tailWord_852434, baseEnd_852434] using wordTrace_append hprefix tailTrace_852434
  have hstable : (prefixWord ++ tailWord_852434).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852434).length < 2 ^ (prefixWord ++ tailWord_852434).sum := by decide
  have hdescent : baseEnd_852434 < baseStart_852434 := by decide
  rcases family_descends (prefixWord ++ tailWord_852434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852469 : List Nat := [1, 3, 5, 1, 2, 1, 1, 3, 3]
def baseStart_852469 : Nat := 118140960795 + 852469 * 2 ^ 59
def prefixEnd_852469 : Nat := 4983230072969 + 3 ^ 40 * 852469 * 2
def baseEnd_852469 : Nat := 389090080051315950948509

theorem tailTrace_852469 : CollatzResearch.WordTrace tailWord_852469 prefixEnd_852469 389090080051315950948509 := by
  unfold tailWord_852469
  simp only [CollatzResearch.WordTrace]
  refine ⟨31092098748657877959288461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20728065832438585306192307 31092098748657877959288461)
  ·
    refine ⟨11659537030746704234733173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31092098748657877959288461 11659537030746704234733173)
    ·
      refine ⟨1093081596632503522006235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11659537030746704234733173 1093081596632503522006235)
      ·
        refine ⟨1639622394948755283009353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1093081596632503522006235 1639622394948755283009353)
        ·
          refine ⟨1229716796211566462257015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1639622394948755283009353 1229716796211566462257015)
          ·
            refine ⟨1844575194317349693385523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1229716796211566462257015 1844575194317349693385523)
            ·
              refine ⟨2766862791476024540078285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1844575194317349693385523 2766862791476024540078285)
              ·
                refine ⟨1037573546803509202529357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2766862791476024540078285 1037573546803509202529357)
                ·
                  refine ⟨389090080051315950948509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1037573546803509202529357 389090080051315950948509)
                  ·
                    rfl

theorem cell20_852469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 3, 3].length) (baseStart_852469 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_852469 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_852469 prefixEnd_852469 := by exact prefixLift 852469
  have htrace : WordTrace (prefixWord ++ tailWord_852469) baseStart_852469 baseEnd_852469 := by
    simpa [prefixWord, tailWord_852469, baseEnd_852469] using wordTrace_append hprefix tailTrace_852469
  have hstable : (prefixWord ++ tailWord_852469).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852469).length < 2 ^ (prefixWord ++ tailWord_852469).sum := by decide
  have hdescent : baseEnd_852469 < baseStart_852469 := by decide
  rcases family_descends (prefixWord ++ tailWord_852469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852601 : List Nat := [1, 2, 1, 3, 3, 3, 1, 6]
def baseStart_852601 : Nat := 118140960795 + 852601 * 2 ^ 59
def prefixEnd_852601 : Nat := 4983230072969 + 3 ^ 40 * 852601 * 2
def baseEnd_852601 : Nat := 129716776149370052849323

theorem tailTrace_852601 : CollatzResearch.WordTrace tailWord_852601 prefixEnd_852601 129716776149370052849323 := by
  unfold tailWord_852601
  simp only [CollatzResearch.WordTrace]
  refine ⟨31096913184179664503093657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20731275456119776335395771 31096913184179664503093657)
  ·
    refine ⟨23322684888134748377320243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31096913184179664503093657 23322684888134748377320243)
    ·
      refine ⟨34984027332202122565980365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23322684888134748377320243 34984027332202122565980365)
      ·
        refine ⟨13119010249575795962242637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34984027332202122565980365 13119010249575795962242637)
        ·
          refine ⟨4919628843590923485840989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13119010249575795962242637 4919628843590923485840989)
          ·
            refine ⟨1844860816346596307190371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4919628843590923485840989 1844860816346596307190371)
            ·
              refine ⟨2767291224519894460785557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1844860816346596307190371 2767291224519894460785557)
              ·
                refine ⟨129716776149370052849323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2767291224519894460785557 129716776149370052849323)
                ·
                  rfl

theorem cell20_852601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 6].length) (baseStart_852601 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_852601 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_852601 prefixEnd_852601 := by exact prefixLift 852601
  have htrace : WordTrace (prefixWord ++ tailWord_852601) baseStart_852601 baseEnd_852601 := by
    simpa [prefixWord, tailWord_852601, baseEnd_852601] using wordTrace_append hprefix tailTrace_852601
  have hstable : (prefixWord ++ tailWord_852601).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852601).length < 2 ^ (prefixWord ++ tailWord_852601).sum := by decide
  have hdescent : baseEnd_852601 < baseStart_852601 := by decide
  rcases family_descends (prefixWord ++ tailWord_852601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852608 : List Nat := [2, 1, 1, 2, 1, 5, 1, 2, 5]
def baseStart_852608 : Nat := 118140960795 + 852608 * 2 ^ 59
def prefixEnd_852608 : Nat := 4983230072969 + 3 ^ 40 * 852608 * 2
def baseEnd_852608 : Nat := 389153523438849245314607

theorem tailTrace_852608 : CollatzResearch.WordTrace tailWord_852608 prefixEnd_852608 389153523438849245314607 := by
  unfold tailWord_852608
  simp only [CollatzResearch.WordTrace]
  refine ⟨15548584247577152349299239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20731445663436203132398985 15548584247577152349299239)
  ·
    refine ⟨23322876371365728523948859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15548584247577152349299239 23322876371365728523948859)
    ·
      refine ⟨34984314557048592785923289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23322876371365728523948859 34984314557048592785923289)
      ·
        refine ⟨26238235917786444589442467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34984314557048592785923289 26238235917786444589442467)
        ·
          refine ⟨39357353876679666884163701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26238235917786444589442467 39357353876679666884163701)
          ·
            refine ⟨3689751925938718770390347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39357353876679666884163701 3689751925938718770390347)
            ·
              refine ⟨5534627888908078155585521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3689751925938718770390347 5534627888908078155585521)
              ·
                refine ⟨4150970916681058616689141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5534627888908078155585521 4150970916681058616689141)
                ·
                  refine ⟨389153523438849245314607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4150970916681058616689141 389153523438849245314607)
                  ·
                    rfl

theorem cell20_852608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 2, 5].length) (baseStart_852608 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_852608 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_852608 prefixEnd_852608 := by exact prefixLift 852608
  have htrace : WordTrace (prefixWord ++ tailWord_852608) baseStart_852608 baseEnd_852608 := by
    simpa [prefixWord, tailWord_852608, baseEnd_852608] using wordTrace_append hprefix tailTrace_852608
  have hstable : (prefixWord ++ tailWord_852608).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852608).length < 2 ^ (prefixWord ++ tailWord_852608).sum := by decide
  have hdescent : baseEnd_852608 < baseStart_852608 := by decide
  rcases family_descends (prefixWord ++ tailWord_852608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852611 : List Nat := [1, 1, 1, 3, 3, 1, 5, 3, 2]
def baseStart_852611 : Nat := 118140960795 + 852611 * 2 ^ 59
def prefixEnd_852611 : Nat := 4983230072969 + 3 ^ 40 * 852611 * 2
def baseEnd_852611 : Nat := 389154892720594568214595

theorem tailTrace_852611 : CollatzResearch.WordTrace tailWord_852611 prefixEnd_852611 389154892720594568214595 := by
  unfold tailWord_852611
  simp only [CollatzResearch.WordTrace]
  refine ⟨31097277914143436210957687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20731518609428957473971791 31097277914143436210957687)
  ·
    refine ⟨46645916871215154316436531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31097277914143436210957687 46645916871215154316436531)
    ·
      refine ⟨69968875306822731474654797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46645916871215154316436531 69968875306822731474654797)
      ·
        refine ⟨26238328240058524302995549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69968875306822731474654797 26238328240058524302995549)
        ·
          refine ⟨9839373090021946613623331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26238328240058524302995549 9839373090021946613623331)
          ·
            refine ⟨14759059635032919920434997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9839373090021946613623331 14759059635032919920434997)
            ·
              refine ⟨1383661840784336242540781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14759059635032919920434997 1383661840784336242540781)
              ·
                refine ⟨518873190294126090952793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1383661840784336242540781 518873190294126090952793)
                ·
                  refine ⟨389154892720594568214595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 518873190294126090952793 389154892720594568214595)
                  ·
                    rfl

theorem cell20_852611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 5, 3, 2].length) (baseStart_852611 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_852611 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_852611 prefixEnd_852611 := by exact prefixLift 852611
  have htrace : WordTrace (prefixWord ++ tailWord_852611) baseStart_852611 baseEnd_852611 := by
    simpa [prefixWord, tailWord_852611, baseEnd_852611] using wordTrace_append hprefix tailTrace_852611
  have hstable : (prefixWord ++ tailWord_852611).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852611).length < 2 ^ (prefixWord ++ tailWord_852611).sum := by decide
  have hdescent : baseEnd_852611 < baseStart_852611 := by decide
  rcases family_descends (prefixWord ++ tailWord_852611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852618 : List Nat := [3, 1, 2, 3, 3, 2, 6]
def baseStart_852618 : Nat := 118140960795 + 852618 * 2 ^ 59
def prefixEnd_852618 : Nat := 4983230072969 + 3 ^ 40 * 852618 * 2
def baseEnd_852618 : Nat := 43239787523481517220137

theorem tailTrace_852618 : CollatzResearch.WordTrace tailWord_852618 prefixEnd_852618 43239787523481517220137 := by
  unfold tailWord_852618
  simp only [CollatzResearch.WordTrace]
  refine ⟨7774383306279519101615627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20731688816745384270975005 7774383306279519101615627)
  ·
    refine ⟨11661574959419278652423441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7774383306279519101615627 11661574959419278652423441)
    ·
      refine ⟨8746181219564458989317581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11661574959419278652423441 8746181219564458989317581)
      ·
        refine ⟨3279817957336672120994093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8746181219564458989317581 3279817957336672120994093)
        ·
          refine ⟨1229931734001252045372785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3279817957336672120994093 1229931734001252045372785)
          ·
            refine ⟨922448800500939034029589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1229931734001252045372785 922448800500939034029589)
            ·
              refine ⟨43239787523481517220137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 922448800500939034029589 43239787523481517220137)
              ·
                rfl

theorem cell20_852618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 6].length) (baseStart_852618 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_852618 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_852618 prefixEnd_852618 := by exact prefixLift 852618
  have htrace : WordTrace (prefixWord ++ tailWord_852618) baseStart_852618 baseEnd_852618 := by
    simpa [prefixWord, tailWord_852618, baseEnd_852618] using wordTrace_append hprefix tailTrace_852618
  have hstable : (prefixWord ++ tailWord_852618).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852618).length < 2 ^ (prefixWord ++ tailWord_852618).sum := by decide
  have hdescent : baseEnd_852618 < baseStart_852618 := by decide
  rcases family_descends (prefixWord ++ tailWord_852618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852628 : List Nat := [2, 4, 2, 2, 1, 3, 1, 1, 4]
def baseStart_852628 : Nat := 118140960795 + 852628 * 2 ^ 59
def prefixEnd_852628 : Nat := 4983230072969 + 3 ^ 40 * 852628 * 2
def baseEnd_852628 : Nat := 389162651983818064647859

theorem tailTrace_852628 : CollatzResearch.WordTrace tailWord_852628 prefixEnd_852628 389162651983818064647859 := by
  unfold tailWord_852628
  simp only [CollatzResearch.WordTrace]
  refine ⟨15548948977540924057163269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20731931970054565409551025 15548948977540924057163269)
  ·
    refine ⟨2915427933288923260718113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15548948977540924057163269 2915427933288923260718113)
    ·
      refine ⟨2186570949966692445538585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2915427933288923260718113 2186570949966692445538585)
      ·
        refine ⟨1639928212475019334153939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2186570949966692445538585 1639928212475019334153939)
        ·
          refine ⟨2459892318712529001230909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1639928212475019334153939 2459892318712529001230909)
          ·
            refine ⟨922459619517198375461591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2459892318712529001230909 922459619517198375461591)
            ·
              refine ⟨1383689429275797563192387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 922459619517198375461591 1383689429275797563192387)
              ·
                refine ⟨2075534143913696344788581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1383689429275797563192387 2075534143913696344788581)
                ·
                  refine ⟨389162651983818064647859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2075534143913696344788581 389162651983818064647859)
                  ·
                    rfl

theorem cell20_852628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 1, 1, 4].length) (baseStart_852628 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_852628 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_852628 prefixEnd_852628 := by exact prefixLift 852628
  have htrace : WordTrace (prefixWord ++ tailWord_852628) baseStart_852628 baseEnd_852628 := by
    simpa [prefixWord, tailWord_852628, baseEnd_852628] using wordTrace_append hprefix tailTrace_852628
  have hstable : (prefixWord ++ tailWord_852628).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852628).length < 2 ^ (prefixWord ++ tailWord_852628).sum := by decide
  have hdescent : baseEnd_852628 < baseStart_852628 := by decide
  rcases family_descends (prefixWord ++ tailWord_852628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852673 : List Nat := [1, 2, 6, 2, 2, 7]
def baseStart_852673 : Nat := 118140960795 + 852673 * 2 ^ 59
def prefixEnd_852673 : Nat := 4983230072969 + 3 ^ 40 * 852673 * 2
def baseEnd_852673 : Nat := 14414192267036959561025

theorem tailTrace_852673 : CollatzResearch.WordTrace tailWord_852673 prefixEnd_852673 14414192267036959561025 := by
  unfold tailWord_852673
  simp only [CollatzResearch.WordTrace]
  refine ⟨31099539239918820799714673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20733026159945880533143115 31099539239918820799714673)
  ·
    refine ⟨23324654429939115599786005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31099539239918820799714673 23324654429939115599786005)
    ·
      refine ⟨1093343176403396043739969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 23324654429939115599786005 1093343176403396043739969)
      ·
        refine ⟨820007382302547032804977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1093343176403396043739969 820007382302547032804977)
        ·
          refine ⟨615005536726910274603733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 820007382302547032804977 615005536726910274603733)
          ·
            refine ⟨14414192267036959561025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 615005536726910274603733 14414192267036959561025)
            ·
              rfl

theorem cell20_852673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 7].length) (baseStart_852673 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_852673 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_852673 prefixEnd_852673 := by exact prefixLift 852673
  have htrace : WordTrace (prefixWord ++ tailWord_852673) baseStart_852673 baseEnd_852673 := by
    simpa [prefixWord, tailWord_852673, baseEnd_852673] using wordTrace_append hprefix tailTrace_852673
  have hstable : (prefixWord ++ tailWord_852673).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852673).length < 2 ^ (prefixWord ++ tailWord_852673).sum := by decide
  have hdescent : baseEnd_852673 < baseStart_852673 := by decide
  rcases family_descends (prefixWord ++ tailWord_852673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852708 : List Nat := [2, 3, 1, 1, 1, 5, 1, 2, 4]
def baseStart_852708 : Nat := 118140960795 + 852708 * 2 ^ 59
def prefixEnd_852708 : Nat := 4983230072969 + 3 ^ 40 * 852708 * 2
def baseEnd_852708 : Nat := 389199166163693341980865

theorem tailTrace_852708 : CollatzResearch.WordTrace tailWord_852708 prefixEnd_852708 389199166163693341980865 := by
  unfold tailWord_852708
  simp only [CollatzResearch.WordTrace]
  refine ⟨15550407897396010888619389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20733877196528014518159185 15550407897396010888619389)
  ·
    refine ⟨5831402961523504083232271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15550407897396010888619389 5831402961523504083232271)
    ·
      refine ⟨8747104442285256124848407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5831402961523504083232271 8747104442285256124848407)
      ·
        refine ⟨13120656663427884187272611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8747104442285256124848407 13120656663427884187272611)
        ·
          refine ⟨19680984995141826280908917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13120656663427884187272611 19680984995141826280908917)
          ·
            refine ⟨1845092343294546213835211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19680984995141826280908917 1845092343294546213835211)
            ·
              refine ⟨2767638514941819320752817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1845092343294546213835211 2767638514941819320752817)
              ·
                refine ⟨2075728886206364490564613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2767638514941819320752817 2075728886206364490564613)
                ·
                  refine ⟨389199166163693341980865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2075728886206364490564613 389199166163693341980865)
                  ·
                    rfl

theorem cell20_852708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 2, 4].length) (baseStart_852708 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_852708 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_852708 prefixEnd_852708 := by exact prefixLift 852708
  have htrace : WordTrace (prefixWord ++ tailWord_852708) baseStart_852708 baseEnd_852708 := by
    simpa [prefixWord, tailWord_852708, baseEnd_852708] using wordTrace_append hprefix tailTrace_852708
  have hstable : (prefixWord ++ tailWord_852708).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852708).length < 2 ^ (prefixWord ++ tailWord_852708).sum := by decide
  have hdescent : baseEnd_852708 < baseStart_852708 := by decide
  rcases family_descends (prefixWord ++ tailWord_852708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852746 : List Nat := [3, 1, 2, 2, 1, 2, 4, 1, 4]
def baseStart_852746 : Nat := 118140960795 + 852746 * 2 ^ 59
def prefixEnd_852746 : Nat := 4983230072969 + 3 ^ 40 * 852746 * 2
def baseEnd_852746 : Nat := 389216510399134098714043

theorem tailTrace_852746 : CollatzResearch.WordTrace tailWord_852746 prefixEnd_852746 389216510399134098714043 := by
  unfold tailWord_852746
  simp only [CollatzResearch.WordTrace]
  refine ⟨7775550442163588566780523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20734801179102902844748061 7775550442163588566780523)
  ·
    refine ⟨11663325663245382850170785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7775550442163588566780523 11663325663245382850170785)
    ·
      refine ⟨8747494247434037137628089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11663325663245382850170785 8747494247434037137628089)
      ·
        refine ⟨6560620685575527853221067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8747494247434037137628089 6560620685575527853221067)
        ·
          refine ⟨9840931028363291779831601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6560620685575527853221067 9840931028363291779831601)
          ·
            refine ⟨7380698271272468834873701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9840931028363291779831601 7380698271272468834873701)
            ·
              refine ⟨1383880925863587906538819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7380698271272468834873701 1383880925863587906538819)
              ·
                refine ⟨2075821388795381859808229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1383880925863587906538819 2075821388795381859808229)
                ·
                  refine ⟨389216510399134098714043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2075821388795381859808229 389216510399134098714043)
                  ·
                    rfl

theorem cell20_852746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 4, 1, 4].length) (baseStart_852746 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_852746 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_852746 prefixEnd_852746 := by exact prefixLift 852746
  have htrace : WordTrace (prefixWord ++ tailWord_852746) baseStart_852746 baseEnd_852746 := by
    simpa [prefixWord, tailWord_852746, baseEnd_852746] using wordTrace_append hprefix tailTrace_852746
  have hstable : (prefixWord ++ tailWord_852746).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852746).length < 2 ^ (prefixWord ++ tailWord_852746).sum := by decide
  have hdescent : baseEnd_852746 < baseStart_852746 := by decide
  rcases family_descends (prefixWord ++ tailWord_852746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852770 : List Nat := [3, 3, 1, 1, 2, 2, 4, 4]
def baseStart_852770 : Nat := 118140960795 + 852770 * 2 ^ 59
def prefixEnd_852770 : Nat := 4983230072969 + 3 ^ 40 * 852770 * 2
def baseEnd_852770 : Nat := 129742488217698893971315

theorem tailTrace_852770 : CollatzResearch.WordTrace tailWord_852770 prefixEnd_852770 129742488217698893971315 := by
  unfold tailWord_852770
  simp only [CollatzResearch.WordTrace]
  refine ⟨7775769280141851591498941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20735384747044937577330509 7775769280141851591498941)
  ·
    refine ⟨2915913480053194346812103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7775769280141851591498941 2915913480053194346812103)
    ·
      refine ⟨4373870220079791520218155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2915913480053194346812103 4373870220079791520218155)
      ·
        refine ⟨6560805330119687280327233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4373870220079791520218155 6560805330119687280327233)
        ·
          refine ⟨4920603997589765460245425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6560805330119687280327233 4920603997589765460245425)
          ·
            refine ⟨3690452998192324095184069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4920603997589765460245425 3690452998192324095184069)
            ·
              refine ⟨691959937161060767847013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3690452998192324095184069 691959937161060767847013)
              ·
                refine ⟨129742488217698893971315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 691959937161060767847013 129742488217698893971315)
                ·
                  rfl

theorem cell20_852770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 4, 4].length) (baseStart_852770 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_852770 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_852770 prefixEnd_852770 := by exact prefixLift 852770
  have htrace : WordTrace (prefixWord ++ tailWord_852770) baseStart_852770 baseEnd_852770 := by
    simpa [prefixWord, tailWord_852770, baseEnd_852770] using wordTrace_append hprefix tailTrace_852770
  have hstable : (prefixWord ++ tailWord_852770).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852770).length < 2 ^ (prefixWord ++ tailWord_852770).sum := by decide
  have hdescent : baseEnd_852770 < baseStart_852770 := by decide
  rcases family_descends (prefixWord ++ tailWord_852770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852797 : List Nat := [1, 4, 1, 4, 2, 1, 3, 2, 2]
def baseStart_852797 : Nat := 118140960795 + 852797 * 2 ^ 59
def prefixEnd_852797 : Nat := 4983230072969 + 3 ^ 40 * 852797 * 2
def baseEnd_852797 : Nat := 389239788188804588013835

theorem tailTrace_852797 : CollatzResearch.WordTrace tailWord_852797 prefixEnd_852797 389239788188804588013835 := by
  unfold tailWord_852797
  simp only [CollatzResearch.WordTrace]
  refine ⟨31104061891469589977228645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20736041260979726651485763 31104061891469589977228645)
  ·
    refine ⟨5832011604650548120730371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31104061891469589977228645 5832011604650548120730371)
    ·
      refine ⟨8748017406975822181095557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5832011604650548120730371 8748017406975822181095557)
      ·
        refine ⟨1640253263807966658955417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8748017406975822181095557 1640253263807966658955417)
        ·
          refine ⟨1230189947855974994216563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1640253263807966658955417 1230189947855974994216563)
          ·
            refine ⟨1845284921783962491324845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1230189947855974994216563 1845284921783962491324845)
            ·
              refine ⟨691981845668985934246817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1845284921783962491324845 691981845668985934246817)
              ·
                refine ⟨518986384251739450685113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 691981845668985934246817 518986384251739450685113)
                ·
                  refine ⟨389239788188804588013835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 518986384251739450685113 389239788188804588013835)
                  ·
                    rfl

theorem cell20_852797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 3, 2, 2].length) (baseStart_852797 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_852797 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_852797 prefixEnd_852797 := by exact prefixLift 852797
  have htrace : WordTrace (prefixWord ++ tailWord_852797) baseStart_852797 baseEnd_852797 := by
    simpa [prefixWord, tailWord_852797, baseEnd_852797] using wordTrace_append hprefix tailTrace_852797
  have hstable : (prefixWord ++ tailWord_852797).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852797).length < 2 ^ (prefixWord ++ tailWord_852797).sum := by decide
  have hdescent : baseEnd_852797 < baseStart_852797 := by decide
  rcases family_descends (prefixWord ++ tailWord_852797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852805 : List Nat := [1, 3, 1, 1, 1, 2, 2, 5, 4]
def baseStart_852805 : Nat := 118140960795 + 852805 * 2 ^ 59
def prefixEnd_852805 : Nat := 4983230072969 + 3 ^ 40 * 852805 * 2
def baseEnd_852805 : Nat := 389243439606792115747135

theorem tailTrace_852805 : CollatzResearch.WordTrace tailWord_852805 prefixEnd_852805 389243439606792115747135 := by
  unfold tailWord_852805
  simp only [CollatzResearch.WordTrace]
  refine ⟨31104353675440607343519869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20736235783627071562346579 31104353675440607343519869)
  ·
    refine ⟨11664132628290227753819951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31104353675440607343519869 11664132628290227753819951)
    ·
      refine ⟨17496198942435341630729927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11664132628290227753819951 17496198942435341630729927)
      ·
        refine ⟨26244298413653012446094891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17496198942435341630729927 26244298413653012446094891)
        ·
          refine ⟨39366447620479518669142337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26244298413653012446094891 39366447620479518669142337)
          ·
            refine ⟨29524835715359639001856753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39366447620479518669142337 29524835715359639001856753)
            ·
              refine ⟨22143626786519729251392565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29524835715359639001856753 22143626786519729251392565)
              ·
                refine ⟨2075965011236224617318053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22143626786519729251392565 2075965011236224617318053)
                ·
                  refine ⟨389243439606792115747135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2075965011236224617318053 389243439606792115747135)
                  ·
                    rfl

theorem cell20_852805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 5, 4].length) (baseStart_852805 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_852805 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_852805 prefixEnd_852805 := by exact prefixLift 852805
  have htrace : WordTrace (prefixWord ++ tailWord_852805) baseStart_852805 baseEnd_852805 := by
    simpa [prefixWord, tailWord_852805, baseEnd_852805] using wordTrace_append hprefix tailTrace_852805
  have hstable : (prefixWord ++ tailWord_852805).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852805).length < 2 ^ (prefixWord ++ tailWord_852805).sum := by decide
  have hdescent : baseEnd_852805 < baseStart_852805 := by decide
  rcases family_descends (prefixWord ++ tailWord_852805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852846 : List Nat := [4, 1, 2, 3, 3, 7]
def baseStart_852846 : Nat := 118140960795 + 852846 * 2 ^ 59
def prefixEnd_852846 : Nat := 4983230072969 + 3 ^ 40 * 852846 * 2
def baseEnd_852846 : Nat := 14417116782369562791863

theorem tailTrace_852846 : CollatzResearch.WordTrace tailWord_852846 prefixEnd_852846 14417116782369562791863 := by
  unfold tailWord_852846
  simp only [CollatzResearch.WordTrace]
  refine ⟨3888231133536508918220299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20737232712194714230508261 3888231133536508918220299)
  ·
    refine ⟨5832346700304763377330449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3888231133536508918220299 5832346700304763377330449)
    ·
      refine ⟨4374260025228572532997837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5832346700304763377330449 4374260025228572532997837)
      ·
        refine ⟨1640347509460714699874189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4374260025228572532997837 1640347509460714699874189)
        ·
          refine ⟨615130316047768012452821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1640347509460714699874189 615130316047768012452821)
          ·
            refine ⟨14417116782369562791863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 615130316047768012452821 14417116782369562791863)
            ·
              rfl

theorem cell20_852846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 7].length) (baseStart_852846 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_852846 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_852846 prefixEnd_852846 := by exact prefixLift 852846
  have htrace : WordTrace (prefixWord ++ tailWord_852846) baseStart_852846 baseEnd_852846 := by
    simpa [prefixWord, tailWord_852846, baseEnd_852846] using wordTrace_append hprefix tailTrace_852846
  have hstable : (prefixWord ++ tailWord_852846).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852846).length < 2 ^ (prefixWord ++ tailWord_852846).sum := by decide
  have hdescent : baseEnd_852846 < baseStart_852846 := by decide
  rcases family_descends (prefixWord ++ tailWord_852846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852853 : List Nat := [1, 3, 4, 1, 1, 2, 1, 4, 3]
def baseStart_852853 : Nat := 118140960795 + 852853 * 2 ^ 59
def prefixEnd_852853 : Nat := 4983230072969 + 3 ^ 40 * 852853 * 2
def baseEnd_852853 : Nat := 389265348114717282146939

theorem tailTrace_852853 : CollatzResearch.WordTrace tailWord_852853 prefixEnd_852853 389265348114717282146939 := by
  unfold tailWord_852853
  simp only [CollatzResearch.WordTrace]
  refine ⟨31106104379266711541267213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20737402919511141027511475 31106104379266711541267213)
  ·
    refine ⟨11664789142225016827975205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31106104379266711541267213 11664789142225016827975205)
    ·
      refine ⟨2187147964167190655245351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11664789142225016827975205 2187147964167190655245351)
      ·
        refine ⟨3280721946250785982868027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2187147964167190655245351 3280721946250785982868027)
        ·
          refine ⟨4921082919376178974302041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3280721946250785982868027 4921082919376178974302041)
          ·
            refine ⟨3690812189532134230726531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4921082919376178974302041 3690812189532134230726531)
            ·
              refine ⟨5536218284298201346089797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3690812189532134230726531 5536218284298201346089797)
              ·
                refine ⟨1038040928305912752391837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5536218284298201346089797 1038040928305912752391837)
                ·
                  refine ⟨389265348114717282146939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1038040928305912752391837 389265348114717282146939)
                  ·
                    rfl

theorem cell20_852853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 4, 3].length) (baseStart_852853 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_852853 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_852853 prefixEnd_852853 := by exact prefixLift 852853
  have htrace : WordTrace (prefixWord ++ tailWord_852853) baseStart_852853 baseEnd_852853 := by
    simpa [prefixWord, tailWord_852853, baseEnd_852853] using wordTrace_append hprefix tailTrace_852853
  have hstable : (prefixWord ++ tailWord_852853).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852853).length < 2 ^ (prefixWord ++ tailWord_852853).sum := by decide
  have hdescent : baseEnd_852853 < baseStart_852853 := by decide
  rcases family_descends (prefixWord ++ tailWord_852853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852884 : List Nat := [2, 4, 2, 1, 1, 1, 5, 4]
def baseStart_852884 : Nat := 118140960795 + 852884 * 2 ^ 59
def prefixEnd_852884 : Nat := 4983230072969 + 3 ^ 40 * 852884 * 2
def baseEnd_852884 : Nat := 129759832453139650704493

theorem tailTrace_852884 : CollatzResearch.WordTrace tailWord_852884 prefixEnd_852884 129759832453139650704493 := by
  unfold tailWord_852884
  simp only [CollatzResearch.WordTrace]
  refine ⟨15553617521077201917822853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20738156694769602557097137 15553617521077201917822853)
  ·
    refine ⟨2916303285201975359591785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15553617521077201917822853 2916303285201975359591785)
    ·
      refine ⟨2187227463901481519693839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2916303285201975359591785 2187227463901481519693839)
      ·
        refine ⟨3280841195852222279540759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2187227463901481519693839 3280841195852222279540759)
        ·
          refine ⟨4921261793778333419311139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3280841195852222279540759 4921261793778333419311139)
          ·
            refine ⟨7381892690667500128966709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4921261793778333419311139 7381892690667500128966709)
            ·
              refine ⟨692052439750078137090629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7381892690667500128966709 692052439750078137090629)
              ·
                refine ⟨129759832453139650704493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 692052439750078137090629 129759832453139650704493)
                ·
                  rfl

theorem cell20_852884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 5, 4].length) (baseStart_852884 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_852884 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_852884 prefixEnd_852884 := by exact prefixLift 852884
  have htrace : WordTrace (prefixWord ++ tailWord_852884) baseStart_852884 baseEnd_852884 := by
    simpa [prefixWord, tailWord_852884, baseEnd_852884] using wordTrace_append hprefix tailTrace_852884
  have hstable : (prefixWord ++ tailWord_852884).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852884).length < 2 ^ (prefixWord ++ tailWord_852884).sum := by decide
  have hdescent : baseEnd_852884 < baseStart_852884 := by decide
  rcases family_descends (prefixWord ++ tailWord_852884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852919 : List Nat := [1, 1, 3, 1, 3, 1, 3, 3, 4]
def baseStart_852919 : Nat := 118140960795 + 852919 * 2 ^ 59
def prefixEnd_852919 : Nat := 4983230072969 + 3 ^ 40 * 852919 * 2
def baseEnd_852919 : Nat := 389295472313114385946669

theorem tailTrace_852919 : CollatzResearch.WordTrace tailWord_852919 prefixEnd_852919 389295472313114385946669 := by
  unfold tailWord_852919
  simp only [CollatzResearch.WordTrace]
  refine ⟨31108511597027604813169811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20739007731351736542113207 31108511597027604813169811)
  ·
    refine ⟨46662767395541407219754717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31108511597027604813169811 46662767395541407219754717)
    ·
      refine ⟨17498537773328027707408019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46662767395541407219754717 17498537773328027707408019)
      ·
        refine ⟨26247806659992041561112029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17498537773328027707408019 26247806659992041561112029)
        ·
          refine ⟨9842927497497015585417011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26247806659992041561112029 9842927497497015585417011)
          ·
            refine ⟨14764391246245523378125517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9842927497497015585417011 14764391246245523378125517)
            ·
              refine ⟨5536646717342071266797069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14764391246245523378125517 5536646717342071266797069)
              ·
                refine ⟨2076242519003276725048901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5536646717342071266797069 2076242519003276725048901)
                ·
                  refine ⟨389295472313114385946669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2076242519003276725048901 389295472313114385946669)
                  ·
                    rfl

theorem cell20_852919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 3, 4].length) (baseStart_852919 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_852919 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_852919 prefixEnd_852919 := by exact prefixLift 852919
  have htrace : WordTrace (prefixWord ++ tailWord_852919) baseStart_852919 baseEnd_852919 := by
    simpa [prefixWord, tailWord_852919, baseEnd_852919] using wordTrace_append hprefix tailTrace_852919
  have hstable : (prefixWord ++ tailWord_852919).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852919).length < 2 ^ (prefixWord ++ tailWord_852919).sum := by decide
  have hdescent : baseEnd_852919 < baseStart_852919 := by decide
  rcases family_descends (prefixWord ++ tailWord_852919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852943 : List Nat := [1, 1, 2, 1, 1, 6, 4, 4]
def baseStart_852943 : Nat := 118140960795 + 852943 * 2 ^ 59
def prefixEnd_852943 : Nat := 4983230072969 + 3 ^ 40 * 852943 * 2
def baseEnd_852943 : Nat := 129768808855692323048857

theorem tailTrace_852943 : CollatzResearch.WordTrace tailWord_852943 prefixEnd_852943 129768808855692323048857 := by
  unfold tailWord_852943
  simp only [CollatzResearch.WordTrace]
  refine ⟨31109386948940656912043483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20739591299293771274695655 31109386948940656912043483)
  ·
    refine ⟨46664080423410985368065225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31109386948940656912043483 46664080423410985368065225)
    ·
      refine ⟨34998060317558239026048919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46664080423410985368065225 34998060317558239026048919)
      ·
        refine ⟨52497090476337358539073379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34998060317558239026048919 52497090476337358539073379)
        ·
          refine ⟨78745635714506037808610069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52497090476337358539073379 78745635714506037808610069)
          ·
            refine ⟨3691201674117470522278597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 78745635714506037808610069 3691201674117470522278597)
            ·
              refine ⟨692100313897025722927237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3691201674117470522278597 692100313897025722927237)
              ·
                refine ⟨129768808855692323048857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 692100313897025722927237 129768808855692323048857)
                ·
                  rfl

theorem cell20_852943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 4, 4].length) (baseStart_852943 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_852943 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_852943 prefixEnd_852943 := by exact prefixLift 852943
  have htrace : WordTrace (prefixWord ++ tailWord_852943) baseStart_852943 baseEnd_852943 := by
    simpa [prefixWord, tailWord_852943, baseEnd_852943] using wordTrace_append hprefix tailTrace_852943
  have hstable : (prefixWord ++ tailWord_852943).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852943).length < 2 ^ (prefixWord ++ tailWord_852943).sum := by decide
  have hdescent : baseEnd_852943 < baseStart_852943 := by decide
  rcases family_descends (prefixWord ++ tailWord_852943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852949 : List Nat := [1, 3, 2, 3, 4, 1, 1, 3, 2]
def baseStart_852949 : Nat := 118140960795 + 852949 * 2 ^ 59
def prefixEnd_852949 : Nat := 4983230072969 + 3 ^ 40 * 852949 * 2
def baseEnd_852949 : Nat := 389309165130567614946547

theorem tailTrace_852949 : CollatzResearch.WordTrace tailWord_852949 prefixEnd_852949 389309165130567614946547 := by
  unfold tailWord_852949
  simp only [CollatzResearch.WordTrace]
  refine ⟨31109605786918919936761901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20739737191279279957841267 31109605786918919936761901)
  ·
    refine ⟨11666102170094594976285713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31109605786918919936761901 11666102170094594976285713)
    ·
      refine ⟨8749576627570946232214285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11666102170094594976285713 8749576627570946232214285)
      ·
        refine ⟨3281091235339104837080357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8749576627570946232214285 3281091235339104837080357)
        ·
          refine ⟨615204606626082156952567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3281091235339104837080357 615204606626082156952567)
          ·
            refine ⟨922806909939123235428851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 615204606626082156952567 922806909939123235428851)
            ·
              refine ⟨1384210364908684853143277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 922806909939123235428851 1384210364908684853143277)
              ·
                refine ⟨519078886840756819928729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1384210364908684853143277 519078886840756819928729)
                ·
                  refine ⟨389309165130567614946547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 519078886840756819928729 389309165130567614946547)
                  ·
                    rfl

theorem cell20_852949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 1, 3, 2].length) (baseStart_852949 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_852949 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_852949 prefixEnd_852949 := by exact prefixLift 852949
  have htrace : WordTrace (prefixWord ++ tailWord_852949) baseStart_852949 baseEnd_852949 := by
    simpa [prefixWord, tailWord_852949, baseEnd_852949] using wordTrace_append hprefix tailTrace_852949
  have hstable : (prefixWord ++ tailWord_852949).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852949).length < 2 ^ (prefixWord ++ tailWord_852949).sum := by decide
  have hdescent : baseEnd_852949 < baseStart_852949 := by decide
  rcases family_descends (prefixWord ++ tailWord_852949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852953 : List Nat := [1, 2, 1, 2, 5, 1, 3, 3, 2]
def baseStart_852953 : Nat := 118140960795 + 852953 * 2 ^ 59
def prefixEnd_852953 : Nat := 4983230072969 + 3 ^ 40 * 852953 * 2
def baseEnd_852953 : Nat := 389310990839561378813197

theorem tailTrace_852953 : CollatzResearch.WordTrace tailWord_852953 prefixEnd_852953 389310990839561378813197 := by
  unfold tailWord_852953
  simp only [CollatzResearch.WordTrace]
  refine ⟨31109751678904428619907513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20739834452602952413271675 31109751678904428619907513)
  ·
    refine ⟨23332313759178321464930635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31109751678904428619907513 23332313759178321464930635)
    ·
      refine ⟨34998470638767482197395953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23332313759178321464930635 34998470638767482197395953)
      ·
        refine ⟨26248852979075611648046965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34998470638767482197395953 26248852979075611648046965)
        ·
          refine ⟨2460829966788338592004403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26248852979075611648046965 2460829966788338592004403)
          ·
            refine ⟨3691244950182507888006605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2460829966788338592004403 3691244950182507888006605)
            ·
              refine ⟨1384216856318440458002477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3691244950182507888006605 1384216856318440458002477)
              ·
                refine ⟨519081321119415171750929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1384216856318440458002477 519081321119415171750929)
                ·
                  refine ⟨389310990839561378813197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 519081321119415171750929 389310990839561378813197)
                  ·
                    rfl

theorem cell20_852953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 3, 3, 2].length) (baseStart_852953 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_852953 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_852953 prefixEnd_852953 := by exact prefixLift 852953
  have htrace : WordTrace (prefixWord ++ tailWord_852953) baseStart_852953 baseEnd_852953 := by
    simpa [prefixWord, tailWord_852953, baseEnd_852953] using wordTrace_append hprefix tailTrace_852953
  have hstable : (prefixWord ++ tailWord_852953).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852953).length < 2 ^ (prefixWord ++ tailWord_852953).sum := by decide
  have hdescent : baseEnd_852953 < baseStart_852953 := by decide
  rcases family_descends (prefixWord ++ tailWord_852953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_852970 : List Nat := [3, 1, 3, 1, 2, 3, 3, 2, 2]
def baseStart_852970 : Nat := 118140960795 + 852970 * 2 ^ 59
def prefixEnd_852970 : Nat := 4983230072969 + 3 ^ 40 * 852970 * 2
def baseEnd_852970 : Nat := 389318750102784875246461

theorem tailTrace_852970 : CollatzResearch.WordTrace tailWord_852970 prefixEnd_852970 389318750102784875246461 := by
  unfold tailWord_852970
  simp only [CollatzResearch.WordTrace]
  refine ⟨7777592929960710130819091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20740247813228560348850909 7777592929960710130819091)
  ·
    refine ⟨11666389394941065196228637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7777592929960710130819091 11666389394941065196228637)
    ·
      refine ⟨4374896023102899448585739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11666389394941065196228637 4374896023102899448585739)
      ·
        refine ⟨6562344034654349172878609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4374896023102899448585739 6562344034654349172878609)
        ·
          refine ⟨4921758025990761879658957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6562344034654349172878609 4921758025990761879658957)
          ·
            refine ⟨1845659259746535704872109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4921758025990761879658957 1845659259746535704872109)
            ·
              refine ⟨692122222404950889327041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1845659259746535704872109 692122222404950889327041)
              ·
                refine ⟨519091666803713166995281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 692122222404950889327041 519091666803713166995281)
                ·
                  refine ⟨389318750102784875246461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 519091666803713166995281 389318750102784875246461)
                  ·
                    rfl

theorem cell20_852970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 3, 2, 2].length) (baseStart_852970 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_852970 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_852970 prefixEnd_852970 := by exact prefixLift 852970
  have htrace : WordTrace (prefixWord ++ tailWord_852970) baseStart_852970 baseEnd_852970 := by
    simpa [prefixWord, tailWord_852970, baseEnd_852970] using wordTrace_append hprefix tailTrace_852970
  have hstable : (prefixWord ++ tailWord_852970).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_852970).length < 2 ^ (prefixWord ++ tailWord_852970).sum := by decide
  have hdescent : baseEnd_852970 < baseStart_852970 := by decide
  rcases family_descends (prefixWord ++ tailWord_852970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853009 : List Nat := [1, 2, 2, 1, 1, 2, 1, 3, 7]
def baseStart_853009 : Nat := 118140960795 + 853009 * 2 ^ 59
def prefixEnd_853009 : Nat := 4983230072969 + 3 ^ 40 * 853009 * 2
def baseEnd_853009 : Nat := 389336550765474072946301

theorem tailTrace_853009 : CollatzResearch.WordTrace tailWord_853009 prefixEnd_853009 389336550765474072946301 := by
  unfold tailWord_853009
  simp only [CollatzResearch.WordTrace]
  refine ⟨31111794166701550183946081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20741196111134366789297387 31111794166701550183946081)
  ·
    refine ⟨23333845625026162637959561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31111794166701550183946081 23333845625026162637959561)
    ·
      refine ⟨17500384218769621978469671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23333845625026162637959561 17500384218769621978469671)
      ·
        refine ⟨26250576328154432967704507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17500384218769621978469671 26250576328154432967704507)
        ·
          refine ⟨39375864492231649451556761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26250576328154432967704507 39375864492231649451556761)
          ·
            refine ⟨29531898369173737088667571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39375864492231649451556761 29531898369173737088667571)
            ·
              refine ⟨44297847553760605633001357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29531898369173737088667571 44297847553760605633001357)
              ·
                refine ⟨16611692832660227112375509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44297847553760605633001357 16611692832660227112375509)
                ·
                  refine ⟨389336550765474072946301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16611692832660227112375509 389336550765474072946301)
                  ·
                    rfl

theorem cell20_853009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 7].length) (baseStart_853009 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_853009 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_853009 prefixEnd_853009 := by exact prefixLift 853009
  have htrace : WordTrace (prefixWord ++ tailWord_853009) baseStart_853009 baseEnd_853009 := by
    simpa [prefixWord, tailWord_853009, baseEnd_853009] using wordTrace_append hprefix tailTrace_853009
  have hstable : (prefixWord ++ tailWord_853009).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853009).length < 2 ^ (prefixWord ++ tailWord_853009).sum := by decide
  have hdescent : baseEnd_853009 < baseStart_853009 := by decide
  rcases family_descends (prefixWord ++ tailWord_853009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853047 : List Nat := [1, 1, 3, 1, 2, 2, 1, 2, 7]
def baseStart_853047 : Nat := 118140960795 + 853047 * 2 ^ 59
def prefixEnd_853047 : Nat := 4983230072969 + 3 ^ 40 * 853047 * 2
def baseEnd_853047 : Nat := 389353895000914829679479

theorem tailTrace_853047 : CollatzResearch.WordTrace tailWord_853047 prefixEnd_853047 389353895000914829679479 := by
  unfold tailWord_853047
  simp only [CollatzResearch.WordTrace]
  refine ⟨31113180140563882673829395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20742120093709255115886263 31113180140563882673829395)
  ·
    refine ⟨46669770210845824010744093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31113180140563882673829395 46669770210845824010744093)
    ·
      refine ⟨17501163829067184004029035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46669770210845824010744093 17501163829067184004029035)
      ·
        refine ⟨26251745743600776006043553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17501163829067184004029035 26251745743600776006043553)
        ·
          refine ⟨19688809307700582004532665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26251745743600776006043553 19688809307700582004532665)
          ·
            refine ⟨14766606980775436503399499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19688809307700582004532665 14766606980775436503399499)
            ·
              refine ⟨22149910471163154755099249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14766606980775436503399499 22149910471163154755099249)
              ·
                refine ⟨16612432853372366066324437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22149910471163154755099249 16612432853372366066324437)
                ·
                  refine ⟨389353895000914829679479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16612432853372366066324437 389353895000914829679479)
                  ·
                    rfl

theorem cell20_853047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 7].length) (baseStart_853047 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_853047 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_853047 prefixEnd_853047 := by exact prefixLift 853047
  have htrace : WordTrace (prefixWord ++ tailWord_853047) baseStart_853047 baseEnd_853047 := by
    simpa [prefixWord, tailWord_853047, baseEnd_853047] using wordTrace_append hprefix tailTrace_853047
  have hstable : (prefixWord ++ tailWord_853047).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853047).length < 2 ^ (prefixWord ++ tailWord_853047).sum := by decide
  have hdescent : baseEnd_853047 < baseStart_853047 := by decide
  rcases family_descends (prefixWord ++ tailWord_853047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853088 : List Nat := [2, 1, 1, 3, 2, 2, 1, 6, 2]
def baseStart_853088 : Nat := 118140960795 + 853088 * 2 ^ 59
def prefixEnd_853088 : Nat := 4983230072969 + 3 ^ 40 * 853088 * 2
def baseEnd_853088 : Nat := 389372608518100909312645

theorem tailTrace_853088 : CollatzResearch.WordTrace tailWord_853088 prefixEnd_853088 389372608518100909312645 := by
  unfold tailWord_853088
  simp only [CollatzResearch.WordTrace]
  refine ⟨15557337766707673338035959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20743117022276897784047945 15557337766707673338035959)
  ·
    refine ⟨23336006650061510007053939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15557337766707673338035959 23336006650061510007053939)
    ·
      refine ⟨35004009975092265010580909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23336006650061510007053939 35004009975092265010580909)
      ·
        refine ⟨13126503740659599378967841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35004009975092265010580909 13126503740659599378967841)
        ·
          refine ⟨9844877805494699534225881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13126503740659599378967841 9844877805494699534225881)
          ·
            refine ⟨7383658354121024650669411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9844877805494699534225881 7383658354121024650669411)
            ·
              refine ⟨11075487531181536976004117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7383658354121024650669411 11075487531181536976004117)
              ·
                refine ⟨519163478024134545750193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11075487531181536976004117 519163478024134545750193)
                ·
                  refine ⟨389372608518100909312645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 519163478024134545750193 389372608518100909312645)
                  ·
                    rfl

theorem cell20_853088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 6, 2].length) (baseStart_853088 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_853088 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_853088 prefixEnd_853088 := by exact prefixLift 853088
  have htrace : WordTrace (prefixWord ++ tailWord_853088) baseStart_853088 baseEnd_853088 := by
    simpa [prefixWord, tailWord_853088, baseEnd_853088] using wordTrace_append hprefix tailTrace_853088
  have hstable : (prefixWord ++ tailWord_853088).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853088).length < 2 ^ (prefixWord ++ tailWord_853088).sum := by decide
  have hdescent : baseEnd_853088 < baseStart_853088 := by decide
  rcases family_descends (prefixWord ++ tailWord_853088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853098 : List Nat := [3, 1, 3, 2, 2, 2, 3, 1, 3]
def baseStart_853098 : Nat := 118140960795 + 853098 * 2 ^ 59
def prefixEnd_853098 : Nat := 4983230072969 + 3 ^ 40 * 853098 * 2
def baseEnd_853098 : Nat := 389377172790585318979271

theorem tailTrace_853098 : CollatzResearch.WordTrace tailWord_853098 prefixEnd_853098 389377172790585318979271 := by
  unfold tailWord_853098
  simp only [CollatzResearch.WordTrace]
  refine ⟨7778760065844779595983987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20743360175586078922623965 7778760065844779595983987)
  ·
    refine ⟨11668140098767169393975981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7778760065844779595983987 11668140098767169393975981)
    ·
      refine ⟨4375552537037688522740993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11668140098767169393975981 4375552537037688522740993)
      ·
        refine ⟨3281664402778266392055745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4375552537037688522740993 3281664402778266392055745)
        ·
          refine ⟨2461248302083699794041809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3281664402778266392055745 2461248302083699794041809)
          ·
            refine ⟨1845936226562774845531357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2461248302083699794041809 1845936226562774845531357)
            ·
              refine ⟨692226084961040567074259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1845936226562774845531357 692226084961040567074259)
              ·
                refine ⟨1038339127441560850611389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 692226084961040567074259 1038339127441560850611389)
                ·
                  refine ⟨389377172790585318979271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1038339127441560850611389 389377172790585318979271)
                  ·
                    rfl

theorem cell20_853098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 3, 1, 3].length) (baseStart_853098 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_853098 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_853098 prefixEnd_853098 := by exact prefixLift 853098
  have htrace : WordTrace (prefixWord ++ tailWord_853098) baseStart_853098 baseEnd_853098 := by
    simpa [prefixWord, tailWord_853098, baseEnd_853098] using wordTrace_append hprefix tailTrace_853098
  have hstable : (prefixWord ++ tailWord_853098).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853098).length < 2 ^ (prefixWord ++ tailWord_853098).sum := by decide
  have hdescent : baseEnd_853098 < baseStart_853098 := by decide
  rcases family_descends (prefixWord ++ tailWord_853098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853116 : List Nat := [2, 2, 2, 1, 1, 3, 3, 6]
def baseStart_853116 : Nat := 118140960795 + 853116 * 2 ^ 59
def prefixEnd_853116 : Nat := 4983230072969 + 3 ^ 40 * 853116 * 2
def baseEnd_853116 : Nat := 129795129493685752126399

theorem tailTrace_853116 : CollatzResearch.WordTrace tailWord_853116 prefixEnd_853116 129795129493685752126399 := by
  unfold tailWord_853116
  simp only [CollatzResearch.WordTrace]
  refine ⟨15557848388656953729045601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20743797851542604972060801 15557848388656953729045601)
  ·
    refine ⟨11668386291492715296784201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15557848388656953729045601 11668386291492715296784201)
    ·
      refine ⟨8751289718619536472588151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11668386291492715296784201 8751289718619536472588151)
      ·
        refine ⟨13126934577929304708882227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8751289718619536472588151 13126934577929304708882227)
        ·
          refine ⟨19690401866893957063323341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13126934577929304708882227 19690401866893957063323341)
          ·
            refine ⟨7383900700085233898746253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19690401866893957063323341 7383900700085233898746253)
            ·
              refine ⟨2768962762531962712029845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7383900700085233898746253 2768962762531962712029845)
              ·
                refine ⟨129795129493685752126399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2768962762531962712029845 129795129493685752126399)
                ·
                  rfl

theorem cell20_853116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 6].length) (baseStart_853116 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_853116 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_853116 prefixEnd_853116 := by exact prefixLift 853116
  have htrace : WordTrace (prefixWord ++ tailWord_853116) baseStart_853116 baseEnd_853116 := by
    simpa [prefixWord, tailWord_853116, baseEnd_853116] using wordTrace_append hprefix tailTrace_853116
  have hstable : (prefixWord ++ tailWord_853116).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853116).length < 2 ^ (prefixWord ++ tailWord_853116).sum := by decide
  have hdescent : baseEnd_853116 < baseStart_853116 := by decide
  rcases family_descends (prefixWord ++ tailWord_853116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853123 : List Nat := [1, 1, 1, 3, 3, 2, 1, 1, 7]
def baseStart_853123 : Nat := 118140960795 + 853123 * 2 ^ 59
def prefixEnd_853123 : Nat := 4983230072969 + 3 ^ 40 * 853123 * 2
def baseEnd_853123 : Nat := 389388583471796343145835

theorem tailTrace_853123 : CollatzResearch.WordTrace tailWord_853123 prefixEnd_853123 389388583471796343145835 := by
  unfold tailWord_853123
  simp only [CollatzResearch.WordTrace]
  refine ⟨31115952088288547653596023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20743968058859031769064015 31115952088288547653596023)
  ·
    refine ⟨46673928132432821480394035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31115952088288547653596023 46673928132432821480394035)
    ·
      refine ⟨70010892198649232220591053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46673928132432821480394035 70010892198649232220591053)
      ·
        refine ⟨26254084574493462082721645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70010892198649232220591053 26254084574493462082721645)
        ·
          refine ⟨9845281715435048281020617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26254084574493462082721645 9845281715435048281020617)
          ·
            refine ⟨7383961286576286210765463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9845281715435048281020617 7383961286576286210765463)
            ·
              refine ⟨11075941929864429316148195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7383961286576286210765463 11075941929864429316148195)
              ·
                refine ⟨16613912894796643974222293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11075941929864429316148195 16613912894796643974222293)
                ·
                  refine ⟨389388583471796343145835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16613912894796643974222293 389388583471796343145835)
                  ·
                    rfl

theorem cell20_853123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 7].length) (baseStart_853123 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_853123 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_853123 prefixEnd_853123 := by exact prefixLift 853123
  have htrace : WordTrace (prefixWord ++ tailWord_853123) baseStart_853123 baseEnd_853123 := by
    simpa [prefixWord, tailWord_853123, baseEnd_853123] using wordTrace_append hprefix tailTrace_853123
  have hstable : (prefixWord ++ tailWord_853123).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853123).length < 2 ^ (prefixWord ++ tailWord_853123).sum := by decide
  have hdescent : baseEnd_853123 < baseStart_853123 := by decide
  rcases family_descends (prefixWord ++ tailWord_853123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853150 : List Nat := [4, 3, 1, 1, 2, 2, 2, 5]
def baseStart_853150 : Nat := 118140960795 + 853150 * 2 ^ 59
def prefixEnd_853150 : Nat := 4983230072969 + 3 ^ 40 * 853150 * 2
def baseEnd_853150 : Nat := 129800302335834749748575

theorem tailTrace_853150 : CollatzResearch.WordTrace tailWord_853150 prefixEnd_853150 129800302335834749748575 := by
  unfold tailWord_853150
  simp only [CollatzResearch.WordTrace]
  refine ⟨3889617107398841408103613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20744624572793820843219269 3889617107398841408103613)
  ·
    refine ⟨1458606415274565528038855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3889617107398841408103613 1458606415274565528038855)
    ·
      refine ⟨2187909622911848292058283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1458606415274565528038855 2187909622911848292058283)
      ·
        refine ⟨3281864434367772438087425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2187909622911848292058283 3281864434367772438087425)
        ·
          refine ⟨2461398325775829328565569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3281864434367772438087425 2461398325775829328565569)
          ·
            refine ⟨1846048744331871996424177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2461398325775829328565569 1846048744331871996424177)
            ·
              refine ⟨1384536558248903997318133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1846048744331871996424177 1384536558248903997318133)
              ·
                refine ⟨129800302335834749748575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1384536558248903997318133 129800302335834749748575)
                ·
                  rfl

theorem cell20_853150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 2, 5].length) (baseStart_853150 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_853150 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_853150 prefixEnd_853150 := by exact prefixLift 853150
  have htrace : WordTrace (prefixWord ++ tailWord_853150) baseStart_853150 baseEnd_853150 := by
    simpa [prefixWord, tailWord_853150, baseEnd_853150] using wordTrace_append hprefix tailTrace_853150
  have hstable : (prefixWord ++ tailWord_853150).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853150).length < 2 ^ (prefixWord ++ tailWord_853150).sum := by decide
  have hdescent : baseEnd_853150 < baseStart_853150 := by decide
  rcases family_descends (prefixWord ++ tailWord_853150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853157 : List Nat := [1, 3, 1, 2, 1, 4, 4, 1, 3]
def baseStart_853157 : Nat := 118140960795 + 853157 * 2 ^ 59
def prefixEnd_853157 : Nat := 4983230072969 + 3 ^ 40 * 853157 * 2
def baseEnd_853157 : Nat := 389404101998243336012363

theorem tailTrace_853157 : CollatzResearch.WordTrace tailWord_853157 prefixEnd_853157 389404101998243336012363 := by
  unfold tailWord_853157
  simp only [CollatzResearch.WordTrace]
  refine ⟨31117192170165371460333725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20744794780110247640222483 31117192170165371460333725)
  ·
    refine ⟨11668947063812014297625147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31117192170165371460333725 11668947063812014297625147)
    ·
      refine ⟨17503420595718021446437721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11668947063812014297625147 17503420595718021446437721)
      ·
        refine ⟨13127565446788516084828291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17503420595718021446437721 13127565446788516084828291)
        ·
          refine ⟨19691348170182774127242437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13127565446788516084828291 19691348170182774127242437)
          ·
            refine ⟨3692127781909270148857957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19691348170182774127242437 3692127781909270148857957)
            ·
              refine ⟨692273959107988152910867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3692127781909270148857957 692273959107988152910867)
              ·
                refine ⟨1038410938661982229366301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 692273959107988152910867 1038410938661982229366301)
                ·
                  refine ⟨389404101998243336012363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1038410938661982229366301 389404101998243336012363)
                  ·
                    rfl

theorem cell20_853157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 4, 1, 3].length) (baseStart_853157 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_853157 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_853157 prefixEnd_853157 := by exact prefixLift 853157
  have htrace : WordTrace (prefixWord ++ tailWord_853157) baseStart_853157 baseEnd_853157 := by
    simpa [prefixWord, tailWord_853157, baseEnd_853157] using wordTrace_append hprefix tailTrace_853157
  have hstable : (prefixWord ++ tailWord_853157).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853157).length < 2 ^ (prefixWord ++ tailWord_853157).sum := by decide
  have hdescent : baseEnd_853157 < baseStart_853157 := by decide
  rcases family_descends (prefixWord ++ tailWord_853157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853190 : List Nat := [6, 1, 2, 2, 2, 1, 2, 2, 2]
def baseStart_853190 : Nat := 118140960795 + 853190 * 2 ^ 59
def prefixEnd_853190 : Nat := 4983230072969 + 3 ^ 40 * 853190 * 2
def baseEnd_853190 : Nat := 389419164097441887912229

theorem tailTrace_853190 : CollatzResearch.WordTrace tailWord_853190 prefixEnd_853190 389419164097441887912229 := by
  unfold tailWord_853190
  simp only [CollatzResearch.WordTrace]
  refine ⟨972449868095181815508907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 20745597186030545397523349 972449868095181815508907)
  ·
    refine ⟨1458674802142772723263361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 972449868095181815508907 1458674802142772723263361)
    ·
      refine ⟨1094006101607079542447521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1458674802142772723263361 1094006101607079542447521)
      ·
        refine ⟨820504576205309656835641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1094006101607079542447521 820504576205309656835641)
        ·
          refine ⟨615378432153982242626731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 820504576205309656835641 615378432153982242626731)
          ·
            refine ⟨923067648230973363940097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 615378432153982242626731 923067648230973363940097)
            ·
              refine ⟨692300736173230022955073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 923067648230973363940097 692300736173230022955073)
              ·
                refine ⟨519225552129922517216305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 692300736173230022955073 519225552129922517216305)
                ·
                  refine ⟨389419164097441887912229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 519225552129922517216305 389419164097441887912229)
                  ·
                    rfl

theorem cell20_853190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 2, 2, 2].length) (baseStart_853190 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_853190 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_853190 prefixEnd_853190 := by exact prefixLift 853190
  have htrace : WordTrace (prefixWord ++ tailWord_853190) baseStart_853190 baseEnd_853190 := by
    simpa [prefixWord, tailWord_853190, baseEnd_853190] using wordTrace_append hprefix tailTrace_853190
  have hstable : (prefixWord ++ tailWord_853190).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853190).length < 2 ^ (prefixWord ++ tailWord_853190).sum := by decide
  have hdescent : baseEnd_853190 < baseStart_853190 := by decide
  rcases family_descends (prefixWord ++ tailWord_853190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853216 : List Nat := [2, 1, 1, 3, 1, 4, 2, 3, 3]
def baseStart_853216 : Nat := 118140960795 + 853216 * 2 ^ 59
def prefixEnd_853216 : Nat := 4983230072969 + 3 ^ 40 * 853216 * 2
def baseEnd_853216 : Nat := 389431031205901353045455

theorem tailTrace_853216 : CollatzResearch.WordTrace tailWord_853216 prefixEnd_853216 389431031205901353045455 := by
  unfold tailWord_853216
  simp only [CollatzResearch.WordTrace]
  refine ⟨15559672038475812268365751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20746229384634416357821001 15559672038475812268365751)
  ·
    refine ⟨23339508057713718402548627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15559672038475812268365751 23339508057713718402548627)
    ·
      refine ⟨35009262086570577603822941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23339508057713718402548627 35009262086570577603822941)
      ·
        refine ⟨13128473282463966601433603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35009262086570577603822941 13128473282463966601433603)
        ·
          refine ⟨19692709923695949902150405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13128473282463966601433603 19692709923695949902150405)
          ·
            refine ⟨3692383110692990606653201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19692709923695949902150405 3692383110692990606653201)
            ·
              refine ⟨2769287333019742954989901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3692383110692990606653201 2769287333019742954989901)
              ·
                refine ⟨1038482749882403608121213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2769287333019742954989901 1038482749882403608121213)
                ·
                  refine ⟨389431031205901353045455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1038482749882403608121213 389431031205901353045455)
                  ·
                    rfl

theorem cell20_853216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 3, 3].length) (baseStart_853216 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_853216 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_853216 prefixEnd_853216 := by exact prefixLift 853216
  have htrace : WordTrace (prefixWord ++ tailWord_853216) baseStart_853216 baseEnd_853216 := by
    simpa [prefixWord, tailWord_853216, baseEnd_853216] using wordTrace_append hprefix tailTrace_853216
  have hstable : (prefixWord ++ tailWord_853216).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853216).length < 2 ^ (prefixWord ++ tailWord_853216).sum := by decide
  have hdescent : baseEnd_853216 < baseStart_853216 := by decide
  rcases family_descends (prefixWord ++ tailWord_853216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853230 : List Nat := [4, 1, 2, 1, 1, 1, 2, 8]
def baseStart_853230 : Nat := 118140960795 + 853230 * 2 ^ 59
def prefixEnd_853230 : Nat := 4983230072969 + 3 ^ 40 * 853230 * 2
def baseEnd_853230 : Nat := 129812473729126508859577

theorem tailTrace_853230 : CollatzResearch.WordTrace tailWord_853230 prefixEnd_853230 129812473729126508859577 := by
  unfold tailWord_853230
  simp only [CollatzResearch.WordTrace]
  refine ⟨3889981837362613115967643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20746569799267269951827429 3889981837362613115967643)
  ·
    refine ⟨5834972756043919673951465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3889981837362613115967643 5834972756043919673951465)
    ·
      refine ⟨4376229567032939755463599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5834972756043919673951465 4376229567032939755463599)
      ·
        refine ⟨6564344350549409633195399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4376229567032939755463599 6564344350549409633195399)
        ·
          refine ⟨9846516525824114449793099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6564344350549409633195399 9846516525824114449793099)
          ·
            refine ⟨14769774788736171674689649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9846516525824114449793099 14769774788736171674689649)
            ·
              refine ⟨11077331091552128756017237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14769774788736171674689649 11077331091552128756017237)
              ·
                refine ⟨129812473729126508859577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11077331091552128756017237 129812473729126508859577)
                ·
                  rfl

theorem cell20_853230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 8].length) (baseStart_853230 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_853230 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_853230 prefixEnd_853230 := by exact prefixLift 853230
  have htrace : WordTrace (prefixWord ++ tailWord_853230) baseStart_853230 baseEnd_853230 := by
    simpa [prefixWord, tailWord_853230, baseEnd_853230] using wordTrace_append hprefix tailTrace_853230
  have hstable : (prefixWord ++ tailWord_853230).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853230).length < 2 ^ (prefixWord ++ tailWord_853230).sum := by decide
  have hdescent : baseEnd_853230 < baseStart_853230 := by decide
  rcases family_descends (prefixWord ++ tailWord_853230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853271 : List Nat := [1, 1, 3, 4, 1, 1, 5, 1, 3]
def baseStart_853271 : Nat := 118140960795 + 853271 * 2 ^ 59
def prefixEnd_853271 : Nat := 4983230072969 + 3 ^ 40 * 853271 * 2
def baseEnd_853271 : Nat := 389456134704565606211897

theorem tailTrace_853271 : CollatzResearch.WordTrace tailWord_853271 prefixEnd_853271 389456134704565606211897 := by
  unfold tailWord_853271
  simp only [CollatzResearch.WordTrace]
  refine ⟨31121350091752368929983667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20747566727834912619989111 31121350091752368929983667)
  ·
    refine ⟨46682025137628553394975501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31121350091752368929983667 46682025137628553394975501)
    ·
      refine ⟨17505759426610707523115813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46682025137628553394975501 17505759426610707523115813)
      ·
        refine ⟨3282329892489507660584215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17505759426610707523115813 3282329892489507660584215)
        ·
          refine ⟨4923494838734261490876323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3282329892489507660584215 4923494838734261490876323)
          ·
            refine ⟨7385242258101392236314485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4923494838734261490876323 7385242258101392236314485)
            ·
              refine ⟨692366461697005522154483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7385242258101392236314485 692366461697005522154483)
              ·
                refine ⟨1038549692545508283231725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 692366461697005522154483 1038549692545508283231725)
                ·
                  refine ⟨389456134704565606211897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1038549692545508283231725 389456134704565606211897)
                  ·
                    rfl

theorem cell20_853271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 5, 1, 3].length) (baseStart_853271 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_853271 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_853271 prefixEnd_853271 := by exact prefixLift 853271
  have htrace : WordTrace (prefixWord ++ tailWord_853271) baseStart_853271 baseEnd_853271 := by
    simpa [prefixWord, tailWord_853271, baseEnd_853271] using wordTrace_append hprefix tailTrace_853271
  have hstable : (prefixWord ++ tailWord_853271).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853271).length < 2 ^ (prefixWord ++ tailWord_853271).sum := by decide
  have hdescent : baseEnd_853271 < baseStart_853271 := by decide
  rcases family_descends (prefixWord ++ tailWord_853271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853285 : List Nat := [1, 3, 1, 2, 4, 1, 4, 4]
def baseStart_853285 : Nat := 118140960795 + 853285 * 2 ^ 59
def prefixEnd_853285 : Nat := 4983230072969 + 3 ^ 40 * 853285 * 2
def baseEnd_853285 : Nat := 129820841562014593248391

theorem tailTrace_853285 : CollatzResearch.WordTrace tailWord_853285 prefixEnd_853285 129820841562014593248391 := by
  unfold tailWord_853285
  simp only [CollatzResearch.WordTrace]
  refine ⟨31121860713701649320993309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20747907142467766213995539 31121860713701649320993309)
  ·
    refine ⟨11670697767638118495372491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31121860713701649320993309 11670697767638118495372491)
    ·
      refine ⟨17506046651457177743058737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11670697767638118495372491 17506046651457177743058737)
      ·
        refine ⟨13129534988592883307294053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17506046651457177743058737 13129534988592883307294053)
        ·
          refine ⟨2461787810361165620117635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13129534988592883307294053 2461787810361165620117635)
          ·
            refine ⟨3692681715541748430176453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2461787810361165620117635 3692681715541748430176453)
            ·
              refine ⟨692377821664077830658085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3692681715541748430176453 692377821664077830658085)
              ·
                refine ⟨129820841562014593248391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 692377821664077830658085 129820841562014593248391)
                ·
                  rfl

theorem cell20_853285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 4, 4].length) (baseStart_853285 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_853285 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_853285 prefixEnd_853285 := by exact prefixLift 853285
  have htrace : WordTrace (prefixWord ++ tailWord_853285) baseStart_853285 baseEnd_853285 := by
    simpa [prefixWord, tailWord_853285, baseEnd_853285] using wordTrace_append hprefix tailTrace_853285
  have hstable : (prefixWord ++ tailWord_853285).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853285).length < 2 ^ (prefixWord ++ tailWord_853285).sum := by decide
  have hdescent : baseEnd_853285 < baseStart_853285 := by decide
  rcases family_descends (prefixWord ++ tailWord_853285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853344 : List Nat := [2, 1, 1, 3, 4, 1, 2, 6]
def baseStart_853344 : Nat := 118140960795 + 853344 * 2 ^ 59
def prefixEnd_853344 : Nat := 4983230072969 + 3 ^ 40 * 853344 * 2
def baseEnd_853344 : Nat := 129829817964567265592755

theorem tailTrace_853344 : CollatzResearch.WordTrace tailWord_853344 prefixEnd_853344 129829817964567265592755 := by
  unfold tailWord_853344
  simp only [CollatzResearch.WordTrace]
  refine ⟨15562006310243951198695543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20749341746991934931594057 15562006310243951198695543)
  ·
    refine ⟨23343009465365926798043315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15562006310243951198695543 23343009465365926798043315)
    ·
      refine ⟨35014514198048890197064973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23343009465365926798043315 35014514198048890197064973)
      ·
        refine ⟨13130442824268333823899365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35014514198048890197064973 13130442824268333823899365)
        ·
          refine ⟨2461958029550312591981131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13130442824268333823899365 2461958029550312591981131)
          ·
            refine ⟨3692937044325468887971697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2461958029550312591981131 3692937044325468887971697)
            ·
              refine ⟨2769702783244101665978773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3692937044325468887971697 2769702783244101665978773)
              ·
                refine ⟨129829817964567265592755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2769702783244101665978773 129829817964567265592755)
                ·
                  rfl

theorem cell20_853344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 6].length) (baseStart_853344 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_853344 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_853344 prefixEnd_853344 := by exact prefixLift 853344
  have htrace : WordTrace (prefixWord ++ tailWord_853344) baseStart_853344 baseEnd_853344 := by
    simpa [prefixWord, tailWord_853344, baseEnd_853344] using wordTrace_append hprefix tailTrace_853344
  have hstable : (prefixWord ++ tailWord_853344).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853344).length < 2 ^ (prefixWord ++ tailWord_853344).sum := by decide
  have hdescent : baseEnd_853344 < baseStart_853344 := by decide
  rcases family_descends (prefixWord ++ tailWord_853344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853374 : List Nat := [4, 2, 3, 2, 2, 1, 1, 5]
def baseStart_853374 : Nat := 118140960795 + 853374 * 2 ^ 59
def prefixEnd_853374 : Nat := 4983230072969 + 3 ^ 40 * 853374 * 2
def baseEnd_853374 : Nat := 129834382237051675259381

theorem tailTrace_853374 : CollatzResearch.WordTrace tailWord_853374 prefixEnd_853374 129834382237051675259381 := by
  unfold tailWord_853374
  simp only [CollatzResearch.WordTrace]
  refine ⟨3890638351297402190122897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20750071206919478347322117 3890638351297402190122897)
  ·
    refine ⟨2917978763473051642592173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3890638351297402190122897 2917978763473051642592173)
    ·
      refine ⟨1094242036302394365972065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2917978763473051642592173 1094242036302394365972065)
      ·
        refine ⟨820681527226795774479049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1094242036302394365972065 820681527226795774479049)
        ·
          refine ⟨615511145420096830859287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 820681527226795774479049 615511145420096830859287)
          ·
            refine ⟨923266718130145246288931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 615511145420096830859287 923266718130145246288931)
            ·
              refine ⟨1384900077195217869433397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 923266718130145246288931 1384900077195217869433397)
              ·
                refine ⟨129834382237051675259381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1384900077195217869433397 129834382237051675259381)
                ·
                  rfl

theorem cell20_853374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 1, 5].length) (baseStart_853374 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_853374 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_853374 prefixEnd_853374 := by exact prefixLift 853374
  have htrace : WordTrace (prefixWord ++ tailWord_853374) baseStart_853374 baseEnd_853374 := by
    simpa [prefixWord, tailWord_853374, baseEnd_853374] using wordTrace_append hprefix tailTrace_853374
  have hstable : (prefixWord ++ tailWord_853374).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853374).length < 2 ^ (prefixWord ++ tailWord_853374).sum := by decide
  have hdescent : baseEnd_853374 < baseStart_853374 := by decide
  rcases family_descends (prefixWord ++ tailWord_853374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853378 : List Nat := [3, 4, 2, 1, 1, 1, 3, 5]
def baseStart_853378 : Nat := 118140960795 + 853378 * 2 ^ 59
def prefixEnd_853378 : Nat := 4983230072969 + 3 ^ 40 * 853378 * 2
def baseEnd_853378 : Nat := 129834990806716263214931

theorem tailTrace_853378 : CollatzResearch.WordTrace tailWord_853378 prefixEnd_853378 129834990806716263214931 := by
  unfold tailWord_853378
  simp only [CollatzResearch.WordTrace]
  refine ⟨7781313175591181551032197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20750168468243150802752525 7781313175591181551032197)
  ·
    refine ⟨1458996220423346540818537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7781313175591181551032197 1458996220423346540818537)
    ·
      refine ⟨1094247165317509905613903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1458996220423346540818537 1094247165317509905613903)
      ·
        refine ⟨1641370747976264858420855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1094247165317509905613903 1641370747976264858420855)
        ·
          refine ⟨2462056121964397287631283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1641370747976264858420855 2462056121964397287631283)
          ·
            refine ⟨3693084182946595931446925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2462056121964397287631283 3693084182946595931446925)
            ·
              refine ⟨1384906568604973474292597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3693084182946595931446925 1384906568604973474292597)
              ·
                refine ⟨129834990806716263214931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1384906568604973474292597 129834990806716263214931)
                ·
                  rfl

theorem cell20_853378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 3, 5].length) (baseStart_853378 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_853378 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_853378 prefixEnd_853378 := by exact prefixLift 853378
  have htrace : WordTrace (prefixWord ++ tailWord_853378) baseStart_853378 baseEnd_853378 := by
    simpa [prefixWord, tailWord_853378, baseEnd_853378] using wordTrace_append hprefix tailTrace_853378
  have hstable : (prefixWord ++ tailWord_853378).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853378).length < 2 ^ (prefixWord ++ tailWord_853378).sum := by decide
  have hdescent : baseEnd_853378 < baseStart_853378 := by decide
  rcases family_descends (prefixWord ++ tailWord_853378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853465 : List Nat := [1, 2, 1, 2, 4, 2, 1, 2, 5]
def baseStart_853465 : Nat := 118140960795 + 853465 * 2 ^ 59
def prefixEnd_853465 : Nat := 4983230072969 + 3 ^ 40 * 853465 * 2
def baseEnd_853465 : Nat := 389544681590763153744437

theorem tailTrace_853465 : CollatzResearch.WordTrace tailWord_853465 prefixEnd_853465 389544681590763153744437 := by
  unfold tailWord_853465
  simp only [CollatzResearch.WordTrace]
  refine ⟨31128425853049540062545849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20752283902033026708363899 31128425853049540062545849)
  ·
    refine ⟨23346319389787155046909387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31128425853049540062545849 23346319389787155046909387)
    ·
      refine ⟨35019479084680732570364081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23346319389787155046909387 35019479084680732570364081)
      ·
        refine ⟨26264609313510549427773061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35019479084680732570364081 26264609313510549427773061)
        ·
          refine ⟨4924614246283228017707449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26264609313510549427773061 4924614246283228017707449)
          ·
            refine ⟨3693460684712421013280587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4924614246283228017707449 3693460684712421013280587)
            ·
              refine ⟨5540191027068631519920881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3693460684712421013280587 5540191027068631519920881)
              ·
                refine ⟨4155143270301473639940661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5540191027068631519920881 4155143270301473639940661)
                ·
                  refine ⟨389544681590763153744437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4155143270301473639940661 389544681590763153744437)
                  ·
                    rfl

theorem cell20_853465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 2, 5].length) (baseStart_853465 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_853465 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_853465 prefixEnd_853465 := by exact prefixLift 853465
  have htrace : WordTrace (prefixWord ++ tailWord_853465) baseStart_853465 baseEnd_853465 := by
    simpa [prefixWord, tailWord_853465, baseEnd_853465] using wordTrace_append hprefix tailTrace_853465
  have hstable : (prefixWord ++ tailWord_853465).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853465).length < 2 ^ (prefixWord ++ tailWord_853465).sum := by decide
  have hdescent : baseEnd_853465 < baseStart_853465 := by decide
  rcases family_descends (prefixWord ++ tailWord_853465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853485 : List Nat := [1, 5, 1, 3, 2, 2, 1, 1, 4]
def baseStart_853485 : Nat := 118140960795 + 853485 * 2 ^ 59
def prefixEnd_853485 : Nat := 4983230072969 + 3 ^ 40 * 853485 * 2
def baseEnd_853485 : Nat := 389553810135731973077689

theorem tailTrace_853485 : CollatzResearch.WordTrace tailWord_853485 prefixEnd_853485 389553810135731973077689 := by
  unfold tailWord_853485
  simp only [CollatzResearch.WordTrace]
  refine ⟨31129155312977083478273909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20752770208651388985515939 31129155312977083478273909)
  ·
    refine ⟨2918358310591601576088179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31129155312977083478273909 2918358310591601576088179)
    ·
      refine ⟨4377537465887402364132269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2918358310591601576088179 4377537465887402364132269)
      ·
        refine ⟨1641576549707775886549601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4377537465887402364132269 1641576549707775886549601)
        ·
          refine ⟨1231182412280831914912201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1641576549707775886549601 1231182412280831914912201)
          ·
            refine ⟨923386809210623936184151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1231182412280831914912201 923386809210623936184151)
            ·
              refine ⟨1385080213815935904276227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 923386809210623936184151 1385080213815935904276227)
              ·
                refine ⟨2077620320723903856414341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1385080213815935904276227 2077620320723903856414341)
                ·
                  refine ⟨389553810135731973077689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2077620320723903856414341 389553810135731973077689)
                  ·
                    rfl

theorem cell20_853485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 1, 1, 4].length) (baseStart_853485 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_853485 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_853485 prefixEnd_853485 := by exact prefixLift 853485
  have htrace : WordTrace (prefixWord ++ tailWord_853485) baseStart_853485 baseEnd_853485 := by
    simpa [prefixWord, tailWord_853485, baseEnd_853485] using wordTrace_append hprefix tailTrace_853485
  have hstable : (prefixWord ++ tailWord_853485).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853485).length < 2 ^ (prefixWord ++ tailWord_853485).sum := by decide
  have hdescent : baseEnd_853485 < baseStart_853485 := by decide
  rcases family_descends (prefixWord ++ tailWord_853485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853489 : List Nat := [1, 2, 2, 2, 3, 2, 3, 1, 4]
def baseStart_853489 : Nat := 118140960795 + 853489 * 2 ^ 59
def prefixEnd_853489 : Nat := 4983230072969 + 3 ^ 40 * 853489 * 2
def baseEnd_853489 : Nat := 389555635844725736944339

theorem tailTrace_853489 : CollatzResearch.WordTrace tailWord_853489 prefixEnd_853489 389555635844725736944339 := by
  unfold tailWord_853489
  simp only [CollatzResearch.WordTrace]
  refine ⟨31129301204962592161419521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20752867469975061440946347 31129301204962592161419521)
  ·
    refine ⟨23346975903721944121064641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31129301204962592161419521 23346975903721944121064641)
    ·
      refine ⟨17510231927791458090798481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23346975903721944121064641 17510231927791458090798481)
      ·
        refine ⟨13132673945843593568098861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17510231927791458090798481 13132673945843593568098861)
        ·
          refine ⟨4924752729691347588037073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13132673945843593568098861 4924752729691347588037073)
          ·
            refine ⟨3693564547268510691027805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4924752729691347588037073 3693564547268510691027805)
            ·
              refine ⟨1385086705225691509135427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3693564547268510691027805 1385086705225691509135427)
              ·
                refine ⟨2077630057838537263703141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1385086705225691509135427 2077630057838537263703141)
                ·
                  refine ⟨389555635844725736944339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2077630057838537263703141 389555635844725736944339)
                  ·
                    rfl

theorem cell20_853489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 3, 1, 4].length) (baseStart_853489 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_853489 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_853489 prefixEnd_853489 := by exact prefixLift 853489
  have htrace : WordTrace (prefixWord ++ tailWord_853489) baseStart_853489 baseEnd_853489 := by
    simpa [prefixWord, tailWord_853489, baseEnd_853489] using wordTrace_append hprefix tailTrace_853489
  have hstable : (prefixWord ++ tailWord_853489).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853489).length < 2 ^ (prefixWord ++ tailWord_853489).sum := by decide
  have hdescent : baseEnd_853489 < baseStart_853489 := by decide
  rcases family_descends (prefixWord ++ tailWord_853489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853496 : List Nat := [2, 1, 2, 1, 1, 6, 2, 5]
def baseStart_853496 : Nat := 118140960795 + 853496 * 2 ^ 59
def prefixEnd_853496 : Nat := 4983230072969 + 3 ^ 40 * 853496 * 2
def baseEnd_853496 : Nat := 129852943611821607903659

theorem tailTrace_853496 : CollatzResearch.WordTrace tailWord_853496 prefixEnd_853496 129852943611821607903659 := by
  unfold tailWord_853496
  simp only [CollatzResearch.WordTrace]
  refine ⟨15564778257968616178462171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20753037677291488237949561 15564778257968616178462171)
  ·
    refine ⟨23347167386952924267693257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15564778257968616178462171 23347167386952924267693257)
    ·
      refine ⟨17510375540214693200769943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23347167386952924267693257 17510375540214693200769943)
      ·
        refine ⟨26265563310322039801154915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17510375540214693200769943 26265563310322039801154915)
        ·
          refine ⟨39398344965483059701732373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26265563310322039801154915 39398344965483059701732373)
          ·
            refine ⟨1846797420257018423518705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 39398344965483059701732373 1846797420257018423518705)
            ·
              refine ⟨1385098065192763817639029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1846797420257018423518705 1385098065192763817639029)
              ·
                refine ⟨129852943611821607903659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1385098065192763817639029 129852943611821607903659)
                ·
                  rfl

theorem cell20_853496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 2, 5].length) (baseStart_853496 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_853496 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_853496 prefixEnd_853496 := by exact prefixLift 853496
  have htrace : WordTrace (prefixWord ++ tailWord_853496) baseStart_853496 baseEnd_853496 := by
    simpa [prefixWord, tailWord_853496, baseEnd_853496] using wordTrace_append hprefix tailTrace_853496
  have hstable : (prefixWord ++ tailWord_853496).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853496).length < 2 ^ (prefixWord ++ tailWord_853496).sum := by decide
  have hdescent : baseEnd_853496 < baseStart_853496 := by decide
  rcases family_descends (prefixWord ++ tailWord_853496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853596 : List Nat := [2, 2, 4, 1, 2, 2, 1, 1, 5]
def baseStart_853596 : Nat := 118140960795 + 853596 * 2 ^ 59
def prefixEnd_853596 : Nat := 4983230072969 + 3 ^ 40 * 853596 * 2
def baseEnd_853596 : Nat := 389604473560308920377235

theorem tailTrace_853596 : CollatzResearch.WordTrace tailWord_853596 prefixEnd_853596 389604473560308920377235 := by
  unfold tailWord_853596
  simp only [CollatzResearch.WordTrace]
  refine ⟨15566601907787474717782321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20755469210383299623709761 15566601907787474717782321)
  ·
    refine ⟨11674951430840606038336741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15566601907787474717782321 11674951430840606038336741)
    ·
      refine ⟨2189053393282613632188139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11674951430840606038336741 2189053393282613632188139)
      ·
        refine ⟨3283580089923920448282209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2189053393282613632188139 3283580089923920448282209)
        ·
          refine ⟨2462685067442940336211657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3283580089923920448282209 2462685067442940336211657)
          ·
            refine ⟨1847013800582205252158743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2462685067442940336211657 1847013800582205252158743)
            ·
              refine ⟨2770520700873307878238115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1847013800582205252158743 2770520700873307878238115)
              ·
                refine ⟨4155781051309961817357173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2770520700873307878238115 4155781051309961817357173)
                ·
                  refine ⟨389604473560308920377235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4155781051309961817357173 389604473560308920377235)
                  ·
                    rfl

theorem cell20_853596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 1, 5].length) (baseStart_853596 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_853596 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_853596 prefixEnd_853596 := by exact prefixLift 853596
  have htrace : WordTrace (prefixWord ++ tailWord_853596) baseStart_853596 baseEnd_853596 := by
    simpa [prefixWord, tailWord_853596, baseEnd_853596] using wordTrace_append hprefix tailTrace_853596
  have hstable : (prefixWord ++ tailWord_853596).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853596).length < 2 ^ (prefixWord ++ tailWord_853596).sum := by decide
  have hdescent : baseEnd_853596 < baseStart_853596 := by decide
  rcases family_descends (prefixWord ++ tailWord_853596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853603 : List Nat := [1, 1, 1, 5, 1, 4, 2, 1, 4]
def baseStart_853603 : Nat := 118140960795 + 853603 * 2 ^ 59
def prefixEnd_853603 : Nat := 4983230072969 + 3 ^ 40 * 853603 * 2
def baseEnd_853603 : Nat := 389607668551048007143873

theorem tailTrace_853603 : CollatzResearch.WordTrace tailWord_853603 prefixEnd_853603 389607668551048007143873 := by
  unfold tailWord_853603
  simp only [CollatzResearch.WordTrace]
  refine ⟨31133459126549589631069463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20755639417699726420712975 31133459126549589631069463)
  ·
    refine ⟨46700188689824384446604195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31133459126549589631069463 46700188689824384446604195)
    ·
      refine ⟨70050283034736576669906293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46700188689824384446604195 70050283034736576669906293)
      ·
        refine ⟨6567214034506554062803715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 70050283034736576669906293 6567214034506554062803715)
        ·
          refine ⟨9850821051759831094205573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6567214034506554062803715 9850821051759831094205573)
          ·
            refine ⟨1847028947204968330163545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9850821051759831094205573 1847028947204968330163545)
            ·
              refine ⟨1385271710403726247622659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1847028947204968330163545 1385271710403726247622659)
              ·
                refine ⟨2077907565605589371433989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1385271710403726247622659 2077907565605589371433989)
                ·
                  refine ⟨389607668551048007143873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2077907565605589371433989 389607668551048007143873)
                  ·
                    rfl

theorem cell20_853603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 2, 1, 4].length) (baseStart_853603 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_853603 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_853603 prefixEnd_853603 := by exact prefixLift 853603
  have htrace : WordTrace (prefixWord ++ tailWord_853603) baseStart_853603 baseEnd_853603 := by
    simpa [prefixWord, tailWord_853603, baseEnd_853603] using wordTrace_append hprefix tailTrace_853603
  have hstable : (prefixWord ++ tailWord_853603).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853603).length < 2 ^ (prefixWord ++ tailWord_853603).sum := by decide
  have hdescent : baseEnd_853603 < baseStart_853603 := by decide
  rcases family_descends (prefixWord ++ tailWord_853603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853617 : List Nat := [1, 2, 2, 2, 1, 1, 1, 7, 3]
def baseStart_853617 : Nat := 118140960795 + 853617 * 2 ^ 59
def prefixEnd_853617 : Nat := 4983230072969 + 3 ^ 40 * 853617 * 2
def baseEnd_853617 : Nat := 389614058532526180677149

theorem tailTrace_853617 : CollatzResearch.WordTrace tailWord_853617 prefixEnd_853617 389614058532526180677149 := by
  unfold tailWord_853617
  simp only [CollatzResearch.WordTrace]
  refine ⟨31133969748498870022079105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20755979832332580014719403 31133969748498870022079105)
  ·
    refine ⟨23350477311374152516559329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31133969748498870022079105 23350477311374152516559329)
    ·
      refine ⟨17512857983530614387419497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23350477311374152516559329 17512857983530614387419497)
      ·
        refine ⟨13134643487647960790564623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17512857983530614387419497 13134643487647960790564623)
        ·
          refine ⟨19701965231471941185846935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13134643487647960790564623 19701965231471941185846935)
          ·
            refine ⟨29552947847207911778770403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19701965231471941185846935 29552947847207911778770403)
            ·
              refine ⟨44329421770811867668155605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29552947847207911778770403 44329421770811867668155605)
              ·
                refine ⟨1038970822753403148472397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 44329421770811867668155605 1038970822753403148472397)
                ·
                  refine ⟨389614058532526180677149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1038970822753403148472397 389614058532526180677149)
                  ·
                    rfl

theorem cell20_853617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 7, 3].length) (baseStart_853617 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_853617 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_853617 prefixEnd_853617 := by exact prefixLift 853617
  have htrace : WordTrace (prefixWord ++ tailWord_853617) baseStart_853617 baseEnd_853617 := by
    simpa [prefixWord, tailWord_853617, baseEnd_853617] using wordTrace_append hprefix tailTrace_853617
  have hstable : (prefixWord ++ tailWord_853617).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853617).length < 2 ^ (prefixWord ++ tailWord_853617).sum := by decide
  have hdescent : baseEnd_853617 < baseStart_853617 := by decide
  rcases family_descends (prefixWord ++ tailWord_853617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853655 : List Nat := [1, 1, 3, 3, 2, 2, 2, 1, 5]
def baseStart_853655 : Nat := 118140960795 + 853655 * 2 ^ 59
def prefixEnd_853655 : Nat := 4983230072969 + 3 ^ 40 * 853655 * 2
def baseEnd_853655 : Nat := 389631402767966937410327

theorem tailTrace_853655 : CollatzResearch.WordTrace tailWord_853655 prefixEnd_853655 389631402767966937410327 := by
  unfold tailWord_853655
  simp only [CollatzResearch.WordTrace]
  refine ⟨31135355722361202511962419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20756903814907468341308279 31135355722361202511962419)
  ·
    refine ⟨46703033583541803767943629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31135355722361202511962419 46703033583541803767943629)
    ·
      refine ⟨17513637593828176412978861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46703033583541803767943629 17513637593828176412978861)
      ·
        refine ⟨6567614097685566154867073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17513637593828176412978861 6567614097685566154867073)
        ·
          refine ⟨4925710573264174616150305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6567614097685566154867073 4925710573264174616150305)
          ·
            refine ⟨3694282929948130962112729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4925710573264174616150305 3694282929948130962112729)
            ·
              refine ⟨2770712197461098221584547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3694282929948130962112729 2770712197461098221584547)
              ·
                refine ⟨4156068296191647332376821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2770712197461098221584547 4156068296191647332376821)
                ·
                  refine ⟨389631402767966937410327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4156068296191647332376821 389631402767966937410327)
                  ·
                    rfl

theorem cell20_853655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 1, 5].length) (baseStart_853655 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_853655 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_853655 prefixEnd_853655 := by exact prefixLift 853655
  have htrace : WordTrace (prefixWord ++ tailWord_853655) baseStart_853655 baseEnd_853655 := by
    simpa [prefixWord, tailWord_853655, baseEnd_853655] using wordTrace_append hprefix tailTrace_853655
  have hstable : (prefixWord ++ tailWord_853655).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853655).length < 2 ^ (prefixWord ++ tailWord_853655).sum := by decide
  have hdescent : baseEnd_853655 < baseStart_853655 := by decide
  rcases family_descends (prefixWord ++ tailWord_853655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853669 : List Nat := [1, 3, 1, 2, 1, 2, 3, 7]
def baseStart_853669 : Nat := 118140960795 + 853669 * 2 ^ 59
def prefixEnd_853669 : Nat := 4983230072969 + 3 ^ 40 * 853669 * 2
def baseEnd_853669 : Nat := 129879264249815036981201

theorem tailTrace_853669 : CollatzResearch.WordTrace tailWord_853669 prefixEnd_853669 129879264249815036981201 := by
  unfold tailWord_853669
  simp only [CollatzResearch.WordTrace]
  refine ⟨31135866344310482902972061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20757244229540321935314707 31135866344310482902972061)
  ·
    refine ⟨11675949879116431088614523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31135866344310482902972061 11675949879116431088614523)
    ·
      refine ⟨17513924818674646632921785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11675949879116431088614523 17513924818674646632921785)
      ·
        refine ⟨13135443614005984974691339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17513924818674646632921785 13135443614005984974691339)
        ·
          refine ⟨19703165421008977462037009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13135443614005984974691339 19703165421008977462037009)
          ·
            refine ⟨14777374065756733096527757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19703165421008977462037009 14777374065756733096527757)
            ·
              refine ⟨5541515274658774911197909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14777374065756733096527757 5541515274658774911197909)
              ·
                refine ⟨129879264249815036981201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5541515274658774911197909 129879264249815036981201)
                ·
                  rfl

theorem cell20_853669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 7].length) (baseStart_853669 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_853669 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_853669 prefixEnd_853669 := by exact prefixLift 853669
  have htrace : WordTrace (prefixWord ++ tailWord_853669) baseStart_853669 baseEnd_853669 := by
    simpa [prefixWord, tailWord_853669, baseEnd_853669] using wordTrace_append hprefix tailTrace_853669
  have hstable : (prefixWord ++ tailWord_853669).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853669).length < 2 ^ (prefixWord ++ tailWord_853669).sum := by decide
  have hdescent : baseEnd_853669 < baseStart_853669 := by decide
  rcases family_descends (prefixWord ++ tailWord_853669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853709 : List Nat := [1, 6, 2, 1, 1, 3, 2, 2, 2]
def baseStart_853709 : Nat := 118140960795 + 853709 * 2 ^ 59
def prefixEnd_853709 : Nat := 4983230072969 + 3 ^ 40 * 853709 * 2
def baseEnd_853709 : Nat := 389656049839382749610107

theorem tailTrace_853709 : CollatzResearch.WordTrace tailWord_853709 prefixEnd_853709 389656049839382749610107 := by
  unfold tailWord_853709
  simp only [CollatzResearch.WordTrace]
  refine ⟨31137325264165569734428181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20758216842777046489618787 31137325264165569734428181)
  ·
    refine ⟨1459562121757761081301321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 31137325264165569734428181 1459562121757761081301321)
    ·
      refine ⟨1094671591318320810975991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1459562121757761081301321 1094671591318320810975991)
      ·
        refine ⟨1642007386977481216463987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1094671591318320810975991 1642007386977481216463987)
        ·
          refine ⟨2463011080466221824695981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1642007386977481216463987 2463011080466221824695981)
          ·
            refine ⟨923629155174833184260993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2463011080466221824695981 923629155174833184260993)
            ·
              refine ⟨692721866381124888195745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 923629155174833184260993 692721866381124888195745)
              ·
                refine ⟨519541399785843666146809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 692721866381124888195745 519541399785843666146809)
                ·
                  refine ⟨389656049839382749610107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 519541399785843666146809 389656049839382749610107)
                  ·
                    rfl

theorem cell20_853709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 2, 2, 2].length) (baseStart_853709 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_853709 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_853709 prefixEnd_853709 := by exact prefixLift 853709
  have htrace : WordTrace (prefixWord ++ tailWord_853709) baseStart_853709 baseEnd_853709 := by
    simpa [prefixWord, tailWord_853709, baseEnd_853709] using wordTrace_append hprefix tailTrace_853709
  have hstable : (prefixWord ++ tailWord_853709).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853709).length < 2 ^ (prefixWord ++ tailWord_853709).sum := by decide
  have hdescent : baseEnd_853709 < baseStart_853709 := by decide
  rcases family_descends (prefixWord ++ tailWord_853709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853710 : List Nat := [4, 1, 1, 1, 3, 1, 4, 2, 3]
def baseStart_853710 : Nat := 118140960795 + 853710 * 2 ^ 59
def prefixEnd_853710 : Nat := 4983230072969 + 3 ^ 40 * 853710 * 2
def baseEnd_853710 : Nat := 389656506266631190576769

theorem tailTrace_853710 : CollatzResearch.WordTrace tailWord_853710 prefixEnd_853710 389656506266631190576769 := by
  unfold tailWord_853710
  simp only [CollatzResearch.WordTrace]
  refine ⟨3892170217145243363151823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20758241158107964603476389 3892170217145243363151823)
  ·
    refine ⟨5838255325717865044727735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3892170217145243363151823 5838255325717865044727735)
    ·
      refine ⟨8757382988576797567091603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5838255325717865044727735 8757382988576797567091603)
      ·
        refine ⟨13136074482865196350637405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8757382988576797567091603 13136074482865196350637405)
        ·
          refine ⟨4926027931074448631489027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13136074482865196350637405 4926027931074448631489027)
          ·
            refine ⟨7389041896611672947233541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4926027931074448631489027 7389041896611672947233541)
            ·
              refine ⟨1385445355614688677606289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7389041896611672947233541 1385445355614688677606289)
              ·
                refine ⟨1039084016711016508204717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1385445355614688677606289 1039084016711016508204717)
                ·
                  refine ⟨389656506266631190576769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1039084016711016508204717 389656506266631190576769)
                  ·
                    rfl

theorem cell20_853710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 4, 2, 3].length) (baseStart_853710 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_853710 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_853710 prefixEnd_853710 := by exact prefixLift 853710
  have htrace : WordTrace (prefixWord ++ tailWord_853710) baseStart_853710 baseEnd_853710 := by
    simpa [prefixWord, tailWord_853710, baseEnd_853710] using wordTrace_append hprefix tailTrace_853710
  have hstable : (prefixWord ++ tailWord_853710).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853710).length < 2 ^ (prefixWord ++ tailWord_853710).sum := by decide
  have hdescent : baseEnd_853710 < baseStart_853710 := by decide
  rcases family_descends (prefixWord ++ tailWord_853710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853713 : List Nat := [1, 2, 2, 1, 2, 6, 2, 2, 2]
def baseStart_853713 : Nat := 118140960795 + 853713 * 2 ^ 59
def prefixEnd_853713 : Nat := 4983230072969 + 3 ^ 40 * 853713 * 2
def baseEnd_853713 : Nat := 389657875548376513476757

theorem tailTrace_853713 : CollatzResearch.WordTrace tailWord_853713 prefixEnd_853713 389657875548376513476757 := by
  unfold tailWord_853713
  simp only [CollatzResearch.WordTrace]
  refine ⟨31137471156151078417573793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20758314104100718945049195 31137471156151078417573793)
  ·
    refine ⟨23353103367113308813180345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31137471156151078417573793 23353103367113308813180345)
    ·
      refine ⟨17514827525334981609885259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23353103367113308813180345 17514827525334981609885259)
      ·
        refine ⟨26272241288002472414827889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17514827525334981609885259 26272241288002472414827889)
        ·
          refine ⟨19704180966001854311120917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26272241288002472414827889 19704180966001854311120917)
          ·
            refine ⟨923633482781336920833793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 19704180966001854311120917 923633482781336920833793)
            ·
              refine ⟨692725112086002690625345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 923633482781336920833793 692725112086002690625345)
              ·
                refine ⟨519543834064502017969009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 692725112086002690625345 519543834064502017969009)
                ·
                  refine ⟨389657875548376513476757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 519543834064502017969009 389657875548376513476757)
                  ·
                    rfl

theorem cell20_853713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 6, 2, 2, 2].length) (baseStart_853713 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_853713 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_853713 prefixEnd_853713 := by exact prefixLift 853713
  have htrace : WordTrace (prefixWord ++ tailWord_853713) baseStart_853713 baseEnd_853713 := by
    simpa [prefixWord, tailWord_853713, baseEnd_853713] using wordTrace_append hprefix tailTrace_853713
  have hstable : (prefixWord ++ tailWord_853713).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853713).length < 2 ^ (prefixWord ++ tailWord_853713).sum := by decide
  have hdescent : baseEnd_853713 < baseStart_853713 := by decide
  rcases family_descends (prefixWord ++ tailWord_853713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853738 : List Nat := [3, 1, 3, 1, 1, 1, 3, 1, 6]
def baseStart_853738 : Nat := 118140960795 + 853738 * 2 ^ 59
def prefixEnd_853738 : Nat := 4983230072969 + 3 ^ 40 * 853738 * 2
def baseEnd_853738 : Nat := 389669286229587537643321

theorem tailTrace_853738 : CollatzResearch.WordTrace tailWord_853738 prefixEnd_853738 389669286229587537643321 := by
  unfold tailWord_853738
  simp only [CollatzResearch.WordTrace]
  refine ⟨7784595745265126921808467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20758921987373671791489245 7784595745265126921808467)
  ·
    refine ⟨11676893617897690382712701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7784595745265126921808467 11676893617897690382712701)
    ·
      refine ⟨4378835106711633893517263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11676893617897690382712701 4378835106711633893517263)
      ·
        refine ⟨6568252660067450840275895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4378835106711633893517263 6568252660067450840275895)
        ·
          refine ⟨9852378990101176260413843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6568252660067450840275895 9852378990101176260413843)
          ·
            refine ⟨14778568485151764390620765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9852378990101176260413843 14778568485151764390620765)
            ·
              refine ⟨5541963181931911646482787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14778568485151764390620765 5541963181931911646482787)
              ·
                refine ⟨8312944772897867469724181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5541963181931911646482787 8312944772897867469724181)
                ·
                  refine ⟨389669286229587537643321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8312944772897867469724181 389669286229587537643321)
                  ·
                    rfl

theorem cell20_853738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 1, 6].length) (baseStart_853738 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_853738 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_853738 prefixEnd_853738 := by exact prefixLift 853738
  have htrace : WordTrace (prefixWord ++ tailWord_853738) baseStart_853738 baseEnd_853738 := by
    simpa [prefixWord, tailWord_853738, baseEnd_853738] using wordTrace_append hprefix tailTrace_853738
  have hstable : (prefixWord ++ tailWord_853738).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853738).length < 2 ^ (prefixWord ++ tailWord_853738).sum := by decide
  have hdescent : baseEnd_853738 < baseStart_853738 := by decide
  rcases family_descends (prefixWord ++ tailWord_853738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853741 : List Nat := [1, 5, 1, 2, 1, 3, 3, 4]
def baseStart_853741 : Nat := 118140960795 + 853741 * 2 ^ 59
def prefixEnd_853741 : Nat := 4983230072969 + 3 ^ 40 * 853741 * 2
def baseEnd_853741 : Nat := 129890218503777620181103

theorem tailTrace_853741 : CollatzResearch.WordTrace tailWord_853741 prefixEnd_853741 129890218503777620181103 := by
  unfold tailWord_853741
  simp only [CollatzResearch.WordTrace]
  refine ⟨31138492400049639199593077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20758994933366426133062051 31138492400049639199593077)
  ·
    refine ⟨2919233662504653674961851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31138492400049639199593077 2919233662504653674961851)
    ·
      refine ⟨4378850493756980512442777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2919233662504653674961851 4378850493756980512442777)
      ·
        refine ⟨3284137870317735384332083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4378850493756980512442777 3284137870317735384332083)
        ·
          refine ⟨4926206805476603076498125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3284137870317735384332083 4926206805476603076498125)
          ·
            refine ⟨1847327552053726153686797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4926206805476603076498125 1847327552053726153686797)
            ·
              refine ⟨692747832020147307632549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1847327552053726153686797 692747832020147307632549)
              ·
                refine ⟨129890218503777620181103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 692747832020147307632549 129890218503777620181103)
                ·
                  rfl

theorem cell20_853741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 3, 4].length) (baseStart_853741 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_853741 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_853741 prefixEnd_853741 := by exact prefixLift 853741
  have htrace : WordTrace (prefixWord ++ tailWord_853741) baseStart_853741 baseEnd_853741 := by
    simpa [prefixWord, tailWord_853741, baseEnd_853741] using wordTrace_append hprefix tailTrace_853741
  have hstable : (prefixWord ++ tailWord_853741).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853741).length < 2 ^ (prefixWord ++ tailWord_853741).sum := by decide
  have hdescent : baseEnd_853741 < baseStart_853741 := by decide
  rcases family_descends (prefixWord ++ tailWord_853741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853762 : List Nat := [3, 4, 1, 1, 1, 1, 9]
def baseStart_853762 : Nat := 118140960795 + 853762 * 2 ^ 59
def prefixEnd_853762 : Nat := 4983230072969 + 3 ^ 40 * 853762 * 2
def baseEnd_853762 : Nat := 43297804498172235649247

theorem tailTrace_853762 : CollatzResearch.WordTrace tailWord_853762 prefixEnd_853762 43297804498172235649247 := by
  unfold tailWord_853762
  simp only [CollatzResearch.WordTrace]
  refine ⟨7784814583243389946526885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20759505555315706524071693 7784814583243389946526885)
  ·
    refine ⟨1459652734358135614973791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7784814583243389946526885 1459652734358135614973791)
    ·
      refine ⟨2189479101537203422460687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1459652734358135614973791 2189479101537203422460687)
      ·
        refine ⟨3284218652305805133691031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2189479101537203422460687 3284218652305805133691031)
        ·
          refine ⟨4926327978458707700536547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3284218652305805133691031 4926327978458707700536547)
          ·
            refine ⟨7389491967688061550804821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4926327978458707700536547 7389491967688061550804821)
            ·
              refine ⟨43297804498172235649247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7389491967688061550804821 43297804498172235649247)
              ·
                rfl

theorem cell20_853762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 9].length) (baseStart_853762 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_853762 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_853762 prefixEnd_853762 := by exact prefixLift 853762
  have htrace : WordTrace (prefixWord ++ tailWord_853762) baseStart_853762 baseEnd_853762 := by
    simpa [prefixWord, tailWord_853762, baseEnd_853762] using wordTrace_append hprefix tailTrace_853762
  have hstable : (prefixWord ++ tailWord_853762).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853762).length < 2 ^ (prefixWord ++ tailWord_853762).sum := by decide
  have hdescent : baseEnd_853762 < baseStart_853762 := by decide
  rcases family_descends (prefixWord ++ tailWord_853762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853800 : List Nat := [2, 1, 5, 1, 1, 3, 1, 6]
def baseStart_853800 : Nat := 118140960795 + 853800 * 2 ^ 59
def prefixEnd_853800 : Nat := 4983230072969 + 3 ^ 40 * 853800 * 2
def baseEnd_853800 : Nat := 129899194906330292525467

theorem tailTrace_853800 : CollatzResearch.WordTrace tailWord_853800 prefixEnd_853800 129899194906330292525467 := by
  unfold tailWord_853800
  simp only [CollatzResearch.WordTrace]
  refine ⟨15570322153417946137995427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20760429537890594850660569 15570322153417946137995427)
  ·
    refine ⟨23355483230126919206993141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15570322153417946137995427 23355483230126919206993141)
    ·
      refine ⟨2189576552824398675655607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23355483230126919206993141 2189576552824398675655607)
      ·
        refine ⟨3284364829236598013483411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2189576552824398675655607 3284364829236598013483411)
        ·
          refine ⟨4926547243854897020225117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3284364829236598013483411 4926547243854897020225117)
          ·
            refine ⟨1847455216445586382584419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4926547243854897020225117 1847455216445586382584419)
            ·
              refine ⟨2771182824668379573876629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1847455216445586382584419 2771182824668379573876629)
              ·
                refine ⟨129899194906330292525467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2771182824668379573876629 129899194906330292525467)
                ·
                  rfl

theorem cell20_853800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 6].length) (baseStart_853800 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_853800 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_853800 prefixEnd_853800 := by exact prefixLift 853800
  have htrace : WordTrace (prefixWord ++ tailWord_853800) baseStart_853800 baseEnd_853800 := by
    simpa [prefixWord, tailWord_853800, baseEnd_853800] using wordTrace_append hprefix tailTrace_853800
  have hstable : (prefixWord ++ tailWord_853800).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853800).length < 2 ^ (prefixWord ++ tailWord_853800).sum := by decide
  have hdescent : baseEnd_853800 < baseStart_853800 := by decide
  rcases family_descends (prefixWord ++ tailWord_853800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853806 : List Nat := [4, 1, 3, 2, 2, 2, 1, 3, 2]
def baseStart_853806 : Nat := 118140960795 + 853806 * 2 ^ 59
def prefixEnd_853806 : Nat := 4983230072969 + 3 ^ 40 * 853806 * 2
def baseEnd_853806 : Nat := 389700323282481523376377

theorem tailTrace_853806 : CollatzResearch.WordTrace tailWord_853806 prefixEnd_853806 389700323282481523376377 := by
  unfold tailWord_853806
  simp only [CollatzResearch.WordTrace]
  refine ⟨3892607893101769412588659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20760575429876103533806181 3892607893101769412588659)
  ·
    refine ⟨5838911839652654118882989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3892607893101769412588659 5838911839652654118882989)
    ·
      refine ⟨2189591939869745294581121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5838911839652654118882989 2189591939869745294581121)
      ·
        refine ⟨1642193954902308970935841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2189591939869745294581121 1642193954902308970935841)
        ·
          refine ⟨1231645466176731728201881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1642193954902308970935841 1231645466176731728201881)
          ·
            refine ⟨923734099632548796151411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1231645466176731728201881 923734099632548796151411)
            ·
              refine ⟨1385601149448823194227117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 923734099632548796151411 1385601149448823194227117)
              ·
                refine ⟨519600431043308697835169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1385601149448823194227117 519600431043308697835169)
                ·
                  refine ⟨389700323282481523376377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 519600431043308697835169 389700323282481523376377)
                  ·
                    rfl

theorem cell20_853806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 1, 3, 2].length) (baseStart_853806 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_853806 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_853806 prefixEnd_853806 := by exact prefixLift 853806
  have htrace : WordTrace (prefixWord ++ tailWord_853806) baseStart_853806 baseEnd_853806 := by
    simpa [prefixWord, tailWord_853806, baseEnd_853806] using wordTrace_append hprefix tailTrace_853806
  have hstable : (prefixWord ++ tailWord_853806).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853806).length < 2 ^ (prefixWord ++ tailWord_853806).sum := by decide
  have hdescent : baseEnd_853806 < baseStart_853806 := by decide
  rcases family_descends (prefixWord ++ tailWord_853806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853810 : List Nat := [3, 2, 1, 1, 3, 2, 3, 3, 2]
def baseStart_853810 : Nat := 118140960795 + 853810 * 2 ^ 59
def prefixEnd_853810 : Nat := 4983230072969 + 3 ^ 40 * 853810 * 2
def baseEnd_853810 : Nat := 389702148991475287243027

theorem tailTrace_853810 : CollatzResearch.WordTrace tailWord_853810 prefixEnd_853810 389702148991475287243027 := by
  unfold tailWord_853810
  simp only [CollatzResearch.WordTrace]
  refine ⟨7785252259199915995963721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20760672691199775989236589 7785252259199915995963721)
  ·
    refine ⟨5838939194399936996972791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7785252259199915995963721 5838939194399936996972791)
    ·
      refine ⟨8758408791599905495459187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5838939194399936996972791 8758408791599905495459187)
      ·
        refine ⟨13137613187399858243188781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8758408791599905495459187 13137613187399858243188781)
        ·
          refine ⟨4926604945274946841195793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13137613187399858243188781 4926604945274946841195793)
          ·
            refine ⟨3694953708956210130896845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4926604945274946841195793 3694953708956210130896845)
            ·
              refine ⟨1385607640858578799086317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3694953708956210130896845 1385607640858578799086317)
              ·
                refine ⟨519602865321967049657369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1385607640858578799086317 519602865321967049657369)
                ·
                  refine ⟨389702148991475287243027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 519602865321967049657369 389702148991475287243027)
                  ·
                    rfl

theorem cell20_853810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 3, 3, 2].length) (baseStart_853810 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_853810 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_853810 prefixEnd_853810 := by exact prefixLift 853810
  have htrace : WordTrace (prefixWord ++ tailWord_853810) baseStart_853810 baseEnd_853810 := by
    simpa [prefixWord, tailWord_853810, baseEnd_853810] using wordTrace_append hprefix tailTrace_853810
  have hstable : (prefixWord ++ tailWord_853810).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853810).length < 2 ^ (prefixWord ++ tailWord_853810).sum := by decide
  have hdescent : baseEnd_853810 < baseStart_853810 := by decide
  rcases family_descends (prefixWord ++ tailWord_853810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853817 : List Nat := [1, 2, 1, 7, 1, 2, 6]
def baseStart_853817 : Nat := 118140960795 + 853817 * 2 ^ 59
def prefixEnd_853817 : Nat := 4983230072969 + 3 ^ 40 * 853817 * 2
def baseEnd_853817 : Nat := 43300593775801597112185

theorem tailTrace_853817 : CollatzResearch.WordTrace tailWord_853817 prefixEnd_853817 43300593775801597112185 := by
  unfold tailWord_853817
  simp only [CollatzResearch.WordTrace]
  refine ⟨31141264347774304179359705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20760842898516202786239803 31141264347774304179359705)
  ·
    refine ⟨23355948260830728134519779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31141264347774304179359705 23355948260830728134519779)
    ·
      refine ⟨35033922391246092201779669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23355948260830728134519779 35033922391246092201779669)
      ·
        refine ⟨821107556044830285979211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 35033922391246092201779669 821107556044830285979211)
        ·
          refine ⟨1231661334067245428968817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 821107556044830285979211 1231661334067245428968817)
          ·
            refine ⟨923746000550434071726613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1231661334067245428968817 923746000550434071726613)
            ·
              refine ⟨43300593775801597112185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 923746000550434071726613 43300593775801597112185)
              ·
                rfl

theorem cell20_853817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 6].length) (baseStart_853817 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_853817 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_853817 prefixEnd_853817 := by exact prefixLift 853817
  have htrace : WordTrace (prefixWord ++ tailWord_853817) baseStart_853817 baseEnd_853817 := by
    simpa [prefixWord, tailWord_853817, baseEnd_853817] using wordTrace_append hprefix tailTrace_853817
  have hstable : (prefixWord ++ tailWord_853817).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853817).length < 2 ^ (prefixWord ++ tailWord_853817).sum := by decide
  have hdescent : baseEnd_853817 < baseStart_853817 := by decide
  rcases family_descends (prefixWord ++ tailWord_853817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853831 : List Nat := [1, 1, 4, 1, 2, 1, 2, 6, 2]
def baseStart_853831 : Nat := 118140960795 + 853831 * 2 ^ 59
def prefixEnd_853831 : Nat := 4983230072969 + 3 ^ 40 * 853831 * 2
def baseEnd_853831 : Nat := 389711733963692547542941

theorem tailTrace_853831 : CollatzResearch.WordTrace tailWord_853831 prefixEnd_853831 389711733963692547542941 := by
  unfold tailWord_853831
  simp only [CollatzResearch.WordTrace]
  refine ⟨31141774969723584570369347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20761183313149056380246231 31141774969723584570369347)
  ·
    refine ⟨46712662454585376855554021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31141774969723584570369347 46712662454585376855554021)
    ·
      refine ⟨8758624210234758160416379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46712662454585376855554021 8758624210234758160416379)
      ·
        refine ⟨13137936315352137240624569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8758624210234758160416379 13137936315352137240624569)
        ·
          refine ⟨9853452236514102930468427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13137936315352137240624569 9853452236514102930468427)
          ·
            refine ⟨14780178354771154395702641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9853452236514102930468427 14780178354771154395702641)
            ·
              refine ⟨11085133766078365796776981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14780178354771154395702641 11085133766078365796776981)
              ·
                refine ⟨519615645284923396723921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11085133766078365796776981 519615645284923396723921)
                ·
                  refine ⟨389711733963692547542941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 519615645284923396723921 389711733963692547542941)
                  ·
                    rfl

theorem cell20_853831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 6, 2].length) (baseStart_853831 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_853831 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_853831 prefixEnd_853831 := by exact prefixLift 853831
  have htrace : WordTrace (prefixWord ++ tailWord_853831) baseStart_853831 baseEnd_853831 := by
    simpa [prefixWord, tailWord_853831, baseEnd_853831] using wordTrace_append hprefix tailTrace_853831
  have hstable : (prefixWord ++ tailWord_853831).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853831).length < 2 ^ (prefixWord ++ tailWord_853831).sum := by decide
  have hdescent : baseEnd_853831 < baseStart_853831 := by decide
  rcases family_descends (prefixWord ++ tailWord_853831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853841 : List Nat := [1, 2, 2, 1, 5, 3, 2, 1, 3]
def baseStart_853841 : Nat := 118140960795 + 853841 * 2 ^ 59
def prefixEnd_853841 : Nat := 4983230072969 + 3 ^ 40 * 853841 * 2
def baseEnd_853841 : Nat := 389716298236176957209567

theorem tailTrace_853841 : CollatzResearch.WordTrace tailWord_853841 prefixEnd_853841 389716298236176957209567 := by
  unfold tailWord_853841
  simp only [CollatzResearch.WordTrace]
  refine ⟨31142139699687356278233377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20761426466458237518822251 31142139699687356278233377)
  ·
    refine ⟨23356604774765517208675033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31142139699687356278233377 23356604774765517208675033)
    ·
      refine ⟨17517453581074137906506275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23356604774765517208675033 17517453581074137906506275)
      ·
        refine ⟨26276180371611206859759413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17517453581074137906506275 26276180371611206859759413)
        ·
          refine ⟨2463391909838550643102445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26276180371611206859759413 2463391909838550643102445)
          ·
            refine ⟨923771966189456491163417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2463391909838550643102445 923771966189456491163417)
            ·
              refine ⟨692828974642092368372563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 923771966189456491163417 692828974642092368372563)
              ·
                refine ⟨1039243461963138552558845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 692828974642092368372563 1039243461963138552558845)
                ·
                  refine ⟨389716298236176957209567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1039243461963138552558845 389716298236176957209567)
                  ·
                    rfl

theorem cell20_853841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 2, 1, 3].length) (baseStart_853841 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_853841 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_853841 prefixEnd_853841 := by exact prefixLift 853841
  have htrace : WordTrace (prefixWord ++ tailWord_853841) baseStart_853841 baseEnd_853841 := by
    simpa [prefixWord, tailWord_853841, baseEnd_853841] using wordTrace_append hprefix tailTrace_853841
  have hstable : (prefixWord ++ tailWord_853841).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853841).length < 2 ^ (prefixWord ++ tailWord_853841).sum := by decide
  have hdescent : baseEnd_853841 < baseStart_853841 := by decide
  rcases family_descends (prefixWord ++ tailWord_853841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853924 : List Nat := [2, 3, 1, 2, 1, 4, 2, 3, 2]
def baseStart_853924 : Nat := 118140960795 + 853924 * 2 ^ 59
def prefixEnd_853924 : Nat := 4983230072969 + 3 ^ 40 * 853924 * 2
def baseEnd_853924 : Nat := 389754181697797557442561

theorem tailTrace_853924 : CollatzResearch.WordTrace tailWord_853924 prefixEnd_853924 389754181697797557442561 := by
  unfold tailWord_853924
  simp only [CollatzResearch.WordTrace]
  refine ⟨15572583479193330726752413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20763444638924440969003217 15572583479193330726752413)
  ·
    refine ⟨5839718804697499022532155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15572583479193330726752413 5839718804697499022532155)
    ·
      refine ⟨8759578207046248533798233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5839718804697499022532155 8759578207046248533798233)
      ·
        refine ⟨6569683655284686400348675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8759578207046248533798233 6569683655284686400348675)
        ·
          refine ⟨9854525482927029600523013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6569683655284686400348675 9854525482927029600523013)
          ·
            refine ⟨1847723528048818050098065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9854525482927029600523013 1847723528048818050098065)
            ·
              refine ⟨1385792646036613537573549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1847723528048818050098065 1385792646036613537573549)
              ·
                refine ⟨519672242263730076590081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1385792646036613537573549 519672242263730076590081)
                ·
                  refine ⟨389754181697797557442561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 519672242263730076590081 389754181697797557442561)
                  ·
                    rfl

theorem cell20_853924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 2, 3, 2].length) (baseStart_853924 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_853924 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_853924 prefixEnd_853924 := by exact prefixLift 853924
  have htrace : WordTrace (prefixWord ++ tailWord_853924) baseStart_853924 baseEnd_853924 := by
    simpa [prefixWord, tailWord_853924, baseEnd_853924] using wordTrace_append hprefix tailTrace_853924
  have hstable : (prefixWord ++ tailWord_853924).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853924).length < 2 ^ (prefixWord ++ tailWord_853924).sum := by decide
  have hdescent : baseEnd_853924 < baseStart_853924 := by decide
  rcases family_descends (prefixWord ++ tailWord_853924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853934 : List Nat := [4, 1, 5, 1, 1, 1, 1, 1, 5]
def baseStart_853934 : Nat := 118140960795 + 853934 * 2 ^ 59
def prefixEnd_853934 : Nat := 4983230072969 + 3 ^ 40 * 853934 * 2
def baseEnd_853934 : Nat := 389758745970281967109187

theorem tailTrace_853934 : CollatzResearch.WordTrace tailWord_853934 prefixEnd_853934 389758745970281967109187 := by
  unfold tailWord_853934
  simp only [CollatzResearch.WordTrace]
  refine ⟨3893191461043804145171107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20763687792233622107579237 3893191461043804145171107)
  ·
    refine ⟨5839787191565706217756661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3893191461043804145171107 5839787191565706217756661)
    ·
      refine ⟨547480049209284957914687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5839787191565706217756661 547480049209284957914687)
      ·
        refine ⟨821220073813927436872031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 547480049209284957914687 821220073813927436872031)
        ·
          refine ⟨1231830110720891155308047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 821220073813927436872031 1231830110720891155308047)
          ·
            refine ⟨1847745166081336732962071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1231830110720891155308047 1847745166081336732962071)
            ·
              refine ⟨2771617749122005099443107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1847745166081336732962071 2771617749122005099443107)
              ·
                refine ⟨4157426623683007649164661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2771617749122005099443107 4157426623683007649164661)
                ·
                  refine ⟨389758745970281967109187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4157426623683007649164661 389758745970281967109187)
                  ·
                    rfl

theorem cell20_853934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 1, 5].length) (baseStart_853934 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_853934 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_853934 prefixEnd_853934 := by exact prefixLift 853934
  have htrace : WordTrace (prefixWord ++ tailWord_853934) baseStart_853934 baseEnd_853934 := by
    simpa [prefixWord, tailWord_853934, baseEnd_853934] using wordTrace_append hprefix tailTrace_853934
  have hstable : (prefixWord ++ tailWord_853934).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853934).length < 2 ^ (prefixWord ++ tailWord_853934).sum := by decide
  have hdescent : baseEnd_853934 < baseStart_853934 := by decide
  rcases family_descends (prefixWord ++ tailWord_853934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853945 : List Nat := [1, 2, 1, 4, 2, 1, 1, 6, 2]
def baseStart_853945 : Nat := 118140960795 + 853945 * 2 ^ 59
def prefixEnd_853945 : Nat := 4983230072969 + 3 ^ 40 * 853945 * 2
def baseEnd_853945 : Nat := 389763766670014817742475

theorem tailTrace_853945 : CollatzResearch.WordTrace tailWord_853945 prefixEnd_853945 389763766670014817742475 := by
  unfold tailWord_853945
  simp only [CollatzResearch.WordTrace]
  refine ⟨31145932891310582040019289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20763955260873721360012859 31145932891310582040019289)
  ·
    refine ⟨23359449668482936530014467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31145932891310582040019289 23359449668482936530014467)
    ·
      refine ⟨35039174502724404795021701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23359449668482936530014467 35039174502724404795021701)
      ·
        refine ⟨6569845219260825899066569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35039174502724404795021701 6569845219260825899066569)
        ·
          refine ⟨4927383914445619424299927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6569845219260825899066569 4927383914445619424299927)
          ·
            refine ⟨7391075871668429136449891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4927383914445619424299927 7391075871668429136449891)
            ·
              refine ⟨11086613807502643704674837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7391075871668429136449891 11086613807502643704674837)
              ·
                refine ⟨519685022226686423656633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11086613807502643704674837 519685022226686423656633)
                ·
                  refine ⟨389763766670014817742475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 519685022226686423656633 389763766670014817742475)
                  ·
                    rfl

theorem cell20_853945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 6, 2].length) (baseStart_853945 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_853945 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_853945 prefixEnd_853945 := by exact prefixLift 853945
  have htrace : WordTrace (prefixWord ++ tailWord_853945) baseStart_853945 baseEnd_853945 := by
    simpa [prefixWord, tailWord_853945, baseEnd_853945] using wordTrace_append hprefix tailTrace_853945
  have hstable : (prefixWord ++ tailWord_853945).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853945).length < 2 ^ (prefixWord ++ tailWord_853945).sum := by decide
  have hdescent : baseEnd_853945 < baseStart_853945 := by decide
  rcases family_descends (prefixWord ++ tailWord_853945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853966 : List Nat := [4, 1, 1, 1, 2, 2, 1, 4, 4]
def baseStart_853966 : Nat := 118140960795 + 853966 * 2 ^ 59
def prefixEnd_853966 : Nat := 4983230072969 + 3 ^ 40 * 853966 * 2
def baseEnd_853966 : Nat := 389773351642232078042389

theorem tailTrace_853966 : CollatzResearch.WordTrace tailWord_853966 prefixEnd_853966 389773351642232078042389 := by
  unfold tailWord_853966
  simp only [CollatzResearch.WordTrace]
  refine ⟨3893337353029312828316719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20764465882823001751022501 3893337353029312828316719)
  ·
    refine ⟨5840006029543969242475079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3893337353029312828316719 5840006029543969242475079)
    ·
      refine ⟨8760009044315953863712619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5840006029543969242475079 8760009044315953863712619)
      ·
        refine ⟨13140013566473930795568929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8760009044315953863712619 13140013566473930795568929)
        ·
          refine ⟨9855010174855448096676697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13140013566473930795568929 9855010174855448096676697)
          ·
            refine ⟨7391257631141586072507523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9855010174855448096676697 7391257631141586072507523)
            ·
              refine ⟨11086886446712379108761285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7391257631141586072507523 11086886446712379108761285)
              ·
                refine ⟨2078791208758571082892741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11086886446712379108761285 2078791208758571082892741)
                ·
                  refine ⟨389773351642232078042389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2078791208758571082892741 389773351642232078042389)
                  ·
                    rfl

theorem cell20_853966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 4, 4].length) (baseStart_853966 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_853966 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_853966 prefixEnd_853966 := by exact prefixLift 853966
  have htrace : WordTrace (prefixWord ++ tailWord_853966) baseStart_853966 baseEnd_853966 := by
    simpa [prefixWord, tailWord_853966, baseEnd_853966] using wordTrace_append hprefix tailTrace_853966
  have hstable : (prefixWord ++ tailWord_853966).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853966).length < 2 ^ (prefixWord ++ tailWord_853966).sum := by decide
  have hdescent : baseEnd_853966 < baseStart_853966 := by decide
  rcases family_descends (prefixWord ++ tailWord_853966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_853986 : List Nat := [3, 3, 3, 1, 3, 1, 6]
def baseStart_853986 : Nat := 118140960795 + 853986 * 2 ^ 59
def prefixEnd_853986 : Nat := 4983230072969 + 3 ^ 40 * 853986 * 2
def baseEnd_853986 : Nat := 43309164465244544152849

theorem tailTrace_853986 : CollatzResearch.WordTrace tailWord_853986 prefixEnd_853986 43309164465244544152849 := by
  unfold tailWord_853986
  simp only [CollatzResearch.WordTrace]
  refine ⟨7786857071040511510565453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20764952189441364028174541 7786857071040511510565453)
  ·
    refine ⟨2920071401640191816462045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7786857071040511510565453 2920071401640191816462045)
    ·
      refine ⟨1095026775615071931173267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2920071401640191816462045 1095026775615071931173267)
      ·
        refine ⟨1642540163422607896759901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1095026775615071931173267 1642540163422607896759901)
        ·
          refine ⟨615952561283477961284963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1642540163422607896759901 615952561283477961284963)
          ·
            refine ⟨923928841925216941927445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 615952561283477961284963 923928841925216941927445)
            ·
              refine ⟨43309164465244544152849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 923928841925216941927445 43309164465244544152849)
              ·
                rfl

theorem cell20_853986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 6].length) (baseStart_853986 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_853986 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_853986 prefixEnd_853986 := by exact prefixLift 853986
  have htrace : WordTrace (prefixWord ++ tailWord_853986) baseStart_853986 baseEnd_853986 := by
    simpa [prefixWord, tailWord_853986, baseEnd_853986] using wordTrace_append hprefix tailTrace_853986
  have hstable : (prefixWord ++ tailWord_853986).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_853986).length < 2 ^ (prefixWord ++ tailWord_853986).sum := by decide
  have hdescent : baseEnd_853986 < baseStart_853986 := by decide
  rcases family_descends (prefixWord ++ tailWord_853986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854049 : List Nat := [1, 2, 3, 2, 4, 8]
def baseStart_854049 : Nat := 118140960795 + 854049 * 2 ^ 59
def prefixEnd_854049 : Nat := 4983230072969 + 3 ^ 40 * 854049 * 2
def baseEnd_854049 : Nat := 14437453151994543639829

theorem tailTrace_854049 : CollatzResearch.WordTrace tailWord_854049 prefixEnd_854049 14437453151994543639829 := by
  unfold tailWord_854049
  simp only [CollatzResearch.WordTrace]
  refine ⟨31149726082933807801805201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20766484055289205201203467 31149726082933807801805201)
  ·
    refine ⟨23362294562200355851353901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31149726082933807801805201 23362294562200355851353901)
    ·
      refine ⟨8760860460825133444257713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23362294562200355851353901 8760860460825133444257713)
      ·
        refine ⟨6570645345618850083193285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8760860460825133444257713 6570645345618850083193285)
        ·
          refine ⟨1231996002303534390598741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6570645345618850083193285 1231996002303534390598741)
          ·
            refine ⟨14437453151994543639829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1231996002303534390598741 14437453151994543639829)
            ·
              rfl

theorem cell20_854049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 8].length) (baseStart_854049 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_854049 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_854049 prefixEnd_854049 := by exact prefixLift 854049
  have htrace : WordTrace (prefixWord ++ tailWord_854049) baseStart_854049 baseEnd_854049 := by
    simpa [prefixWord, tailWord_854049, baseEnd_854049] using wordTrace_append hprefix tailTrace_854049
  have hstable : (prefixWord ++ tailWord_854049).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854049).length < 2 ^ (prefixWord ++ tailWord_854049).sum := by decide
  have hdescent : baseEnd_854049 < baseStart_854049 := by decide
  rcases family_descends (prefixWord ++ tailWord_854049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854055 : List Nat := [1, 1, 7, 1, 2, 1, 1, 4, 2]
def baseStart_854055 : Nat := 118140960795 + 854055 * 2 ^ 59
def prefixEnd_854055 : Nat := 4983230072969 + 3 ^ 40 * 854055 * 2
def baseEnd_854055 : Nat := 389813973667343324075359

theorem tailTrace_854055 : CollatzResearch.WordTrace tailWord_854055 prefixEnd_854055 389813973667343324075359 := by
  unfold tailWord_854055
  simp only [CollatzResearch.WordTrace]
  refine ⟨31149944920912070826523619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20766629947274713884349079 31149944920912070826523619)
  ·
    refine ⟨46724917381368106239785429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31149944920912070826523619 46724917381368106239785429)
    ·
      refine ⟨1095115251125814989994971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 46724917381368106239785429 1095115251125814989994971)
      ·
        refine ⟨1642672876688722484992457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1095115251125814989994971 1642672876688722484992457)
        ·
          refine ⟨1232004657516541863744343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1642672876688722484992457 1232004657516541863744343)
          ·
            refine ⟨1848006986274812795616515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1232004657516541863744343 1848006986274812795616515)
            ·
              refine ⟨2772010479412219193424773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1848006986274812795616515 2772010479412219193424773)
              ·
                refine ⟨519751964889791098767145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2772010479412219193424773 519751964889791098767145)
                ·
                  refine ⟨389813973667343324075359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 519751964889791098767145 389813973667343324075359)
                  ·
                    rfl

theorem cell20_854055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 4, 2].length) (baseStart_854055 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_854055 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_854055 prefixEnd_854055 := by exact prefixLift 854055
  have htrace : WordTrace (prefixWord ++ tailWord_854055) baseStart_854055 baseEnd_854055 := by
    simpa [prefixWord, tailWord_854055, baseEnd_854055] using wordTrace_append hprefix tailTrace_854055
  have hstable : (prefixWord ++ tailWord_854055).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854055).length < 2 ^ (prefixWord ++ tailWord_854055).sum := by decide
  have hdescent : baseEnd_854055 < baseStart_854055 := by decide
  rcases family_descends (prefixWord ++ tailWord_854055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854066 : List Nat := [3, 2, 1, 1, 2, 5, 1, 5]
def baseStart_854066 : Nat := 118140960795 + 854066 * 2 ^ 59
def prefixEnd_854066 : Nat := 4983230072969 + 3 ^ 40 * 854066 * 2
def baseEnd_854066 : Nat := 129939664789025391569549

theorem tailTrace_854066 : CollatzResearch.WordTrace tailWord_854066 prefixEnd_854066 129939664789025391569549 := by
  unfold tailWord_854066
  simp only [CollatzResearch.WordTrace]
  refine ⟨7787586530968054926293513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20766897415914813136782701 7787586530968054926293513)
  ·
    refine ⟨5840689898226041194720135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7787586530968054926293513 5840689898226041194720135)
    ·
      refine ⟨8761034847339061792080203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5840689898226041194720135 8761034847339061792080203)
      ·
        refine ⟨13141552271008592688120305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8761034847339061792080203 13141552271008592688120305)
        ·
          refine ⟨9856164203256444516090229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13141552271008592688120305 9856164203256444516090229)
          ·
            refine ⟨924015394055291673383459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9856164203256444516090229 924015394055291673383459)
            ·
              refine ⟨1386023091082937510075189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 924015394055291673383459 1386023091082937510075189)
              ·
                refine ⟨129939664789025391569549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1386023091082937510075189 129939664789025391569549)
                ·
                  rfl

theorem cell20_854066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 1, 5].length) (baseStart_854066 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_854066 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_854066 prefixEnd_854066 := by exact prefixLift 854066
  have htrace : WordTrace (prefixWord ++ tailWord_854066) baseStart_854066 baseEnd_854066 := by
    simpa [prefixWord, tailWord_854066, baseEnd_854066] using wordTrace_append hprefix tailTrace_854066
  have hstable : (prefixWord ++ tailWord_854066).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854066).length < 2 ^ (prefixWord ++ tailWord_854066).sum := by decide
  have hdescent : baseEnd_854066 < baseStart_854066 := by decide
  rcases family_descends (prefixWord ++ tailWord_854066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854080 : List Nat := [2, 1, 1, 2, 2, 5, 1, 2, 4]
def baseStart_854080 : Nat := 118140960795 + 854080 * 2 ^ 59
def prefixEnd_854080 : Nat := 4983230072969 + 3 ^ 40 * 854080 * 2
def baseEnd_854080 : Nat := 389825384348554348241923

theorem tailTrace_854080 : CollatzResearch.WordTrace tailWord_854080 prefixEnd_854080 389825384348554348241923 := by
  unfold tailWord_854080
  simp only [CollatzResearch.WordTrace]
  refine ⟨15575428372910750048091847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20767237830547666730789129 15575428372910750048091847)
  ·
    refine ⟨23363142559366125072137771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15575428372910750048091847 23363142559366125072137771)
    ·
      refine ⟨35044713839049187608206657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23363142559366125072137771 35044713839049187608206657)
      ·
        refine ⟨26283535379286890706154993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35044713839049187608206657 26283535379286890706154993)
        ·
          refine ⟨19712651534465168029616245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26283535379286890706154993 19712651534465168029616245)
          ·
            refine ⟨1848061081356109502776523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19712651534465168029616245 1848061081356109502776523)
            ·
              refine ⟨2772091622034164254164785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1848061081356109502776523 2772091622034164254164785)
              ·
                refine ⟨2079068716525623190623589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2772091622034164254164785 2079068716525623190623589)
                ·
                  refine ⟨389825384348554348241923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2079068716525623190623589 389825384348554348241923)
                  ·
                    rfl

theorem cell20_854080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 2, 4].length) (baseStart_854080 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_854080 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_854080 prefixEnd_854080 := by exact prefixLift 854080
  have htrace : WordTrace (prefixWord ++ tailWord_854080) baseStart_854080 baseEnd_854080 := by
    simpa [prefixWord, tailWord_854080, baseEnd_854080] using wordTrace_append hprefix tailTrace_854080
  have hstable : (prefixWord ++ tailWord_854080).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854080).length < 2 ^ (prefixWord ++ tailWord_854080).sum := by decide
  have hdescent : baseEnd_854080 < baseStart_854080 := by decide
  rcases family_descends (prefixWord ++ tailWord_854080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854114 : List Nat := [3, 3, 2, 2, 2, 1, 2, 1, 4]
def baseStart_854114 : Nat := 118140960795 + 854114 * 2 ^ 59
def prefixEnd_854114 : Nat := 4983230072969 + 3 ^ 40 * 854114 * 2
def baseEnd_854114 : Nat := 389840902875001341108451

theorem tailTrace_854114 : CollatzResearch.WordTrace tailWord_854114 prefixEnd_854114 389840902875001341108451 := by
  unfold tailWord_854114
  simp only [CollatzResearch.WordTrace]
  refine ⟨7788024206924580975730349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20768064551798882601947597 7788024206924580975730349)
  ·
    refine ⟨2920509077596717865898881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7788024206924580975730349 2920509077596717865898881)
    ·
      refine ⟨2190381808197538399424161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2920509077596717865898881 2190381808197538399424161)
      ·
        refine ⟨1642786356148153799568121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2190381808197538399424161 1642786356148153799568121)
        ·
          refine ⟨1232089767111115349676091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1642786356148153799568121 1232089767111115349676091)
          ·
            refine ⟨1848134650666673024514137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1232089767111115349676091 1848134650666673024514137)
            ·
              refine ⟨1386100988000004768385603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1848134650666673024514137 1386100988000004768385603)
              ·
                refine ⟨2079151482000007152578405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1386100988000004768385603 2079151482000007152578405)
                ·
                  refine ⟨389840902875001341108451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2079151482000007152578405 389840902875001341108451)
                  ·
                    rfl

theorem cell20_854114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 2, 1, 4].length) (baseStart_854114 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_854114 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_854114 prefixEnd_854114 := by exact prefixLift 854114
  have htrace : WordTrace (prefixWord ++ tailWord_854114) baseStart_854114 baseEnd_854114 := by
    simpa [prefixWord, tailWord_854114, baseEnd_854114] using wordTrace_append hprefix tailTrace_854114
  have hstable : (prefixWord ++ tailWord_854114).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854114).length < 2 ^ (prefixWord ++ tailWord_854114).sum := by decide
  have hdescent : baseEnd_854114 < baseStart_854114 := by decide
  rcases family_descends (prefixWord ++ tailWord_854114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854125 : List Nat := [1, 5, 1, 1, 2, 1, 2, 7]
def baseStart_854125 : Nat := 118140960795 + 854125 * 2 ^ 59
def prefixEnd_854125 : Nat := 4983230072969 + 3 ^ 40 * 854125 * 2
def baseEnd_854125 : Nat := 129948641191578063913913

theorem tailTrace_854125 : CollatzResearch.WordTrace tailWord_854125 prefixEnd_854125 129948641191578063913913 := by
  unfold tailWord_854125
  simp only [CollatzResearch.WordTrace]
  refine ⟨31152498030658472781571829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20768332020438981854381219 31152498030658472781571829)
  ·
    refine ⟨2920546690374231823272359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31152498030658472781571829 2920546690374231823272359)
    ·
      refine ⟨4380820035561347734908539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2920546690374231823272359 4380820035561347734908539)
      ·
        refine ⟨6571230053342021602362809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4380820035561347734908539 6571230053342021602362809)
        ·
          refine ⟨4928422540006516201772107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6571230053342021602362809 4928422540006516201772107)
          ·
            refine ⟨7392633810009774302658161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4928422540006516201772107 7392633810009774302658161)
            ·
              refine ⟨5544475357507330726993621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7392633810009774302658161 5544475357507330726993621)
              ·
                refine ⟨129948641191578063913913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5544475357507330726993621 129948641191578063913913)
                ·
                  rfl

theorem cell20_854125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 7].length) (baseStart_854125 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_854125 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_854125 prefixEnd_854125 := by exact prefixLift 854125
  have htrace : WordTrace (prefixWord ++ tailWord_854125) baseStart_854125 baseEnd_854125 := by
    simpa [prefixWord, tailWord_854125, baseEnd_854125] using wordTrace_append hprefix tailTrace_854125
  have hstable : (prefixWord ++ tailWord_854125).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854125).length < 2 ^ (prefixWord ++ tailWord_854125).sum := by decide
  have hdescent : baseEnd_854125 < baseStart_854125 := by decide
  rcases family_descends (prefixWord ++ tailWord_854125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854128 : List Nat := [2, 1, 1, 1, 5, 3, 3, 1, 3]
def baseStart_854128 : Nat := 118140960795 + 854128 * 2 ^ 59
def prefixEnd_854128 : Nat := 4983230072969 + 3 ^ 40 * 854128 * 2
def baseEnd_854128 : Nat := 389847292856479514641727

theorem tailTrace_854128 : CollatzResearch.WordTrace tailWord_854128 prefixEnd_854128 389847292856479514641727 := by
  unfold tailWord_854128
  simp only [CollatzResearch.WordTrace]
  refine ⟨15576303724823802146965519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20768404966431736195954025 15576303724823802146965519)
  ·
    refine ⟨23364455587235703220448279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15576303724823802146965519 23364455587235703220448279)
    ·
      refine ⟨35046683380853554830672419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23364455587235703220448279 35046683380853554830672419)
      ·
        refine ⟨52570025071280332246008629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35046683380853554830672419 52570025071280332246008629)
        ·
          refine ⟨4928439850432531148063309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52570025071280332246008629 4928439850432531148063309)
          ·
            refine ⟨1848164943912199180523741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4928439850432531148063309 1848164943912199180523741)
            ·
              refine ⟨693061853967074692696403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1848164943912199180523741 693061853967074692696403)
              ·
                refine ⟨1039592780950612039044605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 693061853967074692696403 1039592780950612039044605)
                ·
                  refine ⟨389847292856479514641727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1039592780950612039044605 389847292856479514641727)
                  ·
                    rfl

theorem cell20_854128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 3, 1, 3].length) (baseStart_854128 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_854128 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_854128 prefixEnd_854128 := by exact prefixLift 854128
  have htrace : WordTrace (prefixWord ++ tailWord_854128) baseStart_854128 baseEnd_854128 := by
    simpa [prefixWord, tailWord_854128, baseEnd_854128] using wordTrace_append hprefix tailTrace_854128
  have hstable : (prefixWord ++ tailWord_854128).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854128).length < 2 ^ (prefixWord ++ tailWord_854128).sum := by decide
  have hdescent : baseEnd_854128 < baseStart_854128 := by decide
  rcases family_descends (prefixWord ++ tailWord_854128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854152 : List Nat := [2, 1, 3, 4, 1, 1, 3, 3, 2]
def baseStart_854152 : Nat := 118140960795 + 854152 * 2 ^ 59
def prefixEnd_854152 : Nat := 4983230072969 + 3 ^ 40 * 854152 * 2
def baseEnd_854152 : Nat := 389858247110442097841629

theorem tailTrace_854152 : CollatzResearch.WordTrace tailWord_854152 prefixEnd_854152 389858247110442097841629 := by
  unfold tailWord_854152
  simp only [CollatzResearch.WordTrace]
  refine ⟨15576741400780328196402355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20768988534373770928536473 15576741400780328196402355)
  ·
    refine ⟨23365112101170492294603533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15576741400780328196402355 23365112101170492294603533)
    ·
      refine ⟨8761917037938934610476325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23365112101170492294603533 8761917037938934610476325)
      ·
        refine ⟨1642859444613550239464311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8761917037938934610476325 1642859444613550239464311)
        ·
          refine ⟨2464289166920325359196467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1642859444613550239464311 2464289166920325359196467)
          ·
            refine ⟨3696433750380488038794701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2464289166920325359196467 3696433750380488038794701)
            ·
              refine ⟨1386162656392683014548013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3696433750380488038794701 1386162656392683014548013)
              ·
                refine ⟨519810996147256130455505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1386162656392683014548013 519810996147256130455505)
                ·
                  refine ⟨389858247110442097841629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 519810996147256130455505 389858247110442097841629)
                  ·
                    rfl

theorem cell20_854152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 3, 3, 2].length) (baseStart_854152 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_854152 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_854152 prefixEnd_854152 := by exact prefixLift 854152
  have htrace : WordTrace (prefixWord ++ tailWord_854152) baseStart_854152 baseEnd_854152 := by
    simpa [prefixWord, tailWord_854152, baseEnd_854152] using wordTrace_append hprefix tailTrace_854152
  have hstable : (prefixWord ++ tailWord_854152).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854152).length < 2 ^ (prefixWord ++ tailWord_854152).sum := by decide
  have hdescent : baseEnd_854152 < baseStart_854152 := by decide
  rcases family_descends (prefixWord ++ tailWord_854152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854173 : List Nat := [1, 4, 2, 1, 1, 5, 1, 1, 4]
def baseStart_854173 : Nat := 118140960795 + 854173 * 2 ^ 59
def prefixEnd_854173 : Nat := 4983230072969 + 3 ^ 40 * 854173 * 2
def baseEnd_854173 : Nat := 389867832082659358141543

theorem tailTrace_854173 : CollatzResearch.WordTrace tailWord_854173 prefixEnd_854173 389867832082659358141543 := by
  unfold tailWord_854173
  simp only [CollatzResearch.WordTrace]
  refine ⟨31154248734484576979319173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20769499156323051319546115 31154248734484576979319173)
  ·
    refine ⟨5841421637715858183622345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31154248734484576979319173 5841421637715858183622345)
    ·
      refine ⟨4381066228286893637716759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5841421637715858183622345 4381066228286893637716759)
      ·
        refine ⟨6571599342430340456575139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4381066228286893637716759 6571599342430340456575139)
        ·
          refine ⟨9857399013645510684862709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6571599342430340456575139 9857399013645510684862709)
          ·
            refine ⟨924131157529266626705879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9857399013645510684862709 924131157529266626705879)
            ·
              refine ⟨1386196736293899940058819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 924131157529266626705879 1386196736293899940058819)
              ·
                refine ⟨2079295104440849910088229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1386196736293899940058819 2079295104440849910088229)
                ·
                  refine ⟨389867832082659358141543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2079295104440849910088229 389867832082659358141543)
                  ·
                    rfl

theorem cell20_854173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 1, 1, 4].length) (baseStart_854173 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_854173 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_854173 prefixEnd_854173 := by exact prefixLift 854173
  have htrace : WordTrace (prefixWord ++ tailWord_854173) baseStart_854173 baseEnd_854173 := by
    simpa [prefixWord, tailWord_854173, baseEnd_854173] using wordTrace_append hprefix tailTrace_854173
  have hstable : (prefixWord ++ tailWord_854173).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854173).length < 2 ^ (prefixWord ++ tailWord_854173).sum := by decide
  have hdescent : baseEnd_854173 < baseStart_854173 := by decide
  rcases family_descends (prefixWord ++ tailWord_854173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854180 : List Nat := [2, 3, 1, 2, 4, 1, 2, 5]
def baseStart_854180 : Nat := 118140960795 + 854180 * 2 ^ 59
def prefixEnd_854180 : Nat := 4983230072969 + 3 ^ 40 * 854180 * 2
def baseEnd_854180 : Nat := 129957009024466148302727

theorem tailTrace_854180 : CollatzResearch.WordTrace tailWord_854180 prefixEnd_854180 129957009024466148302727 := by
  unfold tailWord_854180
  simp only [CollatzResearch.WordTrace]
  refine ⟨15577252022729608587411997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20769669363639478116549329 15577252022729608587411997)
  ·
    refine ⟨5841469508523603220279499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15577252022729608587411997 5841469508523603220279499)
    ·
      refine ⟨8762204262785404830419249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5841469508523603220279499 8762204262785404830419249)
      ·
        refine ⟨6571653197089053622814437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8762204262785404830419249 6571653197089053622814437)
        ·
          refine ⟨1232184974454197554277707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6571653197089053622814437 1232184974454197554277707)
          ·
            refine ⟨1848277461681296331416561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1232184974454197554277707 1848277461681296331416561)
            ·
              refine ⟨1386208096260972248562421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1848277461681296331416561 1386208096260972248562421)
              ·
                refine ⟨129957009024466148302727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1386208096260972248562421 129957009024466148302727)
                ·
                  rfl

theorem cell20_854180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 2, 5].length) (baseStart_854180 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_854180 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_854180 prefixEnd_854180 := by exact prefixLift 854180
  have htrace : WordTrace (prefixWord ++ tailWord_854180) baseStart_854180 baseEnd_854180 := by
    simpa [prefixWord, tailWord_854180, baseEnd_854180] using wordTrace_append hprefix tailTrace_854180
  have hstable : (prefixWord ++ tailWord_854180).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854180).length < 2 ^ (prefixWord ++ tailWord_854180).sum := by decide
  have hdescent : baseEnd_854180 < baseStart_854180 := by decide
  rcases family_descends (prefixWord ++ tailWord_854180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854270 : List Nat := [4, 2, 2, 1, 1, 1, 1, 2, 6]
def baseStart_854270 : Nat := 118140960795 + 854270 * 2 ^ 59
def prefixEnd_854270 : Nat := 4983230072969 + 3 ^ 40 * 854270 * 2
def baseEnd_854270 : Nat := 389912105525758131907813

theorem tailTrace_854270 : CollatzResearch.WordTrace tailWord_854270 prefixEnd_854270 389912105525758131907813 := by
  unfold tailWord_854270
  simp only [CollatzResearch.WordTrace]
  refine ⟨3894723326891645318200033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20771857743422108363733509 3894723326891645318200033)
  ·
    refine ⟨2921042495168733988650025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3894723326891645318200033 2921042495168733988650025)
    ·
      refine ⟨2190781871376550491487519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2921042495168733988650025 2190781871376550491487519)
      ·
        refine ⟨3286172807064825737231279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2190781871376550491487519 3286172807064825737231279)
        ·
          refine ⟨4929259210597238605846919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3286172807064825737231279 4929259210597238605846919)
          ·
            refine ⟨7393888815895857908770379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4929259210597238605846919 7393888815895857908770379)
            ·
              refine ⟨11090833223843786863155569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7393888815895857908770379 11090833223843786863155569)
              ·
                refine ⟨8318124917882840147366677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11090833223843786863155569 8318124917882840147366677)
                ·
                  refine ⟨389912105525758131907813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8318124917882840147366677 389912105525758131907813)
                  ·
                    rfl

theorem cell20_854270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_854270 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_854270 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_854270 prefixEnd_854270 := by exact prefixLift 854270
  have htrace : WordTrace (prefixWord ++ tailWord_854270) baseStart_854270 baseEnd_854270 := by
    simpa [prefixWord, tailWord_854270, baseEnd_854270] using wordTrace_append hprefix tailTrace_854270
  have hstable : (prefixWord ++ tailWord_854270).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854270).length < 2 ^ (prefixWord ++ tailWord_854270).sum := by decide
  have hdescent : baseEnd_854270 < baseStart_854270 := by decide
  rcases family_descends (prefixWord ++ tailWord_854270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854280 : List Nat := [2, 1, 3, 2, 3, 3, 1, 2, 3]
def baseStart_854280 : Nat := 118140960795 + 854280 * 2 ^ 59
def prefixEnd_854280 : Nat := 4983230072969 + 3 ^ 40 * 854280 * 2
def baseEnd_854280 : Nat := 389916669798242541574439

theorem tailTrace_854280 : CollatzResearch.WordTrace tailWord_854280 prefixEnd_854280 389916669798242541574439 := by
  unfold tailWord_854280
  simp only [CollatzResearch.WordTrace]
  refine ⟨15579075672548467126732147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20772100896731289502309529 15579075672548467126732147)
  ·
    refine ⟨23368613508822700690098221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15579075672548467126732147 23368613508822700690098221)
    ·
      refine ⟨8763230065808512758786833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23368613508822700690098221 8763230065808512758786833)
      ·
        refine ⟨6572422549356384569090125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8763230065808512758786833 6572422549356384569090125)
        ·
          refine ⟨2464658456008644213408797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6572422549356384569090125 2464658456008644213408797)
          ·
            refine ⟨924246921003241580028299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2464658456008644213408797 924246921003241580028299)
            ·
              refine ⟨1386370381504862370042449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 924246921003241580028299 1386370381504862370042449)
              ·
                refine ⟨1039777786128646777531837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1386370381504862370042449 1039777786128646777531837)
                ·
                  refine ⟨389916669798242541574439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1039777786128646777531837 389916669798242541574439)
                  ·
                    rfl

theorem cell20_854280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 1, 2, 3].length) (baseStart_854280 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_854280 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_854280 prefixEnd_854280 := by exact prefixLift 854280
  have htrace : WordTrace (prefixWord ++ tailWord_854280) baseStart_854280 baseEnd_854280 := by
    simpa [prefixWord, tailWord_854280, baseEnd_854280] using wordTrace_append hprefix tailTrace_854280
  have hstable : (prefixWord ++ tailWord_854280).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854280).length < 2 ^ (prefixWord ++ tailWord_854280).sum := by decide
  have hdescent : baseEnd_854280 < baseStart_854280 := by decide
  rcases family_descends (prefixWord ++ tailWord_854280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854284 : List Nat := [2, 2, 1, 2, 2, 2, 3, 1, 5]
def baseStart_854284 : Nat := 118140960795 + 854284 * 2 ^ 59
def prefixEnd_854284 : Nat := 4983230072969 + 3 ^ 40 * 854284 * 2
def baseEnd_854284 : Nat := 389918495507236305441089

theorem tailTrace_854284 : CollatzResearch.WordTrace tailWord_854284 prefixEnd_854284 389918495507236305441089 := by
  unfold tailWord_854284
  simp only [CollatzResearch.WordTrace]
  refine ⟨15579148618541221468304953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20772198158054961957739937 15579148618541221468304953)
  ·
    refine ⟨11684361463905916101228715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15579148618541221468304953 11684361463905916101228715)
    ·
      refine ⟨17526542195858874151843073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11684361463905916101228715 17526542195858874151843073)
      ·
        refine ⟨13144906646894155613882305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17526542195858874151843073 13144906646894155613882305)
        ·
          refine ⟨9858679985170616710411729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13144906646894155613882305 9858679985170616710411729)
          ·
            refine ⟨7394009988877962532808797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9858679985170616710411729 7394009988877962532808797)
            ·
              refine ⟨2772753745829235949803299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7394009988877962532808797 2772753745829235949803299)
              ·
                refine ⟨4159130618743853924704949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2772753745829235949803299 4159130618743853924704949)
                ·
                  refine ⟨389918495507236305441089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4159130618743853924704949 389918495507236305441089)
                  ·
                    rfl

theorem cell20_854284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 1, 5].length) (baseStart_854284 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_854284 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_854284 prefixEnd_854284 := by exact prefixLift 854284
  have htrace : WordTrace (prefixWord ++ tailWord_854284) baseStart_854284 baseEnd_854284 := by
    simpa [prefixWord, tailWord_854284, baseEnd_854284] using wordTrace_append hprefix tailTrace_854284
  have hstable : (prefixWord ++ tailWord_854284).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854284).length < 2 ^ (prefixWord ++ tailWord_854284).sum := by decide
  have hdescent : baseEnd_854284 < baseStart_854284 := by decide
  rcases family_descends (prefixWord ++ tailWord_854284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854308 : List Nat := [2, 3, 1, 3, 1, 2, 2, 2, 4]
def baseStart_854308 : Nat := 118140960795 + 854308 * 2 ^ 59
def prefixEnd_854308 : Nat := 4983230072969 + 3 ^ 40 * 854308 * 2
def baseEnd_854308 : Nat := 389929449761198888640991

theorem tailTrace_854308 : CollatzResearch.WordTrace tailWord_854308 prefixEnd_854308 389929449761198888640991 := by
  unfold tailWord_854308
  simp only [CollatzResearch.WordTrace]
  refine ⟨15579586294497747517741789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20772781725996996690322385 15579586294497747517741789)
  ·
    refine ⟨5842344860436655319153171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15579586294497747517741789 5842344860436655319153171)
    ·
      refine ⟨8763517290654982978729757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5842344860436655319153171 8763517290654982978729757)
      ·
        refine ⟨3286318983995618617023659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8763517290654982978729757 3286318983995618617023659)
        ·
          refine ⟨4929478475993427925535489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3286318983995618617023659 4929478475993427925535489)
          ·
            refine ⟨3697108856995070944151617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4929478475993427925535489 3697108856995070944151617)
            ·
              refine ⟨2772831642746303208113713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3697108856995070944151617 2772831642746303208113713)
              ·
                refine ⟨2079623732059727406085285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2772831642746303208113713 2079623732059727406085285)
                ·
                  refine ⟨389929449761198888640991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2079623732059727406085285 389929449761198888640991)
                  ·
                    rfl

theorem cell20_854308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 2, 4].length) (baseStart_854308 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_854308 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_854308 prefixEnd_854308 := by exact prefixLift 854308
  have htrace : WordTrace (prefixWord ++ tailWord_854308) baseStart_854308 baseEnd_854308 := by
    simpa [prefixWord, tailWord_854308, baseEnd_854308] using wordTrace_append hprefix tailTrace_854308
  have hstable : (prefixWord ++ tailWord_854308).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854308).length < 2 ^ (prefixWord ++ tailWord_854308).sum := by decide
  have hdescent : baseEnd_854308 < baseStart_854308 := by decide
  rcases family_descends (prefixWord ++ tailWord_854308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854321 : List Nat := [1, 2, 2, 3, 5, 1, 1, 3, 2]
def baseStart_854321 : Nat := 118140960795 + 854321 * 2 ^ 59
def prefixEnd_854321 : Nat := 4983230072969 + 3 ^ 40 * 854321 * 2
def baseEnd_854321 : Nat := 389935383315428621207605

theorem tailTrace_854321 : CollatzResearch.WordTrace tailWord_854321 prefixEnd_854321 389935383315428621207605 := by
  unfold tailWord_854321
  simp only [CollatzResearch.WordTrace]
  refine ⟨31159646737948398255706817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20773097825298932170471211 31159646737948398255706817)
  ·
    refine ⟨23369735053461298691780113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31159646737948398255706817 23369735053461298691780113)
    ·
      refine ⟨17527301290095974018835085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23369735053461298691780113 17527301290095974018835085)
      ·
        refine ⟨6572737983785990257063157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17527301290095974018835085 6572737983785990257063157)
        ·
          refine ⟨616194185979936586599671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6572737983785990257063157 616194185979936586599671)
          ·
            refine ⟨924291278969904879899507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 616194185979936586599671 924291278969904879899507)
            ·
              refine ⟨1386436918454857319849261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 924291278969904879899507 1386436918454857319849261)
              ·
                refine ⟨519913844420571494943473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1386436918454857319849261 519913844420571494943473)
                ·
                  refine ⟨389935383315428621207605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 519913844420571494943473 389935383315428621207605)
                  ·
                    rfl

theorem cell20_854321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 1, 3, 2].length) (baseStart_854321 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_854321 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_854321 prefixEnd_854321 := by exact prefixLift 854321
  have htrace : WordTrace (prefixWord ++ tailWord_854321) baseStart_854321 baseEnd_854321 := by
    simpa [prefixWord, tailWord_854321, baseEnd_854321] using wordTrace_append hprefix tailTrace_854321
  have hstable : (prefixWord ++ tailWord_854321).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854321).length < 2 ^ (prefixWord ++ tailWord_854321).sum := by decide
  have hdescent : baseEnd_854321 < baseStart_854321 := by decide
  rcases family_descends (prefixWord ++ tailWord_854321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854353 : List Nat := [1, 2, 2, 1, 4, 3, 2, 5]
def baseStart_854353 : Nat := 118140960795 + 854353 * 2 ^ 59
def prefixEnd_854353 : Nat := 4983230072969 + 3 ^ 40 * 854353 * 2
def baseEnd_854353 : Nat := 129983329662459577380269

theorem tailTrace_854353 : CollatzResearch.WordTrace tailWord_854353 prefixEnd_854353 129983329662459577380269 := by
  unfold tailWord_854353
  simp only [CollatzResearch.WordTrace]
  refine ⟨31160813873832467720871713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20773875915888311813914475 31160813873832467720871713)
  ·
    refine ⟨23370610405374350790653785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31160813873832467720871713 23370610405374350790653785)
    ·
      refine ⟨17527957804030763092990339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23370610405374350790653785 17527957804030763092990339)
      ·
        refine ⟨26291936706046144639485509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17527957804030763092990339 26291936706046144639485509)
        ·
          refine ⟨4929738132383652119903533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26291936706046144639485509 4929738132383652119903533)
          ·
            refine ⟨1848651799643869544963825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4929738132383652119903533 1848651799643869544963825)
            ·
              refine ⟨1386488849732902158722869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1848651799643869544963825 1386488849732902158722869)
              ·
                refine ⟨129983329662459577380269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1386488849732902158722869 129983329662459577380269)
                ·
                  rfl

theorem cell20_854353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 2, 5].length) (baseStart_854353 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_854353 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_854353 prefixEnd_854353 := by exact prefixLift 854353
  have htrace : WordTrace (prefixWord ++ tailWord_854353) baseStart_854353 baseEnd_854353 := by
    simpa [prefixWord, tailWord_854353, baseEnd_854353] using wordTrace_append hprefix tailTrace_854353
  have hstable : (prefixWord ++ tailWord_854353).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854353).length < 2 ^ (prefixWord ++ tailWord_854353).sum := by decide
  have hdescent : baseEnd_854353 < baseStart_854353 := by decide
  rcases family_descends (prefixWord ++ tailWord_854353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854356 : List Nat := [2, 4, 1, 1, 2, 2, 4, 1, 3]
def baseStart_854356 : Nat := 118140960795 + 854356 * 2 ^ 59
def prefixEnd_854356 : Nat := 4983230072969 + 3 ^ 40 * 854356 * 2
def baseEnd_854356 : Nat := 389951358269124055040795

theorem tailTrace_854356 : CollatzResearch.WordTrace tailWord_854356 prefixEnd_854356 389951358269124055040795 := by
  unfold tailWord_854356
  simp only [CollatzResearch.WordTrace]
  refine ⟨15580461646410799616615461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20773948861881066155487281 15580461646410799616615461)
  ·
    refine ⟨2921336558702024928115399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15580461646410799616615461 2921336558702024928115399)
    ·
      refine ⟨4382004838053037392173099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2921336558702024928115399 4382004838053037392173099)
      ·
        refine ⟨6573007257079556088259649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4382004838053037392173099 6573007257079556088259649)
        ·
          refine ⟨4929755442809667066194737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6573007257079556088259649 4929755442809667066194737)
          ·
            refine ⟨3697316582107250299646053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4929755442809667066194737 3697316582107250299646053)
            ·
              refine ⟨693246859145109431183635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3697316582107250299646053 693246859145109431183635)
              ·
                refine ⟨1039870288717664146775453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 693246859145109431183635 1039870288717664146775453)
                ·
                  refine ⟨389951358269124055040795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1039870288717664146775453 389951358269124055040795)
                  ·
                    rfl

theorem cell20_854356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 4, 1, 3].length) (baseStart_854356 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_854356 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_854356 prefixEnd_854356 := by exact prefixLift 854356
  have htrace : WordTrace (prefixWord ++ tailWord_854356) baseStart_854356 baseEnd_854356 := by
    simpa [prefixWord, tailWord_854356, baseEnd_854356] using wordTrace_append hprefix tailTrace_854356
  have hstable : (prefixWord ++ tailWord_854356).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854356).length < 2 ^ (prefixWord ++ tailWord_854356).sum := by decide
  have hdescent : baseEnd_854356 < baseStart_854356 := by decide
  rcases family_descends (prefixWord ++ tailWord_854356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854367 : List Nat := [1, 1, 2, 3, 1, 2, 2, 4, 4]
def baseStart_854367 : Nat := 118140960795 + 854367 * 2 ^ 59
def prefixEnd_854367 : Nat := 4983230072969 + 3 ^ 40 * 854367 * 2
def baseEnd_854367 : Nat := 389956378968856905674083

theorem tailTrace_854367 : CollatzResearch.WordTrace tailWord_854367 prefixEnd_854367 389956378968856905674083 := by
  unfold tailWord_854367
  simp only [CollatzResearch.WordTrace]
  refine ⟨31161324495781748111881355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20774216330521165407920903 31161324495781748111881355)
  ·
    refine ⟨46741986743672622167822033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31161324495781748111881355 46741986743672622167822033)
    ·
      refine ⟨35056490057754466625866525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46741986743672622167822033 35056490057754466625866525)
      ·
        refine ⟨13146183771657924984699947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35056490057754466625866525 13146183771657924984699947)
        ·
          refine ⟨19719275657486887477049921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13146183771657924984699947 19719275657486887477049921)
          ·
            refine ⟨14789456743115165607787441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19719275657486887477049921 14789456743115165607787441)
            ·
              refine ⟨11092092557336374205840581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14789456743115165607787441 11092092557336374205840581)
              ·
                refine ⟨2079767354500570163595109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11092092557336374205840581 2079767354500570163595109)
                ·
                  refine ⟨389956378968856905674083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2079767354500570163595109 389956378968856905674083)
                  ·
                    rfl

theorem cell20_854367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 4, 4].length) (baseStart_854367 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_854367 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_854367 prefixEnd_854367 := by exact prefixLift 854367
  have htrace : WordTrace (prefixWord ++ tailWord_854367) baseStart_854367 baseEnd_854367 := by
    simpa [prefixWord, tailWord_854367, baseEnd_854367] using wordTrace_append hprefix tailTrace_854367
  have hstable : (prefixWord ++ tailWord_854367).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854367).length < 2 ^ (prefixWord ++ tailWord_854367).sum := by decide
  have hdescent : baseEnd_854367 < baseStart_854367 := by decide
  rcases family_descends (prefixWord ++ tailWord_854367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854405 : List Nat := [1, 3, 1, 1, 3, 1, 1, 5, 4]
def baseStart_854405 : Nat := 118140960795 + 854405 * 2 ^ 59
def prefixEnd_854405 : Nat := 4983230072969 + 3 ^ 40 * 854405 * 2
def baseEnd_854405 : Nat := 389973723204297662407261

theorem tailTrace_854405 : CollatzResearch.WordTrace tailWord_854405 prefixEnd_854405 389973723204297662407261 := by
  unfold tailWord_854405
  simp only [CollatzResearch.WordTrace]
  refine ⟨31162710469644080601764669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20775140313096053734509779 31162710469644080601764669)
  ·
    refine ⟨11686016426116530225661751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31162710469644080601764669 11686016426116530225661751)
    ·
      refine ⟨17529024639174795338492627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11686016426116530225661751 17529024639174795338492627)
      ·
        refine ⟨26293536958762193007738941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17529024639174795338492627 26293536958762193007738941)
        ·
          refine ⟨9860076359535822377902103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26293536958762193007738941 9860076359535822377902103)
          ·
            refine ⟨14790114539303733566853155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9860076359535822377902103 14790114539303733566853155)
            ·
              refine ⟨22185171808955600350279733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14790114539303733566853155 22185171808955600350279733)
              ·
                refine ⟨2079859857089587532838725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 22185171808955600350279733 2079859857089587532838725)
                ·
                  refine ⟨389973723204297662407261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2079859857089587532838725 389973723204297662407261)
                  ·
                    rfl

theorem cell20_854405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 5, 4].length) (baseStart_854405 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_854405 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_854405 prefixEnd_854405 := by exact prefixLift 854405
  have htrace : WordTrace (prefixWord ++ tailWord_854405) baseStart_854405 baseEnd_854405 := by
    simpa [prefixWord, tailWord_854405, baseEnd_854405] using wordTrace_append hprefix tailTrace_854405
  have hstable : (prefixWord ++ tailWord_854405).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854405).length < 2 ^ (prefixWord ++ tailWord_854405).sum := by decide
  have hdescent : baseEnd_854405 < baseStart_854405 := by decide
  rcases family_descends (prefixWord ++ tailWord_854405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854439 : List Nat := [1, 1, 6, 1, 1, 2, 1, 5, 2]
def baseStart_854439 : Nat := 118140960795 + 854439 * 2 ^ 59
def prefixEnd_854439 : Nat := 4983230072969 + 3 ^ 40 * 854439 * 2
def baseEnd_854439 : Nat := 389989241730744655273789

theorem tailTrace_854439 : CollatzResearch.WordTrace tailWord_854439 prefixEnd_854439 389989241730744655273789 := by
  unfold tailWord_854439
  simp only [CollatzResearch.WordTrace]
  refine ⟨31163950551520904408502371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20775967034347269605668247 31163950551520904408502371)
  ·
    refine ⟨46745925827281356612753557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31163950551520904408502371 46745925827281356612753557)
    ·
      refine ⟨2191215273153813591222823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 46745925827281356612753557 2191215273153813591222823)
      ·
        refine ⟨3286822909730720386834235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2191215273153813591222823 3286822909730720386834235)
        ·
          refine ⟨4930234364596080580251353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3286822909730720386834235 4930234364596080580251353)
          ·
            refine ⟨3697675773447060435188515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4930234364596080580251353 3697675773447060435188515)
            ·
              refine ⟨5546513660170590652782773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3697675773447060435188515 5546513660170590652782773)
              ·
                refine ⟨519985655640992873698385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5546513660170590652782773 519985655640992873698385)
                ·
                  refine ⟨389989241730744655273789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 519985655640992873698385 389989241730744655273789)
                  ·
                    rfl

theorem cell20_854439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 5, 2].length) (baseStart_854439 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_854439 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_854439 prefixEnd_854439 := by exact prefixLift 854439
  have htrace : WordTrace (prefixWord ++ tailWord_854439) baseStart_854439 baseEnd_854439 := by
    simpa [prefixWord, tailWord_854439, baseEnd_854439] using wordTrace_append hprefix tailTrace_854439
  have hstable : (prefixWord ++ tailWord_854439).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854439).length < 2 ^ (prefixWord ++ tailWord_854439).sum := by decide
  have hdescent : baseEnd_854439 < baseStart_854439 := by decide
  rcases family_descends (prefixWord ++ tailWord_854439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854450 : List Nat := [3, 2, 1, 1, 1, 1, 11]
def baseStart_854450 : Nat := 118140960795 + 854450 * 2 ^ 59
def prefixEnd_854450 : Nat := 4983230072969 + 3 ^ 40 * 854450 * 2
def baseEnd_854450 : Nat := 43332695825608611767453

theorem tailTrace_854450 : CollatzResearch.WordTrace tailWord_854450 prefixEnd_854450 43332695825608611767453 := by
  unfold tailWord_854450
  simp only [CollatzResearch.WordTrace]
  refine ⟨7791087938620263321788201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20776234502987368858101869 7791087938620263321788201)
  ·
    refine ⟨5843315953965197491341151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7791087938620263321788201 5843315953965197491341151)
    ·
      refine ⟨8764973930947796237011727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5843315953965197491341151 8764973930947796237011727)
      ·
        refine ⟨13147460896421694355517591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8764973930947796237011727 13147460896421694355517591)
        ·
          refine ⟨19721191344632541533276387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13147460896421694355517591 19721191344632541533276387)
          ·
            refine ⟨29581787016948812299914581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19721191344632541533276387 29581787016948812299914581)
            ·
              refine ⟨43332695825608611767453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 29581787016948812299914581 43332695825608611767453)
              ·
                rfl

theorem cell20_854450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 11].length) (baseStart_854450 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_854450 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_854450 prefixEnd_854450 := by exact prefixLift 854450
  have htrace : WordTrace (prefixWord ++ tailWord_854450) baseStart_854450 baseEnd_854450 := by
    simpa [prefixWord, tailWord_854450, baseEnd_854450] using wordTrace_append hprefix tailTrace_854450
  have hstable : (prefixWord ++ tailWord_854450).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854450).length < 2 ^ (prefixWord ++ tailWord_854450).sum := by decide
  have hdescent : baseEnd_854450 < baseStart_854450 := by decide
  rcases family_descends (prefixWord ++ tailWord_854450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854453 : List Nat := [1, 3, 3, 2, 3, 1, 1, 1, 5]
def baseStart_854453 : Nat := 118140960795 + 854453 * 2 ^ 59
def prefixEnd_854453 : Nat := 4983230072969 + 3 ^ 40 * 854453 * 2
def baseEnd_854453 : Nat := 389995631712222828807065

theorem tailTrace_854453 : CollatzResearch.WordTrace tailWord_854453 prefixEnd_854453 389995631712222828807065 := by
  unfold tailWord_854453
  simp only [CollatzResearch.WordTrace]
  refine ⟨31164461173470184799512013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20776307448980123199674675 31164461173470184799512013)
  ·
    refine ⟨11686672940051319299817005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31164461173470184799512013 11686672940051319299817005)
    ·
      refine ⟨4382502352519244737431377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11686672940051319299817005 4382502352519244737431377)
      ·
        refine ⟨3286876764389433553073533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4382502352519244737431377 3286876764389433553073533)
        ·
          refine ⟨1232578786646037582402575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3286876764389433553073533 1232578786646037582402575)
          ·
            refine ⟨1848868179969056373603863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1232578786646037582402575 1848868179969056373603863)
            ·
              refine ⟨2773302269953584560405795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1848868179969056373603863 2773302269953584560405795)
              ·
                refine ⟨4159953404930376840608693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2773302269953584560405795 4159953404930376840608693)
                ·
                  refine ⟨389995631712222828807065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4159953404930376840608693 389995631712222828807065)
                  ·
                    rfl

theorem cell20_854453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 1, 5].length) (baseStart_854453 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_854453 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_854453 prefixEnd_854453 := by exact prefixLift 854453
  have htrace : WordTrace (prefixWord ++ tailWord_854453) baseStart_854453 baseEnd_854453 := by
    simpa [prefixWord, tailWord_854453, baseEnd_854453] using wordTrace_append hprefix tailTrace_854453
  have hstable : (prefixWord ++ tailWord_854453).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854453).length < 2 ^ (prefixWord ++ tailWord_854453).sum := by decide
  have hdescent : baseEnd_854453 < baseStart_854453 := by decide
  rcases family_descends (prefixWord ++ tailWord_854453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854460 : List Nat := [2, 2, 2, 4, 1, 1, 1, 3, 4]
def baseStart_854460 : Nat := 118140960795 + 854460 * 2 ^ 59
def prefixEnd_854460 : Nat := 4983230072969 + 3 ^ 40 * 854460 * 2
def baseEnd_854460 : Nat := 389998826702961915573703

theorem tailTrace_854460 : CollatzResearch.WordTrace tailWord_854460 prefixEnd_854460 389998826702961915573703 := by
  unfold tailWord_854460
  simp only [CollatzResearch.WordTrace]
  refine ⟨15582358242222412497508417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20776477656296549996677889 15582358242222412497508417)
  ·
    refine ⟨11686768681666809373131313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15582358242222412497508417 11686768681666809373131313)
    ·
      refine ⟨8765076511250107029848485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11686768681666809373131313 8765076511250107029848485)
      ·
        refine ⟨1643451845859395068096591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8765076511250107029848485 1643451845859395068096591)
        ·
          refine ⟨2465177768789092602144887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1643451845859395068096591 2465177768789092602144887)
          ·
            refine ⟨3697766653183638903217331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2465177768789092602144887 3697766653183638903217331)
            ·
              refine ⟨5546649979775458354825997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3697766653183638903217331 5546649979775458354825997)
              ·
                refine ⟨2079993742415796883059749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5546649979775458354825997 2079993742415796883059749)
                ·
                  refine ⟨389998826702961915573703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2079993742415796883059749 389998826702961915573703)
                  ·
                    rfl

theorem cell20_854460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 3, 4].length) (baseStart_854460 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_854460 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_854460 prefixEnd_854460 := by exact prefixLift 854460
  have htrace : WordTrace (prefixWord ++ tailWord_854460) baseStart_854460 baseEnd_854460 := by
    simpa [prefixWord, tailWord_854460, baseEnd_854460] using wordTrace_append hprefix tailTrace_854460
  have hstable : (prefixWord ++ tailWord_854460).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854460).length < 2 ^ (prefixWord ++ tailWord_854460).sum := by decide
  have hdescent : baseEnd_854460 < baseStart_854460 := by decide
  rcases family_descends (prefixWord ++ tailWord_854460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854484 : List Nat := [2, 4, 1, 2, 2, 1, 4, 4]
def baseStart_854484 : Nat := 118140960795 + 854484 * 2 ^ 59
def prefixEnd_854484 : Nat := 4983230072969 + 3 ^ 40 * 854484 * 2
def baseEnd_854484 : Nat := 130003260318974832924535

theorem tailTrace_854484 : CollatzResearch.WordTrace tailWord_854484 prefixEnd_854484 130003260318974832924535 := by
  unfold tailWord_854484
  simp only [CollatzResearch.WordTrace]
  refine ⟨15582795918178938546945253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20777061224238584729260337 15582795918178938546945253)
  ·
    refine ⟨2921774234658550977552235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15582795918178938546945253 2921774234658550977552235)
    ·
      refine ⟨4382661351987826466328353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2921774234658550977552235 4382661351987826466328353)
      ·
        refine ⟨3286996013990869849746265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4382661351987826466328353 3286996013990869849746265)
        ·
          refine ⟨2465247010493152387309699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3286996013990869849746265 2465247010493152387309699)
          ·
            refine ⟨3697870515739728580964549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2465247010493152387309699 3697870515739728580964549)
            ·
              refine ⟨693350721701199108930853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3697870515739728580964549 693350721701199108930853)
              ·
                refine ⟨130003260318974832924535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 693350721701199108930853 130003260318974832924535)
                ·
                  rfl

theorem cell20_854484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 4, 4].length) (baseStart_854484 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_854484 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_854484 prefixEnd_854484 := by exact prefixLift 854484
  have htrace : WordTrace (prefixWord ++ tailWord_854484) baseStart_854484 baseEnd_854484 := by
    simpa [prefixWord, tailWord_854484, baseEnd_854484] using wordTrace_append hprefix tailTrace_854484
  have hstable : (prefixWord ++ tailWord_854484).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854484).length < 2 ^ (prefixWord ++ tailWord_854484).sum := by decide
  have hdescent : baseEnd_854484 < baseStart_854484 := by decide
  rcases family_descends (prefixWord ++ tailWord_854484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854512 : List Nat := [2, 1, 1, 1, 3, 3, 2, 4, 3]
def baseStart_854512 : Nat := 118140960795 + 854512 * 2 ^ 59
def prefixEnd_854512 : Nat := 4983230072969 + 3 ^ 40 * 854512 * 2
def baseEnd_854512 : Nat := 390022560919880845840157

theorem tailTrace_854512 : CollatzResearch.WordTrace tailWord_854512 prefixEnd_854512 390022560919880845840157 := by
  unfold tailWord_854512
  simp only [CollatzResearch.WordTrace]
  refine ⟨15583306540128218937954895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20777742053504291917273193 15583306540128218937954895)
  ·
    refine ⟨23374959810192328406932343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15583306540128218937954895 23374959810192328406932343)
    ·
      refine ⟨35062439715288492610398515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23374959810192328406932343 35062439715288492610398515)
      ·
        refine ⟨52593659572932738915597773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35062439715288492610398515 52593659572932738915597773)
        ·
          refine ⟨19722622339849777093349165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52593659572932738915597773 19722622339849777093349165)
          ·
            refine ⟨7395983377443666410005937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19722622339849777093349165 7395983377443666410005937)
            ·
              refine ⟨5546987533082749807504453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7395983377443666410005937 5546987533082749807504453)
              ·
                refine ⟨1040060162453015588907085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5546987533082749807504453 1040060162453015588907085)
                ·
                  refine ⟨390022560919880845840157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1040060162453015588907085 390022560919880845840157)
                  ·
                    rfl

theorem cell20_854512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 4, 3].length) (baseStart_854512 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_854512 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_854512 prefixEnd_854512 := by exact prefixLift 854512
  have htrace : WordTrace (prefixWord ++ tailWord_854512) baseStart_854512 baseEnd_854512 := by
    simpa [prefixWord, tailWord_854512, baseEnd_854512] using wordTrace_append hprefix tailTrace_854512
  have hstable : (prefixWord ++ tailWord_854512).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854512).length < 2 ^ (prefixWord ++ tailWord_854512).sum := by decide
  have hdescent : baseEnd_854512 < baseStart_854512 := by decide
  rcases family_descends (prefixWord ++ tailWord_854512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854515 : List Nat := [1, 1, 1, 2, 2, 2, 7, 2, 2]
def baseStart_854515 : Nat := 118140960795 + 854515 * 2 ^ 59
def prefixEnd_854515 : Nat := 4983230072969 + 3 ^ 40 * 854515 * 2
def baseEnd_854515 : Nat := 390023930201626168740145

theorem tailTrace_854515 : CollatzResearch.WordTrace tailWord_854515 prefixEnd_854515 390023930201626168740145 := by
  unfold tailWord_854515
  simp only [CollatzResearch.WordTrace]
  refine ⟨31166722499245569388268999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20777814999497046258845999 31166722499245569388268999)
  ·
    refine ⟨46750083748868354082403499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31166722499245569388268999 46750083748868354082403499)
    ·
      refine ⟨70125125623302531123605249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46750083748868354082403499 70125125623302531123605249)
      ·
        refine ⟨52593844217476898342703937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70125125623302531123605249 52593844217476898342703937)
        ·
          refine ⟨39445383163107673757027953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52593844217476898342703937 39445383163107673757027953)
          ·
            refine ⟨29584037372330755317770965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39445383163107673757027953 29584037372330755317770965)
            ·
              refine ⟨693375875914002077760257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 29584037372330755317770965 693375875914002077760257)
              ·
                refine ⟨520031906935501558320193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 693375875914002077760257 520031906935501558320193)
                ·
                  refine ⟨390023930201626168740145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 520031906935501558320193 390023930201626168740145)
                  ·
                    rfl

theorem cell20_854515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 7, 2, 2].length) (baseStart_854515 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_854515 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_854515 prefixEnd_854515 := by exact prefixLift 854515
  have htrace : WordTrace (prefixWord ++ tailWord_854515) baseStart_854515 baseEnd_854515 := by
    simpa [prefixWord, tailWord_854515, baseEnd_854515] using wordTrace_append hprefix tailTrace_854515
  have hstable : (prefixWord ++ tailWord_854515).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854515).length < 2 ^ (prefixWord ++ tailWord_854515).sum := by decide
  have hdescent : baseEnd_854515 < baseStart_854515 := by decide
  rcases family_descends (prefixWord ++ tailWord_854515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854529 : List Nat := [1, 2, 4, 1, 3, 2, 1, 3, 3]
def baseStart_854529 : Nat := 118140960795 + 854529 * 2 ^ 59
def prefixEnd_854529 : Nat := 4983230072969 + 3 ^ 40 * 854529 * 2
def baseEnd_854529 : Nat := 390030320183104342273421

theorem tailTrace_854529 : CollatzResearch.WordTrace tailWord_854529 prefixEnd_854529 390030320183104342273421 := by
  unfold tailWord_854529
  simp only [CollatzResearch.WordTrace]
  refine ⟨31167233121194849779278641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20778155414129899852852427 31167233121194849779278641)
  ·
    refine ⟨23375424840896137334458981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31167233121194849779278641 23375424840896137334458981)
    ·
      refine ⟨4382892157668025750211059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23375424840896137334458981 4382892157668025750211059)
      ·
        refine ⟨6574338236502038625316589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4382892157668025750211059 6574338236502038625316589)
        ·
          refine ⟨2465376838688264484493721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6574338236502038625316589 2465376838688264484493721)
          ·
            refine ⟨1849032629016198363370291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2465376838688264484493721 1849032629016198363370291)
            ·
              refine ⟨2773548943524297545055437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1849032629016198363370291 2773548943524297545055437)
              ·
                refine ⟨1040080853821611579395789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2773548943524297545055437 1040080853821611579395789)
                ·
                  refine ⟨390030320183104342273421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1040080853821611579395789 390030320183104342273421)
                  ·
                    rfl

theorem cell20_854529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 3, 3].length) (baseStart_854529 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_854529 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_854529 prefixEnd_854529 := by exact prefixLift 854529
  have htrace : WordTrace (prefixWord ++ tailWord_854529) baseStart_854529 baseEnd_854529 := by
    simpa [prefixWord, tailWord_854529, baseEnd_854529] using wordTrace_append hprefix tailTrace_854529
  have hstable : (prefixWord ++ tailWord_854529).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854529).length < 2 ^ (prefixWord ++ tailWord_854529).sum := by decide
  have hdescent : baseEnd_854529 < baseStart_854529 := by decide
  rcases family_descends (prefixWord ++ tailWord_854529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854570 : List Nat := [3, 1, 4, 1, 1, 2, 4, 2, 2]
def baseStart_854570 : Nat := 118140960795 + 854570 * 2 ^ 59
def prefixEnd_854570 : Nat := 4983230072969 + 3 ^ 40 * 854570 * 2
def baseEnd_854570 : Nat := 390049033700290421906587

theorem tailTrace_854570 : CollatzResearch.WordTrace tailWord_854570 prefixEnd_854570 390049033700290421906587 := by
  unfold tailWord_854570
  simp only [CollatzResearch.WordTrace]
  refine ⟨7792182128511578445380291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20779152342697542521014109 7792182128511578445380291)
  ·
    refine ⟨11688273192767367668070437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7792182128511578445380291 11688273192767367668070437)
    ·
      refine ⟨2191551223643881437763207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11688273192767367668070437 2191551223643881437763207)
      ·
        refine ⟨3287326835465822156644811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2191551223643881437763207 3287326835465822156644811)
        ·
          refine ⟨4930990253198733234967217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3287326835465822156644811 4930990253198733234967217)
          ·
            refine ⟨3698242689899049926225413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4930990253198733234967217 3698242689899049926225413)
            ·
              refine ⟨693420504356071861167265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3698242689899049926225413 693420504356071861167265)
              ·
                refine ⟨520065378267053895875449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 693420504356071861167265 520065378267053895875449)
                ·
                  refine ⟨390049033700290421906587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 520065378267053895875449 390049033700290421906587)
                  ·
                    rfl

theorem cell20_854570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 4, 2, 2].length) (baseStart_854570 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_854570 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_854570 prefixEnd_854570 := by exact prefixLift 854570
  have htrace : WordTrace (prefixWord ++ tailWord_854570) baseStart_854570 baseEnd_854570 := by
    simpa [prefixWord, tailWord_854570, baseEnd_854570] using wordTrace_append hprefix tailTrace_854570
  have hstable : (prefixWord ++ tailWord_854570).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854570).length < 2 ^ (prefixWord ++ tailWord_854570).sum := by decide
  have hdescent : baseEnd_854570 < baseStart_854570 := by decide
  rcases family_descends (prefixWord ++ tailWord_854570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854571 : List Nat := [1, 1, 1, 1, 2, 1, 3, 5, 5]
def baseStart_854571 : Nat := 118140960795 + 854571 * 2 ^ 59
def prefixEnd_854571 : Nat := 4983230072969 + 3 ^ 40 * 854571 * 2
def baseEnd_854571 : Nat := 390049490127538862873249

theorem tailTrace_854571 : CollatzResearch.WordTrace tailWord_854571 prefixEnd_854571 390049490127538862873249 := by
  unfold tailWord_854571
  simp only [CollatzResearch.WordTrace]
  refine ⟨31168764987042690952307567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20779176658028460634871711 31168764987042690952307567)
  ·
    refine ⟨46753147480564036428461351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31168764987042690952307567 46753147480564036428461351)
    ·
      refine ⟨70129721220846054642692027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46753147480564036428461351 70129721220846054642692027)
      ·
        refine ⟨105194581831269081964038041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70129721220846054642692027 105194581831269081964038041)
        ·
          refine ⟨78895936373451811473028531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105194581831269081964038041 78895936373451811473028531)
          ·
            refine ⟨118343904560177717209542797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78895936373451811473028531 118343904560177717209542797)
            ·
              refine ⟨44378964210066643953578549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118343904560177717209542797 44378964210066643953578549)
              ·
                refine ⟨4160527894693747870647989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44378964210066643953578549 4160527894693747870647989)
                ·
                  refine ⟨390049490127538862873249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4160527894693747870647989 390049490127538862873249)
                  ·
                    rfl

theorem cell20_854571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 5, 5].length) (baseStart_854571 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_854571 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_854571 prefixEnd_854571 := by exact prefixLift 854571
  have htrace : WordTrace (prefixWord ++ tailWord_854571) baseStart_854571 baseEnd_854571 := by
    simpa [prefixWord, tailWord_854571, baseEnd_854571] using wordTrace_append hprefix tailTrace_854571
  have hstable : (prefixWord ++ tailWord_854571).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854571).length < 2 ^ (prefixWord ++ tailWord_854571).sum := by decide
  have hdescent : baseEnd_854571 < baseStart_854571 := by decide
  rcases family_descends (prefixWord ++ tailWord_854571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854573 : List Nat := [1, 5, 4, 1, 2, 1, 1, 5]
def baseStart_854573 : Nat := 118140960795 + 854573 * 2 ^ 59
def prefixEnd_854573 : Nat := 4983230072969 + 3 ^ 40 * 854573 * 2
def baseEnd_854573 : Nat := 130016800994011914935525

theorem tailTrace_854573 : CollatzResearch.WordTrace tailWord_854573 prefixEnd_854573 130016800994011914935525 := by
  unfold tailWord_854573
  simp only [CollatzResearch.WordTrace]
  refine ⟨31168837933035445293880373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20779225288690296862586915 31168837933035445293880373)
  ·
    refine ⟨2922078556222072996301285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31168837933035445293880373 2922078556222072996301285)
    ·
      refine ⟨547889729291638686806491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2922078556222072996301285 547889729291638686806491)
      ·
        refine ⟨821834593937458030209737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 547889729291638686806491 821834593937458030209737)
        ·
          refine ⟨616375945453093522657303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 821834593937458030209737 616375945453093522657303)
          ·
            refine ⟨924563918179640283985955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 616375945453093522657303 924563918179640283985955)
            ·
              refine ⟨1386845877269460425978933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 924563918179640283985955 1386845877269460425978933)
              ·
                refine ⟨130016800994011914935525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1386845877269460425978933 130016800994011914935525)
                ·
                  rfl

theorem cell20_854573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 1, 5].length) (baseStart_854573 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_854573 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_854573 prefixEnd_854573 := by exact prefixLift 854573
  have htrace : WordTrace (prefixWord ++ tailWord_854573) baseStart_854573 baseEnd_854573 := by
    simpa [prefixWord, tailWord_854573, baseEnd_854573] using wordTrace_append hprefix tailTrace_854573
  have hstable : (prefixWord ++ tailWord_854573).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854573).length < 2 ^ (prefixWord ++ tailWord_854573).sum := by decide
  have hdescent : baseEnd_854573 < baseStart_854573 := by decide
  rcases family_descends (prefixWord ++ tailWord_854573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854653 : List Nat := [1, 4, 1, 1, 6, 1, 2, 4]
def baseStart_854653 : Nat := 118140960795 + 854653 * 2 ^ 59
def prefixEnd_854653 : Nat := 4983230072969 + 3 ^ 40 * 854653 * 2
def baseEnd_854653 : Nat := 130028972387303674046527

theorem tailTrace_854653 : CollatzResearch.WordTrace tailWord_854653 prefixEnd_854653 130028972387303674046527 := by
  unfold tailWord_854653
  simp only [CollatzResearch.WordTrace]
  refine ⟨31171755772745618956792613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20781170515163745971195075 31171755772745618956792613)
  ·
    refine ⟨5844704207389803554398615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31171755772745618956792613 5844704207389803554398615)
    ·
      refine ⟨8767056311084705331597923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5844704207389803554398615 8767056311084705331597923)
      ·
        refine ⟨13150584466627057997396885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8767056311084705331597923 13150584466627057997396885)
        ·
          refine ⟨616433646873143343627979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 13150584466627057997396885 616433646873143343627979)
          ·
            refine ⟨924650470309715015441969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 616433646873143343627979 924650470309715015441969)
            ·
              refine ⟨693487852732286261581477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 924650470309715015441969 693487852732286261581477)
              ·
                refine ⟨130028972387303674046527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 693487852732286261581477 130028972387303674046527)
                ·
                  rfl

theorem cell20_854653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 2, 4].length) (baseStart_854653 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_854653 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_854653 prefixEnd_854653 := by exact prefixLift 854653
  have htrace : WordTrace (prefixWord ++ tailWord_854653) baseStart_854653 baseEnd_854653 := by
    simpa [prefixWord, tailWord_854653, baseEnd_854653] using wordTrace_append hprefix tailTrace_854653
  have hstable : (prefixWord ++ tailWord_854653).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854653).length < 2 ^ (prefixWord ++ tailWord_854653).sum := by decide
  have hdescent : baseEnd_854653 < baseStart_854653 := by decide
  rcases family_descends (prefixWord ++ tailWord_854653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854684 : List Nat := [2, 2, 3, 2, 2, 2, 3, 2, 2]
def baseStart_854684 : Nat := 118140960795 + 854684 * 2 ^ 59
def prefixEnd_854684 : Nat := 4983230072969 + 3 ^ 40 * 854684 * 2
def baseEnd_854684 : Nat := 390101066406612692106121

theorem tailTrace_854684 : CollatzResearch.WordTrace tailWord_854684 prefixEnd_854684 390101066406612692106121 := by
  unfold tailWord_854684
  simp only [CollatzResearch.WordTrace]
  refine ⟨15586443217816655625585553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20781924290422207500780737 15586443217816655625585553)
  ·
    refine ⟨11689832413362491719189165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15586443217816655625585553 11689832413362491719189165)
    ·
      refine ⟨4383687155010934394695937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11689832413362491719189165 4383687155010934394695937)
      ·
        refine ⟨3287765366258200796021953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4383687155010934394695937 3287765366258200796021953)
        ·
          refine ⟨2465824024693650597016465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3287765366258200796021953 2465824024693650597016465)
          ·
            refine ⟨1849368018520237947762349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2465824024693650597016465 1849368018520237947762349)
            ·
              refine ⟨693513006945089230410881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1849368018520237947762349 693513006945089230410881)
              ·
                refine ⟨520134755208816922808161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 693513006945089230410881 520134755208816922808161)
                ·
                  refine ⟨390101066406612692106121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 520134755208816922808161 390101066406612692106121)
                  ·
                    rfl

theorem cell20_854684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 3, 2, 2].length) (baseStart_854684 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_854684 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_854684 prefixEnd_854684 := by exact prefixLift 854684
  have htrace : WordTrace (prefixWord ++ tailWord_854684) baseStart_854684 baseEnd_854684 := by
    simpa [prefixWord, tailWord_854684, baseEnd_854684] using wordTrace_append hprefix tailTrace_854684
  have hstable : (prefixWord ++ tailWord_854684).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854684).length < 2 ^ (prefixWord ++ tailWord_854684).sum := by decide
  have hdescent : baseEnd_854684 < baseStart_854684 := by decide
  rcases family_descends (prefixWord ++ tailWord_854684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854716 : List Nat := [2, 2, 2, 3, 1, 1, 1, 8]
def baseStart_854716 : Nat := 118140960795 + 854716 * 2 ^ 59
def prefixEnd_854716 : Nat := 4983230072969 + 3 ^ 40 * 854716 * 2
def baseEnd_854716 : Nat := 130038557359520934346441

theorem tailTrace_854716 : CollatzResearch.WordTrace tailWord_854716 prefixEnd_854716 130038557359520934346441 := by
  unfold tailWord_854716
  simp only [CollatzResearch.WordTrace]
  refine ⟨15587026785758690358168001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20782702381011587144224001 15587026785758690358168001)
  ·
    refine ⟨11690270089319017768626001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15587026785758690358168001 11690270089319017768626001)
    ·
      refine ⟨8767702566989263326469501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11690270089319017768626001 8767702566989263326469501)
      ·
        refine ⟨3287888462620973747426063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8767702566989263326469501 3287888462620973747426063)
        ·
          refine ⟨4931832693931460621139095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3287888462620973747426063 4931832693931460621139095)
          ·
            refine ⟨7397749040897190931708643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4931832693931460621139095 7397749040897190931708643)
            ·
              refine ⟨11096623561345786397562965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7397749040897190931708643 11096623561345786397562965)
              ·
                refine ⟨130038557359520934346441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11096623561345786397562965 130038557359520934346441)
                ·
                  rfl

theorem cell20_854716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 8].length) (baseStart_854716 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_854716 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_854716 prefixEnd_854716 := by exact prefixLift 854716
  have htrace : WordTrace (prefixWord ++ tailWord_854716) baseStart_854716 baseEnd_854716 := by
    simpa [prefixWord, tailWord_854716, baseEnd_854716] using wordTrace_append hprefix tailTrace_854716
  have hstable : (prefixWord ++ tailWord_854716).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854716).length < 2 ^ (prefixWord ++ tailWord_854716).sum := by decide
  have hdescent : baseEnd_854716 < baseStart_854716 := by decide
  rcases family_descends (prefixWord ++ tailWord_854716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854733 : List Nat := [1, 6, 2, 1, 10]
def baseStart_854733 : Nat := 118140960795 + 854733 * 2 ^ 59
def prefixEnd_854733 : Nat := 4983230072969 + 3 ^ 40 * 854733 * 2
def baseEnd_854733 : Nat := 4816338658540571598427

theorem tailTrace_854733 : CollatzResearch.WordTrace tailWord_854733 prefixEnd_854733 4816338658540571598427 := by
  unfold tailWord_854733
  simp only [CollatzResearch.WordTrace]
  refine ⟨31174673612455792619704853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20783115741637195079803235 31174673612455792619704853)
  ·
    refine ⟨1461312825583865279048665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 31174673612455792619704853 1461312825583865279048665)
    ·
      refine ⟨1095984619187898959286499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1461312825583865279048665 1095984619187898959286499)
      ·
        refine ⟨1643976928781848438929749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1095984619187898959286499 1643976928781848438929749)
        ·
          refine ⟨4816338658540571598427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1643976928781848438929749 4816338658540571598427)
          ·
            rfl

theorem cell20_854733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 10].length) (baseStart_854733 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_854733 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_854733 prefixEnd_854733 := by exact prefixLift 854733
  have htrace : WordTrace (prefixWord ++ tailWord_854733) baseStart_854733 baseEnd_854733 := by
    simpa [prefixWord, tailWord_854733, baseEnd_854733] using wordTrace_append hprefix tailTrace_854733
  have hstable : (prefixWord ++ tailWord_854733).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854733).length < 2 ^ (prefixWord ++ tailWord_854733).sum := by decide
  have hdescent : baseEnd_854733 < baseStart_854733 := by decide
  rcases family_descends (prefixWord ++ tailWord_854733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854743 : List Nat := [1, 1, 3, 2, 1, 4, 4, 2, 2]
def baseStart_854743 : Nat := 118140960795 + 854743 * 2 ^ 59
def prefixEnd_854743 : Nat := 4983230072969 + 3 ^ 40 * 854743 * 2
def baseEnd_854743 : Nat := 390127995614270709139213

theorem tailTrace_854743 : CollatzResearch.WordTrace tailWord_854743 prefixEnd_854743 390127995614270709139213 := by
  unfold tailWord_854743
  simp only [CollatzResearch.WordTrace]
  refine ⟨31175038342419564327568883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20783358894946376218379255 31175038342419564327568883)
  ·
    refine ⟨46762557513629346491353325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31175038342419564327568883 46762557513629346491353325)
    ·
      refine ⟨17535959067611004934257497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46762557513629346491353325 17535959067611004934257497)
      ·
        refine ⟨13151969300708253700693123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17535959067611004934257497 13151969300708253700693123)
        ·
          refine ⟨19727953951062380551039685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13151969300708253700693123 19727953951062380551039685)
          ·
            refine ⟨3698991365824196353319941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19727953951062380551039685 3698991365824196353319941)
            ·
              refine ⟨693560881092036816247489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3698991365824196353319941 693560881092036816247489)
              ·
                refine ⟨520170660819027612185617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 693560881092036816247489 520170660819027612185617)
                ·
                  refine ⟨390127995614270709139213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 520170660819027612185617 390127995614270709139213)
                  ·
                    rfl

theorem cell20_854743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 4, 2, 2].length) (baseStart_854743 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_854743 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_854743 prefixEnd_854743 := by exact prefixLift 854743
  have htrace : WordTrace (prefixWord ++ tailWord_854743) baseStart_854743 baseEnd_854743 := by
    simpa [prefixWord, tailWord_854743, baseEnd_854743] using wordTrace_append hprefix tailTrace_854743
  have hstable : (prefixWord ++ tailWord_854743).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854743).length < 2 ^ (prefixWord ++ tailWord_854743).sum := by decide
  have hdescent : baseEnd_854743 < baseStart_854743 := by decide
  rcases family_descends (prefixWord ++ tailWord_854743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854792 : List Nat := [2, 1, 3, 2, 2, 3, 7]
def baseStart_854792 : Nat := 118140960795 + 854792 * 2 ^ 59
def prefixEnd_854792 : Nat := 4983230072969 + 3 ^ 40 * 854792 * 2
def baseEnd_854792 : Nat := 43350040061049368500631

theorem tailTrace_854792 : CollatzResearch.WordTrace tailWord_854792 prefixEnd_854792 43350040061049368500631 := by
  unfold tailWord_854792
  simp only [CollatzResearch.WordTrace]
  refine ⟨15588412759621022848051315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20784550346161363797401753 15588412759621022848051315)
  ·
    refine ⟨23382619139431534272076973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15588412759621022848051315 23382619139431534272076973)
    ·
      refine ⟨8768482177286825352028865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23382619139431534272076973 8768482177286825352028865)
      ·
        refine ⟨6576361632965119014021649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8768482177286825352028865 6576361632965119014021649)
        ·
          refine ⟨4932271224723839260516237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6576361632965119014021649 4932271224723839260516237)
          ·
            refine ⟨1849601709271439722693589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4932271224723839260516237 1849601709271439722693589)
            ·
              refine ⟨43350040061049368500631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1849601709271439722693589 43350040061049368500631)
              ·
                rfl

theorem cell20_854792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 7].length) (baseStart_854792 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_854792 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_854792 prefixEnd_854792 := by exact prefixLift 854792
  have htrace : WordTrace (prefixWord ++ tailWord_854792) baseStart_854792 baseEnd_854792 := by
    simpa [prefixWord, tailWord_854792, baseEnd_854792] using wordTrace_append hprefix tailTrace_854792
  have hstable : (prefixWord ++ tailWord_854792).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854792).length < 2 ^ (prefixWord ++ tailWord_854792).sum := by decide
  have hdescent : baseEnd_854792 < baseStart_854792 := by decide
  rcases family_descends (prefixWord ++ tailWord_854792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854799 : List Nat := [1, 1, 2, 1, 1, 1, 7, 1, 5]
def baseStart_854799 : Nat := 118140960795 + 854799 * 2 ^ 59
def prefixEnd_854799 : Nat := 4983230072969 + 3 ^ 40 * 854799 * 2
def baseEnd_854799 : Nat := 390153555540183403272317

theorem tailTrace_854799 : CollatzResearch.WordTrace tailWord_854799 prefixEnd_854799 390153555540183403272317 := by
  unfold tailWord_854799
  simp only [CollatzResearch.WordTrace]
  refine ⟨31177080830216685891607451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20784720553477790594404967 31177080830216685891607451)
  ·
    refine ⟨46765621245325028837411177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31177080830216685891607451 46765621245325028837411177)
    ·
      refine ⟨35074215933993771628058383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46765621245325028837411177 35074215933993771628058383)
      ·
        refine ⟨52611323900990657442087575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35074215933993771628058383 52611323900990657442087575)
        ·
          refine ⟨78916985851485986163131363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52611323900990657442087575 78916985851485986163131363)
          ·
            refine ⟨118375478777228979244697045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78916985851485986163131363 118375478777228979244697045)
            ·
              refine ⟨2774425283841304201047587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 118375478777228979244697045 2774425283841304201047587)
              ·
                refine ⟨4161637925761956301571381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2774425283841304201047587 4161637925761956301571381)
                ·
                  refine ⟨390153555540183403272317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4161637925761956301571381 390153555540183403272317)
                  ·
                    rfl

theorem cell20_854799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 1, 5].length) (baseStart_854799 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_854799 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_854799 prefixEnd_854799 := by exact prefixLift 854799
  have htrace : WordTrace (prefixWord ++ tailWord_854799) baseStart_854799 baseEnd_854799 := by
    simpa [prefixWord, tailWord_854799, baseEnd_854799] using wordTrace_append hprefix tailTrace_854799
  have hstable : (prefixWord ++ tailWord_854799).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854799).length < 2 ^ (prefixWord ++ tailWord_854799).sum := by decide
  have hdescent : baseEnd_854799 < baseStart_854799 := by decide
  rcases family_descends (prefixWord ++ tailWord_854799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854826 : List Nat := [3, 1, 4, 3, 1, 1, 1, 6]
def baseStart_854826 : Nat := 118140960795 + 854826 * 2 ^ 59
def prefixEnd_854826 : Nat := 4983230072969 + 3 ^ 40 * 854826 * 2
def baseEnd_854826 : Nat := 130055293025297103124069

theorem tailTrace_854826 : CollatzResearch.WordTrace tailWord_854826 prefixEnd_854826 130055293025297103124069 := by
  unfold tailWord_854826
  simp only [CollatzResearch.WordTrace]
  refine ⟨7794516400279717375710083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20785377067412579668560221 7794516400279717375710083)
  ·
    refine ⟨11691774600419576063565125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7794516400279717375710083 11691774600419576063565125)
    ·
      refine ⟨2192207737578670511918461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11691774600419576063565125 2192207737578670511918461)
      ·
        refine ⟨822077901592001441969423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2192207737578670511918461 822077901592001441969423)
        ·
          refine ⟨1233116852388002162954135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 822077901592001441969423 1233116852388002162954135)
          ·
            refine ⟨1849675278582003244431203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1233116852388002162954135 1849675278582003244431203)
            ·
              refine ⟨2774512917873004866646805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1849675278582003244431203 2774512917873004866646805)
              ·
                refine ⟨130055293025297103124069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2774512917873004866646805 130055293025297103124069)
                ·
                  rfl

theorem cell20_854826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 6].length) (baseStart_854826 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_854826 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_854826 prefixEnd_854826 := by exact prefixLift 854826
  have htrace : WordTrace (prefixWord ++ tailWord_854826) baseStart_854826 baseEnd_854826 := by
    simpa [prefixWord, tailWord_854826, baseEnd_854826] using wordTrace_append hprefix tailTrace_854826
  have hstable : (prefixWord ++ tailWord_854826).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854826).length < 2 ^ (prefixWord ++ tailWord_854826).sum := by decide
  have hdescent : baseEnd_854826 < baseStart_854826 := by decide
  rcases family_descends (prefixWord ++ tailWord_854826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854857 : List Nat := [1, 2, 1, 1, 2, 6, 3, 2, 2]
def baseStart_854857 : Nat := 118140960795 + 854857 * 2 ^ 59
def prefixEnd_854857 : Nat := 4983230072969 + 3 ^ 40 * 854857 * 2
def baseEnd_854857 : Nat := 390180028320592979338747

theorem tailTrace_854857 : CollatzResearch.WordTrace tailWord_854857 prefixEnd_854857 390180028320592979338747 := by
  unfold tailWord_854857
  simp only [CollatzResearch.WordTrace]
  refine ⟨31179196264006561797218825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20786130842671041198145883 31179196264006561797218825)
  ·
    refine ⟨23384397198004921347914119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31179196264006561797218825 23384397198004921347914119)
    ·
      refine ⟨35076595797007382021871179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23384397198004921347914119 35076595797007382021871179)
      ·
        refine ⟨52614893695511073032806769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35076595797007382021871179 52614893695511073032806769)
        ·
          refine ⟨39461170271633304774605077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52614893695511073032806769 39461170271633304774605077)
          ·
            refine ⟨1849742356482811161309613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 39461170271633304774605077 1849742356482811161309613)
            ·
              refine ⟨693653383681054185491105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1849742356482811161309613 693653383681054185491105)
              ·
                refine ⟨520240037760790639118329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 693653383681054185491105 520240037760790639118329)
                ·
                  refine ⟨390180028320592979338747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 520240037760790639118329 390180028320592979338747)
                  ·
                    rfl

theorem cell20_854857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 3, 2, 2].length) (baseStart_854857 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_854857 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_854857 prefixEnd_854857 := by exact prefixLift 854857
  have htrace : WordTrace (prefixWord ++ tailWord_854857) baseStart_854857 baseEnd_854857 := by
    simpa [prefixWord, tailWord_854857, baseEnd_854857] using wordTrace_append hprefix tailTrace_854857
  have hstable : (prefixWord ++ tailWord_854857).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854857).length < 2 ^ (prefixWord ++ tailWord_854857).sum := by decide
  have hdescent : baseEnd_854857 < baseStart_854857 := by decide
  rcases family_descends (prefixWord ++ tailWord_854857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854871 : List Nat := [1, 1, 3, 2, 4, 1, 4, 1, 3]
def baseStart_854871 : Nat := 118140960795 + 854871 * 2 ^ 59
def prefixEnd_854871 : Nat := 4983230072969 + 3 ^ 40 * 854871 * 2
def baseEnd_854871 : Nat := 390186418302071152872023

theorem tailTrace_854871 : CollatzResearch.WordTrace tailWord_854871 prefixEnd_854871 390186418302071152872023 := by
  unfold tailWord_854871
  simp only [CollatzResearch.WordTrace]
  refine ⟨31179706885955842188228467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20786471257303894792152311 31179706885955842188228467)
  ·
    refine ⟨46769560328933763282342701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31179706885955842188228467 46769560328933763282342701)
    ·
      refine ⟨17538585123350161230878513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46769560328933763282342701 17538585123350161230878513)
      ·
        refine ⟨13153938842512620923158885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17538585123350161230878513 13153938842512620923158885)
        ·
          refine ⟨2466363532971116423092291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13153938842512620923158885 2466363532971116423092291)
          ·
            refine ⟨3699545299456674634638437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2466363532971116423092291 3699545299456674634638437)
            ·
              refine ⟨693664743648126493994707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3699545299456674634638437 693664743648126493994707)
              ·
                refine ⟨1040497115472189740992061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 693664743648126493994707 1040497115472189740992061)
                ·
                  refine ⟨390186418302071152872023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1040497115472189740992061 390186418302071152872023)
                  ·
                    rfl

theorem cell20_854871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 4, 1, 3].length) (baseStart_854871 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_854871 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_854871 prefixEnd_854871 := by exact prefixLift 854871
  have htrace : WordTrace (prefixWord ++ tailWord_854871) baseStart_854871 baseEnd_854871 := by
    simpa [prefixWord, tailWord_854871, baseEnd_854871] using wordTrace_append hprefix tailTrace_854871
  have hstable : (prefixWord ++ tailWord_854871).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854871).length < 2 ^ (prefixWord ++ tailWord_854871).sum := by decide
  have hdescent : baseEnd_854871 < baseStart_854871 := by decide
  rcases family_descends (prefixWord ++ tailWord_854871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854940 : List Nat := [2, 2, 3, 3, 2, 1, 3, 4]
def baseStart_854940 : Nat := 118140960795 + 854940 * 2 ^ 59
def prefixEnd_854940 : Nat := 4983230072969 + 3 ^ 40 * 854940 * 2
def baseEnd_854940 : Nat := 130072637260737859857247

theorem tailTrace_854940 : CollatzResearch.WordTrace tailWord_854940 prefixEnd_854940 130072637260737859857247 := by
  unfold tailWord_854940
  simp only [CollatzResearch.WordTrace]
  refine ⟨15591111761352933486245137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20788149015137244648326849 15591111761352933486245137)
  ·
    refine ⟨11693333821014700114683853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15591111761352933486245137 11693333821014700114683853)
    ·
      refine ⟨4385000182880512543006445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11693333821014700114683853 4385000182880512543006445)
      ·
        refine ⟨1644375068580192203627417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4385000182880512543006445 1644375068580192203627417)
        ·
          refine ⟨1233281301435144152720563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1644375068580192203627417 1233281301435144152720563)
          ·
            refine ⟨1849921952152716229080845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1233281301435144152720563 1849921952152716229080845)
            ·
              refine ⟨693720732057268585905317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1849921952152716229080845 693720732057268585905317)
              ·
                refine ⟨130072637260737859857247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 693720732057268585905317 130072637260737859857247)
                ·
                  rfl

theorem cell20_854940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 3, 4].length) (baseStart_854940 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_854940 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_854940 prefixEnd_854940 := by exact prefixLift 854940
  have htrace : WordTrace (prefixWord ++ tailWord_854940) baseStart_854940 baseEnd_854940 := by
    simpa [prefixWord, tailWord_854940, baseEnd_854940] using wordTrace_append hprefix tailTrace_854940
  have hstable : (prefixWord ++ tailWord_854940).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854940).length < 2 ^ (prefixWord ++ tailWord_854940).sum := by decide
  have hdescent : baseEnd_854940 < baseStart_854940 := by decide
  rcases family_descends (prefixWord ++ tailWord_854940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854964 : List Nat := [2, 5, 2, 1, 1, 1, 3, 2, 3]
def baseStart_854964 : Nat := 118140960795 + 854964 * 2 ^ 59
def prefixEnd_854964 : Nat := 4983230072969 + 3 ^ 40 * 854964 * 2
def baseEnd_854964 : Nat := 390228866036176162771643

theorem tailTrace_854964 : CollatzResearch.WordTrace tailWord_854964 prefixEnd_854964 390228866036176162771643 := by
  unfold tailWord_854964
  simp only [CollatzResearch.WordTrace]
  refine ⟨15591549437309459535681973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20788732583079279380909297 15591549437309459535681973)
  ·
    refine ⟨1461707759747761831470185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15591549437309459535681973 1461707759747761831470185)
    ·
      refine ⟨1096280819810821373602639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1461707759747761831470185 1096280819810821373602639)
      ·
        refine ⟨1644421229716232060403959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1096280819810821373602639 1644421229716232060403959)
        ·
          refine ⟨2466631844574348090605939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1644421229716232060403959 2466631844574348090605939)
          ·
            refine ⟨3699947766861522135908909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2466631844574348090605939 3699947766861522135908909)
            ·
              refine ⟨1387480412573070800965841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3699947766861522135908909 1387480412573070800965841)
              ·
                refine ⟨1040610309429803100724381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1387480412573070800965841 1040610309429803100724381)
                ·
                  refine ⟨390228866036176162771643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1040610309429803100724381 390228866036176162771643)
                  ·
                    rfl

theorem cell20_854964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_854964 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_854964 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_854964 prefixEnd_854964 := by exact prefixLift 854964
  have htrace : WordTrace (prefixWord ++ tailWord_854964) baseStart_854964 baseEnd_854964 := by
    simpa [prefixWord, tailWord_854964, baseEnd_854964] using wordTrace_append hprefix tailTrace_854964
  have hstable : (prefixWord ++ tailWord_854964).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854964).length < 2 ^ (prefixWord ++ tailWord_854964).sum := by decide
  have hdescent : baseEnd_854964 < baseStart_854964 := by decide
  rcases family_descends (prefixWord ++ tailWord_854964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_854968 : List Nat := [2, 1, 2, 1, 2, 4, 3, 2, 3]
def baseStart_854968 : Nat := 118140960795 + 854968 * 2 ^ 59
def prefixEnd_854968 : Nat := 4983230072969 + 3 ^ 40 * 854968 * 2
def baseEnd_854968 : Nat := 390230691745169926638293

theorem tailTrace_854968 : CollatzResearch.WordTrace tailWord_854968 prefixEnd_854968 390230691745169926638293 := by
  unfold tailWord_854968
  simp only [CollatzResearch.WordTrace]
  refine ⟨15591622383302213877254779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20788829844402951836339705 15591622383302213877254779)
  ·
    refine ⟨23387433574953320815882169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15591622383302213877254779 23387433574953320815882169)
    ·
      refine ⟨17540575181214990611911627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23387433574953320815882169 17540575181214990611911627)
      ·
        refine ⟨26310862771822485917867441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17540575181214990611911627 26310862771822485917867441)
        ·
          refine ⟨19733147078866864438400581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26310862771822485917867441 19733147078866864438400581)
          ·
            refine ⟨3699965077287537082200109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19733147078866864438400581 3699965077287537082200109)
            ·
              refine ⟨1387486903982826405825041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3699965077287537082200109 1387486903982826405825041)
              ·
                refine ⟨1040615177987119804368781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1387486903982826405825041 1040615177987119804368781)
                ·
                  refine ⟨390230691745169926638293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1040615177987119804368781 390230691745169926638293)
                  ·
                    rfl

theorem cell20_854968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 3, 2, 3].length) (baseStart_854968 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_854968 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_854968 prefixEnd_854968 := by exact prefixLift 854968
  have htrace : WordTrace (prefixWord ++ tailWord_854968) baseStart_854968 baseEnd_854968 := by
    simpa [prefixWord, tailWord_854968, baseEnd_854968] using wordTrace_append hprefix tailTrace_854968
  have hstable : (prefixWord ++ tailWord_854968).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_854968).length < 2 ^ (prefixWord ++ tailWord_854968).sum := by decide
  have hdescent : baseEnd_854968 < baseStart_854968 := by decide
  rcases family_descends (prefixWord ++ tailWord_854968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855026 : List Nat := [3, 2, 1, 5, 2, 1, 1, 1, 4]
def baseStart_855026 : Nat := 118140960795 + 855026 * 2 ^ 59
def prefixEnd_855026 : Nat := 4983230072969 + 3 ^ 40 * 855026 * 2
def baseEnd_855026 : Nat := 390257164525579502704723

theorem tailTrace_855026 : CollatzResearch.WordTrace tailWord_855026 prefixEnd_855026 390257164525579502704723 := by
  unfold tailWord_855026
  simp only [CollatzResearch.WordTrace]
  refine ⟨7796340050098575915030233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20790240133596202440080621 7796340050098575915030233)
  ·
    refine ⟨5847255037573931936272675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7796340050098575915030233 5847255037573931936272675)
    ·
      refine ⟨8770882556360897904409013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5847255037573931936272675 8770882556360897904409013)
      ·
        refine ⟨822270239658834178538345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8770882556360897904409013 822270239658834178538345)
        ·
          refine ⟨616702679744125633903759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 822270239658834178538345 616702679744125633903759)
          ·
            refine ⟨925054019616188450855639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 616702679744125633903759 925054019616188450855639)
            ·
              refine ⟨1387581029424282676283459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 925054019616188450855639 1387581029424282676283459)
              ·
                refine ⟨2081371544136424014425189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1387581029424282676283459 2081371544136424014425189)
                ·
                  refine ⟨390257164525579502704723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2081371544136424014425189 390257164525579502704723)
                  ·
                    rfl

theorem cell20_855026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 1, 1, 4].length) (baseStart_855026 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_855026 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_855026 prefixEnd_855026 := by exact prefixLift 855026
  have htrace : WordTrace (prefixWord ++ tailWord_855026) baseStart_855026 baseEnd_855026 := by
    simpa [prefixWord, tailWord_855026, baseEnd_855026] using wordTrace_append hprefix tailTrace_855026
  have hstable : (prefixWord ++ tailWord_855026).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855026).length < 2 ^ (prefixWord ++ tailWord_855026).sum := by decide
  have hdescent : baseEnd_855026 < baseStart_855026 := by decide
  rcases family_descends (prefixWord ++ tailWord_855026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855030 : List Nat := [5, 1, 1, 1, 3, 1, 3, 1, 4]
def baseStart_855030 : Nat := 118140960795 + 855030 * 2 ^ 59
def prefixEnd_855030 : Nat := 4983230072969 + 3 ^ 40 * 855030 * 2
def baseEnd_855030 : Nat := 390258990234573266571373

theorem tailTrace_855030 : CollatzResearch.WordTrace tailWord_855030 prefixEnd_855030 390258990234573266571373 := by
  unfold tailWord_855030
  simp only [CollatzResearch.WordTrace]
  refine ⟨1949094130773738271454159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20790337394919874895511029 1949094130773738271454159)
  ·
    refine ⟨2923641196160607407181239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1949094130773738271454159 2923641196160607407181239)
    ·
      refine ⟨4385461794240911110771859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2923641196160607407181239 4385461794240911110771859)
      ·
        refine ⟨6578192691361366666157789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4385461794240911110771859 6578192691361366666157789)
        ·
          refine ⟨2466822259260512499809171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6578192691361366666157789 2466822259260512499809171)
          ·
            refine ⟨3700233388890768749713757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2466822259260512499809171 3700233388890768749713757)
            ·
              refine ⟨1387587520834038281142659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3700233388890768749713757 1387587520834038281142659)
              ·
                refine ⟨2081381281251057421713989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1387587520834038281142659 2081381281251057421713989)
                ·
                  refine ⟨390258990234573266571373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2081381281251057421713989 390258990234573266571373)
                  ·
                    rfl

theorem cell20_855030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_855030 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_855030 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_855030 prefixEnd_855030 := by exact prefixLift 855030
  have htrace : WordTrace (prefixWord ++ tailWord_855030) baseStart_855030 baseEnd_855030 := by
    simpa [prefixWord, tailWord_855030, baseEnd_855030] using wordTrace_append hprefix tailTrace_855030
  have hstable : (prefixWord ++ tailWord_855030).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855030).length < 2 ^ (prefixWord ++ tailWord_855030).sum := by decide
  have hdescent : baseEnd_855030 < baseStart_855030 := by decide
  rcases family_descends (prefixWord ++ tailWord_855030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855092 : List Nat := [2, 5, 1, 2, 1, 3, 1, 5]
def baseStart_855092 : Nat := 118140960795 + 855092 * 2 ^ 59
def prefixEnd_855092 : Nat := 4983230072969 + 3 ^ 40 * 855092 * 2
def baseEnd_855092 : Nat := 130095762907992202168151

theorem tailTrace_855092 : CollatzResearch.WordTrace tailWord_855092 prefixEnd_855092 130095762907992202168151 := by
  unfold tailWord_855092
  simp only [CollatzResearch.WordTrace]
  refine ⟨15593883709077598466011765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20791844945436797954682353 15593883709077598466011765)
  ·
    refine ⟨1461926597726024856188603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15593883709077598466011765 1461926597726024856188603)
    ·
      refine ⟨2192889896589037284282905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1461926597726024856188603 2192889896589037284282905)
      ·
        refine ⟨1644667422441777963212179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2192889896589037284282905 1644667422441777963212179)
        ·
          refine ⟨2467001133662666944818269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1644667422441777963212179 2467001133662666944818269)
          ·
            refine ⟨925125425123500104306851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2467001133662666944818269 925125425123500104306851)
            ·
              refine ⟨1387688137685250156460277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 925125425123500104306851 1387688137685250156460277)
              ·
                refine ⟨130095762907992202168151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1387688137685250156460277 130095762907992202168151)
                ·
                  rfl

theorem cell20_855092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 1, 5].length) (baseStart_855092 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_855092 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_855092 prefixEnd_855092 := by exact prefixLift 855092
  have htrace : WordTrace (prefixWord ++ tailWord_855092) baseStart_855092 baseEnd_855092 := by
    simpa [prefixWord, tailWord_855092, baseEnd_855092] using wordTrace_append hprefix tailTrace_855092
  have hstable : (prefixWord ++ tailWord_855092).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855092).length < 2 ^ (prefixWord ++ tailWord_855092).sum := by decide
  have hdescent : baseEnd_855092 < baseStart_855092 := by decide
  rcases family_descends (prefixWord ++ tailWord_855092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855096 : List Nat := [2, 1, 2, 1, 5, 1, 3, 5]
def baseStart_855096 : Nat := 118140960795 + 855096 * 2 ^ 59
def prefixEnd_855096 : Nat := 4983230072969 + 3 ^ 40 * 855096 * 2
def baseEnd_855096 : Nat := 130096371477656790123701

theorem tailTrace_855096 : CollatzResearch.WordTrace tailWord_855096 prefixEnd_855096 130096371477656790123701 := by
  unfold tailWord_855096
  simp only [CollatzResearch.WordTrace]
  refine ⟨15593956655070352807584571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20791942206760470410112761 15593956655070352807584571)
  ·
    refine ⟨23390934982605529211376857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15593956655070352807584571 23390934982605529211376857)
    ·
      refine ⟨17543201236954146908532643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23390934982605529211376857 17543201236954146908532643)
      ·
        refine ⟨26314801855431220362798965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17543201236954146908532643 26314801855431220362798965)
        ·
          refine ⟨2467012673946676909012403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26314801855431220362798965 2467012673946676909012403)
          ·
            refine ⟨3700519010920015363518605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2467012673946676909012403 3700519010920015363518605)
            ·
              refine ⟨1387694629095005761319477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3700519010920015363518605 1387694629095005761319477)
              ·
                refine ⟨130096371477656790123701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1387694629095005761319477 130096371477656790123701)
                ·
                  rfl

theorem cell20_855096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 3, 5].length) (baseStart_855096 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_855096 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_855096 prefixEnd_855096 := by exact prefixLift 855096
  have htrace : WordTrace (prefixWord ++ tailWord_855096) baseStart_855096 baseEnd_855096 := by
    simpa [prefixWord, tailWord_855096, baseEnd_855096] using wordTrace_append hprefix tailTrace_855096
  have hstable : (prefixWord ++ tailWord_855096).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855096).length < 2 ^ (prefixWord ++ tailWord_855096).sum := by decide
  have hdescent : baseEnd_855096 < baseStart_855096 := by decide
  rcases family_descends (prefixWord ++ tailWord_855096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855133 : List Nat := [1, 4, 4, 1, 3, 1, 1, 2, 3]
def baseStart_855133 : Nat := 118140960795 + 855133 * 2 ^ 59
def prefixEnd_855133 : Nat := 4983230072969 + 3 ^ 40 * 855133 * 2
def baseEnd_855133 : Nat := 390306002241162686137619

theorem tailTrace_855133 : CollatzResearch.WordTrace tailWord_855133 prefixEnd_855133 390306002241162686137619 := by
  unfold tailWord_855133
  simp only [CollatzResearch.WordTrace]
  refine ⟨31189262811006660934266053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20792841874004440622844035 31189262811006660934266053)
  ·
    refine ⟨5847986777063748925174885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31189262811006660934266053 5847986777063748925174885)
    ·
      refine ⟨1096497520699452923470291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5847986777063748925174885 1096497520699452923470291)
      ·
        refine ⟨1644746281049179385205437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1096497520699452923470291 1644746281049179385205437)
        ·
          refine ⟨616779855393442269452039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1644746281049179385205437 616779855393442269452039)
          ·
            refine ⟨925169783090163404178059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 616779855393442269452039 925169783090163404178059)
            ·
              refine ⟨1387754674635245106267089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 925169783090163404178059 1387754674635245106267089)
              ·
                refine ⟨1040816005976433829700317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1387754674635245106267089 1040816005976433829700317)
                ·
                  refine ⟨390306002241162686137619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1040816005976433829700317 390306002241162686137619)
                  ·
                    rfl

theorem cell20_855133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 1, 2, 3].length) (baseStart_855133 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_855133 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_855133 prefixEnd_855133 := by exact prefixLift 855133
  have htrace : WordTrace (prefixWord ++ tailWord_855133) baseStart_855133 baseEnd_855133 := by
    simpa [prefixWord, tailWord_855133, baseEnd_855133] using wordTrace_append hprefix tailTrace_855133
  have hstable : (prefixWord ++ tailWord_855133).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855133).length < 2 ^ (prefixWord ++ tailWord_855133).sum := by decide
  have hdescent : baseEnd_855133 < baseStart_855133 := by decide
  rcases family_descends (prefixWord ++ tailWord_855133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855141 : List Nat := [1, 3, 1, 3, 2, 1, 3, 1, 5]
def baseStart_855141 : Nat := 118140960795 + 855141 * 2 ^ 59
def prefixEnd_855141 : Nat := 4983230072969 + 3 ^ 40 * 855141 * 2
def baseEnd_855141 : Nat := 390309653659150213870919

theorem tailTrace_855141 : CollatzResearch.WordTrace tailWord_855141 prefixEnd_855141 390309653659150213870919 := by
  unfold tailWord_855141
  simp only [CollatzResearch.WordTrace]
  refine ⟨31189554594977678300557277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20793036396651785533704851 31189554594977678300557277)
  ·
    refine ⟨11696082973116629362708979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31189554594977678300557277 11696082973116629362708979)
    ·
      refine ⟨17544124459674944044063469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11696082973116629362708979 17544124459674944044063469)
      ·
        refine ⟨6579046672378104016523801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17544124459674944044063469 6579046672378104016523801)
        ·
          refine ⟨4934285004283578012392851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6579046672378104016523801 4934285004283578012392851)
          ·
            refine ⟨7401427506425367018589277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4934285004283578012392851 7401427506425367018589277)
            ·
              refine ⟨2775535314909512631970979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7401427506425367018589277 2775535314909512631970979)
              ·
                refine ⟨4163302972364268947956469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2775535314909512631970979 4163302972364268947956469)
                ·
                  refine ⟨390309653659150213870919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4163302972364268947956469 390309653659150213870919)
                  ·
                    rfl

theorem cell20_855141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 1, 5].length) (baseStart_855141 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_855141 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_855141 prefixEnd_855141 := by exact prefixLift 855141
  have htrace : WordTrace (prefixWord ++ tailWord_855141) baseStart_855141 baseEnd_855141 := by
    simpa [prefixWord, tailWord_855141, baseEnd_855141] using wordTrace_append hprefix tailTrace_855141
  have hstable : (prefixWord ++ tailWord_855141).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855141).length < 2 ^ (prefixWord ++ tailWord_855141).sum := by decide
  have hdescent : baseEnd_855141 < baseStart_855141 := by decide
  rcases family_descends (prefixWord ++ tailWord_855141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855172 : List Nat := [2, 3, 2, 1, 2, 3, 1, 6]
def baseStart_855172 : Nat := 118140960795 + 855172 * 2 ^ 59
def prefixEnd_855172 : Nat := 4983230072969 + 3 ^ 40 * 855172 * 2
def baseEnd_855172 : Nat := 130107934301283961279153

theorem tailTrace_855172 : CollatzResearch.WordTrace tailWord_855172 prefixEnd_855172 130107934301283961279153 := by
  unfold tailWord_855172
  simp only [CollatzResearch.WordTrace]
  refine ⟨15595342628932685297467885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20793790171910247063290513 15595342628932685297467885)
  ·
    refine ⟨5848253485849756986550457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15595342628932685297467885 5848253485849756986550457)
    ·
      refine ⟨4386190114387317739912843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5848253485849756986550457 4386190114387317739912843)
      ·
        refine ⟨6579285171580976609869265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4386190114387317739912843 6579285171580976609869265)
        ·
          refine ⟨4934463878685732457401949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6579285171580976609869265 4934463878685732457401949)
          ·
            refine ⟨1850423954507149671525731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4934463878685732457401949 1850423954507149671525731)
            ·
              refine ⟨2775635931760724507288597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1850423954507149671525731 2775635931760724507288597)
              ·
                refine ⟨130107934301283961279153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2775635931760724507288597 130107934301283961279153)
                ·
                  rfl

theorem cell20_855172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 6].length) (baseStart_855172 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_855172 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_855172 prefixEnd_855172 := by exact prefixLift 855172
  have htrace : WordTrace (prefixWord ++ tailWord_855172) baseStart_855172 baseEnd_855172 := by
    simpa [prefixWord, tailWord_855172, baseEnd_855172] using wordTrace_append hprefix tailTrace_855172
  have hstable : (prefixWord ++ tailWord_855172).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855172).length < 2 ^ (prefixWord ++ tailWord_855172).sum := by decide
  have hdescent : baseEnd_855172 < baseStart_855172 := by decide
  rcases family_descends (prefixWord ++ tailWord_855172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855199 : List Nat := [1, 1, 2, 6, 3, 1, 1, 1, 4]
def baseStart_855199 : Nat := 118140960795 + 855199 * 2 ^ 59
def prefixEnd_855199 : Nat := 4983230072969 + 3 ^ 40 * 855199 * 2
def baseEnd_855199 : Nat := 390336126439559789937349

theorem tailTrace_855199 : CollatzResearch.WordTrace tailWord_855199 prefixEnd_855199 390336126439559789937349 := by
  unfold tailWord_855199
  simp only [CollatzResearch.WordTrace]
  refine ⟨31191670028767554206168651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20794446685845036137445767 31191670028767554206168651)
  ·
    refine ⟨46787505043151331309252977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31191670028767554206168651 46787505043151331309252977)
    ·
      refine ⟨35090628782363498481939733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46787505043151331309252977 35090628782363498481939733)
      ·
        refine ⟨1644873224173288991340925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 35090628782363498481939733 1644873224173288991340925)
        ·
          refine ⟨616827459064983371752847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1644873224173288991340925 616827459064983371752847)
          ·
            refine ⟨925241188597475057629271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 616827459064983371752847 925241188597475057629271)
            ·
              refine ⟨1387861782896212586443907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 925241188597475057629271 1387861782896212586443907)
              ·
                refine ⟨2081792674344318879665861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1387861782896212586443907 2081792674344318879665861)
                ·
                  refine ⟨390336126439559789937349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2081792674344318879665861 390336126439559789937349)
                  ·
                    rfl

theorem cell20_855199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 1, 1, 4].length) (baseStart_855199 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_855199 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_855199 prefixEnd_855199 := by exact prefixLift 855199
  have htrace : WordTrace (prefixWord ++ tailWord_855199) baseStart_855199 baseEnd_855199 := by
    simpa [prefixWord, tailWord_855199, baseEnd_855199] using wordTrace_append hprefix tailTrace_855199
  have hstable : (prefixWord ++ tailWord_855199).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855199).length < 2 ^ (prefixWord ++ tailWord_855199).sum := by decide
  have hdescent : baseEnd_855199 < baseStart_855199 := by decide
  rcases family_descends (prefixWord ++ tailWord_855199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855203 : List Nat := [1, 1, 1, 4, 1, 1, 1, 8, 2]
def baseStart_855203 : Nat := 118140960795 + 855203 * 2 ^ 59
def prefixEnd_855203 : Nat := 4983230072969 + 3 ^ 40 * 855203 * 2
def baseEnd_855203 : Nat := 390337952148553553803999

theorem tailTrace_855203 : CollatzResearch.WordTrace tailWord_855203 prefixEnd_855203 390337952148553553803999 := by
  unfold tailWord_855203
  simp only [CollatzResearch.WordTrace]
  refine ⟨31191815920753062889314263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20794543947168708592876175 31191815920753062889314263)
  ·
    refine ⟨46787723881129594333971395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31191815920753062889314263 46787723881129594333971395)
    ·
      refine ⟨70181585821694391500957093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46787723881129594333971395 70181585821694391500957093)
      ·
        refine ⟨13159047341567698406429455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70181585821694391500957093 13159047341567698406429455)
        ·
          refine ⟨19738571012351547609644183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13159047341567698406429455 19738571012351547609644183)
          ·
            refine ⟨29607856518527321414466275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19738571012351547609644183 29607856518527321414466275)
            ·
              refine ⟨44411784777790982121699413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29607856518527321414466275 44411784777790982121699413)
              ·
                refine ⟨520450602864738071738665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 44411784777790982121699413 520450602864738071738665)
                ·
                  refine ⟨390337952148553553803999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 520450602864738071738665 390337952148553553803999)
                  ·
                    rfl

theorem cell20_855203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 8, 2].length) (baseStart_855203 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_855203 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_855203 prefixEnd_855203 := by exact prefixLift 855203
  have htrace : WordTrace (prefixWord ++ tailWord_855203) baseStart_855203 baseEnd_855203 := by
    simpa [prefixWord, tailWord_855203, baseEnd_855203] using wordTrace_append hprefix tailTrace_855203
  have hstable : (prefixWord ++ tailWord_855203).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855203).length < 2 ^ (prefixWord ++ tailWord_855203).sum := by decide
  have hdescent : baseEnd_855203 < baseStart_855203 := by decide
  rcases family_descends (prefixWord ++ tailWord_855203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855213 : List Nat := [1, 5, 2, 1, 3, 1, 1, 3, 3]
def baseStart_855213 : Nat := 118140960795 + 855213 * 2 ^ 59
def prefixEnd_855213 : Nat := 4983230072969 + 3 ^ 40 * 855213 * 2
def baseEnd_855213 : Nat := 390342516421037963470625

theorem tailTrace_855213 : CollatzResearch.WordTrace tailWord_855213 prefixEnd_855213 390342516421037963470625 := by
  unfold tailWord_855213
  simp only [CollatzResearch.WordTrace]
  refine ⟨31192180650716834597178293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20794787100477889731452195 31192180650716834597178293)
  ·
    refine ⟨2924266936004703243485465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31192180650716834597178293 2924266936004703243485465)
    ·
      refine ⟨2193200202003527432614099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2924266936004703243485465 2193200202003527432614099)
      ·
        refine ⟨3289800303005291148921149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2193200202003527432614099 3289800303005291148921149)
        ·
          refine ⟨1233675113626984180845431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3289800303005291148921149 1233675113626984180845431)
          ·
            refine ⟨1850512670440476271268147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1233675113626984180845431 1850512670440476271268147)
            ·
              refine ⟨2775769005660714406902221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1850512670440476271268147 2775769005660714406902221)
              ·
                refine ⟨1040913377122767902588333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2775769005660714406902221 1040913377122767902588333)
                ·
                  refine ⟨390342516421037963470625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1040913377122767902588333 390342516421037963470625)
                  ·
                    rfl

theorem cell20_855213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 3, 3].length) (baseStart_855213 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_855213 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_855213 prefixEnd_855213 := by exact prefixLift 855213
  have htrace : WordTrace (prefixWord ++ tailWord_855213) baseStart_855213 baseEnd_855213 := by
    simpa [prefixWord, tailWord_855213, baseEnd_855213] using wordTrace_append hprefix tailTrace_855213
  have hstable : (prefixWord ++ tailWord_855213).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855213).length < 2 ^ (prefixWord ++ tailWord_855213).sum := by decide
  have hdescent : baseEnd_855213 < baseStart_855213 := by decide
  rcases family_descends (prefixWord ++ tailWord_855213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855231 : List Nat := [1, 1, 2, 2, 2, 2, 4, 6]
def baseStart_855231 : Nat := 118140960795 + 855231 * 2 ^ 59
def prefixEnd_855231 : Nat := 4983230072969 + 3 ^ 40 * 855231 * 2
def baseEnd_855231 : Nat := 130116910703836633623517

theorem tailTrace_855231 : CollatzResearch.WordTrace tailWord_855231 prefixEnd_855231 130116910703836633623517 := by
  unfold tailWord_855231
  simp only [CollatzResearch.WordTrace]
  refine ⟨31192837164651623671333547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20795224776434415780889031 31192837164651623671333547)
  ·
    refine ⟨46789255746977435507000321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31192837164651623671333547 46789255746977435507000321)
    ·
      refine ⟨35091941810233076630250241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46789255746977435507000321 35091941810233076630250241)
      ·
        refine ⟨26318956357674807472687681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35091941810233076630250241 26318956357674807472687681)
        ·
          refine ⟨19739217268256105604515761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26318956357674807472687681 19739217268256105604515761)
          ·
            refine ⟨14804412951192079203386821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19739217268256105604515761 14804412951192079203386821)
            ·
              refine ⟨2775827428348514850635029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14804412951192079203386821 2775827428348514850635029)
              ·
                refine ⟨130116910703836633623517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2775827428348514850635029 130116910703836633623517)
                ·
                  rfl

theorem cell20_855231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 6].length) (baseStart_855231 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_855231 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_855231 prefixEnd_855231 := by exact prefixLift 855231
  have htrace : WordTrace (prefixWord ++ tailWord_855231) baseStart_855231 baseEnd_855231 := by
    simpa [prefixWord, tailWord_855231, baseEnd_855231] using wordTrace_append hprefix tailTrace_855231
  have hstable : (prefixWord ++ tailWord_855231).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855231).length < 2 ^ (prefixWord ++ tailWord_855231).sum := by decide
  have hdescent : baseEnd_855231 < baseStart_855231 := by decide
  rcases family_descends (prefixWord ++ tailWord_855231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855254 : List Nat := [5, 2, 1, 2, 2, 1, 1, 4, 2]
def baseStart_855254 : Nat := 118140960795 + 855254 * 2 ^ 59
def prefixEnd_855254 : Nat := 4983230072969 + 3 ^ 40 * 855254 * 2
def baseEnd_855254 : Nat := 390361229938224043103791

theorem tailTrace_855254 : CollatzResearch.WordTrace tailWord_855254 prefixEnd_855254 390361229938224043103791 := by
  unfold tailWord_855254
  simp only [CollatzResearch.WordTrace]
  refine ⟨1949604752723018662463801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20795784029045532399613877 1949604752723018662463801)
  ·
    refine ⟨1462203564542263996847851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1949604752723018662463801 1462203564542263996847851)
    ·
      refine ⟨2193305346813395995271777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1462203564542263996847851 2193305346813395995271777)
      ·
        refine ⟨1644979010110046996453833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2193305346813395995271777 1644979010110046996453833)
        ·
          refine ⟨1233734257582535247340375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1644979010110046996453833 1233734257582535247340375)
          ·
            refine ⟨1850601386373802871010563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1233734257582535247340375 1850601386373802871010563)
            ·
              refine ⟨2775902079560704306515845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1850601386373802871010563 2775902079560704306515845)
              ·
                refine ⟨520481639917632057471721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2775902079560704306515845 520481639917632057471721)
                ·
                  refine ⟨390361229938224043103791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 520481639917632057471721 390361229938224043103791)
                  ·
                    rfl

theorem cell20_855254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 4, 2].length) (baseStart_855254 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_855254 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_855254 prefixEnd_855254 := by exact prefixLift 855254
  have htrace : WordTrace (prefixWord ++ tailWord_855254) baseStart_855254 baseEnd_855254 := by
    simpa [prefixWord, tailWord_855254, baseEnd_855254] using wordTrace_append hprefix tailTrace_855254
  have hstable : (prefixWord ++ tailWord_855254).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855254).length < 2 ^ (prefixWord ++ tailWord_855254).sum := by decide
  have hdescent : baseEnd_855254 < baseStart_855254 := by decide
  rcases family_descends (prefixWord ++ tailWord_855254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855255 : List Nat := [1, 1, 3, 2, 1, 2, 3, 4, 3]
def baseStart_855255 : Nat := 118140960795 + 855255 * 2 ^ 59
def prefixEnd_855255 : Nat := 4983230072969 + 3 ^ 40 * 855255 * 2
def baseEnd_855255 : Nat := 390361686365472484070453

theorem tailTrace_855255 : CollatzResearch.WordTrace tailWord_855255 prefixEnd_855255 390361686365472484070453 := by
  unfold tailWord_855255
  simp only [CollatzResearch.WordTrace]
  refine ⟨31193712516564675770207219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20795808344376450513471479 31193712516564675770207219)
  ·
    refine ⟨46790568774847013655310829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31193712516564675770207219 46790568774847013655310829)
    ·
      refine ⟨17546463290567630120741561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46790568774847013655310829 17546463290567630120741561)
      ·
        refine ⟨13159847467925722590556171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17546463290567630120741561 13159847467925722590556171)
        ·
          refine ⟨19739771201888583885834257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13159847467925722590556171 19739771201888583885834257)
          ·
            refine ⟨14804828401416437914375693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19739771201888583885834257 14804828401416437914375693)
            ·
              refine ⟨5551810650531164217890885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14804828401416437914375693 5551810650531164217890885)
              ·
                refine ⟨1040964496974593290854541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5551810650531164217890885 1040964496974593290854541)
                ·
                  refine ⟨390361686365472484070453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1040964496974593290854541 390361686365472484070453)
                  ·
                    rfl

theorem cell20_855255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 4, 3].length) (baseStart_855255 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_855255 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_855255 prefixEnd_855255 := by exact prefixLift 855255
  have htrace : WordTrace (prefixWord ++ tailWord_855255) baseStart_855255 baseEnd_855255 := by
    simpa [prefixWord, tailWord_855255, baseEnd_855255] using wordTrace_append hprefix tailTrace_855255
  have hstable : (prefixWord ++ tailWord_855255).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855255).length < 2 ^ (prefixWord ++ tailWord_855255).sum := by decide
  have hdescent : baseEnd_855255 < baseStart_855255 := by decide
  rcases family_descends (prefixWord ++ tailWord_855255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855279 : List Nat := [1, 1, 2, 1, 7, 1, 1, 2, 4]
def baseStart_855279 : Nat := 118140960795 + 855279 * 2 ^ 59
def prefixEnd_855279 : Nat := 4983230072969 + 3 ^ 40 * 855279 * 2
def baseEnd_855279 : Nat := 390372640619435067270355

theorem tailTrace_855279 : CollatzResearch.WordTrace tailWord_855279 prefixEnd_855279 390372640619435067270355 := by
  unfold tailWord_855279
  simp only [CollatzResearch.WordTrace]
  refine ⟨31194587868477727869080891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20796391912318485246053927 31194587868477727869080891)
  ·
    refine ⟨46791881802716591803621337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31194587868477727869080891 46791881802716591803621337)
    ·
      refine ⟨35093911352037443852716003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46791881802716591803621337 35093911352037443852716003)
      ·
        refine ⟨52640867028056165779074005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35093911352037443852716003 52640867028056165779074005)
        ·
          refine ⟨1233770320970066385447047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 52640867028056165779074005 1233770320970066385447047)
          ·
            refine ⟨1850655481455099578170571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1233770320970066385447047 1850655481455099578170571)
            ·
              refine ⟨2775983222182649367255857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1850655481455099578170571 2775983222182649367255857)
              ·
                refine ⟨2081987416636987025441893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2775983222182649367255857 2081987416636987025441893)
                ·
                  refine ⟨390372640619435067270355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2081987416636987025441893 390372640619435067270355)
                  ·
                    rfl

theorem cell20_855279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 2, 4].length) (baseStart_855279 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_855279 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_855279 prefixEnd_855279 := by exact prefixLift 855279
  have htrace : WordTrace (prefixWord ++ tailWord_855279) baseStart_855279 baseEnd_855279 := by
    simpa [prefixWord, tailWord_855279, baseEnd_855279] using wordTrace_append hprefix tailTrace_855279
  have hstable : (prefixWord ++ tailWord_855279).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855279).length < 2 ^ (prefixWord ++ tailWord_855279).sum := by decide
  have hdescent : baseEnd_855279 < baseStart_855279 := by decide
  rcases family_descends (prefixWord ++ tailWord_855279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855307 : List Nat := [1, 1, 1, 1, 5, 4, 7]
def baseStart_855307 : Nat := 118140960795 + 855307 * 2 ^ 59
def prefixEnd_855307 : Nat := 4983230072969 + 3 ^ 40 * 855307 * 2
def baseEnd_855307 : Nat := 43376157842487934926323

theorem tailTrace_855307 : CollatzResearch.WordTrace tailWord_855307 prefixEnd_855307 43376157842487934926323 := by
  unfold tailWord_855307
  simp only [CollatzResearch.WordTrace]
  refine ⟨31195609112376288651100175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20797072741584192434066783 31195609112376288651100175)
  ·
    refine ⟨46793413668564432976650263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31195609112376288651100175 46793413668564432976650263)
    ·
      refine ⟨70190120502846649464975395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46793413668564432976650263 70190120502846649464975395)
      ·
        refine ⟨105285180754269974197463093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70190120502846649464975395 105285180754269974197463093)
        ·
          refine ⟨9870485695712810081012165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 105285180754269974197463093 9870485695712810081012165)
          ·
            refine ⟨1850716067946151890189781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9870485695712810081012165 1850716067946151890189781)
            ·
              refine ⟨43376157842487934926323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1850716067946151890189781 43376157842487934926323)
              ·
                rfl

theorem cell20_855307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 7].length) (baseStart_855307 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_855307 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_855307 prefixEnd_855307 := by exact prefixLift 855307
  have htrace : WordTrace (prefixWord ++ tailWord_855307) baseStart_855307 baseEnd_855307 := by
    simpa [prefixWord, tailWord_855307, baseEnd_855307] using wordTrace_append hprefix tailTrace_855307
  have hstable : (prefixWord ++ tailWord_855307).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855307).length < 2 ^ (prefixWord ++ tailWord_855307).sum := by decide
  have hdescent : baseEnd_855307 < baseStart_855307 := by decide
  rcases family_descends (prefixWord ++ tailWord_855307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855310 : List Nat := [4, 1, 1, 2, 1, 3, 3, 2, 3]
def baseStart_855310 : Nat := 118140960795 + 855310 * 2 ^ 59
def prefixEnd_855310 : Nat := 4983230072969 + 3 ^ 40 * 855310 * 2
def baseEnd_855310 : Nat := 390386789864136737236895

theorem tailTrace_855310 : CollatzResearch.WordTrace tailWord_855310 prefixEnd_855310 390386789864136737236895 := by
  unfold tailWord_855310
  simp only [CollatzResearch.WordTrace]
  refine ⟨3899464816420677520432423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20797145687576946775639589 3899464816420677520432423)
  ·
    refine ⟨5849197224631016280648635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3899464816420677520432423 5849197224631016280648635)
    ·
      refine ⟨8773795836946524420972953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5849197224631016280648635 8773795836946524420972953)
      ·
        refine ⟨6580346877709893315729715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8773795836946524420972953 6580346877709893315729715)
        ·
          refine ⟨9870520316564839973594573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6580346877709893315729715 9870520316564839973594573)
          ·
            refine ⟨3701445118711814990097965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9870520316564839973594573 3701445118711814990097965)
            ·
              refine ⟨1388041919516930621286737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3701445118711814990097965 1388041919516930621286737)
              ·
                refine ⟨1041031439637697965965053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1388041919516930621286737 1041031439637697965965053)
                ·
                  refine ⟨390386789864136737236895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1041031439637697965965053 390386789864136737236895)
                  ·
                    rfl

theorem cell20_855310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 3, 2, 3].length) (baseStart_855310 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_855310 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_855310 prefixEnd_855310 := by exact prefixLift 855310
  have htrace : WordTrace (prefixWord ++ tailWord_855310) baseStart_855310 baseEnd_855310 := by
    simpa [prefixWord, tailWord_855310, baseEnd_855310] using wordTrace_append hprefix tailTrace_855310
  have hstable : (prefixWord ++ tailWord_855310).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855310).length < 2 ^ (prefixWord ++ tailWord_855310).sum := by decide
  have hdescent : baseEnd_855310 < baseStart_855310 := by decide
  rcases family_descends (prefixWord ++ tailWord_855310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855327 : List Nat := [1, 1, 2, 4, 4, 1, 3, 1, 3]
def baseStart_855327 : Nat := 118140960795 + 855327 * 2 ^ 59
def prefixEnd_855327 : Nat := 4983230072969 + 3 ^ 40 * 855327 * 2
def baseEnd_855327 : Nat := 390394549127360233670159

theorem tailTrace_855327 : CollatzResearch.WordTrace tailWord_855327 prefixEnd_855327 390394549127360233670159 := by
  unfold tailWord_855327
  simp only [CollatzResearch.WordTrace]
  refine ⟨31196338572303832066828235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20797559048202554711218823 31196338572303832066828235)
  ·
    refine ⟨46794507858455748100242353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31196338572303832066828235 46794507858455748100242353)
    ·
      refine ⟨35095880893841811075181765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46794507858455748100242353 35095880893841811075181765)
      ·
        refine ⟨6580477667595339576596581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35095880893841811075181765 6580477667595339576596581)
        ·
          refine ⟨1233839562674126170611859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6580477667595339576596581 1233839562674126170611859)
          ·
            refine ⟨1850759344011189255917789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1233839562674126170611859 1850759344011189255917789)
            ·
              refine ⟨694034754004195970969171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1850759344011189255917789 694034754004195970969171)
              ·
                refine ⟨1041052131006293956453757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 694034754004195970969171 1041052131006293956453757)
                ·
                  refine ⟨390394549127360233670159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1041052131006293956453757 390394549127360233670159)
                  ·
                    rfl

theorem cell20_855327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 3, 1, 3].length) (baseStart_855327 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_855327 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_855327 prefixEnd_855327 := by exact prefixLift 855327
  have htrace : WordTrace (prefixWord ++ tailWord_855327) baseStart_855327 baseEnd_855327 := by
    simpa [prefixWord, tailWord_855327, baseEnd_855327] using wordTrace_append hprefix tailTrace_855327
  have hstable : (prefixWord ++ tailWord_855327).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855327).length < 2 ^ (prefixWord ++ tailWord_855327).sum := by decide
  have hdescent : baseEnd_855327 < baseStart_855327 := by decide
  rcases family_descends (prefixWord ++ tailWord_855327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855341 : List Nat := [1, 5, 3, 1, 1, 2, 1, 6]
def baseStart_855341 : Nat := 118140960795 + 855341 * 2 ^ 59
def prefixEnd_855341 : Nat := 4983230072969 + 3 ^ 40 * 855341 * 2
def baseEnd_855341 : Nat := 130133646369612802401145

theorem tailTrace_855341 : CollatzResearch.WordTrace tailWord_855341 prefixEnd_855341 130133646369612802401145 := by
  unfold tailWord_855341
  simp only [CollatzResearch.WordTrace]
  refine ⟨31196849194253112457837877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20797899462835408305225251 31196849194253112457837877)
  ·
    refine ⟨2924704611961229292922301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31196849194253112457837877 2924704611961229292922301)
    ·
      refine ⟨1096764229485460984845863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2924704611961229292922301 1096764229485460984845863)
      ·
        refine ⟨1645146344228191477268795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1096764229485460984845863 1645146344228191477268795)
        ·
          refine ⟨2467719516342287215903193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1645146344228191477268795 2467719516342287215903193)
          ·
            refine ⟨1850789637256715411927395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2467719516342287215903193 1850789637256715411927395)
            ·
              refine ⟨2776184455885073117891093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1850789637256715411927395 2776184455885073117891093)
              ·
                refine ⟨130133646369612802401145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2776184455885073117891093 130133646369612802401145)
                ·
                  rfl

theorem cell20_855341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 6].length) (baseStart_855341 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_855341 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_855341 prefixEnd_855341 := by exact prefixLift 855341
  have htrace : WordTrace (prefixWord ++ tailWord_855341) baseStart_855341 baseEnd_855341 := by
    simpa [prefixWord, tailWord_855341, baseEnd_855341] using wordTrace_append hprefix tailTrace_855341
  have hstable : (prefixWord ++ tailWord_855341).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855341).length < 2 ^ (prefixWord ++ tailWord_855341).sum := by decide
  have hdescent : baseEnd_855341 < baseStart_855341 := by decide
  rcases family_descends (prefixWord ++ tailWord_855341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855383 : List Nat := [1, 1, 3, 2, 3, 2, 1, 7]
def baseStart_855383 : Nat := 118140960795 + 855383 * 2 ^ 59
def prefixEnd_855383 : Nat := 4983230072969 + 3 ^ 40 * 855383 * 2
def baseEnd_855383 : Nat := 130140036351090975934421

theorem tailTrace_855383 : CollatzResearch.WordTrace tailWord_855383 prefixEnd_855383 130140036351090975934421 := by
  unfold tailWord_855383
  simp only [CollatzResearch.WordTrace]
  refine ⟨31198381060100953630866803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20798920706733969087244535 31198381060100953630866803)
  ·
    refine ⟨46797571590151430446300205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31198381060100953630866803 46797571590151430446300205)
    ·
      refine ⟨17549089346306786417362577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46797571590151430446300205 17549089346306786417362577)
      ·
        refine ⟨13161817009730089813021933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17549089346306786417362577 13161817009730089813021933)
        ·
          refine ⟨4935681378648783679883225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13161817009730089813021933 4935681378648783679883225)
          ·
            refine ⟨3701761033986587759912419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4935681378648783679883225 3701761033986587759912419)
            ·
              refine ⟨5552641550979881639868629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3701761033986587759912419 5552641550979881639868629)
              ·
                refine ⟨130140036351090975934421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5552641550979881639868629 130140036351090975934421)
                ·
                  rfl

theorem cell20_855383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 7].length) (baseStart_855383 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_855383 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_855383 prefixEnd_855383 := by exact prefixLift 855383
  have htrace : WordTrace (prefixWord ++ tailWord_855383) baseStart_855383 baseEnd_855383 := by
    simpa [prefixWord, tailWord_855383, baseEnd_855383] using wordTrace_append hprefix tailTrace_855383
  have hstable : (prefixWord ++ tailWord_855383).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855383).length < 2 ^ (prefixWord ++ tailWord_855383).sum := by decide
  have hdescent : baseEnd_855383 < baseStart_855383 := by decide
  rcases family_descends (prefixWord ++ tailWord_855383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855386 : List Nat := [3, 1, 1, 2, 1, 2, 6, 1, 3]
def baseStart_855386 : Nat := 118140960795 + 855386 * 2 ^ 59
def prefixEnd_855386 : Nat := 4983230072969 + 3 ^ 40 * 855386 * 2
def baseEnd_855386 : Nat := 390421478335018250703251

theorem tailTrace_855386 : CollatzResearch.WordTrace tailWord_855386 prefixEnd_855386 390421478335018250703251 := by
  unfold tailWord_855386
  simp only [CollatzResearch.WordTrace]
  refine ⟨7799622619772521285806503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20798993652726723428817341 7799622619772521285806503)
  ·
    refine ⟨11699433929658781928709755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7799622619772521285806503 11699433929658781928709755)
    ·
      refine ⟨17549150894488172893064633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11699433929658781928709755 17549150894488172893064633)
      ·
        refine ⟨13161863170866129669798475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17549150894488172893064633 13161863170866129669798475)
        ·
          refine ⟨19742794756299194504697713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13161863170866129669798475 19742794756299194504697713)
          ·
            refine ⟨14807096067224395878523285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19742794756299194504697713 14807096067224395878523285)
            ·
              refine ⟨694082628151143556805779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 14807096067224395878523285 694082628151143556805779)
              ·
                refine ⟨1041123942226715335208669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 694082628151143556805779 1041123942226715335208669)
                ·
                  refine ⟨390421478335018250703251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1041123942226715335208669 390421478335018250703251)
                  ·
                    rfl

theorem cell20_855386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 6, 1, 3].length) (baseStart_855386 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_855386 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_855386 prefixEnd_855386 := by exact prefixLift 855386
  have htrace : WordTrace (prefixWord ++ tailWord_855386) baseStart_855386 baseEnd_855386 := by
    simpa [prefixWord, tailWord_855386, baseEnd_855386] using wordTrace_append hprefix tailTrace_855386
  have hstable : (prefixWord ++ tailWord_855386).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855386).length < 2 ^ (prefixWord ++ tailWord_855386).sum := by decide
  have hdescent : baseEnd_855386 < baseStart_855386 := by decide
  rcases family_descends (prefixWord ++ tailWord_855386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855427 : List Nat := [1, 1, 1, 3, 5, 3, 2, 2, 2]
def baseStart_855427 : Nat := 118140960795 + 855427 * 2 ^ 59
def prefixEnd_855427 : Nat := 4983230072969 + 3 ^ 40 * 855427 * 2
def baseEnd_855427 : Nat := 390440191852204330336417

theorem tailTrace_855427 : CollatzResearch.WordTrace tailWord_855427 prefixEnd_855427 390440191852204330336417 := by
  unfold tailWord_855427
  simp only [CollatzResearch.WordTrace]
  refine ⟨31199985871941549145468535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20799990581294366096979023 31199985871941549145468535)
  ·
    refine ⟨46799978807912323718202803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31199985871941549145468535 46799978807912323718202803)
    ·
      refine ⟨70199968211868485577304205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46799978807912323718202803 70199968211868485577304205)
      ·
        refine ⟨26324988079450682091489077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70199968211868485577304205 26324988079450682091489077)
        ·
          refine ⟨2467967632448501446077101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26324988079450682091489077 2467967632448501446077101)
          ·
            refine ⟨925487862168188042278913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2467967632448501446077101 925487862168188042278913)
            ·
              refine ⟨694115896626141031709185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 925487862168188042278913 694115896626141031709185)
              ·
                refine ⟨520586922469605773781889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 694115896626141031709185 520586922469605773781889)
                ·
                  refine ⟨390440191852204330336417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 520586922469605773781889 390440191852204330336417)
                  ·
                    rfl

theorem cell20_855427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 2, 2, 2].length) (baseStart_855427 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_855427 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_855427 prefixEnd_855427 := by exact prefixLift 855427
  have htrace : WordTrace (prefixWord ++ tailWord_855427) baseStart_855427 baseEnd_855427 := by
    simpa [prefixWord, tailWord_855427, baseEnd_855427] using wordTrace_append hprefix tailTrace_855427
  have hstable : (prefixWord ++ tailWord_855427).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855427).length < 2 ^ (prefixWord ++ tailWord_855427).sum := by decide
  have hdescent : baseEnd_855427 < baseStart_855427 := by decide
  rcases family_descends (prefixWord ++ tailWord_855427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855445 : List Nat := [1, 3, 2, 1, 1, 2, 4, 3, 3]
def baseStart_855445 : Nat := 118140960795 + 855445 * 2 ^ 59
def prefixEnd_855445 : Nat := 4983230072969 + 3 ^ 40 * 855445 * 2
def baseEnd_855445 : Nat := 390448407542676267736343

theorem tailTrace_855445 : CollatzResearch.WordTrace tailWord_855445 prefixEnd_855445 390448407542676267736343 := by
  unfold tailWord_855445
  simp only [CollatzResearch.WordTrace]
  refine ⟨31200642385876338219623789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20800428257250892146415859 31200642385876338219623789)
  ·
    refine ⟨11700240894703626832358921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31200642385876338219623789 11700240894703626832358921)
    ·
      refine ⟨8775180671027720124269191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11700240894703626832358921 8775180671027720124269191)
      ·
        refine ⟨13162771006541580186403787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8775180671027720124269191 13162771006541580186403787)
        ·
          refine ⟨19744156509812370279605681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13162771006541580186403787 19744156509812370279605681)
          ·
            refine ⟨14808117382359277709704261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19744156509812370279605681 14808117382359277709704261)
            ·
              refine ⟨2776522009192364570569549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14808117382359277709704261 2776522009192364570569549)
              ·
                refine ⟨1041195753447136713963581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2776522009192364570569549 1041195753447136713963581)
                ·
                  refine ⟨390448407542676267736343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1041195753447136713963581 390448407542676267736343)
                  ·
                    rfl

theorem cell20_855445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 3, 3].length) (baseStart_855445 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_855445 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_855445 prefixEnd_855445 := by exact prefixLift 855445
  have htrace : WordTrace (prefixWord ++ tailWord_855445) baseStart_855445 baseEnd_855445 := by
    simpa [prefixWord, tailWord_855445, baseEnd_855445] using wordTrace_append hprefix tailTrace_855445
  have hstable : (prefixWord ++ tailWord_855445).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855445).length < 2 ^ (prefixWord ++ tailWord_855445).sum := by decide
  have hdescent : baseEnd_855445 < baseStart_855445 := by decide
  rcases family_descends (prefixWord ++ tailWord_855445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855510 : List Nat := [5, 2, 1, 1, 1, 4, 2, 4]
def baseStart_855510 : Nat := 118140960795 + 855510 * 2 ^ 59
def prefixEnd_855510 : Nat := 4983230072969 + 3 ^ 40 * 855510 * 2
def baseEnd_855510 : Nat := 130159358437941643523137

theorem tailTrace_855510 : CollatzResearch.WordTrace tailWord_855510 prefixEnd_855510 130159358437941643523137 := by
  unfold tailWord_855510
  simp only [CollatzResearch.WordTrace]
  refine ⟨1950188320665053395046249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20802008753760569547159989 1950188320665053395046249)
  ·
    refine ⟨1462641240498790046284687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1950188320665053395046249 1462641240498790046284687)
    ·
      refine ⟨2193961860748185069427031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1462641240498790046284687 2193961860748185069427031)
      ·
        refine ⟨3290942791122277604140547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2193961860748185069427031 3290942791122277604140547)
        ·
          refine ⟨4936414186683416406210821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3290942791122277604140547 4936414186683416406210821)
          ·
            refine ⟨925577660003140576164529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4936414186683416406210821 925577660003140576164529)
            ·
              refine ⟨694183245002355432123397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 925577660003140576164529 694183245002355432123397)
              ·
                refine ⟨130159358437941643523137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 694183245002355432123397 130159358437941643523137)
                ·
                  rfl

theorem cell20_855510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 2, 4].length) (baseStart_855510 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_855510 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_855510 prefixEnd_855510 := by exact prefixLift 855510
  have htrace : WordTrace (prefixWord ++ tailWord_855510) baseStart_855510 baseEnd_855510 := by
    simpa [prefixWord, tailWord_855510, baseEnd_855510] using wordTrace_append hprefix tailTrace_855510
  have hstable : (prefixWord ++ tailWord_855510).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855510).length < 2 ^ (prefixWord ++ tailWord_855510).sum := by decide
  have hdescent : baseEnd_855510 < baseStart_855510 := by decide
  rcases family_descends (prefixWord ++ tailWord_855510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855514 : List Nat := [3, 1, 1, 2, 3, 2, 4, 4]
def baseStart_855514 : Nat := 118140960795 + 855514 * 2 ^ 59
def prefixEnd_855514 : Nat := 4983230072969 + 3 ^ 40 * 855514 * 2
def baseEnd_855514 : Nat := 130159967007606231478687

theorem tailTrace_855514 : CollatzResearch.WordTrace tailWord_855514 prefixEnd_855514 130159967007606231478687 := by
  unfold tailWord_855514
  simp only [CollatzResearch.WordTrace]
  refine ⟨7800789755656590750971399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20802106015084242002590397 7800789755656590750971399)
  ·
    refine ⟨11701184633484886126457099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7800789755656590750971399 11701184633484886126457099)
    ·
      refine ⟨17551776950227329189685649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11701184633484886126457099 17551776950227329189685649)
      ·
        refine ⟨13163832712670496892264237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17551776950227329189685649 13163832712670496892264237)
        ·
          refine ⟨4936437267251436334599089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13163832712670496892264237 4936437267251436334599089)
          ·
            refine ⟨3702327950438577250949317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4936437267251436334599089 3702327950438577250949317)
            ·
              refine ⟨694186490707233234552997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3702327950438577250949317 694186490707233234552997)
              ·
                refine ⟨130159967007606231478687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 694186490707233234552997 130159967007606231478687)
                ·
                  rfl

theorem cell20_855514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 4, 4].length) (baseStart_855514 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_855514 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_855514 prefixEnd_855514 := by exact prefixLift 855514
  have htrace : WordTrace (prefixWord ++ tailWord_855514) baseStart_855514 baseEnd_855514 := by
    simpa [prefixWord, tailWord_855514, baseEnd_855514] using wordTrace_append hprefix tailTrace_855514
  have hstable : (prefixWord ++ tailWord_855514).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855514).length < 2 ^ (prefixWord ++ tailWord_855514).sum := by decide
  have hdescent : baseEnd_855514 < baseStart_855514 := by decide
  rcases family_descends (prefixWord ++ tailWord_855514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855573 : List Nat := [1, 3, 2, 1, 3, 2, 2, 6]
def baseStart_855573 : Nat := 118140960795 + 855573 * 2 ^ 59
def prefixEnd_855573 : Nat := 4983230072969 + 3 ^ 40 * 855573 * 2
def baseEnd_855573 : Nat := 130168943410158903823051

theorem tailTrace_855573 : CollatzResearch.WordTrace tailWord_855573 prefixEnd_855573 130168943410158903823051 := by
  unfold tailWord_855573
  simp only [CollatzResearch.WordTrace]
  refine ⟨31205310929412616080283373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20803540619608410720188915 31205310929412616080283373)
  ·
    refine ⟨11701991598529731030106265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31205310929412616080283373 11701991598529731030106265)
    ·
      refine ⟨8776493698897298272579699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11701991598529731030106265 8776493698897298272579699)
      ·
        refine ⟨13164740548345947408869549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8776493698897298272579699 13164740548345947408869549)
        ·
          refine ⟨4936777705629730278326081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13164740548345947408869549 4936777705629730278326081)
          ·
            refine ⟨3702583279222297708744561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4936777705629730278326081 3702583279222297708744561)
            ·
              refine ⟨2776937459416723281558421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3702583279222297708744561 2776937459416723281558421)
              ·
                refine ⟨130168943410158903823051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2776937459416723281558421 130168943410158903823051)
                ·
                  rfl

theorem cell20_855573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 6].length) (baseStart_855573 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_855573 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_855573 prefixEnd_855573 := by exact prefixLift 855573
  have htrace : WordTrace (prefixWord ++ tailWord_855573) baseStart_855573 baseEnd_855573 := by
    simpa [prefixWord, tailWord_855573, baseEnd_855573] using wordTrace_append hprefix tailTrace_855573
  have hstable : (prefixWord ++ tailWord_855573).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855573).length < 2 ^ (prefixWord ++ tailWord_855573).sum := by decide
  have hdescent : baseEnd_855573 < baseStart_855573 := by decide
  rcases family_descends (prefixWord ++ tailWord_855573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855628 : List Nat := [2, 2, 1, 3, 1, 4, 3, 4]
def baseStart_855628 : Nat := 118140960795 + 855628 * 2 ^ 59
def prefixEnd_855628 : Nat := 4983230072969 + 3 ^ 40 * 855628 * 2
def baseEnd_855628 : Nat := 130177311243046988211865

theorem tailTrace_855628 : CollatzResearch.WordTrace tailWord_855628 prefixEnd_855628 130177311243046988211865 := by
  unfold tailWord_855628
  simp only [CollatzResearch.WordTrace]
  refine ⟨15603658472106680236767769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20804877962808906982357025 15603658472106680236767769)
  ·
    refine ⟨11702743854080010177575827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15603658472106680236767769 11702743854080010177575827)
    ·
      refine ⟨17554115781120015266363741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11702743854080010177575827 17554115781120015266363741)
      ·
        refine ⟨6582793417920005724886403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17554115781120015266363741 6582793417920005724886403)
        ·
          refine ⟨9874190126880008587329605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6582793417920005724886403 9874190126880008587329605)
          ·
            refine ⟨1851410648790001610124301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9874190126880008587329605 1851410648790001610124301)
            ·
              refine ⟨694278993296250603796613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1851410648790001610124301 694278993296250603796613)
              ·
                refine ⟨130177311243046988211865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 694278993296250603796613 130177311243046988211865)
                ·
                  rfl

theorem cell20_855628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 3, 4].length) (baseStart_855628 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_855628 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_855628 prefixEnd_855628 := by exact prefixLift 855628
  have htrace : WordTrace (prefixWord ++ tailWord_855628) baseStart_855628 baseEnd_855628 := by
    simpa [prefixWord, tailWord_855628, baseEnd_855628] using wordTrace_append hprefix tailTrace_855628
  have hstable : (prefixWord ++ tailWord_855628).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855628).length < 2 ^ (prefixWord ++ tailWord_855628).sum := by decide
  have hdescent : baseEnd_855628 < baseStart_855628 := by decide
  rcases family_descends (prefixWord ++ tailWord_855628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855645 : List Nat := [1, 4, 4, 2, 1, 1, 7]
def baseStart_855645 : Nat := 118140960795 + 855645 * 2 ^ 59
def prefixEnd_855645 : Nat := 4983230072969 + 3 ^ 40 * 855645 * 2
def baseEnd_855645 : Nat := 43393299221373829007651

theorem tailTrace_855645 : CollatzResearch.WordTrace tailWord_855645 prefixEnd_855645 43393299221373829007651 := by
  unfold tailWord_855645
  simp only [CollatzResearch.WordTrace]
  refine ⟨31207936985151772376904389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20805291323434514917936259 31207936985151772376904389)
  ·
    refine ⟨5851488184715957320669573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31207936985151772376904389 5851488184715957320669573)
    ·
      refine ⟨1097154034634241997625545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5851488184715957320669573 1097154034634241997625545)
      ·
        refine ⟨822865525975681498219159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1097154034634241997625545 822865525975681498219159)
        ·
          refine ⟨1234298288963522247328739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 822865525975681498219159 1234298288963522247328739)
          ·
            refine ⟨1851447433445283370993109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1234298288963522247328739 1851447433445283370993109)
            ·
              refine ⟨43393299221373829007651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1851447433445283370993109 43393299221373829007651)
              ·
                rfl

theorem cell20_855645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 7].length) (baseStart_855645 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_855645 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_855645 prefixEnd_855645 := by exact prefixLift 855645
  have htrace : WordTrace (prefixWord ++ tailWord_855645) baseStart_855645 baseEnd_855645 := by
    simpa [prefixWord, tailWord_855645, baseEnd_855645] using wordTrace_append hprefix tailTrace_855645
  have hstable : (prefixWord ++ tailWord_855645).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855645).length < 2 ^ (prefixWord ++ tailWord_855645).sum := by decide
  have hdescent : baseEnd_855645 < baseStart_855645 := by decide
  rcases family_descends (prefixWord ++ tailWord_855645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855652 : List Nat := [2, 3, 1, 1, 2, 5, 1, 2, 3]
def baseStart_855652 : Nat := 118140960795 + 855652 * 2 ^ 59
def prefixEnd_855652 : Nat := 4983230072969 + 3 ^ 40 * 855652 * 2
def baseEnd_855652 : Nat := 390542887983103547835497

theorem tailTrace_855652 : CollatzResearch.WordTrace tailWord_855652 prefixEnd_855652 390542887983103547835497 := by
  unfold tailWord_855652
  simp only [CollatzResearch.WordTrace]
  refine ⟨15604096148063206286204605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20805461530750941714939473 15604096148063206286204605)
  ·
    refine ⟨5851536055523702357326727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15604096148063206286204605 5851536055523702357326727)
    ·
      refine ⟨8777304083285553535990091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5851536055523702357326727 8777304083285553535990091)
      ·
        refine ⟨13165956124928330303985137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8777304083285553535990091 13165956124928330303985137)
        ·
          refine ⟨9874467093696247727988853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13165956124928330303985137 9874467093696247727988853)
          ·
            refine ⟨925731290034023224498955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9874467093696247727988853 925731290034023224498955)
            ·
              refine ⟨1388596935051034836748433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 925731290034023224498955 1388596935051034836748433)
              ·
                refine ⟨1041447701288276127561325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1388596935051034836748433 1041447701288276127561325)
                ·
                  refine ⟨390542887983103547835497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1041447701288276127561325 390542887983103547835497)
                  ·
                    rfl

theorem cell20_855652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 1, 2, 3].length) (baseStart_855652 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_855652 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_855652 prefixEnd_855652 := by exact prefixLift 855652
  have htrace : WordTrace (prefixWord ++ tailWord_855652) baseStart_855652 baseEnd_855652 := by
    simpa [prefixWord, tailWord_855652, baseEnd_855652] using wordTrace_append hprefix tailTrace_855652
  have hstable : (prefixWord ++ tailWord_855652).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855652).length < 2 ^ (prefixWord ++ tailWord_855652).sum := by decide
  have hdescent : baseEnd_855652 < baseStart_855652 := by decide
  rcases family_descends (prefixWord ++ tailWord_855652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855669 : List Nat := [1, 3, 4, 2, 1, 2, 3, 1, 3]
def baseStart_855669 : Nat := 118140960795 + 855669 * 2 ^ 59
def prefixEnd_855669 : Nat := 4983230072969 + 3 ^ 40 * 855669 * 2
def baseEnd_855669 : Nat := 390550647246327044268761

theorem tailTrace_855669 : CollatzResearch.WordTrace tailWord_855669 prefixEnd_855669 390550647246327044268761 := by
  unfold tailWord_855669
  simp only [CollatzResearch.WordTrace]
  refine ⟨31208812337064824475778061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20805874891376549650518707 31208812337064824475778061)
  ·
    refine ⟨11703304626399309178416773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31208812337064824475778061 11703304626399309178416773)
    ·
      refine ⟨2194369617449870470953145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11703304626399309178416773 2194369617449870470953145)
      ·
        refine ⟨1645777213087402853214859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2194369617449870470953145 1645777213087402853214859)
        ·
          refine ⟨2468665819631104279822289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1645777213087402853214859 2468665819631104279822289)
          ·
            refine ⟨1851499364723328209866717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2468665819631104279822289 1851499364723328209866717)
            ·
              refine ⟨694312261771248078700019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1851499364723328209866717 694312261771248078700019)
              ·
                refine ⟨1041468392656872118050029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 694312261771248078700019 1041468392656872118050029)
                ·
                  refine ⟨390550647246327044268761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1041468392656872118050029 390550647246327044268761)
                  ·
                    rfl

theorem cell20_855669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 3, 1, 3].length) (baseStart_855669 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_855669 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_855669 prefixEnd_855669 := by exact prefixLift 855669
  have htrace : WordTrace (prefixWord ++ tailWord_855669) baseStart_855669 baseEnd_855669 := by
    simpa [prefixWord, tailWord_855669, baseEnd_855669] using wordTrace_append hprefix tailTrace_855669
  have hstable : (prefixWord ++ tailWord_855669).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855669).length < 2 ^ (prefixWord ++ tailWord_855669).sum := by decide
  have hdescent : baseEnd_855669 < baseStart_855669 := by decide
  rcases family_descends (prefixWord ++ tailWord_855669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855687 : List Nat := [1, 1, 4, 2, 1, 4, 1, 6]
def baseStart_855687 : Nat := 118140960795 + 855687 * 2 ^ 59
def prefixEnd_855687 : Nat := 4983230072969 + 3 ^ 40 * 855687 * 2
def baseEnd_855687 : Nat := 130186287645599660556229

theorem tailTrace_855687 : CollatzResearch.WordTrace tailWord_855687 prefixEnd_855687 130186287645599660556229 := by
  unfold tailWord_855687
  simp only [CollatzResearch.WordTrace]
  refine ⟨31209468850999613549933315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20806312567333075699955543 31209468850999613549933315)
  ·
    refine ⟨46814203276499420324899973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31209468850999613549933315 46814203276499420324899973)
    ·
      refine ⟨8777663114343641310918745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46814203276499420324899973 8777663114343641310918745)
      ·
        refine ⟨6583247335757730983189059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8777663114343641310918745 6583247335757730983189059)
        ·
          refine ⟨9874871003636596474783589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6583247335757730983189059 9874871003636596474783589)
          ·
            refine ⟨1851538313181861839021923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9874871003636596474783589 1851538313181861839021923)
            ·
              refine ⟨2777307469772792758532885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1851538313181861839021923 2777307469772792758532885)
              ·
                refine ⟨130186287645599660556229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2777307469772792758532885 130186287645599660556229)
                ·
                  rfl

theorem cell20_855687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 6].length) (baseStart_855687 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_855687 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_855687 prefixEnd_855687 := by exact prefixLift 855687
  have htrace : WordTrace (prefixWord ++ tailWord_855687) baseStart_855687 baseEnd_855687 := by
    simpa [prefixWord, tailWord_855687, baseEnd_855687] using wordTrace_append hprefix tailTrace_855687
  have hstable : (prefixWord ++ tailWord_855687).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855687).length < 2 ^ (prefixWord ++ tailWord_855687).sum := by decide
  have hdescent : baseEnd_855687 < baseStart_855687 := by decide
  rcases family_descends (prefixWord ++ tailWord_855687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855701 : List Nat := [1, 3, 2, 1, 1, 1, 1, 4, 6]
def baseStart_855701 : Nat := 118140960795 + 855701 * 2 ^ 59
def prefixEnd_855701 : Nat := 4983230072969 + 3 ^ 40 * 855701 * 2
def baseEnd_855701 : Nat := 390565252918277155201963

theorem tailTrace_855701 : CollatzResearch.WordTrace tailWord_855701 prefixEnd_855701 390565252918277155201963 := by
  unfold tailWord_855701
  simp only [CollatzResearch.WordTrace]
  refine ⟨31209979472948893940942957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20806652981965929293961971 31209979472948893940942957)
  ·
    refine ⟨11703742302355835227853609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31209979472948893940942957 11703742302355835227853609)
    ·
      refine ⟨8777806726766876420890207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11703742302355835227853609 8777806726766876420890207)
      ·
        refine ⟨13166710090150314631335311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8777806726766876420890207 13166710090150314631335311)
        ·
          refine ⟨19750065135225471947002967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13166710090150314631335311 19750065135225471947002967)
          ·
            refine ⟨29625097702838207920504451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19750065135225471947002967 29625097702838207920504451)
            ·
              refine ⟨44437646554257311880756677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29625097702838207920504451 44437646554257311880756677)
              ·
                refine ⟨8332058728923245977641877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44437646554257311880756677 8332058728923245977641877)
                ·
                  refine ⟨390565252918277155201963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8332058728923245977641877 390565252918277155201963)
                  ·
                    rfl

theorem cell20_855701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 4, 6].length) (baseStart_855701 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_855701 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_855701 prefixEnd_855701 := by exact prefixLift 855701
  have htrace : WordTrace (prefixWord ++ tailWord_855701) baseStart_855701 baseEnd_855701 := by
    simpa [prefixWord, tailWord_855701, baseEnd_855701] using wordTrace_append hprefix tailTrace_855701
  have hstable : (prefixWord ++ tailWord_855701).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855701).length < 2 ^ (prefixWord ++ tailWord_855701).sum := by decide
  have hdescent : baseEnd_855701 < baseStart_855701 := by decide
  rcases family_descends (prefixWord ++ tailWord_855701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855720 : List Nat := [2, 1, 7, 1, 2, 1, 2, 1, 3]
def baseStart_855720 : Nat := 118140960795 + 855720 * 2 ^ 59
def prefixEnd_855720 : Nat := 4983230072969 + 3 ^ 40 * 855720 * 2
def baseEnd_855720 : Nat := 390573925035997533568553

theorem tailTrace_855720 : CollatzResearch.WordTrace tailWord_855720 prefixEnd_855720 390573925035997533568553 := by
  unfold tailWord_855720
  simp only [CollatzResearch.WordTrace]
  refine ⟨15605336229940030092942307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20807114973253373457256409 15605336229940030092942307)
  ·
    refine ⟨23408004344910045139413461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15605336229940030092942307 23408004344910045139413461)
    ·
      refine ⟨548625101833829182955003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 23408004344910045139413461 548625101833829182955003)
      ·
        refine ⟨822937652750743774432505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 548625101833829182955003 822937652750743774432505)
        ·
          refine ⟨617203239563057830824379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 822937652750743774432505 617203239563057830824379)
          ·
            refine ⟨925804859344586746236569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 617203239563057830824379 925804859344586746236569)
            ·
              refine ⟨694353644508440059677427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 925804859344586746236569 694353644508440059677427)
              ·
                refine ⟨1041530466762660089516141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 694353644508440059677427 1041530466762660089516141)
                ·
                  refine ⟨390573925035997533568553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1041530466762660089516141 390573925035997533568553)
                  ·
                    rfl

theorem cell20_855720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 2, 1, 3].length) (baseStart_855720 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_855720 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_855720 prefixEnd_855720 := by exact prefixLift 855720
  have htrace : WordTrace (prefixWord ++ tailWord_855720) baseStart_855720 baseEnd_855720 := by
    simpa [prefixWord, tailWord_855720, baseEnd_855720] using wordTrace_append hprefix tailTrace_855720
  have hstable : (prefixWord ++ tailWord_855720).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855720).length < 2 ^ (prefixWord ++ tailWord_855720).sum := by decide
  have hdescent : baseEnd_855720 < baseStart_855720 := by decide
  rcases family_descends (prefixWord ++ tailWord_855720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855739 : List Nat := [1, 1, 1, 1, 1, 2, 3, 6, 4]
def baseStart_855739 : Nat := 118140960795 + 855739 * 2 ^ 59
def prefixEnd_855739 : Nat := 4983230072969 + 3 ^ 40 * 855739 * 2
def baseEnd_855739 : Nat := 390582597153717911935141

theorem tailTrace_855739 : CollatzResearch.WordTrace tailWord_855739 prefixEnd_855739 390582597153717911935141 := by
  unfold tailWord_855739
  simp only [CollatzResearch.WordTrace]
  refine ⟨31211365446811226430826271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20807576964540817620550847 31211365446811226430826271)
  ·
    refine ⟨46817048170216839646239407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31211365446811226430826271 46817048170216839646239407)
    ·
      refine ⟨70225572255325259469359111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46817048170216839646239407 70225572255325259469359111)
      ·
        refine ⟨105338358382987889204038667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70225572255325259469359111 105338358382987889204038667)
        ·
          refine ⟨158007537574481833806058001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105338358382987889204038667 158007537574481833806058001)
          ·
            refine ⟨118505653180861375354543501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158007537574481833806058001 118505653180861375354543501)
            ·
              refine ⟨44439619942823015757953813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118505653180861375354543501 44439619942823015757953813)
              ·
                refine ⟨2083107184819828863654085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 44439619942823015757953813 2083107184819828863654085)
                ·
                  refine ⟨390582597153717911935141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2083107184819828863654085 390582597153717911935141)
                  ·
                    rfl

theorem cell20_855739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 6, 4].length) (baseStart_855739 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_855739 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_855739 prefixEnd_855739 := by exact prefixLift 855739
  have htrace : WordTrace (prefixWord ++ tailWord_855739) baseStart_855739 baseEnd_855739 := by
    simpa [prefixWord, tailWord_855739, baseEnd_855739] using wordTrace_append hprefix tailTrace_855739
  have hstable : (prefixWord ++ tailWord_855739).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855739).length < 2 ^ (prefixWord ++ tailWord_855739).sum := by decide
  have hdescent : baseEnd_855739 < baseStart_855739 := by decide
  rcases family_descends (prefixWord ++ tailWord_855739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855794 : List Nat := [3, 2, 1, 3, 1, 1, 3, 2, 4]
def baseStart_855794 : Nat := 118140960795 + 855794 * 2 ^ 59
def prefixEnd_855794 : Nat := 4983230072969 + 3 ^ 40 * 855794 * 2
def baseEnd_855794 : Nat := 390607700652382165101583

theorem tailTrace_855794 : CollatzResearch.WordTrace tailWord_855794 prefixEnd_855794 390607700652382165101583 := by
  unfold tailWord_855794
  simp only [CollatzResearch.WordTrace]
  refine ⟨7803342865402992706019609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20808914307741313882718957 7803342865402992706019609)
  ·
    refine ⟨5852507149052244529514707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7803342865402992706019609 5852507149052244529514707)
    ·
      refine ⟨8778760723578366794272061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5852507149052244529514707 8778760723578366794272061)
      ·
        refine ⟨3292035271341887547852023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8778760723578366794272061 3292035271341887547852023)
        ·
          refine ⟨4938052907012831321778035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3292035271341887547852023 4938052907012831321778035)
          ·
            refine ⟨7407079360519246982667053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4938052907012831321778035 7407079360519246982667053)
            ·
              refine ⟨2777654760194717618500145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7407079360519246982667053 2777654760194717618500145)
              ·
                refine ⟨2083241070146038213875109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2777654760194717618500145 2083241070146038213875109)
                ·
                  refine ⟨390607700652382165101583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2083241070146038213875109 390607700652382165101583)
                  ·
                    rfl

theorem cell20_855794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 2, 4].length) (baseStart_855794 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_855794 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_855794 prefixEnd_855794 := by exact prefixLift 855794
  have htrace : WordTrace (prefixWord ++ tailWord_855794) baseStart_855794 baseEnd_855794 := by
    simpa [prefixWord, tailWord_855794, baseEnd_855794] using wordTrace_append hprefix tailTrace_855794
  have hstable : (prefixWord ++ tailWord_855794).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855794).length < 2 ^ (prefixWord ++ tailWord_855794).sum := by decide
  have hdescent : baseEnd_855794 < baseStart_855794 := by decide
  rcases family_descends (prefixWord ++ tailWord_855794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855842 : List Nat := [3, 3, 1, 1, 2, 1, 5, 1, 3]
def baseStart_855842 : Nat := 118140960795 + 855842 * 2 ^ 59
def prefixEnd_855842 : Nat := 4983230072969 + 3 ^ 40 * 855842 * 2
def baseEnd_855842 : Nat := 390629609160307331501387

theorem tailTrace_855842 : CollatzResearch.WordTrace tailWord_855842 prefixEnd_855842 390629609160307331501387 := by
  unfold tailWord_855842
  simp only [CollatzResearch.WordTrace]
  refine ⟨7803780541359518755456445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20810081443625383347883853 7803780541359518755456445)
  ·
    refine ⟨2926417703009819533296167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7803780541359518755456445 2926417703009819533296167)
    ·
      refine ⟨4389626554514729299944251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2926417703009819533296167 4389626554514729299944251)
      ·
        refine ⟨6584439831772093949916377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4389626554514729299944251 6584439831772093949916377)
        ·
          refine ⟨4938329873829070462437283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6584439831772093949916377 4938329873829070462437283)
          ·
            refine ⟨7407494810743605693655925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4938329873829070462437283 7407494810743605693655925)
            ·
              refine ⟨694452638507213033780243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7407494810743605693655925 694452638507213033780243)
              ·
                refine ⟨1041678957760819550670365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 694452638507213033780243 1041678957760819550670365)
                ·
                  refine ⟨390629609160307331501387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1041678957760819550670365 390629609160307331501387)
                  ·
                    rfl

theorem cell20_855842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 5, 1, 3].length) (baseStart_855842 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_855842 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_855842 prefixEnd_855842 := by exact prefixLift 855842
  have htrace : WordTrace (prefixWord ++ tailWord_855842) baseStart_855842 baseEnd_855842 := by
    simpa [prefixWord, tailWord_855842, baseEnd_855842] using wordTrace_append hprefix tailTrace_855842
  have hstable : (prefixWord ++ tailWord_855842).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855842).length < 2 ^ (prefixWord ++ tailWord_855842).sum := by decide
  have hdescent : baseEnd_855842 < baseStart_855842 := by decide
  rcases family_descends (prefixWord ++ tailWord_855842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855866 : List Nat := [3, 1, 1, 1, 5, 3, 1, 3, 2]
def baseStart_855866 : Nat := 118140960795 + 855866 * 2 ^ 59
def prefixEnd_855866 : Nat := 4983230072969 + 3 ^ 40 * 855866 * 2
def baseEnd_855866 : Nat := 390640563414269914701289

theorem tailTrace_855866 : CollatzResearch.WordTrace tailWord_855866 prefixEnd_855866 390640563414269914701289 := by
  unfold tailWord_855866
  simp only [CollatzResearch.WordTrace]
  refine ⟨7803999379337781780174863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20810665011567418080466301 7803999379337781780174863)
  ·
    refine ⟨11705999069006672670262295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7803999379337781780174863 11705999069006672670262295)
    ·
      refine ⟨17558998603510009005393443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11705999069006672670262295 17558998603510009005393443)
      ·
        refine ⟨26338497905265013508090165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17558998603510009005393443 26338497905265013508090165)
        ·
          refine ⟨2469234178618595016383453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26338497905265013508090165 2469234178618595016383453)
          ·
            refine ⟨925962816981973131143795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2469234178618595016383453 925962816981973131143795)
            ·
              refine ⟨1388944225472959696715693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 925962816981973131143795 1388944225472959696715693)
              ·
                refine ⟨520854084552359886268385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1388944225472959696715693 520854084552359886268385)
                ·
                  refine ⟨390640563414269914701289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 520854084552359886268385 390640563414269914701289)
                  ·
                    rfl

theorem cell20_855866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 1, 3, 2].length) (baseStart_855866 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_855866 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_855866 prefixEnd_855866 := by exact prefixLift 855866
  have htrace : WordTrace (prefixWord ++ tailWord_855866) baseStart_855866 baseEnd_855866 := by
    simpa [prefixWord, tailWord_855866, baseEnd_855866] using wordTrace_append hprefix tailTrace_855866
  have hstable : (prefixWord ++ tailWord_855866).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855866).length < 2 ^ (prefixWord ++ tailWord_855866).sum := by decide
  have hdescent : baseEnd_855866 < baseStart_855866 := by decide
  rcases family_descends (prefixWord ++ tailWord_855866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855925 : List Nat := [1, 3, 4, 1, 1, 1, 2, 5, 2]
def baseStart_855925 : Nat := 118140960795 + 855925 * 2 ^ 59
def prefixEnd_855925 : Nat := 4983230072969 + 3 ^ 40 * 855925 * 2
def baseEnd_855925 : Nat := 390667492621927931734381

theorem tailTrace_855925 : CollatzResearch.WordTrace tailWord_855925 prefixEnd_855925 390667492621927931734381 := by
  unfold tailWord_855925
  simp only [CollatzResearch.WordTrace]
  refine ⟨31218149424137380197097229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20812099616091586798064819 31218149424137380197097229)
  ·
    refine ⟨11706806034051517573911461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31218149424137380197097229 11706806034051517573911461)
    ·
      refine ⟨2195026131384659545108399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11706806034051517573911461 2195026131384659545108399)
      ·
        refine ⟨3292539197076989317662599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2195026131384659545108399 3292539197076989317662599)
        ·
          refine ⟨4938808795615483976493899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3292539197076989317662599 4938808795615483976493899)
          ·
            refine ⟨7408213193423225964740849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4938808795615483976493899 7408213193423225964740849)
            ·
              refine ⟨5556159895067419473555637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7408213193423225964740849 5556159895067419473555637)
              ·
                refine ⟨520889990162570575645841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5556159895067419473555637 520889990162570575645841)
                ·
                  refine ⟨390667492621927931734381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 520889990162570575645841 390667492621927931734381)
                  ·
                    rfl

theorem cell20_855925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 5, 2].length) (baseStart_855925 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_855925 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_855925 prefixEnd_855925 := by exact prefixLift 855925
  have htrace : WordTrace (prefixWord ++ tailWord_855925) baseStart_855925 baseEnd_855925 := by
    simpa [prefixWord, tailWord_855925, baseEnd_855925] using wordTrace_append hprefix tailTrace_855925
  have hstable : (prefixWord ++ tailWord_855925).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855925).length < 2 ^ (prefixWord ++ tailWord_855925).sum := by decide
  have hdescent : baseEnd_855925 < baseStart_855925 := by decide
  rcases family_descends (prefixWord ++ tailWord_855925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855939 : List Nat := [1, 1, 1, 3, 4, 3, 2, 2, 3]
def baseStart_855939 : Nat := 118140960795 + 855939 * 2 ^ 59
def prefixEnd_855939 : Nat := 4983230072969 + 3 ^ 40 * 855939 * 2
def baseEnd_855939 : Nat := 390673882603406105267657

theorem tailTrace_855939 : CollatzResearch.WordTrace tailWord_855939 prefixEnd_855939 390673882603406105267657 := by
  unfold tailWord_855939
  simp only [CollatzResearch.WordTrace]
  refine ⟨31218660046086660588106871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20812440030724440392071247 31218660046086660588106871)
  ·
    refine ⟨46827990069129990882160307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31218660046086660588106871 46827990069129990882160307)
    ·
      refine ⟨70241985103694986323240461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46827990069129990882160307 70241985103694986323240461)
      ·
        refine ⟨26340744413885619871215173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70241985103694986323240461 26340744413885619871215173)
        ·
          refine ⟨4938889577603553725852845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26340744413885619871215173 4938889577603553725852845)
          ·
            refine ⟨1852083591601332647194817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4938889577603553725852845 1852083591601332647194817)
            ·
              refine ⟨1389062693700999485396113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1852083591601332647194817 1389062693700999485396113)
              ·
                refine ⟨1041797020275749614047085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1389062693700999485396113 1041797020275749614047085)
                ·
                  refine ⟨390673882603406105267657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1041797020275749614047085 390673882603406105267657)
                  ·
                    rfl

theorem cell20_855939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 2, 2, 3].length) (baseStart_855939 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_855939 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_855939 prefixEnd_855939 := by exact prefixLift 855939
  have htrace : WordTrace (prefixWord ++ tailWord_855939) baseStart_855939 baseEnd_855939 := by
    simpa [prefixWord, tailWord_855939, baseEnd_855939] using wordTrace_append hprefix tailTrace_855939
  have hstable : (prefixWord ++ tailWord_855939).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855939).length < 2 ^ (prefixWord ++ tailWord_855939).sum := by decide
  have hdescent : baseEnd_855939 < baseStart_855939 := by decide
  rcases family_descends (prefixWord ++ tailWord_855939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_855966 : List Nat := [4, 3, 1, 3, 1, 1, 3, 4]
def baseStart_855966 : Nat := 118140960795 + 855966 * 2 ^ 59
def prefixEnd_855966 : Nat := 4983230072969 + 3 ^ 40 * 855966 * 2
def baseEnd_855966 : Nat := 130228735379704670455849

theorem tailTrace_855966 : CollatzResearch.WordTrace tailWord_855966 prefixEnd_855966 130228735379704670455849 := by
  unfold tailWord_855966
  simp only [CollatzResearch.WordTrace]
  refine ⟨3902455602123605524917469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20813096544659229466226501 3902455602123605524917469)
  ·
    refine ⟨1463420850796352071844051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3902455602123605524917469 1463420850796352071844051)
    ·
      refine ⟨2195131276194528107766077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1463420850796352071844051 2195131276194528107766077)
      ·
        refine ⟨823174228572948040412279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2195131276194528107766077 823174228572948040412279)
        ·
          refine ⟨1234761342859422060618419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 823174228572948040412279 1234761342859422060618419)
          ·
            refine ⟨1852142014289133090927629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1234761342859422060618419 1852142014289133090927629)
            ·
              refine ⟨694553255358424909097861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1852142014289133090927629 694553255358424909097861)
              ·
                refine ⟨130228735379704670455849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 694553255358424909097861 130228735379704670455849)
                ·
                  rfl

theorem cell20_855966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 3, 4].length) (baseStart_855966 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_855966 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_855966 prefixEnd_855966 := by exact prefixLift 855966
  have htrace : WordTrace (prefixWord ++ tailWord_855966) baseStart_855966 baseEnd_855966 := by
    simpa [prefixWord, tailWord_855966, baseEnd_855966] using wordTrace_append hprefix tailTrace_855966
  have hstable : (prefixWord ++ tailWord_855966).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_855966).length < 2 ^ (prefixWord ++ tailWord_855966).sum := by decide
  have hdescent : baseEnd_855966 < baseStart_855966 := by decide
  rcases family_descends (prefixWord ++ tailWord_855966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856015 : List Nat := [1, 1, 2, 1, 1, 5, 5, 1, 3]
def baseStart_856015 : Nat := 118140960795 + 856015 * 2 ^ 59
def prefixEnd_856015 : Nat := 4983230072969 + 3 ^ 40 * 856015 * 2
def baseEnd_856015 : Nat := 390708571074287618734013

theorem tailTrace_856015 : CollatzResearch.WordTrace tailWord_856015 prefixEnd_856015 390708571074287618734013 := by
  unfold tailWord_856015
  simp only [CollatzResearch.WordTrace]
  refine ⟨31221431993811325567873499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20814287995874217045248999 31221431993811325567873499)
  ·
    refine ⟨46832147990716988351810249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31221431993811325567873499 46832147990716988351810249)
    ·
      refine ⟨35124110993037741263857687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46832147990716988351810249 35124110993037741263857687)
      ·
        refine ⟨52686166489556611895786531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35124110993037741263857687 52686166489556611895786531)
        ·
          refine ⟨79029249734334917843679797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52686166489556611895786531 79029249734334917843679797)
          ·
            refine ⟨7408992162593898547844981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 79029249734334917843679797 7408992162593898547844981)
            ·
              refine ⟨694593015243177988860467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7408992162593898547844981 694593015243177988860467)
              ·
                refine ⟨1041889522864766983290701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 694593015243177988860467 1041889522864766983290701)
                ·
                  refine ⟨390708571074287618734013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1041889522864766983290701 390708571074287618734013)
                  ·
                    rfl

theorem cell20_856015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 5, 1, 3].length) (baseStart_856015 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_856015 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_856015 prefixEnd_856015 := by exact prefixLift 856015
  have htrace : WordTrace (prefixWord ++ tailWord_856015) baseStart_856015 baseEnd_856015 := by
    simpa [prefixWord, tailWord_856015, baseEnd_856015] using wordTrace_append hprefix tailTrace_856015
  have hstable : (prefixWord ++ tailWord_856015).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856015).length < 2 ^ (prefixWord ++ tailWord_856015).sum := by decide
  have hdescent : baseEnd_856015 < baseStart_856015 := by decide
  rcases family_descends (prefixWord ++ tailWord_856015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856025 : List Nat := [1, 2, 1, 2, 7, 1, 2, 4]
def baseStart_856025 : Nat := 118140960795 + 856025 * 2 ^ 59
def prefixEnd_856025 : Nat := 4983230072969 + 3 ^ 40 * 856025 * 2
def baseEnd_856025 : Nat := 130237711782257342800213

theorem tailTrace_856025 : CollatzResearch.WordTrace tailWord_856025 prefixEnd_856025 130237711782257342800213 := by
  unfold tailWord_856025
  simp only [CollatzResearch.WordTrace]
  refine ⟨31221796723775097275737529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20814531149183398183825019 31221796723775097275737529)
  ·
    refine ⟨23416347542831322956803147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31221796723775097275737529 23416347542831322956803147)
    ·
      refine ⟨35124521314246984435204721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23416347542831322956803147 35124521314246984435204721)
      ·
        refine ⟨26343390985685238326403541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35124521314246984435204721 26343390985685238326403541)
        ·
          refine ⟨617423226226997773275083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 26343390985685238326403541 617423226226997773275083)
          ·
            refine ⟨926134839340496659912625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 617423226226997773275083 926134839340496659912625)
            ·
              refine ⟨694601129505372494934469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 926134839340496659912625 694601129505372494934469)
              ·
                refine ⟨130237711782257342800213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 694601129505372494934469 130237711782257342800213)
                ·
                  rfl

theorem cell20_856025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 2, 4].length) (baseStart_856025 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_856025 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_856025 prefixEnd_856025 := by exact prefixLift 856025
  have htrace : WordTrace (prefixWord ++ tailWord_856025) baseStart_856025 baseEnd_856025 := by
    simpa [prefixWord, tailWord_856025, baseEnd_856025] using wordTrace_append hprefix tailTrace_856025
  have hstable : (prefixWord ++ tailWord_856025).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856025).length < 2 ^ (prefixWord ++ tailWord_856025).sum := by decide
  have hdescent : baseEnd_856025 < baseStart_856025 := by decide
  rcases family_descends (prefixWord ++ tailWord_856025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856088 : List Nat := [2, 1, 2, 3, 2, 1, 1, 8]
def baseStart_856088 : Nat := 118140960795 + 856088 * 2 ^ 59
def prefixEnd_856088 : Nat := 4983230072969 + 3 ^ 40 * 856088 * 2
def baseEnd_856088 : Nat := 130247296754474603100127

theorem tailTrace_856088 : CollatzResearch.WordTrace tailWord_856088 prefixEnd_856088 130247296754474603100127 := by
  unfold tailWord_856088
  simp only [CollatzResearch.WordTrace]
  refine ⟨15612047261273429517640459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20816063015031239356853945 15612047261273429517640459)
  ·
    refine ⟨23418070891910144276460689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15612047261273429517640459 23418070891910144276460689)
    ·
      refine ⟨17563553168932608207345517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23418070891910144276460689 17563553168932608207345517)
      ·
        refine ⟨6586332438349728077754569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17563553168932608207345517 6586332438349728077754569)
        ·
          refine ⟨4939749328762296058315927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6586332438349728077754569 4939749328762296058315927)
          ·
            refine ⟨7409623993143444087473891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4939749328762296058315927 7409623993143444087473891)
            ·
              refine ⟨11114435989715166131210837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7409623993143444087473891 11114435989715166131210837)
              ·
                refine ⟨130247296754474603100127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11114435989715166131210837 130247296754474603100127)
                ·
                  rfl

theorem cell20_856088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 8].length) (baseStart_856088 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_856088 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_856088 prefixEnd_856088 := by exact prefixLift 856088
  have htrace : WordTrace (prefixWord ++ tailWord_856088) baseStart_856088 baseEnd_856088 := by
    simpa [prefixWord, tailWord_856088, baseEnd_856088] using wordTrace_append hprefix tailTrace_856088
  have hstable : (prefixWord ++ tailWord_856088).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856088).length < 2 ^ (prefixWord ++ tailWord_856088).sum := by decide
  have hdescent : baseEnd_856088 < baseStart_856088 := by decide
  rcases family_descends (prefixWord ++ tailWord_856088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856112 : List Nat := [2, 1, 1, 1, 2, 5, 1, 4, 3]
def baseStart_856112 : Nat := 118140960795 + 856112 * 2 ^ 59
def prefixEnd_856112 : Nat := 4983230072969 + 3 ^ 40 * 856112 * 2
def baseEnd_856112 : Nat := 390752844517386392500283

theorem tailTrace_856112 : CollatzResearch.WordTrace tailWord_856112 prefixEnd_856112 390752844517386392500283 := by
  unfold tailWord_856112
  simp only [CollatzResearch.WordTrace]
  refine ⟨15612484937229955567077295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20816646582973274089436393 15612484937229955567077295)
  ·
    refine ⟨23418727405844933350615943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15612484937229955567077295 23418727405844933350615943)
    ·
      refine ⟨35128091108767400025923915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23418727405844933350615943 35128091108767400025923915)
      ·
        refine ⟨52692136663151100038885873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35128091108767400025923915 52692136663151100038885873)
        ·
          refine ⟨39519102497363325029164405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52692136663151100038885873 39519102497363325029164405)
          ·
            refine ⟨3704915859127811721484163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39519102497363325029164405 3704915859127811721484163)
            ·
              refine ⟨5557373788691717582226245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3704915859127811721484163 5557373788691717582226245)
              ·
                refine ⟨1042007585379697046667421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5557373788691717582226245 1042007585379697046667421)
                ·
                  refine ⟨390752844517386392500283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1042007585379697046667421 390752844517386392500283)
                  ·
                    rfl

theorem cell20_856112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 4, 3].length) (baseStart_856112 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_856112 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_856112 prefixEnd_856112 := by exact prefixLift 856112
  have htrace : WordTrace (prefixWord ++ tailWord_856112) baseStart_856112 baseEnd_856112 := by
    simpa [prefixWord, tailWord_856112, baseEnd_856112] using wordTrace_append hprefix tailTrace_856112
  have hstable : (prefixWord ++ tailWord_856112).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856112).length < 2 ^ (prefixWord ++ tailWord_856112).sum := by decide
  have hdescent : baseEnd_856112 < baseStart_856112 := by decide
  rcases family_descends (prefixWord ++ tailWord_856112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856115 : List Nat := [1, 1, 1, 2, 4, 1, 6, 2, 2]
def baseStart_856115 : Nat := 118140960795 + 856115 * 2 ^ 59
def prefixEnd_856115 : Nat := 4983230072969 + 3 ^ 40 * 856115 * 2
def baseEnd_856115 : Nat := 390754213799131715400271

theorem tailTrace_856115 : CollatzResearch.WordTrace tailWord_856115 prefixEnd_856115 390754213799131715400271 := by
  unfold tailWord_856115
  simp only [CollatzResearch.WordTrace]
  refine ⟨31225079293449042646513799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20816719528966028431009199 31225079293449042646513799)
  ·
    refine ⟨46837618940173563969770699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31225079293449042646513799 46837618940173563969770699)
    ·
      refine ⟨70256428410260345954656049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46837618940173563969770699 70256428410260345954656049)
      ·
        refine ⟨52692321307695259465992037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70256428410260345954656049 52692321307695259465992037)
        ·
          refine ⟨9879810245192861149873507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52692321307695259465992037 9879810245192861149873507)
          ·
            refine ⟨14819715367789291724810261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9879810245192861149873507 14819715367789291724810261)
            ·
              refine ⟨694674157865123049600481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 14819715367789291724810261 694674157865123049600481)
              ·
                refine ⟨521005618398842287200361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 694674157865123049600481 521005618398842287200361)
                ·
                  refine ⟨390754213799131715400271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 521005618398842287200361 390754213799131715400271)
                  ·
                    rfl

theorem cell20_856115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 6, 2, 2].length) (baseStart_856115 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_856115 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_856115 prefixEnd_856115 := by exact prefixLift 856115
  have htrace : WordTrace (prefixWord ++ tailWord_856115) baseStart_856115 baseEnd_856115 := by
    simpa [prefixWord, tailWord_856115, baseEnd_856115] using wordTrace_append hprefix tailTrace_856115
  have hstable : (prefixWord ++ tailWord_856115).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856115).length < 2 ^ (prefixWord ++ tailWord_856115).sum := by decide
  have hdescent : baseEnd_856115 < baseStart_856115 := by decide
  rcases family_descends (prefixWord ++ tailWord_856115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856129 : List Nat := [1, 2, 5, 1, 2, 1, 2, 3, 3]
def baseStart_856129 : Nat := 118140960795 + 856129 * 2 ^ 59
def prefixEnd_856129 : Nat := 4983230072969 + 3 ^ 40 * 856129 * 2
def baseEnd_856129 : Nat := 390760603780609888933547

theorem tailTrace_856129 : CollatzResearch.WordTrace tailWord_856129 prefixEnd_856129 390760603780609888933547 := by
  unfold tailWord_856129
  simp only [CollatzResearch.WordTrace]
  refine ⟨31225589915398323037523441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20817059943598882025015627 31225589915398323037523441)
  ·
    refine ⟨23419192436548742278142581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31225589915398323037523441 23419192436548742278142581)
    ·
      refine ⟨2195549290926444588575867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23419192436548742278142581 2195549290926444588575867)
      ·
        refine ⟨3293323936389666882863801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2195549290926444588575867 3293323936389666882863801)
        ·
          refine ⟨2469992952292250162147851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3293323936389666882863801 2469992952292250162147851)
          ·
            refine ⟨3704989428438375243221777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2469992952292250162147851 3704989428438375243221777)
            ·
              refine ⟨2778742071328781432416333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3704989428438375243221777 2778742071328781432416333)
              ·
                refine ⟨1042028276748293037156125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2778742071328781432416333 1042028276748293037156125)
                ·
                  refine ⟨390760603780609888933547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1042028276748293037156125 390760603780609888933547)
                  ·
                    rfl

theorem cell20_856129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 3, 3].length) (baseStart_856129 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_856129 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_856129 prefixEnd_856129 := by exact prefixLift 856129
  have htrace : WordTrace (prefixWord ++ tailWord_856129) baseStart_856129 baseEnd_856129 := by
    simpa [prefixWord, tailWord_856129, baseEnd_856129] using wordTrace_append hprefix tailTrace_856129
  have hstable : (prefixWord ++ tailWord_856129).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856129).length < 2 ^ (prefixWord ++ tailWord_856129).sum := by decide
  have hdescent : baseEnd_856129 < baseStart_856129 := by decide
  rcases family_descends (prefixWord ++ tailWord_856129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856133 : List Nat := [1, 3, 1, 1, 1, 3, 1, 2, 7]
def baseStart_856133 : Nat := 118140960795 + 856133 * 2 ^ 59
def prefixEnd_856133 : Nat := 4983230072969 + 3 ^ 40 * 856133 * 2
def baseEnd_856133 : Nat := 390762429489603652800197

theorem tailTrace_856133 : CollatzResearch.WordTrace tailWord_856133 prefixEnd_856133 390762429489603652800197 := by
  unfold tailWord_856133
  simp only [CollatzResearch.WordTrace]
  refine ⟨31225735807383831720669053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20817157204922554480446035 31225735807383831720669053)
  ·
    refine ⟨11709650927768936895250895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31225735807383831720669053 11709650927768936895250895)
    ·
      refine ⟨17564476391653405342876343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11709650927768936895250895 17564476391653405342876343)
      ·
        refine ⟨26346714587480108014314515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17564476391653405342876343 26346714587480108014314515)
        ·
          refine ⟨39520071881220162021471773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26346714587480108014314515 39520071881220162021471773)
          ·
            refine ⟨14820026955457560758051915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39520071881220162021471773 14820026955457560758051915)
            ·
              refine ⟨22230040433186341137077873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14820026955457560758051915 22230040433186341137077873)
              ·
                refine ⟨16672530324889755852808405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22230040433186341137077873 16672530324889755852808405)
                ·
                  refine ⟨390762429489603652800197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16672530324889755852808405 390762429489603652800197)
                  ·
                    rfl

theorem cell20_856133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 7].length) (baseStart_856133 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_856133 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_856133 prefixEnd_856133 := by exact prefixLift 856133
  have htrace : WordTrace (prefixWord ++ tailWord_856133) baseStart_856133 baseEnd_856133 := by
    simpa [prefixWord, tailWord_856133, baseEnd_856133] using wordTrace_append hprefix tailTrace_856133
  have hstable : (prefixWord ++ tailWord_856133).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856133).length < 2 ^ (prefixWord ++ tailWord_856133).sum := by decide
  have hdescent : baseEnd_856133 < baseStart_856133 := by decide
  rcases family_descends (prefixWord ++ tailWord_856133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856174 : List Nat := [4, 1, 2, 2, 1, 1, 4, 1, 4]
def baseStart_856174 : Nat := 118140960795 + 856174 * 2 ^ 59
def prefixEnd_856174 : Nat := 4983230072969 + 3 ^ 40 * 856174 * 2
def baseEnd_856174 : Nat := 390781143006789732433363

theorem tailTrace_856174 : CollatzResearch.WordTrace tailWord_856174 prefixEnd_856174 390781143006789732433363 := by
  unfold tailWord_856174
  simp only [CollatzResearch.WordTrace]
  refine ⟨3903403900029411965363947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20818154133490197148607717 3903403900029411965363947)
  ·
    refine ⟨5855105850044117948045921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3903403900029411965363947 5855105850044117948045921)
    ·
      refine ⟨4391329387533088461034441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5855105850044117948045921 4391329387533088461034441)
      ·
        refine ⟨3293497040649816345775831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4391329387533088461034441 3293497040649816345775831)
        ·
          refine ⟨4940245560974724518663747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3293497040649816345775831 4940245560974724518663747)
          ·
            refine ⟨7410368341462086777995621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4940245560974724518663747 7410368341462086777995621)
            ·
              refine ⟨1389444064024141270874179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7410368341462086777995621 1389444064024141270874179)
              ·
                refine ⟨2084166096036211906311269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1389444064024141270874179 2084166096036211906311269)
                ·
                  refine ⟨390781143006789732433363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2084166096036211906311269 390781143006789732433363)
                  ·
                    rfl

theorem cell20_856174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 4, 1, 4].length) (baseStart_856174 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_856174 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_856174 prefixEnd_856174 := by exact prefixLift 856174
  have htrace : WordTrace (prefixWord ++ tailWord_856174) baseStart_856174 baseEnd_856174 := by
    simpa [prefixWord, tailWord_856174, baseEnd_856174] using wordTrace_append hprefix tailTrace_856174
  have hstable : (prefixWord ++ tailWord_856174).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856174).length < 2 ^ (prefixWord ++ tailWord_856174).sum := by decide
  have hdescent : baseEnd_856174 < baseStart_856174 := by decide
  rcases family_descends (prefixWord ++ tailWord_856174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856195 : List Nat := [1, 1, 1, 3, 3, 3, 2, 2, 4]
def baseStart_856195 : Nat := 118140960795 + 856195 * 2 ^ 59
def prefixEnd_856195 : Nat := 4983230072969 + 3 ^ 40 * 856195 * 2
def baseEnd_856195 : Nat := 390790727979006992733277

theorem tailTrace_856195 : CollatzResearch.WordTrace tailWord_856195 prefixEnd_856195 390790727979006992733277 := by
  unfold tailWord_856195
  simp only [CollatzResearch.WordTrace]
  refine ⟨31227997133159216309426039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20818664755439477539617359 31227997133159216309426039)
  ·
    refine ⟨46841995699738824464139059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31227997133159216309426039 46841995699738824464139059)
    ·
      refine ⟨70262993549608236696208589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46841995699738824464139059 70262993549608236696208589)
      ·
        refine ⟨26348622581103088761078221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70262993549608236696208589 26348622581103088761078221)
        ·
          refine ⟨9880733467913658285404333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26348622581103088761078221 9880733467913658285404333)
          ·
            refine ⟨3705275050467621857026625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9880733467913658285404333 3705275050467621857026625)
            ·
              refine ⟨2778956287850716392769969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3705275050467621857026625 2778956287850716392769969)
              ·
                refine ⟨2084217215888037294577477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2778956287850716392769969 2084217215888037294577477)
                ·
                  refine ⟨390790727979006992733277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2084217215888037294577477 390790727979006992733277)
                  ·
                    rfl

theorem cell20_856195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 2, 4].length) (baseStart_856195 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_856195 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_856195 prefixEnd_856195 := by exact prefixLift 856195
  have htrace : WordTrace (prefixWord ++ tailWord_856195) baseStart_856195 baseEnd_856195 := by
    simpa [prefixWord, tailWord_856195, baseEnd_856195] using wordTrace_append hprefix tailTrace_856195
  have hstable : (prefixWord ++ tailWord_856195).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856195).length < 2 ^ (prefixWord ++ tailWord_856195).sum := by decide
  have hdescent : baseEnd_856195 < baseStart_856195 := by decide
  rcases family_descends (prefixWord ++ tailWord_856195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856229 : List Nat := [1, 3, 1, 2, 1, 3, 5, 2, 2]
def baseStart_856229 : Nat := 118140960795 + 856229 * 2 ^ 59
def prefixEnd_856229 : Nat := 4983230072969 + 3 ^ 40 * 856229 * 2
def baseEnd_856229 : Nat := 390806246505453985599805

theorem tailTrace_856229 : CollatzResearch.WordTrace tailWord_856229 prefixEnd_856229 390806246505453985599805 := by
  unfold tailWord_856229
  simp only [CollatzResearch.WordTrace]
  refine ⟨31229237215036040116163741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20819491476690693410775827 31229237215036040116163741)
  ·
    refine ⟨11710963955638515043561403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31229237215036040116163741 11710963955638515043561403)
    ·
      refine ⟨17566445933457772565342105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11710963955638515043561403 17566445933457772565342105)
      ·
        refine ⟨13174834450093329424006579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17566445933457772565342105 13174834450093329424006579)
        ·
          refine ⟨19762251675139994136009869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13174834450093329424006579 19762251675139994136009869)
          ·
            refine ⟨7410844378177497801003701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19762251675139994136009869 7410844378177497801003701)
            ·
              refine ⟨694766660454140418844097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7410844378177497801003701 694766660454140418844097)
              ·
                refine ⟨521074995340605314133073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 694766660454140418844097 521074995340605314133073)
                ·
                  refine ⟨390806246505453985599805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 521074995340605314133073 390806246505453985599805)
                  ·
                    rfl

theorem cell20_856229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 5, 2, 2].length) (baseStart_856229 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_856229 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_856229 prefixEnd_856229 := by exact prefixLift 856229
  have htrace : WordTrace (prefixWord ++ tailWord_856229) baseStart_856229 baseEnd_856229 := by
    simpa [prefixWord, tailWord_856229, baseEnd_856229] using wordTrace_append hprefix tailTrace_856229
  have hstable : (prefixWord ++ tailWord_856229).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856229).length < 2 ^ (prefixWord ++ tailWord_856229).sum := by decide
  have hdescent : baseEnd_856229 < baseStart_856229 := by decide
  rcases family_descends (prefixWord ++ tailWord_856229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856288 : List Nat := [2, 1, 1, 3, 1, 3, 3, 4, 2]
def baseStart_856288 : Nat := 118140960795 + 856288 * 2 ^ 59
def prefixEnd_856288 : Nat := 4983230072969 + 3 ^ 40 * 856288 * 2
def baseEnd_856288 : Nat := 390833175713112002632897

theorem tailTrace_856288 : CollatzResearch.WordTrace tailWord_856288 prefixEnd_856288 390833175713112002632897 := by
  unfold tailWord_856288
  simp only [CollatzResearch.WordTrace]
  refine ⟨15615694560911146596280759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20820926081214862128374345 15615694560911146596280759)
  ·
    refine ⟨23423541841366719894421139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15615694560911146596280759 23423541841366719894421139)
    ·
      refine ⟨35135312762050079841631709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23423541841366719894421139 35135312762050079841631709)
      ·
        refine ⟨13175742285768779940611891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35135312762050079841631709 13175742285768779940611891)
        ·
          refine ⟨19763613428653169910917837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13175742285768779940611891 19763613428653169910917837)
          ·
            refine ⟨7411355035744938716594189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19763613428653169910917837 7411355035744938716594189)
            ·
              refine ⟨2779258138404352018722821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7411355035744938716594189 2779258138404352018722821)
              ·
                refine ⟨521110900950816003510529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2779258138404352018722821 521110900950816003510529)
                ·
                  refine ⟨390833175713112002632897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 521110900950816003510529 390833175713112002632897)
                  ·
                    rfl

theorem cell20_856288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 4, 2].length) (baseStart_856288 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_856288 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_856288 prefixEnd_856288 := by exact prefixLift 856288
  have htrace : WordTrace (prefixWord ++ tailWord_856288) baseStart_856288 baseEnd_856288 := by
    simpa [prefixWord, tailWord_856288, baseEnd_856288] using wordTrace_append hprefix tailTrace_856288
  have hstable : (prefixWord ++ tailWord_856288).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856288).length < 2 ^ (prefixWord ++ tailWord_856288).sum := by decide
  have hdescent : baseEnd_856288 < baseStart_856288 := by decide
  rcases family_descends (prefixWord ++ tailWord_856288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856291 : List Nat := [1, 1, 1, 8, 2, 1, 1, 5]
def baseStart_856291 : Nat := 118140960795 + 856291 * 2 ^ 59
def prefixEnd_856291 : Nat := 4983230072969 + 3 ^ 40 * 856291 * 2
def baseEnd_856291 : Nat := 130278181664952441844295

theorem tailTrace_856291 : CollatzResearch.WordTrace tailWord_856291 prefixEnd_856291 130278181664952441844295 := by
  unfold tailWord_856291
  simp only [CollatzResearch.WordTrace]
  refine ⟨31231498540811424704920727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20820999027207616469947151 31231498540811424704920727)
  ·
    refine ⟨46847247811217137057381091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31231498540811424704920727 46847247811217137057381091)
    ·
      refine ⟨70270871716825705586071637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46847247811217137057381091 70270871716825705586071637)
      ·
        refine ⟨823486777931551237336777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 70270871716825705586071637 823486777931551237336777)
        ·
          refine ⟨617615083448663428002583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 823486777931551237336777 617615083448663428002583)
          ·
            refine ⟨926422625172995142003875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 617615083448663428002583 926422625172995142003875)
            ·
              refine ⟨1389633937759492713005813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 926422625172995142003875 1389633937759492713005813)
              ·
                refine ⟨130278181664952441844295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1389633937759492713005813 130278181664952441844295)
                ·
                  rfl

theorem cell20_856291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 1, 5].length) (baseStart_856291 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_856291 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_856291 prefixEnd_856291 := by exact prefixLift 856291
  have htrace : WordTrace (prefixWord ++ tailWord_856291) baseStart_856291 baseEnd_856291 := by
    simpa [prefixWord, tailWord_856291, baseEnd_856291] using wordTrace_append hprefix tailTrace_856291
  have hstable : (prefixWord ++ tailWord_856291).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856291).length < 2 ^ (prefixWord ++ tailWord_856291).sum := by decide
  have hdescent : baseEnd_856291 < baseStart_856291 := by decide
  rcases family_descends (prefixWord ++ tailWord_856291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856295 : List Nat := [1, 1, 5, 3, 1, 1, 3, 5]
def baseStart_856295 : Nat := 118140960795 + 856295 * 2 ^ 59
def prefixEnd_856295 : Nat := 4983230072969 + 3 ^ 40 * 856295 * 2
def baseEnd_856295 : Nat := 130278790234617029799845

theorem tailTrace_856295 : CollatzResearch.WordTrace tailWord_856295 prefixEnd_856295 130278790234617029799845 := by
  unfold tailWord_856295
  simp only [CollatzResearch.WordTrace]
  refine ⟨31231644432796933388066339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20821096288531288925377559 31231644432796933388066339)
  ·
    refine ⟨46847466649195400082099509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31231644432796933388066339 46847466649195400082099509)
    ·
      refine ⟨4391949998362068757696829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46847466649195400082099509 4391949998362068757696829)
      ·
        refine ⟨1646981249385775784136311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4391949998362068757696829 1646981249385775784136311)
        ·
          refine ⟨2470471874078663676204467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1646981249385775784136311 2470471874078663676204467)
          ·
            refine ⟨3705707811117995514306701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2470471874078663676204467 3705707811117995514306701)
            ·
              refine ⟨1389640429169248317865013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3705707811117995514306701 1389640429169248317865013)
              ·
                refine ⟨130278790234617029799845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1389640429169248317865013 130278790234617029799845)
                ·
                  rfl

theorem cell20_856295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 3, 5].length) (baseStart_856295 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_856295 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_856295 prefixEnd_856295 := by exact prefixLift 856295
  have htrace : WordTrace (prefixWord ++ tailWord_856295) baseStart_856295 baseEnd_856295 := by
    simpa [prefixWord, tailWord_856295, baseEnd_856295] using wordTrace_append hprefix tailTrace_856295
  have hstable : (prefixWord ++ tailWord_856295).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856295).length < 2 ^ (prefixWord ++ tailWord_856295).sum := by decide
  have hdescent : baseEnd_856295 < baseStart_856295 := by decide
  rcases family_descends (prefixWord ++ tailWord_856295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856322 : List Nat := [3, 4, 1, 1, 2, 2, 2, 3, 2]
def baseStart_856322 : Nat := 118140960795 + 856322 * 2 ^ 59
def prefixEnd_856322 : Nat := 4983230072969 + 3 ^ 40 * 856322 * 2
def baseEnd_856322 : Nat := 390848694239558995499425

theorem tailTrace_856322 : CollatzResearch.WordTrace tailWord_856322 prefixEnd_856322 390848694239558995499425 := by
  unfold tailWord_856322
  simp only [CollatzResearch.WordTrace]
  refine ⟨7808157300924779249824805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20821752802466077999532813 7808157300924779249824805)
  ·
    refine ⟨1464029493923396109342151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7808157300924779249824805 1464029493923396109342151)
    ·
      refine ⟨2196044240885094164013227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1464029493923396109342151 2196044240885094164013227)
      ·
        refine ⟨3294066361327641246019841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2196044240885094164013227 3294066361327641246019841)
        ·
          refine ⟨2470549770995730934514881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3294066361327641246019841 2470549770995730934514881)
          ·
            refine ⟨1852912328246798200886161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2470549770995730934514881 1852912328246798200886161)
            ·
              refine ⟨1389684246185098650664621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1852912328246798200886161 1389684246185098650664621)
              ·
                refine ⟨521131592319411993999233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1389684246185098650664621 521131592319411993999233)
                ·
                  refine ⟨390848694239558995499425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 521131592319411993999233 390848694239558995499425)
                  ·
                    rfl

theorem cell20_856322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 2, 3, 2].length) (baseStart_856322 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_856322 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_856322 prefixEnd_856322 := by exact prefixLift 856322
  have htrace : WordTrace (prefixWord ++ tailWord_856322) baseStart_856322 baseEnd_856322 := by
    simpa [prefixWord, tailWord_856322, baseEnd_856322] using wordTrace_append hprefix tailTrace_856322
  have hstable : (prefixWord ++ tailWord_856322).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856322).length < 2 ^ (prefixWord ++ tailWord_856322).sum := by decide
  have hdescent : baseEnd_856322 < baseStart_856322 := by decide
  rcases family_descends (prefixWord ++ tailWord_856322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856323 : List Nat := [1, 1, 1, 3, 2, 3, 2, 2, 5]
def baseStart_856323 : Nat := 118140960795 + 856323 * 2 ^ 59
def prefixEnd_856323 : Nat := 4983230072969 + 3 ^ 40 * 856323 * 2
def baseEnd_856323 : Nat := 390849150666807436466087

theorem tailTrace_856323 : CollatzResearch.WordTrace tailWord_856323 prefixEnd_856323 390849150666807436466087 := by
  unfold tailWord_856323
  simp only [CollatzResearch.WordTrace]
  refine ⟨31232665676695494170085623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20821777117796996113390415 31232665676695494170085623)
  ·
    refine ⟨46848998515043241255128435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31232665676695494170085623 46848998515043241255128435)
    ·
      refine ⟨70273497772564861882692653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46848998515043241255128435 70273497772564861882692653)
      ·
        refine ⟨26352561664711823206009745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70273497772564861882692653 26352561664711823206009745)
        ·
          refine ⟨19764421248533867404507309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26352561664711823206009745 19764421248533867404507309)
          ·
            refine ⟨7411657968200200276690241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19764421248533867404507309 7411657968200200276690241)
            ·
              refine ⟨5558743476150150207517681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7411657968200200276690241 5558743476150150207517681)
              ·
                refine ⟨4169057607112612655638261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5558743476150150207517681 4169057607112612655638261)
                ·
                  refine ⟨390849150666807436466087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4169057607112612655638261 390849150666807436466087)
                  ·
                    rfl

theorem cell20_856323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 2, 5].length) (baseStart_856323 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_856323 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_856323 prefixEnd_856323 := by exact prefixLift 856323
  have htrace : WordTrace (prefixWord ++ tailWord_856323) baseStart_856323 baseEnd_856323 := by
    simpa [prefixWord, tailWord_856323, baseEnd_856323] using wordTrace_append hprefix tailTrace_856323
  have hstable : (prefixWord ++ tailWord_856323).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856323).length < 2 ^ (prefixWord ++ tailWord_856323).sum := by decide
  have hdescent : baseEnd_856323 < baseStart_856323 := by decide
  rcases family_descends (prefixWord ++ tailWord_856323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856368 : List Nat := [2, 1, 1, 1, 2, 2, 2, 3, 6]
def baseStart_856368 : Nat := 118140960795 + 856368 * 2 ^ 59
def prefixEnd_856368 : Nat := 4983230072969 + 3 ^ 40 * 856368 * 2
def baseEnd_856368 : Nat := 390869689892987279965903

theorem tailTrace_856368 : CollatzResearch.WordTrace tailWord_856368 prefixEnd_856368 390869689892987279965903 := by
  unfold tailWord_856368
  simp only [CollatzResearch.WordTrace]
  refine ⟨15617153480766233427736879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20822871307688311236982505 15617153480766233427736879)
  ·
    refine ⟨23425730221149350141605319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15617153480766233427736879 23425730221149350141605319)
    ·
      refine ⟨35138595331724025212407979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23425730221149350141605319 35138595331724025212407979)
      ·
        refine ⟨52707892997586037818611969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35138595331724025212407979 52707892997586037818611969)
        ·
          refine ⟨39530919748189528363958977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52707892997586037818611969 39530919748189528363958977)
          ·
            refine ⟨29648189811142146272969233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39530919748189528363958977 29648189811142146272969233)
            ·
              refine ⟨22236142358356609704726925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29648189811142146272969233 22236142358356609704726925)
              ·
                refine ⟨8338553384383728639272597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22236142358356609704726925 8338553384383728639272597)
                ·
                  refine ⟨390869689892987279965903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8338553384383728639272597 390869689892987279965903)
                  ·
                    rfl

theorem cell20_856368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 3, 6].length) (baseStart_856368 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_856368 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_856368 prefixEnd_856368 := by exact prefixLift 856368
  have htrace : WordTrace (prefixWord ++ tailWord_856368) baseStart_856368 baseEnd_856368 := by
    simpa [prefixWord, tailWord_856368, baseEnd_856368] using wordTrace_append hprefix tailTrace_856368
  have hstable : (prefixWord ++ tailWord_856368).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856368).length < 2 ^ (prefixWord ++ tailWord_856368).sum := by decide
  have hdescent : baseEnd_856368 < baseStart_856368 := by decide
  rcases family_descends (prefixWord ++ tailWord_856368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856388 : List Nat := [2, 3, 4, 1, 2, 2, 6]
def baseStart_856388 : Nat := 118140960795 + 856388 * 2 ^ 59
def prefixEnd_856388 : Nat := 4983230072969 + 3 ^ 40 * 856388 * 2
def baseEnd_856388 : Nat := 43430979826439566588795

theorem tailTrace_856388 : CollatzResearch.WordTrace tailWord_856388 prefixEnd_856388 43430979826439566588795 := by
  unfold tailWord_856388
  simp only [CollatzResearch.WordTrace]
  refine ⟨15617518210730005135600909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20823357614306673514134545 15617518210730005135600909)
  ·
    refine ⟨5856569329023751925850341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15617518210730005135600909 5856569329023751925850341)
    ·
      refine ⟨1098106749191953486096939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5856569329023751925850341 1098106749191953486096939)
      ·
        refine ⟨1647160123787930229145409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1098106749191953486096939 1647160123787930229145409)
        ·
          refine ⟨1235370092840947671859057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1647160123787930229145409 1235370092840947671859057)
          ·
            refine ⟨926527569630710753894293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1235370092840947671859057 926527569630710753894293)
            ·
              refine ⟨43430979826439566588795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 926527569630710753894293 43430979826439566588795)
              ·
                rfl

theorem cell20_856388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 2, 6].length) (baseStart_856388 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_856388 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_856388 prefixEnd_856388 := by exact prefixLift 856388
  have htrace : WordTrace (prefixWord ++ tailWord_856388) baseStart_856388 baseEnd_856388 := by
    simpa [prefixWord, tailWord_856388, baseEnd_856388] using wordTrace_append hprefix tailTrace_856388
  have hstable : (prefixWord ++ tailWord_856388).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856388).length < 2 ^ (prefixWord ++ tailWord_856388).sum := by decide
  have hdescent : baseEnd_856388 < baseStart_856388 := by decide
  rcases family_descends (prefixWord ++ tailWord_856388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856402 : List Nat := [3, 2, 2, 1, 1, 1, 2, 6, 2]
def baseStart_856402 : Nat := 118140960795 + 856402 * 2 ^ 59
def prefixEnd_856402 : Nat := 4983230072969 + 3 ^ 40 * 856402 * 2
def baseEnd_856402 : Nat := 390885208419434272832431

theorem tailTrace_856402 : CollatzResearch.WordTrace tailWord_856402 prefixEnd_856402 390885208419434272832431 := by
  unfold tailWord_856402
  simp only [CollatzResearch.WordTrace]
  refine ⟨7808886760852322665552865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20823698028939527108140973 7808886760852322665552865)
  ·
    refine ⟨5856665070639241999164649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7808886760852322665552865 5856665070639241999164649)
    ·
      refine ⟨4392498802979431499373487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5856665070639241999164649 4392498802979431499373487)
      ·
        refine ⟨6588748204469147249060231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4392498802979431499373487 6588748204469147249060231)
        ·
          refine ⟨9883122306703720873590347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6588748204469147249060231 9883122306703720873590347)
          ·
            refine ⟨14824683460055581310385521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9883122306703720873590347 14824683460055581310385521)
            ·
              refine ⟨11118512595041685982789141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14824683460055581310385521 11118512595041685982789141)
              ·
                refine ⟨521180277892579030443241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11118512595041685982789141 521180277892579030443241)
                ·
                  refine ⟨390885208419434272832431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 521180277892579030443241 390885208419434272832431)
                  ·
                    rfl

theorem cell20_856402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 6, 2].length) (baseStart_856402 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_856402 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_856402 prefixEnd_856402 := by exact prefixLift 856402
  have htrace : WordTrace (prefixWord ++ tailWord_856402) baseStart_856402 baseEnd_856402 := by
    simpa [prefixWord, tailWord_856402, baseEnd_856402] using wordTrace_append hprefix tailTrace_856402
  have hstable : (prefixWord ++ tailWord_856402).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856402).length < 2 ^ (prefixWord ++ tailWord_856402).sum := by decide
  have hdescent : baseEnd_856402 < baseStart_856402 := by decide
  rcases family_descends (prefixWord ++ tailWord_856402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856412 : List Nat := [2, 2, 4, 3, 1, 1, 1, 3, 3]
def baseStart_856412 : Nat := 118140960795 + 856412 * 2 ^ 59
def prefixEnd_856412 : Nat := 4983230072969 + 3 ^ 40 * 856412 * 2
def baseEnd_856412 : Nat := 390889772691918682499057

theorem tailTrace_856412 : CollatzResearch.WordTrace tailWord_856412 prefixEnd_856412 390889772691918682499057 := by
  unfold tailWord_856412
  simp only [CollatzResearch.WordTrace]
  refine ⟨15617955886686531185037745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20823941182248708246716993 15617955886686531185037745)
  ·
    refine ⟨11713466915014898388778309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15617955886686531185037745 11713466915014898388778309)
    ·
      refine ⟨2196275046565293447895933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11713466915014898388778309 2196275046565293447895933)
      ·
        refine ⟨823603142461985042960975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2196275046565293447895933 823603142461985042960975)
        ·
          refine ⟨1235404713692977564441463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 823603142461985042960975 1235404713692977564441463)
          ·
            refine ⟨1853107070539466346662195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1235404713692977564441463 1853107070539466346662195)
            ·
              refine ⟨2779660605809199519993293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1853107070539466346662195 2779660605809199519993293)
              ·
                refine ⟨1042372727178449819997485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2779660605809199519993293 1042372727178449819997485)
                ·
                  refine ⟨390889772691918682499057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1042372727178449819997485 390889772691918682499057)
                  ·
                    rfl

theorem cell20_856412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 3, 3].length) (baseStart_856412 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_856412 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_856412 prefixEnd_856412 := by exact prefixLift 856412
  have htrace : WordTrace (prefixWord ++ tailWord_856412) baseStart_856412 baseEnd_856412 := by
    simpa [prefixWord, tailWord_856412, baseEnd_856412] using wordTrace_append hprefix tailTrace_856412
  have hstable : (prefixWord ++ tailWord_856412).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856412).length < 2 ^ (prefixWord ++ tailWord_856412).sum := by decide
  have hdescent : baseEnd_856412 < baseStart_856412 := by decide
  rcases family_descends (prefixWord ++ tailWord_856412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856444 : List Nat := [2, 2, 2, 1, 1, 1, 2, 1, 8]
def baseStart_856444 : Nat := 118140960795 + 856444 * 2 ^ 59
def prefixEnd_856444 : Nat := 4983230072969 + 3 ^ 40 * 856444 * 2
def baseEnd_856444 : Nat := 390904378363868793432259

theorem tailTrace_856444 : CollatzResearch.WordTrace tailWord_856444 prefixEnd_856444 390904378363868793432259 := by
  unfold tailWord_856444
  simp only [CollatzResearch.WordTrace]
  refine ⟨15618539454628565917620193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20824719272838087890160257 15618539454628565917620193)
  ·
    refine ⟨11713904590971424438215145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15618539454628565917620193 11713904590971424438215145)
    ·
      refine ⟨8785428443228568328661359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11713904590971424438215145 8785428443228568328661359)
      ·
        refine ⟨13178142664842852492992039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8785428443228568328661359 13178142664842852492992039)
        ·
          refine ⟨19767213997264278739488059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13178142664842852492992039 19767213997264278739488059)
          ·
            refine ⟨29650820995896418109232089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19767213997264278739488059 29650820995896418109232089)
            ·
              refine ⟨22238115746922313581924067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29650820995896418109232089 22238115746922313581924067)
              ·
                refine ⟨33357173620383470372886101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22238115746922313581924067 33357173620383470372886101)
                ·
                  refine ⟨390904378363868793432259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33357173620383470372886101 390904378363868793432259)
                  ·
                    rfl

theorem cell20_856444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 8].length) (baseStart_856444 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_856444 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_856444 prefixEnd_856444 := by exact prefixLift 856444
  have htrace : WordTrace (prefixWord ++ tailWord_856444) baseStart_856444 baseEnd_856444 := by
    simpa [prefixWord, tailWord_856444, baseEnd_856444] using wordTrace_append hprefix tailTrace_856444
  have hstable : (prefixWord ++ tailWord_856444).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856444).length < 2 ^ (prefixWord ++ tailWord_856444).sum := by decide
  have hdescent : baseEnd_856444 < baseStart_856444 := by decide
  rcases family_descends (prefixWord ++ tailWord_856444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856451 : List Nat := [1, 1, 1, 3, 14]
def baseStart_856451 : Nat := 118140960795 + 856451 * 2 ^ 59
def prefixEnd_856451 : Nat := 4983230072969 + 3 ^ 40 * 856451 * 2
def baseEnd_856451 : Nat := 4826019424130961483937

theorem tailTrace_856451 : CollatzResearch.WordTrace tailWord_856451 prefixEnd_856451 4826019424130961483937 := by
  unfold tailWord_856451
  simp only [CollatzResearch.WordTrace]
  refine ⟨31237334220231772030745207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20824889480154514687163471 31237334220231772030745207)
  ·
    refine ⟨46856001330347658046117811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31237334220231772030745207 46856001330347658046117811)
    ·
      refine ⟨70284001995521487069176717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46856001330347658046117811 70284001995521487069176717)
      ·
        refine ⟨26356500748320557650941269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70284001995521487069176717 26356500748320557650941269)
        ·
          refine ⟨4826019424130961483937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 26356500748320557650941269 4826019424130961483937)
          ·
            rfl

theorem cell20_856451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 14].length) (baseStart_856451 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_856451 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_856451 prefixEnd_856451 := by exact prefixLift 856451
  have htrace : WordTrace (prefixWord ++ tailWord_856451) baseStart_856451 baseEnd_856451 := by
    simpa [prefixWord, tailWord_856451, baseEnd_856451] using wordTrace_append hprefix tailTrace_856451
  have hstable : (prefixWord ++ tailWord_856451).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856451).length < 2 ^ (prefixWord ++ tailWord_856451).sum := by decide
  have hdescent : baseEnd_856451 < baseStart_856451 := by decide
  rcases family_descends (prefixWord ++ tailWord_856451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856457 : List Nat := [1, 2, 1, 1, 6, 1, 4, 2, 2]
def baseStart_856457 : Nat := 118140960795 + 856457 * 2 ^ 59
def prefixEnd_856457 : Nat := 4983230072969 + 3 ^ 40 * 856457 * 2
def baseEnd_856457 : Nat := 390910311918098525998873

theorem tailTrace_856457 : CollatzResearch.WordTrace tailWord_856457 prefixEnd_856457 390910311918098525998873 := by
  unfold tailWord_856457
  simp only [CollatzResearch.WordTrace]
  refine ⟨31237553058210035055463625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20825035372140023370309083 31237553058210035055463625)
  ·
    refine ⟨23428164793657526291597719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31237553058210035055463625 23428164793657526291597719)
    ·
      refine ⟨35142247190486289437396579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23428164793657526291597719 35142247190486289437396579)
      ·
        refine ⟨52713370785729434156094869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35142247190486289437396579 52713370785729434156094869)
        ·
          refine ⟨2470939255581067226066947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 52713370785729434156094869 2470939255581067226066947)
          ·
            refine ⟨3706408883371600839100421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2470939255581067226066947 3706408883371600839100421)
            ·
              refine ⟨694951665632175157331329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3706408883371600839100421 694951665632175157331329)
              ·
                refine ⟨521213749224131367998497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 694951665632175157331329 521213749224131367998497)
                ·
                  refine ⟨390910311918098525998873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 521213749224131367998497 390910311918098525998873)
                  ·
                    rfl

theorem cell20_856457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 4, 2, 2].length) (baseStart_856457 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_856457 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_856457 prefixEnd_856457 := by exact prefixLift 856457
  have htrace : WordTrace (prefixWord ++ tailWord_856457) baseStart_856457 baseEnd_856457 := by
    simpa [prefixWord, tailWord_856457, baseEnd_856457] using wordTrace_append hprefix tailTrace_856457
  have hstable : (prefixWord ++ tailWord_856457).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856457).length < 2 ^ (prefixWord ++ tailWord_856457).sum := by decide
  have hdescent : baseEnd_856457 < baseStart_856457 := by decide
  rcases family_descends (prefixWord ++ tailWord_856457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856478 : List Nat := [4, 3, 1, 2, 1, 1, 1, 1, 6]
def baseStart_856478 : Nat := 118140960795 + 856478 * 2 ^ 59
def prefixEnd_856478 : Nat := 4983230072969 + 3 ^ 40 * 856478 * 2
def baseEnd_856478 : Nat := 390919896890315786298787

theorem tailTrace_856478 : CollatzResearch.WordTrace tailWord_856478 prefixEnd_856478 390919896890315786298787 := by
  unfold tailWord_856478
  simp only [CollatzResearch.WordTrace]
  refine ⟨3904789873891744455247261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20825545994089303761318725 3904789873891744455247261)
  ·
    refine ⟨1464296202709404170717723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3904789873891744455247261 1464296202709404170717723)
    ·
      refine ⟨2196444304064106256076585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1464296202709404170717723 2196444304064106256076585)
      ·
        refine ⟨1647333228048079692057439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2196444304064106256076585 1647333228048079692057439)
        ·
          refine ⟨2470999842072119538086159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1647333228048079692057439 2470999842072119538086159)
          ·
            refine ⟨3706499763108179307129239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2470999842072119538086159 3706499763108179307129239)
            ·
              refine ⟨5559749644662268960693859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3706499763108179307129239 5559749644662268960693859)
              ·
                refine ⟨8339624466993403441040789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5559749644662268960693859 8339624466993403441040789)
                ·
                  refine ⟨390919896890315786298787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8339624466993403441040789 390919896890315786298787)
                  ·
                    rfl

theorem cell20_856478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_856478 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_856478 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_856478 prefixEnd_856478 := by exact prefixLift 856478
  have htrace : WordTrace (prefixWord ++ tailWord_856478) baseStart_856478 baseEnd_856478 := by
    simpa [prefixWord, tailWord_856478, baseEnd_856478] using wordTrace_append hprefix tailTrace_856478
  have hstable : (prefixWord ++ tailWord_856478).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856478).length < 2 ^ (prefixWord ++ tailWord_856478).sum := by decide
  have hdescent : baseEnd_856478 < baseStart_856478 := by decide
  rcases family_descends (prefixWord ++ tailWord_856478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856489 : List Nat := [1, 2, 1, 1, 1, 1, 3, 10]
def baseStart_856489 : Nat := 118140960795 + 856489 * 2 ^ 59
def prefixEnd_856489 : Nat := 4983230072969 + 3 ^ 40 * 856489 * 2
def baseEnd_856489 : Nat := 130308305863349545644025

theorem tailTrace_856489 : CollatzResearch.WordTrace tailWord_856489 prefixEnd_856489 130308305863349545644025 := by
  unfold tailWord_856489
  simp only [CollatzResearch.WordTrace]
  refine ⟨31238720194094104520628521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20825813462729403013752347 31238720194094104520628521)
  ·
    refine ⟨23429040145570578390471391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31238720194094104520628521 23429040145570578390471391)
    ·
      refine ⟨35143560218355867585707087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23429040145570578390471391 35143560218355867585707087)
      ·
        refine ⟨52715340327533801378560631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35143560218355867585707087 52715340327533801378560631)
        ·
          refine ⟨79073010491300702067840947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52715340327533801378560631 79073010491300702067840947)
          ·
            refine ⟨118609515736951053101761421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79073010491300702067840947 118609515736951053101761421)
            ·
              refine ⟨44478568401356644913160533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118609515736951053101761421 44478568401356644913160533)
              ·
                refine ⟨130308305863349545644025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 44478568401356644913160533 130308305863349545644025)
                ·
                  rfl

theorem cell20_856489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 10].length) (baseStart_856489 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_856489 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_856489 prefixEnd_856489 := by exact prefixLift 856489
  have htrace : WordTrace (prefixWord ++ tailWord_856489) baseStart_856489 baseEnd_856489 := by
    simpa [prefixWord, tailWord_856489, baseEnd_856489] using wordTrace_append hprefix tailTrace_856489
  have hstable : (prefixWord ++ tailWord_856489).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856489).length < 2 ^ (prefixWord ++ tailWord_856489).sum := by decide
  have hdescent : baseEnd_856489 < baseStart_856489 := by decide
  rcases family_descends (prefixWord ++ tailWord_856489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856509 : List Nat := [1, 4, 1, 2, 2, 4, 1, 2, 3]
def baseStart_856509 : Nat := 118140960795 + 856509 * 2 ^ 59
def prefixEnd_856509 : Nat := 4983230072969 + 3 ^ 40 * 856509 * 2
def baseEnd_856509 : Nat := 390934046135017456265327

theorem tailTrace_856509 : CollatzResearch.WordTrace tailWord_856509 prefixEnd_856509 390934046135017456265327 := by
  unfold tailWord_856509
  simp only [CollatzResearch.WordTrace]
  refine ⟨31239449654021647936356581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20826299769347765290904387 31239449654021647936356581)
  ·
    refine ⟨5857396810129058988066859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31239449654021647936356581 5857396810129058988066859)
    ·
      refine ⟨8786095215193588482100289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5857396810129058988066859 8786095215193588482100289)
      ·
        refine ⟨6589571411395191361575217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8786095215193588482100289 6589571411395191361575217)
        ·
          refine ⟨4942178558546393521181413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6589571411395191361575217 4942178558546393521181413)
          ·
            refine ⟨926658479727448785221515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4942178558546393521181413 926658479727448785221515)
            ·
              refine ⟨1389987719591173177832273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 926658479727448785221515 1389987719591173177832273)
              ·
                refine ⟨1042490789693379883374205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1389987719591173177832273 1042490789693379883374205)
                ·
                  refine ⟨390934046135017456265327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1042490789693379883374205 390934046135017456265327)
                  ·
                    rfl

theorem cell20_856509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 1, 2, 3].length) (baseStart_856509 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_856509 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_856509 prefixEnd_856509 := by exact prefixLift 856509
  have htrace : WordTrace (prefixWord ++ tailWord_856509) baseStart_856509 baseEnd_856509 := by
    simpa [prefixWord, tailWord_856509, baseEnd_856509] using wordTrace_append hprefix tailTrace_856509
  have hstable : (prefixWord ++ tailWord_856509).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856509).length < 2 ^ (prefixWord ++ tailWord_856509).sum := by decide
  have hdescent : baseEnd_856509 < baseStart_856509 := by decide
  rcases family_descends (prefixWord ++ tailWord_856509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856527 : List Nat := [1, 1, 2, 1, 1, 4, 1, 9]
def baseStart_856527 : Nat := 118140960795 + 856527 * 2 ^ 59
def prefixEnd_856527 : Nat := 4983230072969 + 3 ^ 40 * 856527 * 2
def baseEnd_856527 : Nat := 130314087275163131221751

theorem tailTrace_856527 : CollatzResearch.WordTrace tailWord_856527 prefixEnd_856527 130314087275163131221751 := by
  unfold tailWord_856527
  simp only [CollatzResearch.WordTrace]
  refine ⟨31240106167956437010511835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20826737445304291340341223 31240106167956437010511835)
  ·
    refine ⟨46860159251934655515767753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31240106167956437010511835 46860159251934655515767753)
    ·
      refine ⟨35145119438950991636825815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46860159251934655515767753 35145119438950991636825815)
      ·
        refine ⟨52717679158426487455238723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35145119438950991636825815 52717679158426487455238723)
        ·
          refine ⟨79076518737639731182858085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52717679158426487455238723 79076518737639731182858085)
          ·
            refine ⟨14826847263307449596785891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79076518737639731182858085 14826847263307449596785891)
            ·
              refine ⟨22240270894961174395178837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14826847263307449596785891 22240270894961174395178837)
              ·
                refine ⟨130314087275163131221751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22240270894961174395178837 130314087275163131221751)
                ·
                  rfl

theorem cell20_856527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 9].length) (baseStart_856527 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_856527 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_856527 prefixEnd_856527 := by exact prefixLift 856527
  have htrace : WordTrace (prefixWord ++ tailWord_856527) baseStart_856527 baseEnd_856527 := by
    simpa [prefixWord, tailWord_856527, baseEnd_856527] using wordTrace_append hprefix tailTrace_856527
  have hstable : (prefixWord ++ tailWord_856527).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856527).length < 2 ^ (prefixWord ++ tailWord_856527).sum := by decide
  have hdescent : baseEnd_856527 < baseStart_856527 := by decide
  rcases family_descends (prefixWord ++ tailWord_856527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856546 : List Nat := [3, 3, 3, 2, 2, 1, 1, 3, 2]
def baseStart_856546 : Nat := 118140960795 + 856546 * 2 ^ 59
def prefixEnd_856546 : Nat := 4983230072969 + 3 ^ 40 * 856546 * 2
def baseEnd_856546 : Nat := 390950933943209772031843

theorem tailTrace_856546 : CollatzResearch.WordTrace tailWord_856546 prefixEnd_856546 390950933943209772031843 := by
  unfold tailWord_856546
  simp only [CollatzResearch.WordTrace]
  refine ⟨7810199788721900813863373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20827199436591735503635661 7810199788721900813863373)
  ·
    refine ⟨2928824920770712805198765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7810199788721900813863373 2928824920770712805198765)
    ·
      refine ⟨1098309345289017301949537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2928824920770712805198765 1098309345289017301949537)
      ·
        refine ⟨823732008966762976462153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1098309345289017301949537 823732008966762976462153)
        ·
          refine ⟨617799006725072232346615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 823732008966762976462153 617799006725072232346615)
          ·
            refine ⟨926698510087608348519923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 617799006725072232346615 926698510087608348519923)
            ·
              refine ⟨1390047765131412522779885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 926698510087608348519923 1390047765131412522779885)
              ·
                refine ⟨521267911924279696042457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1390047765131412522779885 521267911924279696042457)
                ·
                  refine ⟨390950933943209772031843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 521267911924279696042457 390950933943209772031843)
                  ·
                    rfl

theorem cell20_856546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 1, 3, 2].length) (baseStart_856546 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_856546 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_856546 prefixEnd_856546 := by exact prefixLift 856546
  have htrace : WordTrace (prefixWord ++ tailWord_856546) baseStart_856546 baseEnd_856546 := by
    simpa [prefixWord, tailWord_856546, baseEnd_856546] using wordTrace_append hprefix tailTrace_856546
  have hstable : (prefixWord ++ tailWord_856546).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856546).length < 2 ^ (prefixWord ++ tailWord_856546).sum := by decide
  have hdescent : baseEnd_856546 < baseStart_856546 := by decide
  rcases family_descends (prefixWord ++ tailWord_856546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856551 : List Nat := [1, 1, 5, 2, 1, 1, 1, 1, 7]
def baseStart_856551 : Nat := 118140960795 + 856551 * 2 ^ 59
def prefixEnd_856551 : Nat := 4983230072969 + 3 ^ 40 * 856551 * 2
def baseEnd_856551 : Nat := 390953216079451976865155

theorem tailTrace_856551 : CollatzResearch.WordTrace tailWord_856551 prefixEnd_856551 390953216079451976865155 := by
  unfold tailWord_856551
  simp only [CollatzResearch.WordTrace]
  refine ⟨31240981519869489109385507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20827321013246326072923671 31240981519869489109385507)
  ·
    refine ⟨46861472279804233664078261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31240981519869489109385507 46861472279804233664078261)
    ·
      refine ⟨4393263026231646906007337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46861472279804233664078261 4393263026231646906007337)
      ·
        refine ⟨3294947269673735179505503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4393263026231646906007337 3294947269673735179505503)
        ·
          refine ⟨4942420904510602769258255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3294947269673735179505503 4942420904510602769258255)
          ·
            refine ⟨7413631356765904153887383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4942420904510602769258255 7413631356765904153887383)
            ·
              refine ⟨11120447035148856230831075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7413631356765904153887383 11120447035148856230831075)
              ·
                refine ⟨16680670552723284346246613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11120447035148856230831075 16680670552723284346246613)
                ·
                  refine ⟨390953216079451976865155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16680670552723284346246613 390953216079451976865155)
                  ·
                    rfl

theorem cell20_856551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 7].length) (baseStart_856551 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_856551 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_856551 prefixEnd_856551 := by exact prefixLift 856551
  have htrace : WordTrace (prefixWord ++ tailWord_856551) baseStart_856551 baseEnd_856551 := by
    simpa [prefixWord, tailWord_856551, baseEnd_856551] using wordTrace_append hprefix tailTrace_856551
  have hstable : (prefixWord ++ tailWord_856551).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856551).length < 2 ^ (prefixWord ++ tailWord_856551).sum := by decide
  have hdescent : baseEnd_856551 < baseStart_856551 := by decide
  rcases family_descends (prefixWord ++ tailWord_856551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856578 : List Nat := [3, 4, 1, 2, 2, 1, 2, 5]
def baseStart_856578 : Nat := 118140960795 + 856578 * 2 ^ 59
def prefixEnd_856578 : Nat := 4983230072969 + 3 ^ 40 * 856578 * 2
def baseEnd_856578 : Nat := 130321846538386627655015

theorem tailTrace_856578 : CollatzResearch.WordTrace tailWord_856578 prefixEnd_856578 130321846538386627655015 := by
  unfold tailWord_856578
  simp only [CollatzResearch.WordTrace]
  refine ⟨7810491572692918180154597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20827977527181115147078925 7810491572692918180154597)
  ·
    refine ⟨1464467169879922158778987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7810491572692918180154597 1464467169879922158778987)
    ·
      refine ⟨2196700754819883238168481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1464467169879922158778987 2196700754819883238168481)
      ·
        refine ⟨1647525566114912428626361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2196700754819883238168481 1647525566114912428626361)
        ·
          refine ⟨1235644174586184321469771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1647525566114912428626361 1235644174586184321469771)
          ·
            refine ⟨1853466261879276482204657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1235644174586184321469771 1853466261879276482204657)
            ·
              refine ⟨1390099696409457361653493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1853466261879276482204657 1390099696409457361653493)
              ·
                refine ⟨130321846538386627655015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1390099696409457361653493 130321846538386627655015)
                ·
                  rfl

theorem cell20_856578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 2, 5].length) (baseStart_856578 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_856578 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_856578 prefixEnd_856578 := by exact prefixLift 856578
  have htrace : WordTrace (prefixWord ++ tailWord_856578) baseStart_856578 baseEnd_856578 := by
    simpa [prefixWord, tailWord_856578, baseEnd_856578] using wordTrace_append hprefix tailTrace_856578
  have hstable : (prefixWord ++ tailWord_856578).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856578).length < 2 ^ (prefixWord ++ tailWord_856578).sum := by decide
  have hdescent : baseEnd_856578 < baseStart_856578 := by decide
  rcases family_descends (prefixWord ++ tailWord_856578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856637 : List Nat := [1, 4, 1, 3, 2, 3, 1, 5]
def baseStart_856637 : Nat := 118140960795 + 856637 * 2 ^ 59
def prefixEnd_856637 : Nat := 4983230072969 + 3 ^ 40 * 856637 * 2
def baseEnd_856637 : Nat := 130330822940939299999379

theorem tailTrace_856637 : CollatzResearch.WordTrace tailWord_856637 prefixEnd_856637 130330822940939299999379 := by
  unfold tailWord_856637
  simp only [CollatzResearch.WordTrace]
  refine ⟨31244118197557925797016165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20829412131705283864677443 31244118197557925797016165)
  ·
    refine ⟨5858272162042111086940531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31244118197557925797016165 5858272162042111086940531)
    ·
      refine ⟨8787408243063166630410797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5858272162042111086940531 8787408243063166630410797)
      ·
        refine ⟨3295278091148687486404049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8787408243063166630410797 3295278091148687486404049)
        ·
          refine ⟨2471458568361515614803037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3295278091148687486404049 2471458568361515614803037)
          ·
            refine ⟨926796963135568355551139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2471458568361515614803037 926796963135568355551139)
            ·
              refine ⟨1390195444703352533326709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 926796963135568355551139 1390195444703352533326709)
              ·
                refine ⟨130330822940939299999379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1390195444703352533326709 130330822940939299999379)
                ·
                  rfl

theorem cell20_856637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 1, 5].length) (baseStart_856637 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_856637 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_856637 prefixEnd_856637 := by exact prefixLift 856637
  have htrace : WordTrace (prefixWord ++ tailWord_856637) baseStart_856637 baseEnd_856637 := by
    simpa [prefixWord, tailWord_856637, baseEnd_856637] using wordTrace_append hprefix tailTrace_856637
  have hstable : (prefixWord ++ tailWord_856637).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856637).length < 2 ^ (prefixWord ++ tailWord_856637).sum := by decide
  have hdescent : baseEnd_856637 < baseStart_856637 := by decide
  rcases family_descends (prefixWord ++ tailWord_856637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856730 : List Nat := [3, 1, 1, 6, 2, 1, 6]
def baseStart_856730 : Nat := 118140960795 + 856730 * 2 ^ 59
def prefixEnd_856730 : Nat := 4983230072969 + 3 ^ 40 * 856730 * 2
def baseEnd_856730 : Nat := 43448324061880323321973

theorem tailTrace_856730 : CollatzResearch.WordTrace tailWord_856730 prefixEnd_856730 43448324061880323321973 := by
  unfold tailWord_856730
  simp only [CollatzResearch.WordTrace]
  refine ⟨7811877546555250670037911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20831673457480668453434429 7811877546555250670037911)
  ·
    refine ⟨11717816319832876005056867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7811877546555250670037911 11717816319832876005056867)
    ·
      refine ⟨17576724479749314007585301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11717816319832876005056867 17576724479749314007585301)
      ·
        refine ⟨823908959988249094105561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 17576724479749314007585301 823908959988249094105561)
        ·
          refine ⟨617931719991186820579171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 823908959988249094105561 617931719991186820579171)
          ·
            refine ⟨926897579986780230868757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 617931719991186820579171 926897579986780230868757)
            ·
              refine ⟨43448324061880323321973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 926897579986780230868757 43448324061880323321973)
              ·
                rfl

theorem cell20_856730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 6].length) (baseStart_856730 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_856730 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_856730 prefixEnd_856730 := by exact prefixLift 856730
  have htrace : WordTrace (prefixWord ++ tailWord_856730) baseStart_856730 baseEnd_856730 := by
    simpa [prefixWord, tailWord_856730, baseEnd_856730] using wordTrace_append hprefix tailTrace_856730
  have hstable : (prefixWord ++ tailWord_856730).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856730).length < 2 ^ (prefixWord ++ tailWord_856730).sum := by decide
  have hdescent : baseEnd_856730 < baseStart_856730 := by decide
  rcases family_descends (prefixWord ++ tailWord_856730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856741 : List Nat := [1, 3, 1, 2, 1, 2, 1, 6, 3]
def baseStart_856741 : Nat := 118140960795 + 856741 * 2 ^ 59
def prefixEnd_856741 : Nat := 4983230072969 + 3 ^ 40 * 856741 * 2
def baseEnd_856741 : Nat := 391039937256655760531045

theorem tailTrace_856741 : CollatzResearch.WordTrace tailWord_856741 prefixEnd_856741 391039937256655760531045 := by
  unfold tailWord_856741
  simp only [CollatzResearch.WordTrace]
  refine ⟨31247911389181151558802077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20831940926120767705868051 31247911389181151558802077)
  ·
    refine ⟨11717966770942931834550779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31247911389181151558802077 11717966770942931834550779)
    ·
      refine ⟨17576950156414397751826169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11717966770942931834550779 17576950156414397751826169)
      ·
        refine ⟨13182712617310798313869627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17576950156414397751826169 13182712617310798313869627)
        ·
          refine ⟨19774068925966197470804441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13182712617310798313869627 19774068925966197470804441)
          ·
            refine ⟨14830551694474648103103331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19774068925966197470804441 14830551694474648103103331)
            ·
              refine ⟨22245827541711972154654997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14830551694474648103103331 22245827541711972154654997)
              ·
                refine ⟨1042773166017748694749453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 22245827541711972154654997 1042773166017748694749453)
                ·
                  refine ⟨391039937256655760531045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1042773166017748694749453 391039937256655760531045)
                  ·
                    rfl

theorem cell20_856741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 6, 3].length) (baseStart_856741 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_856741 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_856741 prefixEnd_856741 := by exact prefixLift 856741
  have htrace : WordTrace (prefixWord ++ tailWord_856741) baseStart_856741 baseEnd_856741 := by
    simpa [prefixWord, tailWord_856741, baseEnd_856741] using wordTrace_append hprefix tailTrace_856741
  have hstable : (prefixWord ++ tailWord_856741).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856741).length < 2 ^ (prefixWord ++ tailWord_856741).sum := by decide
  have hdescent : baseEnd_856741 < baseStart_856741 := by decide
  rcases family_descends (prefixWord ++ tailWord_856741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856755 : List Nat := [1, 1, 1, 2, 3, 4, 1, 7]
def baseStart_856755 : Nat := 118140960795 + 856755 * 2 ^ 59
def prefixEnd_856755 : Nat := 4983230072969 + 3 ^ 40 * 856755 * 2
def baseEnd_856755 : Nat := 130348775746044644688107

theorem tailTrace_856755 : CollatzResearch.WordTrace tailWord_856755 prefixEnd_856755 130348775746044644688107 := by
  unfold tailWord_856755
  simp only [CollatzResearch.WordTrace]
  refine ⟨31248422011130431949811719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20832281340753621299874479 31248422011130431949811719)
  ·
    refine ⟨46872633016695647924717579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31248422011130431949811719 46872633016695647924717579)
    ·
      refine ⟨70308949525043471887076369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46872633016695647924717579 70308949525043471887076369)
      ·
        refine ⟨52731712143782603915307277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70308949525043471887076369 52731712143782603915307277)
        ·
          refine ⟨19774392053918476468240229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52731712143782603915307277 19774392053918476468240229)
          ·
            refine ⟨3707698510109714337795043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19774392053918476468240229 3707698510109714337795043)
            ·
              refine ⟨5561547765164571506692565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3707698510109714337795043 5561547765164571506692565)
              ·
                refine ⟨130348775746044644688107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5561547765164571506692565 130348775746044644688107)
                ·
                  rfl

theorem cell20_856755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 7].length) (baseStart_856755 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_856755 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_856755 prefixEnd_856755 := by exact prefixLift 856755
  have htrace : WordTrace (prefixWord ++ tailWord_856755) baseStart_856755 baseEnd_856755 := by
    simpa [prefixWord, tailWord_856755, baseEnd_856755] using wordTrace_append hprefix tailTrace_856755
  have hstable : (prefixWord ++ tailWord_856755).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856755).length < 2 ^ (prefixWord ++ tailWord_856755).sum := by decide
  have hdescent : baseEnd_856755 < baseStart_856755 := by decide
  rcases family_descends (prefixWord ++ tailWord_856755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856772 : List Nat := [2, 3, 3, 1, 1, 2, 2, 6]
def baseStart_856772 : Nat := 118140960795 + 856772 * 2 ^ 59
def prefixEnd_856772 : Nat := 4983230072969 + 3 ^ 40 * 856772 * 2
def baseEnd_856772 : Nat := 130351362167119143499195

theorem tailTrace_856772 : CollatzResearch.WordTrace tailWord_856772 prefixEnd_856772 130351362167119143499195 := by
  unfold tailWord_856772
  simp only [CollatzResearch.WordTrace]
  refine ⟨15624521026034421926590285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20832694701379229235453713 15624521026034421926590285)
  ·
    refine ⟨5859195384762908222471357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15624521026034421926590285 5859195384762908222471357)
    ·
      refine ⟨2197198269286090583426759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5859195384762908222471357 2197198269286090583426759)
      ·
        refine ⟨3295797403929135875140139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2197198269286090583426759 3295797403929135875140139)
        ·
          refine ⟨4943696105893703812710209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3295797403929135875140139 4943696105893703812710209)
          ·
            refine ⟨3707772079420277859532657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4943696105893703812710209 3707772079420277859532657)
            ·
              refine ⟨2780829059565208394649493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3707772079420277859532657 2780829059565208394649493)
              ·
                refine ⟨130351362167119143499195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2780829059565208394649493 130351362167119143499195)
                ·
                  rfl

theorem cell20_856772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 6].length) (baseStart_856772 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_856772 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_856772 prefixEnd_856772 := by exact prefixLift 856772
  have htrace : WordTrace (prefixWord ++ tailWord_856772) baseStart_856772 baseEnd_856772 := by
    simpa [prefixWord, tailWord_856772, baseEnd_856772] using wordTrace_append hprefix tailTrace_856772
  have hstable : (prefixWord ++ tailWord_856772).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856772).length < 2 ^ (prefixWord ++ tailWord_856772).sum := by decide
  have hdescent : baseEnd_856772 < baseStart_856772 := by decide
  rcases family_descends (prefixWord ++ tailWord_856772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856789 : List Nat := [1, 3, 2, 5, 2, 7]
def baseStart_856789 : Nat := 118140960795 + 856789 * 2 ^ 59
def prefixEnd_856789 : Nat := 4983230072969 + 3 ^ 40 * 856789 * 2
def baseEnd_856789 : Nat := 14483772065354849145587

theorem tailTrace_856789 : CollatzResearch.WordTrace tailWord_856789 prefixEnd_856789 14483772065354849145587 := by
  unfold tailWord_856789
  simp only [CollatzResearch.WordTrace]
  refine ⟨31249662093007255756549421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20833108062004837171032947 31249662093007255756549421)
  ·
    refine ⟨11718623284877720908706033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31249662093007255756549421 11718623284877720908706033)
    ·
      refine ⟨8788967463658290681529525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11718623284877720908706033 8788967463658290681529525)
      ·
        refine ⟨823965699717964751393393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8788967463658290681529525 823965699717964751393393)
        ·
          refine ⟨617974274788473563545045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 823965699717964751393393 617974274788473563545045)
          ·
            refine ⟨14483772065354849145587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 617974274788473563545045 14483772065354849145587)
            ·
              rfl

theorem cell20_856789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 7].length) (baseStart_856789 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_856789 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_856789 prefixEnd_856789 := by exact prefixLift 856789
  have htrace : WordTrace (prefixWord ++ tailWord_856789) baseStart_856789 baseEnd_856789 := by
    simpa [prefixWord, tailWord_856789, baseEnd_856789] using wordTrace_append hprefix tailTrace_856789
  have hstable : (prefixWord ++ tailWord_856789).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856789).length < 2 ^ (prefixWord ++ tailWord_856789).sum := by decide
  have hdescent : baseEnd_856789 < baseStart_856789 := by decide
  rcases family_descends (prefixWord ++ tailWord_856789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856799 : List Nat := [1, 1, 2, 3, 2, 5, 2, 2, 2]
def baseStart_856799 : Nat := 118140960795 + 856799 * 2 ^ 59
def prefixEnd_856799 : Nat := 4983230072969 + 3 ^ 40 * 856799 * 2
def baseEnd_856799 : Nat := 391066410037065336597475

theorem tailTrace_856799 : CollatzResearch.WordTrace tailWord_856799 prefixEnd_856799 391066410037065336597475 := by
  unfold tailWord_856799
  simp only [CollatzResearch.WordTrace]
  refine ⟨31250026822971027464413451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20833351215314018309608967 31250026822971027464413451)
  ·
    refine ⟨46875040234456541196620177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31250026822971027464413451 46875040234456541196620177)
    ·
      refine ⟨35156280175842405897465133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46875040234456541196620177 35156280175842405897465133)
      ·
        refine ⟨13183605065940902211549425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35156280175842405897465133 13183605065940902211549425)
        ·
          refine ⟨9887703799455676658662069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13183605065940902211549425 9887703799455676658662069)
          ·
            refine ⟨926972231198969686749569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9887703799455676658662069 926972231198969686749569)
            ·
              refine ⟨695229173399227265062177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 926972231198969686749569 695229173399227265062177)
              ·
                refine ⟨521421880049420448796633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 695229173399227265062177 521421880049420448796633)
                ·
                  refine ⟨391066410037065336597475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 521421880049420448796633 391066410037065336597475)
                  ·
                    rfl

theorem cell20_856799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 2, 2, 2].length) (baseStart_856799 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_856799 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_856799 prefixEnd_856799 := by exact prefixLift 856799
  have htrace : WordTrace (prefixWord ++ tailWord_856799) baseStart_856799 baseEnd_856799 := by
    simpa [prefixWord, tailWord_856799, baseEnd_856799] using wordTrace_append hprefix tailTrace_856799
  have hstable : (prefixWord ++ tailWord_856799).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856799).length < 2 ^ (prefixWord ++ tailWord_856799).sum := by decide
  have hdescent : baseEnd_856799 < baseStart_856799 := by decide
  rcases family_descends (prefixWord ++ tailWord_856799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856817 : List Nat := [1, 2, 2, 2, 2, 2, 1, 5, 3]
def baseStart_856817 : Nat := 118140960795 + 856817 * 2 ^ 59
def prefixEnd_856817 : Nat := 4983230072969 + 3 ^ 40 * 856817 * 2
def baseEnd_856817 : Nat := 391074625727537273997401

theorem tailTrace_856817 : CollatzResearch.WordTrace tailWord_856817 prefixEnd_856817 391074625727537273997401 := by
  unfold tailWord_856817
  simp only [CollatzResearch.WordTrace]
  refine ⟨31250683336905816538568705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20833788891270544359045803 31250683336905816538568705)
  ·
    refine ⟨23438012502679362403926529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31250683336905816538568705 23438012502679362403926529)
    ·
      refine ⟨17578509377009521802944897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23438012502679362403926529 17578509377009521802944897)
      ·
        refine ⟨13183882032757141352208673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17578509377009521802944897 13183882032757141352208673)
        ·
          refine ⟨9887911524567856014156505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13183882032757141352208673 9887911524567856014156505)
          ·
            refine ⟨7415933643425892010617379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9887911524567856014156505 7415933643425892010617379)
            ·
              refine ⟨11123900465138838015926069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7415933643425892010617379 11123900465138838015926069)
              ·
                refine ⟨1042865668606766063993069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11123900465138838015926069 1042865668606766063993069)
                ·
                  refine ⟨391074625727537273997401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1042865668606766063993069 391074625727537273997401)
                  ·
                    rfl

theorem cell20_856817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 5, 3].length) (baseStart_856817 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_856817 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_856817 prefixEnd_856817 := by exact prefixLift 856817
  have htrace : WordTrace (prefixWord ++ tailWord_856817) baseStart_856817 baseEnd_856817 := by
    simpa [prefixWord, tailWord_856817, baseEnd_856817] using wordTrace_append hprefix tailTrace_856817
  have hstable : (prefixWord ++ tailWord_856817).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856817).length < 2 ^ (prefixWord ++ tailWord_856817).sum := by decide
  have hdescent : baseEnd_856817 < baseStart_856817 := by decide
  rcases family_descends (prefixWord ++ tailWord_856817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856824 : List Nat := [2, 1, 2, 1, 1, 2, 5, 2, 4]
def baseStart_856824 : Nat := 118140960795 + 856824 * 2 ^ 59
def prefixEnd_856824 : Nat := 4983230072969 + 3 ^ 40 * 856824 * 2
def baseEnd_856824 : Nat := 391077820718276360764039

theorem tailTrace_856824 : CollatzResearch.WordTrace tailWord_856824 prefixEnd_856824 391077820718276360764039 := by
  unfold tailWord_856824
  simp only [CollatzResearch.WordTrace]
  refine ⟨15625469323940228367036763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20833959098586971156049017 15625469323940228367036763)
  ·
    refine ⟨23438203985910342550555145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15625469323940228367036763 23438203985910342550555145)
    ·
      refine ⟨17578652989432756912916359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23438203985910342550555145 17578652989432756912916359)
      ·
        refine ⟨26367979484149135369374539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17578652989432756912916359 26367979484149135369374539)
        ·
          refine ⟨39551969226223703054061809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26367979484149135369374539 39551969226223703054061809)
          ·
            refine ⟨29663976919667777290546357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39551969226223703054061809 29663976919667777290546357)
            ·
              refine ⟨2780997836218854120988721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29663976919667777290546357 2780997836218854120988721)
              ·
                refine ⟨2085748377164140590741541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2780997836218854120988721 2085748377164140590741541)
                ·
                  refine ⟨391077820718276360764039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2085748377164140590741541 391077820718276360764039)
                  ·
                    rfl

theorem cell20_856824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 2, 4].length) (baseStart_856824 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_856824 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_856824 prefixEnd_856824 := by exact prefixLift 856824
  have htrace : WordTrace (prefixWord ++ tailWord_856824) baseStart_856824 baseEnd_856824 := by
    simpa [prefixWord, tailWord_856824, baseEnd_856824] using wordTrace_append hprefix tailTrace_856824
  have hstable : (prefixWord ++ tailWord_856824).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856824).length < 2 ^ (prefixWord ++ tailWord_856824).sum := by decide
  have hdescent : baseEnd_856824 < baseStart_856824 := by decide
  rcases family_descends (prefixWord ++ tailWord_856824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856841 : List Nat := [1, 2, 1, 1, 3, 2, 3, 5, 2]
def baseStart_856841 : Nat := 118140960795 + 856841 * 2 ^ 59
def prefixEnd_856841 : Nat := 4983230072969 + 3 ^ 40 * 856841 * 2
def baseEnd_856841 : Nat := 391085579981499857197303

theorem tailTrace_856841 : CollatzResearch.WordTrace tailWord_856841 prefixEnd_856841 391085579981499857197303 := by
  unfold tailWord_856841
  simp only [CollatzResearch.WordTrace]
  refine ⟨31251558688818868637442377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20834372459212579091628251 31251558688818868637442377)
  ·
    refine ⟨23438669016614151478081783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31251558688818868637442377 23438669016614151478081783)
    ·
      refine ⟨35158003524921227217122675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23438669016614151478081783 35158003524921227217122675)
      ·
        refine ⟨52737005287381840825684013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35158003524921227217122675 52737005287381840825684013)
        ·
          refine ⟨19776376982768190309631505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52737005287381840825684013 19776376982768190309631505)
          ·
            refine ⟨14832282737076142732223629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19776376982768190309631505 14832282737076142732223629)
            ·
              refine ⟨5562106026403553524583861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14832282737076142732223629 5562106026403553524583861)
              ·
                refine ⟨521447439975333142929737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5562106026403553524583861 521447439975333142929737)
                ·
                  refine ⟨391085579981499857197303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 521447439975333142929737 391085579981499857197303)
                  ·
                    rfl

theorem cell20_856841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 5, 2].length) (baseStart_856841 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_856841 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_856841 prefixEnd_856841 := by exact prefixLift 856841
  have htrace : WordTrace (prefixWord ++ tailWord_856841) baseStart_856841 baseEnd_856841 := by
    simpa [prefixWord, tailWord_856841, baseEnd_856841] using wordTrace_append hprefix tailTrace_856841
  have hstable : (prefixWord ++ tailWord_856841).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856841).length < 2 ^ (prefixWord ++ tailWord_856841).sum := by decide
  have hdescent : baseEnd_856841 < baseStart_856841 := by decide
  rcases family_descends (prefixWord ++ tailWord_856841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856869 : List Nat := [1, 3, 1, 2, 3, 1, 2, 7]
def baseStart_856869 : Nat := 118140960795 + 856869 * 2 ^ 59
def prefixEnd_856869 : Nat := 4983230072969 + 3 ^ 40 * 856869 * 2
def baseEnd_856869 : Nat := 130366119981485401421285

theorem tailTrace_856869 : CollatzResearch.WordTrace tailWord_856869 prefixEnd_856869 130366119981485401421285 := by
  unfold tailWord_856869
  simp only [CollatzResearch.WordTrace]
  refine ⟨31252579932717429419461661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20835053288478286279641107 31252579932717429419461661)
  ·
    refine ⟨11719717474769036032298123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31252579932717429419461661 11719717474769036032298123)
    ·
      refine ⟨17579576212153554048447185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11719717474769036032298123 17579576212153554048447185)
      ·
        refine ⟨13184682159115165536335389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17579576212153554048447185 13184682159115165536335389)
        ·
          refine ⟨4944255809668187076125771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13184682159115165536335389 4944255809668187076125771)
          ·
            refine ⟨7416383714502280614188657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4944255809668187076125771 7416383714502280614188657)
            ·
              refine ⟨5562287785876710460641493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7416383714502280614188657 5562287785876710460641493)
              ·
                refine ⟨130366119981485401421285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5562287785876710460641493 130366119981485401421285)
                ·
                  rfl

theorem cell20_856869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 7].length) (baseStart_856869 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_856869 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_856869 prefixEnd_856869 := by exact prefixLift 856869
  have htrace : WordTrace (prefixWord ++ tailWord_856869) baseStart_856869 baseEnd_856869 := by
    simpa [prefixWord, tailWord_856869, baseEnd_856869] using wordTrace_append hprefix tailTrace_856869
  have hstable : (prefixWord ++ tailWord_856869).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856869).length < 2 ^ (prefixWord ++ tailWord_856869).sum := by decide
  have hdescent : baseEnd_856869 < baseStart_856869 := by decide
  rcases family_descends (prefixWord ++ tailWord_856869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856913 : List Nat := [1, 2, 2, 1, 6, 1, 3, 2, 2]
def baseStart_856913 : Nat := 118140960795 + 856913 * 2 ^ 59
def prefixEnd_856913 : Nat := 4983230072969 + 3 ^ 40 * 856913 * 2
def baseEnd_856913 : Nat := 391118442743387606797009

theorem tailTrace_856913 : CollatzResearch.WordTrace tailWord_856913 prefixEnd_856913 391118442743387606797009 := by
  unfold tailWord_856913
  simp only [CollatzResearch.WordTrace]
  refine ⟨31254184744558024934063393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20836123163038683289375595 31254184744558024934063393)
  ·
    refine ⟨23440638558418518700547545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31254184744558024934063393 23440638558418518700547545)
    ·
      refine ⟨17580478918813889025410659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23440638558418518700547545 17580478918813889025410659)
      ·
        refine ⟨26370718378220833538115989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17580478918813889025410659 26370718378220833538115989)
        ·
          refine ⟨1236127423979101572099187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 26370718378220833538115989 1236127423979101572099187)
          ·
            refine ⟨1854191135968652358148781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1236127423979101572099187 1854191135968652358148781)
            ·
              refine ⟨695321675988244634305793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1854191135968652358148781 695321675988244634305793)
              ·
                refine ⟨521491256991183475729345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 695321675988244634305793 521491256991183475729345)
                ·
                  refine ⟨391118442743387606797009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 521491256991183475729345 391118442743387606797009)
                  ·
                    rfl

theorem cell20_856913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 3, 2, 2].length) (baseStart_856913 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_856913 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_856913 prefixEnd_856913 := by exact prefixLift 856913
  have htrace : WordTrace (prefixWord ++ tailWord_856913) baseStart_856913 baseEnd_856913 := by
    simpa [prefixWord, tailWord_856913, baseEnd_856913] using wordTrace_append hprefix tailTrace_856913
  have hstable : (prefixWord ++ tailWord_856913).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856913).length < 2 ^ (prefixWord ++ tailWord_856913).sum := by decide
  have hdescent : baseEnd_856913 < baseStart_856913 := by decide
  rcases family_descends (prefixWord ++ tailWord_856913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856924 : List Nat := [2, 2, 4, 2, 1, 1, 1, 7]
def baseStart_856924 : Nat := 118140960795 + 856924 * 2 ^ 59
def prefixEnd_856924 : Nat := 4983230072969 + 3 ^ 40 * 856924 * 2
def baseEnd_856924 : Nat := 130374487814373485810099

theorem tailTrace_856924 : CollatzResearch.WordTrace tailWord_856924 prefixEnd_856924 130374487814373485810099 := by
  unfold tailWord_856924
  simp only [CollatzResearch.WordTrace]
  refine ⟨15627292973759086906356913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20836390631678782541809217 15627292973759086906356913)
  ·
    refine ⟨11720469730319315179767685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15627292973759086906356913 11720469730319315179767685)
    ·
      refine ⟨2197588074434871596206441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11720469730319315179767685 2197588074434871596206441)
      ·
        refine ⟨1648191055826153697154831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2197588074434871596206441 1648191055826153697154831)
        ·
          refine ⟨2472286583739230545732247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1648191055826153697154831 2472286583739230545732247)
          ·
            refine ⟨3708429875608845818598371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2472286583739230545732247 3708429875608845818598371)
            ·
              refine ⟨5562644813413268727897557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3708429875608845818598371 5562644813413268727897557)
              ·
                refine ⟨130374487814373485810099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5562644813413268727897557 130374487814373485810099)
                ·
                  rfl

theorem cell20_856924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 7].length) (baseStart_856924 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_856924 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_856924 prefixEnd_856924 := by exact prefixLift 856924
  have htrace : WordTrace (prefixWord ++ tailWord_856924) baseStart_856924 baseEnd_856924 := by
    simpa [prefixWord, tailWord_856924, baseEnd_856924] using wordTrace_append hprefix tailTrace_856924
  have hstable : (prefixWord ++ tailWord_856924).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856924).length < 2 ^ (prefixWord ++ tailWord_856924).sum := by decide
  have hdescent : baseEnd_856924 < baseStart_856924 := by decide
  rcases family_descends (prefixWord ++ tailWord_856924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856945 : List Nat := [1, 2, 2, 2, 1, 4, 2, 6]
def baseStart_856945 : Nat := 118140960795 + 856945 * 2 ^ 59
def prefixEnd_856945 : Nat := 4983230072969 + 3 ^ 40 * 856945 * 2
def baseEnd_856945 : Nat := 130377682805112572576737

theorem tailTrace_856945 : CollatzResearch.WordTrace tailWord_856945 prefixEnd_856945 130377682805112572576737 := by
  unfold tailWord_856945
  simp only [CollatzResearch.WordTrace]
  refine ⟨31255351880442094399228289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20836901253628062932818859 31255351880442094399228289)
  ·
    refine ⟨23441513910331570799421217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31255351880442094399228289 23441513910331570799421217)
    ·
      refine ⟨17581135432748678099565913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23441513910331570799421217 17581135432748678099565913)
      ·
        refine ⟨13185851574561508574674435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17581135432748678099565913 13185851574561508574674435)
        ·
          refine ⟨19778777361842262862011653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13185851574561508574674435 19778777361842262862011653)
          ·
            refine ⟨3708520755345424286627185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19778777361842262862011653 3708520755345424286627185)
            ·
              refine ⟨2781390566509068214970389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3708520755345424286627185 2781390566509068214970389)
              ·
                refine ⟨130377682805112572576737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2781390566509068214970389 130377682805112572576737)
                ·
                  rfl

theorem cell20_856945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 6].length) (baseStart_856945 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_856945 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_856945 prefixEnd_856945 := by exact prefixLift 856945
  have htrace : WordTrace (prefixWord ++ tailWord_856945) baseStart_856945 baseEnd_856945 := by
    simpa [prefixWord, tailWord_856945, baseEnd_856945] using wordTrace_append hprefix tailTrace_856945
  have hstable : (prefixWord ++ tailWord_856945).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856945).length < 2 ^ (prefixWord ++ tailWord_856945).sum := by decide
  have hdescent : baseEnd_856945 < baseStart_856945 := by decide
  rcases family_descends (prefixWord ++ tailWord_856945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856952 : List Nat := [2, 1, 2, 1, 1, 1, 1, 6, 5]
def baseStart_856952 : Nat := 118140960795 + 856952 * 2 ^ 59
def prefixEnd_856952 : Nat := 4983230072969 + 3 ^ 40 * 856952 * 2
def baseEnd_856952 : Nat := 391136243406076804496849

theorem tailTrace_856952 : CollatzResearch.WordTrace tailWord_856952 prefixEnd_856952 391136243406076804496849 := by
  unfold tailWord_856952
  simp only [CollatzResearch.WordTrace]
  refine ⟨15627803595708367297366555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20837071460944489729822073 15627803595708367297366555)
  ·
    refine ⟨23441705393562550946049833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15627803595708367297366555 23441705393562550946049833)
    ·
      refine ⟨17581279045171913209537375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23441705393562550946049833 17581279045171913209537375)
      ·
        refine ⟨26371918567757869814306063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17581279045171913209537375 26371918567757869814306063)
        ·
          refine ⟨39557877851636804721459095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26371918567757869814306063 39557877851636804721459095)
          ·
            refine ⟨59336816777455207082188643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39557877851636804721459095 59336816777455207082188643)
            ·
              refine ⟨89005225166182810623282965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59336816777455207082188643 89005225166182810623282965)
              ·
                refine ⟨4172119929664819247966389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 89005225166182810623282965 4172119929664819247966389)
                ·
                  refine ⟨391136243406076804496849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4172119929664819247966389 391136243406076804496849)
                  ·
                    rfl

theorem cell20_856952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 6, 5].length) (baseStart_856952 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_856952 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_856952 prefixEnd_856952 := by exact prefixLift 856952
  have htrace : WordTrace (prefixWord ++ tailWord_856952) baseStart_856952 baseEnd_856952 := by
    simpa [prefixWord, tailWord_856952, baseEnd_856952] using wordTrace_append hprefix tailTrace_856952
  have hstable : (prefixWord ++ tailWord_856952).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856952).length < 2 ^ (prefixWord ++ tailWord_856952).sum := by decide
  have hdescent : baseEnd_856952 < baseStart_856952 := by decide
  rcases family_descends (prefixWord ++ tailWord_856952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856969 : List Nat := [1, 2, 1, 1, 5, 2, 1, 4, 3]
def baseStart_856969 : Nat := 118140960795 + 856969 * 2 ^ 59
def prefixEnd_856969 : Nat := 4983230072969 + 3 ^ 40 * 856969 * 2
def baseEnd_856969 : Nat := 391144002669300300930113

theorem tailTrace_856969 : CollatzResearch.WordTrace tailWord_856969 prefixEnd_856969 391144002669300300930113 := by
  unfold tailWord_856969
  simp only [CollatzResearch.WordTrace]
  refine ⟨31256227232355146498101961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20837484821570097665401307 31256227232355146498101961)
  ·
    refine ⟨23442170424266359873576471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31256227232355146498101961 23442170424266359873576471)
    ·
      refine ⟨35163255636399539810364707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23442170424266359873576471 35163255636399539810364707)
      ·
        refine ⟨52744883454599309715547061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35163255636399539810364707 52744883454599309715547061)
        ·
          refine ⟨4944832823868685285832537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52744883454599309715547061 4944832823868685285832537)
          ·
            refine ⟨3708624617901513964374403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4944832823868685285832537 3708624617901513964374403)
            ·
              refine ⟨5562936926852270946561605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3708624617901513964374403 5562936926852270946561605)
              ·
                refine ⟨1043050673784800802480301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5562936926852270946561605 1043050673784800802480301)
                ·
                  refine ⟨391144002669300300930113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1043050673784800802480301 391144002669300300930113)
                  ·
                    rfl

theorem cell20_856969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 4, 3].length) (baseStart_856969 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_856969 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_856969 prefixEnd_856969 := by exact prefixLift 856969
  have htrace : WordTrace (prefixWord ++ tailWord_856969) baseStart_856969 baseEnd_856969 := by
    simpa [prefixWord, tailWord_856969, baseEnd_856969] using wordTrace_append hprefix tailTrace_856969
  have hstable : (prefixWord ++ tailWord_856969).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856969).length < 2 ^ (prefixWord ++ tailWord_856969).sum := by decide
  have hdescent : baseEnd_856969 < baseStart_856969 := by decide
  rcases family_descends (prefixWord ++ tailWord_856969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856972 : List Nat := [2, 2, 1, 2, 1, 2, 6, 2, 2]
def baseStart_856972 : Nat := 118140960795 + 856972 * 2 ^ 59
def prefixEnd_856972 : Nat := 4983230072969 + 3 ^ 40 * 856972 * 2
def baseEnd_856972 : Nat := 391145371951045623830101

theorem tailTrace_856972 : CollatzResearch.WordTrace tailWord_856972 prefixEnd_856972 391145371951045623830101 := by
  unfold tailWord_856972
  simp only [CollatzResearch.WordTrace]
  refine ⟨15628168325672139005230585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20837557767562852006974113 15628168325672139005230585)
  ·
    refine ⟨11721126244254104253922939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15628168325672139005230585 11721126244254104253922939)
    ·
      refine ⟨17581689366381156380884409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11721126244254104253922939 17581689366381156380884409)
      ·
        refine ⟨13186267024785867285663307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17581689366381156380884409 13186267024785867285663307)
        ·
          refine ⟨19779400537178800928494961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13186267024785867285663307 19779400537178800928494961)
          ·
            refine ⟨14834550402884100696371221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19779400537178800928494961 14834550402884100696371221)
            ·
              refine ⟨695369550135192220142401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 14834550402884100696371221 695369550135192220142401)
              ·
                refine ⟨521527162601394165106801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 695369550135192220142401 521527162601394165106801)
                ·
                  refine ⟨391145371951045623830101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 521527162601394165106801 391145371951045623830101)
                  ·
                    rfl

theorem cell20_856972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 6, 2, 2].length) (baseStart_856972 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_856972 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_856972 prefixEnd_856972 := by exact prefixLift 856972
  have htrace : WordTrace (prefixWord ++ tailWord_856972) baseStart_856972 baseEnd_856972 := by
    simpa [prefixWord, tailWord_856972, baseEnd_856972] using wordTrace_append hprefix tailTrace_856972
  have hstable : (prefixWord ++ tailWord_856972).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856972).length < 2 ^ (prefixWord ++ tailWord_856972).sum := by decide
  have hdescent : baseEnd_856972 < baseStart_856972 := by decide
  rcases family_descends (prefixWord ++ tailWord_856972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856982 : List Nat := [5, 3, 1, 1, 1, 1, 2, 3, 3]
def baseStart_856982 : Nat := 118140960795 + 856982 * 2 ^ 59
def prefixEnd_856982 : Nat := 4983230072969 + 3 ^ 40 * 856982 * 2
def baseEnd_856982 : Nat := 391149936223530033496727

theorem tailTrace_856982 : CollatzResearch.WordTrace tailWord_856982 prefixEnd_856982 391149936223530033496727 := by
  unfold tailWord_856982
  simp only [CollatzResearch.WordTrace]
  refine ⟨1953543836331753107395325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20837800920872033145550133 1953543836331753107395325)
  ·
    refine ⟨732578938624407415273247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1953543836331753107395325 732578938624407415273247)
    ·
      refine ⟨1098868407936611122909871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 732578938624407415273247 1098868407936611122909871)
      ·
        refine ⟨1648302611904916684364807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1098868407936611122909871 1648302611904916684364807)
        ·
          refine ⟨2472453917857375026547211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1648302611904916684364807 2472453917857375026547211)
          ·
            refine ⟨3708680876786062539820817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2472453917857375026547211 3708680876786062539820817)
            ·
              refine ⟨2781510657589546904865613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3708680876786062539820817 2781510657589546904865613)
              ·
                refine ⟨1043066496596080089324605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2781510657589546904865613 1043066496596080089324605)
                ·
                  refine ⟨391149936223530033496727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1043066496596080089324605 391149936223530033496727)
                  ·
                    rfl

theorem cell20_856982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_856982 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_856982 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_856982 prefixEnd_856982 := by exact prefixLift 856982
  have htrace : WordTrace (prefixWord ++ tailWord_856982) baseStart_856982 baseEnd_856982 := by
    simpa [prefixWord, tailWord_856982, baseEnd_856982] using wordTrace_append hprefix tailTrace_856982
  have hstable : (prefixWord ++ tailWord_856982).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856982).length < 2 ^ (prefixWord ++ tailWord_856982).sum := by decide
  have hdescent : baseEnd_856982 < baseStart_856982 := by decide
  rcases family_descends (prefixWord ++ tailWord_856982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_856993 : List Nat := [1, 2, 3, 4, 1, 2, 1, 2, 4]
def baseStart_856993 : Nat := 118140960795 + 856993 * 2 ^ 59
def prefixEnd_856993 : Nat := 4983230072969 + 3 ^ 40 * 856993 * 2
def baseEnd_856993 : Nat := 391154956923262884130015

theorem tailTrace_856993 : CollatzResearch.WordTrace tailWord_856993 prefixEnd_856993 391154956923262884130015 := by
  unfold tailWord_856993
  simp only [CollatzResearch.WordTrace]
  refine ⟨31257102584268198596975633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20838068389512132397983755 31257102584268198596975633)
  ·
    refine ⟨23442826938201148947731725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31257102584268198596975633 23442826938201148947731725)
    ·
      refine ⟨8791060101825430855399397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23442826938201148947731725 8791060101825430855399397)
      ·
        refine ⟨1648323769092268285387387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8791060101825430855399397 1648323769092268285387387)
        ·
          refine ⟨2472485653638402428081081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1648323769092268285387387 2472485653638402428081081)
          ·
            refine ⟨1854364240228801821060811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2472485653638402428081081 1854364240228801821060811)
            ·
              refine ⟨2781546360343202731591217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1854364240228801821060811 2781546360343202731591217)
              ·
                refine ⟨2086159770257402048693413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2781546360343202731591217 2086159770257402048693413)
                ·
                  refine ⟨391154956923262884130015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2086159770257402048693413 391154956923262884130015)
                  ·
                    rfl

theorem cell20_856993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 2, 4].length) (baseStart_856993 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_856993 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_856993 prefixEnd_856993 := by exact prefixLift 856993
  have htrace : WordTrace (prefixWord ++ tailWord_856993) baseStart_856993 baseEnd_856993 := by
    simpa [prefixWord, tailWord_856993, baseEnd_856993] using wordTrace_append hprefix tailTrace_856993
  have hstable : (prefixWord ++ tailWord_856993).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_856993).length < 2 ^ (prefixWord ++ tailWord_856993).sum := by decide
  have hdescent : baseEnd_856993 < baseStart_856993 := by decide
  rcases family_descends (prefixWord ++ tailWord_856993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857024 : List Nat := [2, 1, 1, 2, 3, 5, 1, 2, 3]
def baseStart_857024 : Nat := 118140960795 + 857024 * 2 ^ 59
def prefixEnd_857024 : Nat := 4983230072969 + 3 ^ 40 * 857024 * 2
def baseEnd_857024 : Nat := 391169106167964554096555

theorem tailTrace_857024 : CollatzResearch.WordTrace tailWord_857024 prefixEnd_857024 391169106167964554096555 := by
  unfold tailWord_857024
  simp only [CollatzResearch.WordTrace]
  refine ⟨15629116623577945445677063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20838822164770593927569417 15629116623577945445677063)
  ·
    refine ⟨23443674935366918168515595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15629116623577945445677063 23443674935366918168515595)
    ·
      refine ⟨35165512403050377252773393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23443674935366918168515595 35165512403050377252773393)
      ·
        refine ⟨26374134302287782939580045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35165512403050377252773393 26374134302287782939580045)
        ·
          refine ⟨9890300363357918602342517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26374134302287782939580045 9890300363357918602342517)
          ·
            refine ⟨927215659064804868969611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9890300363357918602342517 927215659064804868969611)
            ·
              refine ⟨1390823488597207303454417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 927215659064804868969611 1390823488597207303454417)
              ·
                refine ⟨1043117616447905477590813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1390823488597207303454417 1043117616447905477590813)
                ·
                  refine ⟨391169106167964554096555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1043117616447905477590813 391169106167964554096555)
                  ·
                    rfl

theorem cell20_857024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 1, 2, 3].length) (baseStart_857024 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_857024 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_857024 prefixEnd_857024 := by exact prefixLift 857024
  have htrace : WordTrace (prefixWord ++ tailWord_857024) baseStart_857024 baseEnd_857024 := by
    simpa [prefixWord, tailWord_857024, baseEnd_857024] using wordTrace_append hprefix tailTrace_857024
  have hstable : (prefixWord ++ tailWord_857024).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857024).length < 2 ^ (prefixWord ++ tailWord_857024).sum := by decide
  have hdescent : baseEnd_857024 < baseStart_857024 := by decide
  rcases family_descends (prefixWord ++ tailWord_857024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857031 : List Nat := [1, 1, 4, 1, 1, 2, 4, 4, 2]
def baseStart_857031 : Nat := 118140960795 + 857031 * 2 ^ 59
def prefixEnd_857031 : Nat := 4983230072969 + 3 ^ 40 * 857031 * 2
def baseEnd_857031 : Nat := 391172301158703640863193

theorem tailTrace_857031 : CollatzResearch.WordTrace tailWord_857031 prefixEnd_857031 391172301158703640863193 := by
  unfold tailWord_857031
  simp only [CollatzResearch.WordTrace]
  refine ⟨31258488558130531086858947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20838992372087020724572631 31258488558130531086858947)
  ·
    refine ⟨46887732837195796630288421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31258488558130531086858947 46887732837195796630288421)
    ·
      refine ⟨8791449906974211868179079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46887732837195796630288421 8791449906974211868179079)
      ·
        refine ⟨13187174860461317802268619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8791449906974211868179079 13187174860461317802268619)
        ·
          refine ⟨19780762290691976703402929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13187174860461317802268619 19780762290691976703402929)
          ·
            refine ⟨14835571718018982527552197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19780762290691976703402929 14835571718018982527552197)
            ·
              refine ⟨2781669697128559223916037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14835571718018982527552197 2781669697128559223916037)
              ·
                refine ⟨521563068211604854484257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2781669697128559223916037 521563068211604854484257)
                ·
                  refine ⟨391172301158703640863193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 521563068211604854484257 391172301158703640863193)
                  ·
                    rfl

theorem cell20_857031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 4, 2].length) (baseStart_857031 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_857031 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_857031 prefixEnd_857031 := by exact prefixLift 857031
  have htrace : WordTrace (prefixWord ++ tailWord_857031) baseStart_857031 baseEnd_857031 := by
    simpa [prefixWord, tailWord_857031, baseEnd_857031] using wordTrace_append hprefix tailTrace_857031
  have hstable : (prefixWord ++ tailWord_857031).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857031).length < 2 ^ (prefixWord ++ tailWord_857031).sum := by decide
  have hdescent : baseEnd_857031 < baseStart_857031 := by decide
  rcases family_descends (prefixWord ++ tailWord_857031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857055 : List Nat := [1, 1, 2, 3, 5, 2, 2, 4]
def baseStart_857055 : Nat := 118140960795 + 857055 * 2 ^ 59
def prefixEnd_857055 : Nat := 4983230072969 + 3 ^ 40 * 857055 * 2
def baseEnd_857055 : Nat := 130394418470888741354365

theorem tailTrace_857055 : CollatzResearch.WordTrace tailWord_857055 prefixEnd_857055 130394418470888741354365 := by
  unfold tailWord_857055
  simp only [CollatzResearch.WordTrace]
  refine ⟨31259363910043583185732619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20839575940029055457155079 31259363910043583185732619)
  ·
    refine ⟨46889045865065374778598929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31259363910043583185732619 46889045865065374778598929)
    ·
      refine ⟨35166784398799031083949197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46889045865065374778598929 35166784398799031083949197)
      ·
        refine ⟨13187544149549636656480949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35166784398799031083949197 13187544149549636656480949)
        ·
          refine ⟨1236332264020278436545089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13187544149549636656480949 1236332264020278436545089)
          ·
            refine ⟨927249198015208827408817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1236332264020278436545089 927249198015208827408817)
            ·
              refine ⟨695436898511406620556613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 927249198015208827408817 695436898511406620556613)
              ·
                refine ⟨130394418470888741354365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 695436898511406620556613 130394418470888741354365)
                ·
                  rfl

theorem cell20_857055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 2, 4].length) (baseStart_857055 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_857055 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_857055 prefixEnd_857055 := by exact prefixLift 857055
  have htrace : WordTrace (prefixWord ++ tailWord_857055) baseStart_857055 baseEnd_857055 := by
    simpa [prefixWord, tailWord_857055, baseEnd_857055] using wordTrace_append hprefix tailTrace_857055
  have hstable : (prefixWord ++ tailWord_857055).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857055).length < 2 ^ (prefixWord ++ tailWord_857055).sum := by decide
  have hdescent : baseEnd_857055 < baseStart_857055 := by decide
  rcases family_descends (prefixWord ++ tailWord_857055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857059 : List Nat := [1, 1, 1, 6, 1, 1, 3, 6]
def baseStart_857059 : Nat := 118140960795 + 857059 * 2 ^ 59
def prefixEnd_857059 : Nat := 4983230072969 + 3 ^ 40 * 857059 * 2
def baseEnd_857059 : Nat := 130395027040553329309915

theorem tailTrace_857059 : CollatzResearch.WordTrace tailWord_857059 prefixEnd_857059 130395027040553329309915 := by
  unfold tailWord_857059
  simp only [CollatzResearch.WordTrace]
  refine ⟨31259509802029091868878231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20839673201352727912585487 31259509802029091868878231)
  ·
    refine ⟨46889264703043637803317347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31259509802029091868878231 46889264703043637803317347)
    ·
      refine ⟨70333897054565456704976021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46889264703043637803317347 70333897054565456704976021)
      ·
        refine ⟨3296901424432755783045751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 70333897054565456704976021 3296901424432755783045751)
        ·
          refine ⟨4945352136649133674568627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3296901424432755783045751 4945352136649133674568627)
          ·
            refine ⟨7418028204973700511852941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4945352136649133674568627 7418028204973700511852941)
            ·
              refine ⟨2781760576865137691944853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7418028204973700511852941 2781760576865137691944853)
              ·
                refine ⟨130395027040553329309915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2781760576865137691944853 130395027040553329309915)
                ·
                  rfl

theorem cell20_857059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 6].length) (baseStart_857059 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_857059 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_857059 prefixEnd_857059 := by exact prefixLift 857059
  have htrace : WordTrace (prefixWord ++ tailWord_857059) baseStart_857059 baseEnd_857059 := by
    simpa [prefixWord, tailWord_857059, baseEnd_857059] using wordTrace_append hprefix tailTrace_857059
  have hstable : (prefixWord ++ tailWord_857059).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857059).length < 2 ^ (prefixWord ++ tailWord_857059).sum := by decide
  have hdescent : baseEnd_857059 < baseStart_857059 := by decide
  rcases family_descends (prefixWord ++ tailWord_857059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857100 : List Nat := [2, 2, 1, 2, 3, 2, 4, 1, 3]
def baseStart_857100 : Nat := 118140960795 + 857100 * 2 ^ 59
def prefixEnd_857100 : Nat := 4983230072969 + 3 ^ 40 * 857100 * 2
def baseEnd_857100 : Nat := 391203794638846067562911

theorem tailTrace_857100 : CollatzResearch.WordTrace tailWord_857100 prefixEnd_857100 391203794638846067562911 := by
  unfold tailWord_857100
  simp only [CollatzResearch.WordTrace]
  refine ⟨15630502597440277935560377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20840670129920370580747169 15630502597440277935560377)
  ·
    refine ⟨11722876948080208451670283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15630502597440277935560377 11722876948080208451670283)
    ·
      refine ⟨17584315422120312677505425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11722876948080208451670283 17584315422120312677505425)
      ·
        refine ⟨13188236566590234508129069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17584315422120312677505425 13188236566590234508129069)
        ·
          refine ⟨4945588712471337940548401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13188236566590234508129069 4945588712471337940548401)
          ·
            refine ⟨3709191534353503455411301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4945588712471337940548401 3709191534353503455411301)
            ·
              refine ⟨695473412691281897889619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3709191534353503455411301 695473412691281897889619)
              ·
                refine ⟨1043210119036922846834429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 695473412691281897889619 1043210119036922846834429)
                ·
                  refine ⟨391203794638846067562911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1043210119036922846834429 391203794638846067562911)
                  ·
                    rfl

theorem cell20_857100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 4, 1, 3].length) (baseStart_857100 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_857100 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_857100 prefixEnd_857100 := by exact prefixLift 857100
  have htrace : WordTrace (prefixWord ++ tailWord_857100) baseStart_857100 baseEnd_857100 := by
    simpa [prefixWord, tailWord_857100, baseEnd_857100] using wordTrace_append hprefix tailTrace_857100
  have hstable : (prefixWord ++ tailWord_857100).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857100).length < 2 ^ (prefixWord ++ tailWord_857100).sum := by decide
  have hdescent : baseEnd_857100 < baseStart_857100 := by decide
  rcases family_descends (prefixWord ++ tailWord_857100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857159 : List Nat := [1, 1, 4, 1, 3, 2, 2, 3, 3]
def baseStart_857159 : Nat := 118140960795 + 857159 * 2 ^ 59
def prefixEnd_857159 : Nat := 4983230072969 + 3 ^ 40 * 857159 * 2
def baseEnd_857159 : Nat := 391230723846504084596003

theorem tailTrace_857159 : CollatzResearch.WordTrace tailWord_857159 prefixEnd_857159 391230723846504084596003 := by
  unfold tailWord_857159
  simp only [CollatzResearch.WordTrace]
  refine ⟨31263157101666808947518531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20842104734444539298345687 31263157101666808947518531)
  ·
    refine ⟨46894735652500213421277797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31263157101666808947518531 46894735652500213421277797)
    ·
      refine ⟨8792762934843790016489587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46894735652500213421277797 8792762934843790016489587)
      ·
        refine ⟨13189144402265685024734381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8792762934843790016489587 13189144402265685024734381)
        ·
          refine ⟨4945929150849631884275393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13189144402265685024734381 4945929150849631884275393)
          ·
            refine ⟨3709446863137223913206545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4945929150849631884275393 3709446863137223913206545)
            ·
              refine ⟨2782085147352917934904909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3709446863137223913206545 2782085147352917934904909)
              ·
                refine ⟨1043281930257344225589341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2782085147352917934904909 1043281930257344225589341)
                ·
                  refine ⟨391230723846504084596003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1043281930257344225589341 391230723846504084596003)
                  ·
                    rfl

theorem cell20_857159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 3, 3].length) (baseStart_857159 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_857159 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_857159 prefixEnd_857159 := by exact prefixLift 857159
  have htrace : WordTrace (prefixWord ++ tailWord_857159) baseStart_857159 baseEnd_857159 := by
    simpa [prefixWord, tailWord_857159, baseEnd_857159] using wordTrace_append hprefix tailTrace_857159
  have hstable : (prefixWord ++ tailWord_857159).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857159).length < 2 ^ (prefixWord ++ tailWord_857159).sum := by decide
  have hdescent : baseEnd_857159 < baseStart_857159 := by decide
  rcases family_descends (prefixWord ++ tailWord_857159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857166 : List Nat := [4, 1, 1, 1, 1, 3, 3, 2, 4]
def baseStart_857166 : Nat := 118140960795 + 857166 * 2 ^ 59
def prefixEnd_857166 : Nat := 4983230072969 + 3 ^ 40 * 857166 * 2
def baseEnd_857166 : Nat := 391233918837243171362641

theorem tailTrace_857166 : CollatzResearch.WordTrace tailWord_857166 prefixEnd_857166 391233918837243171362641 := by
  unfold tailWord_857166
  simp only [CollatzResearch.WordTrace]
  refine ⟨3907926551580181142877919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20842274941760966095348901 3907926551580181142877919)
  ·
    refine ⟨5861889827370271714316879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3907926551580181142877919 5861889827370271714316879)
    ·
      refine ⟨8792834741055407571475319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5861889827370271714316879 8792834741055407571475319)
      ·
        refine ⟨13189252111583111357212979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8792834741055407571475319 13189252111583111357212979)
        ·
          refine ⟨19783878167374667035819469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13189252111583111357212979 19783878167374667035819469)
          ·
            refine ⟨7418954312765500138432301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19783878167374667035819469 7418954312765500138432301)
            ·
              refine ⟨2782107867287062551912113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7418954312765500138432301 2782107867287062551912113)
              ·
                refine ⟨2086580900465296913934085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2782107867287062551912113 2086580900465296913934085)
                ·
                  refine ⟨391233918837243171362641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2086580900465296913934085 391233918837243171362641)
                  ·
                    rfl

theorem cell20_857166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 2, 4].length) (baseStart_857166 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_857166 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_857166 prefixEnd_857166 := by exact prefixLift 857166
  have htrace : WordTrace (prefixWord ++ tailWord_857166) baseStart_857166 baseEnd_857166 := by
    simpa [prefixWord, tailWord_857166, baseEnd_857166] using wordTrace_append hprefix tailTrace_857166
  have hstable : (prefixWord ++ tailWord_857166).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857166).length < 2 ^ (prefixWord ++ tailWord_857166).sum := by decide
  have hdescent : baseEnd_857166 < baseStart_857166 := by decide
  rcases family_descends (prefixWord ++ tailWord_857166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857183 : List Nat := [1, 1, 2, 3, 1, 1, 6, 3, 2]
def baseStart_857183 : Nat := 118140960795 + 857183 * 2 ^ 59
def prefixEnd_857183 : Nat := 4983230072969 + 3 ^ 40 * 857183 * 2
def baseEnd_857183 : Nat := 391241678100466667795905

theorem tailTrace_857183 : CollatzResearch.WordTrace tailWord_857183 prefixEnd_857183 391241678100466667795905 := by
  unfold tailWord_857183
  simp only [CollatzResearch.WordTrace]
  refine ⟨31264032453579861046392203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20842688302386574030928135 31264032453579861046392203)
  ·
    refine ⟨46896048680369791569588305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31264032453579861046392203 46896048680369791569588305)
    ·
      refine ⟨35172036510277343677191229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46896048680369791569588305 35172036510277343677191229)
      ·
        refine ⟨13189513691354003878946711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35172036510277343677191229 13189513691354003878946711)
        ·
          refine ⟨19784270537031005818420067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13189513691354003878946711 19784270537031005818420067)
          ·
            refine ⟨29676405805546508727630101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19784270537031005818420067 29676405805546508727630101)
            ·
              refine ⟨1391081522134992596607661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 29676405805546508727630101 1391081522134992596607661)
              ·
                refine ⟨521655570800622223727873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1391081522134992596607661 521655570800622223727873)
                ·
                  refine ⟨391241678100466667795905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 521655570800622223727873 391241678100466667795905)
                  ·
                    rfl

theorem cell20_857183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 6, 3, 2].length) (baseStart_857183 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_857183 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_857183 prefixEnd_857183 := by exact prefixLift 857183
  have htrace : WordTrace (prefixWord ++ tailWord_857183) baseStart_857183 baseEnd_857183 := by
    simpa [prefixWord, tailWord_857183, baseEnd_857183] using wordTrace_append hprefix tailTrace_857183
  have hstable : (prefixWord ++ tailWord_857183).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857183).length < 2 ^ (prefixWord ++ tailWord_857183).sum := by decide
  have hdescent : baseEnd_857183 < baseStart_857183 := by decide
  rcases family_descends (prefixWord ++ tailWord_857183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857187 : List Nat := [1, 1, 1, 5, 1, 1, 1, 1, 8]
def baseStart_857187 : Nat := 118140960795 + 857187 * 2 ^ 59
def prefixEnd_857187 : Nat := 4983230072969 + 3 ^ 40 * 857187 * 2
def baseEnd_857187 : Nat := 391243503809460431662555

theorem tailTrace_857187 : CollatzResearch.WordTrace tailWord_857187 prefixEnd_857187 391243503809460431662555 := by
  unfold tailWord_857187
  simp only [CollatzResearch.WordTrace]
  refine ⟨31264178345565369729537815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20842785563710246486358543 31264178345565369729537815)
  ·
    refine ⟨46896267518348054594306723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31264178345565369729537815 46896267518348054594306723)
    ·
      refine ⟨70344401277522081891460085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46896267518348054594306723 70344401277522081891460085)
      ·
        refine ⟨6594787619767695177324383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 70344401277522081891460085 6594787619767695177324383)
        ·
          refine ⟨9892181429651542765986575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6594787619767695177324383 9892181429651542765986575)
          ·
            refine ⟨14838272144477314148979863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9892181429651542765986575 14838272144477314148979863)
            ·
              refine ⟨22257408216715971223469795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14838272144477314148979863 22257408216715971223469795)
              ·
                refine ⟨33386112325073956835204693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22257408216715971223469795 33386112325073956835204693)
                ·
                  refine ⟨391243503809460431662555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33386112325073956835204693 391243503809460431662555)
                  ·
                    rfl

theorem cell20_857187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 8].length) (baseStart_857187 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_857187 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_857187 prefixEnd_857187 := by exact prefixLift 857187
  have htrace : WordTrace (prefixWord ++ tailWord_857187) baseStart_857187 baseEnd_857187 := by
    simpa [prefixWord, tailWord_857187, baseEnd_857187] using wordTrace_append hprefix tailTrace_857187
  have hstable : (prefixWord ++ tailWord_857187).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857187).length < 2 ^ (prefixWord ++ tailWord_857187).sum := by decide
  have hdescent : baseEnd_857187 < baseStart_857187 := by decide
  rcases family_descends (prefixWord ++ tailWord_857187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857197 : List Nat := [1, 5, 1, 1, 2, 3, 1, 1, 5]
def baseStart_857197 : Nat := 118140960795 + 857197 * 2 ^ 59
def prefixEnd_857197 : Nat := 4983230072969 + 3 ^ 40 * 857197 * 2
def baseEnd_857197 : Nat := 391248068081944841329181

theorem tailTrace_857197 : CollatzResearch.WordTrace tailWord_857197 prefixEnd_857197 391248068081944841329181 := by
  unfold tailWord_857197
  simp only [CollatzResearch.WordTrace]
  refine ⟨31264543075529141437401845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20843028717019427624934563 31264543075529141437401845)
  ·
    refine ⟨2931050913330857009756423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 31264543075529141437401845 2931050913330857009756423)
    ·
      refine ⟨4396576369996285514634635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2931050913330857009756423 4396576369996285514634635)
      ·
        refine ⟨6594864554994428271951953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4396576369996285514634635 6594864554994428271951953)
        ·
          refine ⟨4946148416245821203963965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6594864554994428271951953 4946148416245821203963965)
          ·
            refine ⟨1854805656092182951486487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4946148416245821203963965 1854805656092182951486487)
            ·
              refine ⟨2782208484138274427229731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1854805656092182951486487 2782208484138274427229731)
              ·
                refine ⟨4173312726207411640844597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2782208484138274427229731 4173312726207411640844597)
                ·
                  refine ⟨391248068081944841329181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4173312726207411640844597 391248068081944841329181)
                  ·
                    rfl

theorem cell20_857197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_857197 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_857197 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_857197 prefixEnd_857197 := by exact prefixLift 857197
  have htrace : WordTrace (prefixWord ++ tailWord_857197) baseStart_857197 baseEnd_857197 := by
    simpa [prefixWord, tailWord_857197, baseEnd_857197] using wordTrace_append hprefix tailTrace_857197
  have hstable : (prefixWord ++ tailWord_857197).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857197).length < 2 ^ (prefixWord ++ tailWord_857197).sum := by decide
  have hdescent : baseEnd_857197 < baseStart_857197 := by decide
  rcases family_descends (prefixWord ++ tailWord_857197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857224 : List Nat := [2, 1, 3, 4, 3, 1, 2, 4]
def baseStart_857224 : Nat := 118140960795 + 857224 * 2 ^ 59
def prefixEnd_857224 : Nat := 4983230072969 + 3 ^ 40 * 857224 * 2
def baseEnd_857224 : Nat := 130420130539217582476357

theorem tailTrace_857224 : CollatzResearch.WordTrace tailWord_857224 prefixEnd_857224 130420130539217582476357 := by
  unfold tailWord_857224
  simp only [CollatzResearch.WordTrace]
  refine ⟨15632763923215662524317363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20843685230954216699089817 15632763923215662524317363)
  ·
    refine ⟨23449145884823493786476045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15632763923215662524317363 23449145884823493786476045)
    ·
      refine ⟨8793429706808810169928517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23449145884823493786476045 8793429706808810169928517)
      ·
        refine ⟨1648768070026651906861597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8793429706808810169928517 1648768070026651906861597)
        ·
          refine ⟨618288026259994465073099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1648768070026651906861597 618288026259994465073099)
          ·
            refine ⟨927432039389991697609649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 618288026259994465073099 927432039389991697609649)
            ·
              refine ⟨695574029542493773207237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 927432039389991697609649 695574029542493773207237)
              ·
                refine ⟨130420130539217582476357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 695574029542493773207237 130420130539217582476357)
                ·
                  rfl

theorem cell20_857224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 2, 4].length) (baseStart_857224 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_857224 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_857224 prefixEnd_857224 := by exact prefixLift 857224
  have htrace : WordTrace (prefixWord ++ tailWord_857224) baseStart_857224 baseEnd_857224 := by
    simpa [prefixWord, tailWord_857224, baseEnd_857224] using wordTrace_append hprefix tailTrace_857224
  have hstable : (prefixWord ++ tailWord_857224).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857224).length < 2 ^ (prefixWord ++ tailWord_857224).sum := by decide
  have hdescent : baseEnd_857224 < baseStart_857224 := by decide
  rcases family_descends (prefixWord ++ tailWord_857224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857255 : List Nat := [1, 1, 6, 2, 1, 2, 3, 2, 2]
def baseStart_857255 : Nat := 118140960795 + 857255 * 2 ^ 59
def prefixEnd_857255 : Nat := 4983230072969 + 3 ^ 40 * 857255 * 2
def baseEnd_857255 : Nat := 391274540862354417395611

theorem tailTrace_857255 : CollatzResearch.WordTrace tailWord_857255 prefixEnd_857255 391274540862354417395611 := by
  unfold tailWord_857255
  simp only [CollatzResearch.WordTrace]
  refine ⟨31266658509319017343013219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20844439006212678228675479 31266658509319017343013219)
  ·
    refine ⟨46899987763978526014519829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31266658509319017343013219 46899987763978526014519829)
    ·
      refine ⟨2198436926436493406930617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 46899987763978526014519829 2198436926436493406930617)
      ·
        refine ⟨1648827694827370055197963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2198436926436493406930617 1648827694827370055197963)
        ·
          refine ⟨2473241542241055082796945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1648827694827370055197963 2473241542241055082796945)
          ·
            refine ⟨1854931156680791312097709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2473241542241055082796945 1854931156680791312097709)
            ·
              refine ⟨695599183755296742036641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1854931156680791312097709 695599183755296742036641)
              ·
                refine ⟨521699387816472556527481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 695599183755296742036641 521699387816472556527481)
                ·
                  refine ⟨391274540862354417395611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 521699387816472556527481 391274540862354417395611)
                  ·
                    rfl

theorem cell20_857255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 3, 2, 2].length) (baseStart_857255 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_857255 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_857255 prefixEnd_857255 := by exact prefixLift 857255
  have htrace : WordTrace (prefixWord ++ tailWord_857255) baseStart_857255 baseEnd_857255 := by
    simpa [prefixWord, tailWord_857255, baseEnd_857255] using wordTrace_append hprefix tailTrace_857255
  have hstable : (prefixWord ++ tailWord_857255).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857255).length < 2 ^ (prefixWord ++ tailWord_857255).sum := by decide
  have hdescent : baseEnd_857255 < baseStart_857255 := by decide
  rcases family_descends (prefixWord ++ tailWord_857255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857273 : List Nat := [1, 2, 1, 4, 1, 4, 1, 3, 3]
def baseStart_857273 : Nat := 118140960795 + 857273 * 2 ^ 59
def prefixEnd_857273 : Nat := 4983230072969 + 3 ^ 40 * 857273 * 2
def baseEnd_857273 : Nat := 391282756552826354795537

theorem tailTrace_857273 : CollatzResearch.WordTrace tailWord_857273 prefixEnd_857273 391282756552826354795537 := by
  unfold tailWord_857273
  simp only [CollatzResearch.WordTrace]
  refine ⟨31267315023253806417168473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20844876682169204278112315 31267315023253806417168473)
  ·
    refine ⟨23450486267440354812876355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31267315023253806417168473 23450486267440354812876355)
    ·
      refine ⟨35175729401160532219314533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23450486267440354812876355 35175729401160532219314533)
      ·
        refine ⟨6595449262717599791121475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35175729401160532219314533 6595449262717599791121475)
        ·
          refine ⟨9893173894076399686682213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6595449262717599791121475 9893173894076399686682213)
          ·
            refine ⟨1854970105139324941252915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9893173894076399686682213 1854970105139324941252915)
            ·
              refine ⟨2782455157708987411879373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1854970105139324941252915 2782455157708987411879373)
              ·
                refine ⟨1043420684140870279454765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2782455157708987411879373 1043420684140870279454765)
                ·
                  refine ⟨391282756552826354795537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1043420684140870279454765 391282756552826354795537)
                  ·
                    rfl

theorem cell20_857273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 3, 3].length) (baseStart_857273 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_857273 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_857273 prefixEnd_857273 := by exact prefixLift 857273
  have htrace : WordTrace (prefixWord ++ tailWord_857273) baseStart_857273 baseEnd_857273 := by
    simpa [prefixWord, tailWord_857273, baseEnd_857273] using wordTrace_append hprefix tailTrace_857273
  have hstable : (prefixWord ++ tailWord_857273).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857273).length < 2 ^ (prefixWord ++ tailWord_857273).sum := by decide
  have hdescent : baseEnd_857273 < baseStart_857273 := by decide
  rcases family_descends (prefixWord ++ tailWord_857273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857352 : List Nat := [2, 1, 3, 2, 4, 1, 2, 3, 2]
def baseStart_857352 : Nat := 118140960795 + 857352 * 2 ^ 59
def prefixEnd_857352 : Nat := 4983230072969 + 3 ^ 40 * 857352 * 2
def baseEnd_857352 : Nat := 391318814305453191161881

theorem tailTrace_857352 : CollatzResearch.WordTrace tailWord_857352 prefixEnd_857352 391318814305453191161881 := by
  unfold tailWord_857352
  simp only [CollatzResearch.WordTrace]
  refine ⟨15635098194983801454647155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20846797593311735272862873 15635098194983801454647155)
  ·
    refine ⟨23452647292475702181970733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15635098194983801454647155 23452647292475702181970733)
    ·
      refine ⟨8794742734678388318239025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23452647292475702181970733 8794742734678388318239025)
      ·
        refine ⟨6596057051008791238679269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8794742734678388318239025 6596057051008791238679269)
        ·
          refine ⟨1236760697064148357252363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6596057051008791238679269 1236760697064148357252363)
          ·
            refine ⟨1855141045596222535878545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1236760697064148357252363 1855141045596222535878545)
            ·
              refine ⟨1391355784197166901908909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1855141045596222535878545 1391355784197166901908909)
              ·
                refine ⟨521758419073937588215841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1391355784197166901908909 521758419073937588215841)
                ·
                  refine ⟨391318814305453191161881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 521758419073937588215841 391318814305453191161881)
                  ·
                    rfl

theorem cell20_857352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 2, 3, 2].length) (baseStart_857352 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_857352 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_857352 prefixEnd_857352 := by exact prefixLift 857352
  have htrace : WordTrace (prefixWord ++ tailWord_857352) baseStart_857352 baseEnd_857352 := by
    simpa [prefixWord, tailWord_857352, baseEnd_857352] using wordTrace_append hprefix tailTrace_857352
  have hstable : (prefixWord ++ tailWord_857352).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857352).length < 2 ^ (prefixWord ++ tailWord_857352).sum := by decide
  have hdescent : baseEnd_857352 < baseStart_857352 := by decide
  rcases family_descends (prefixWord ++ tailWord_857352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857362 : List Nat := [3, 2, 4, 2, 1, 2, 1, 2, 3]
def baseStart_857362 : Nat := 118140960795 + 857362 * 2 ^ 59
def prefixEnd_857362 : Nat := 4983230072969 + 3 ^ 40 * 857362 * 2
def baseEnd_857362 : Nat := 391323378577937600828507

theorem tailTrace_857362 : CollatzResearch.WordTrace tailWord_857362 prefixEnd_857362 391323378577937600828507 := by
  unfold tailWord_857362
  simp only [CollatzResearch.WordTrace]
  refine ⟨7817640279982843654289585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20847040746620916411438893 7817640279982843654289585)
  ·
    refine ⟨5863230209987132740717189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7817640279982843654289585 5863230209987132740717189)
    ·
      refine ⟨1099355664372587388884473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5863230209987132740717189 1099355664372587388884473)
      ·
        refine ⟨824516748279440541663355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1099355664372587388884473 824516748279440541663355)
        ·
          refine ⟨1236775122419160812495033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 824516748279440541663355 1236775122419160812495033)
          ·
            refine ⟨927581341814370609371275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1236775122419160812495033 927581341814370609371275)
            ·
              refine ⟨1391372012721555914056913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 927581341814370609371275 1391372012721555914056913)
              ·
                refine ⟨1043529009541166935542685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1391372012721555914056913 1043529009541166935542685)
                ·
                  refine ⟨391323378577937600828507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1043529009541166935542685 391323378577937600828507)
                  ·
                    rfl

theorem cell20_857362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 1, 2, 3].length) (baseStart_857362 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_857362 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_857362 prefixEnd_857362 := by exact prefixLift 857362
  have htrace : WordTrace (prefixWord ++ tailWord_857362) baseStart_857362 baseEnd_857362 := by
    simpa [prefixWord, tailWord_857362, baseEnd_857362] using wordTrace_append hprefix tailTrace_857362
  have hstable : (prefixWord ++ tailWord_857362).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857362).length < 2 ^ (prefixWord ++ tailWord_857362).sum := by decide
  have hdescent : baseEnd_857362 < baseStart_857362 := by decide
  rcases family_descends (prefixWord ++ tailWord_857362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857373 : List Nat := [1, 4, 2, 3, 1, 2, 2, 1, 4]
def baseStart_857373 : Nat := 118140960795 + 857373 * 2 ^ 59
def prefixEnd_857373 : Nat := 4983230072969 + 3 ^ 40 * 857373 * 2
def baseEnd_857373 : Nat := 391328399277670451461795

theorem tailTrace_857373 : CollatzResearch.WordTrace tailWord_857373 prefixEnd_857373 391328399277670451461795 := by
  unfold tailWord_857373
  simp only [CollatzResearch.WordTrace]
  refine ⟨31270962322891523495808773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20847308215261015663872515 31270962322891523495808773)
  ·
    refine ⟨5863305435542160655464145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31270962322891523495808773 5863305435542160655464145)
    ·
      refine ⟨4397479076656620491598109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5863305435542160655464145 4397479076656620491598109)
      ·
        refine ⟨1649054653746232684349291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4397479076656620491598109 1649054653746232684349291)
        ·
          refine ⟨2473581980619349026523937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1649054653746232684349291 2473581980619349026523937)
          ·
            refine ⟨1855186485464511769892953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2473581980619349026523937 1855186485464511769892953)
            ·
              refine ⟨1391389864098383827419715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1855186485464511769892953 1391389864098383827419715)
              ·
                refine ⟨2087084796147575741129573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1391389864098383827419715 2087084796147575741129573)
                ·
                  refine ⟨391328399277670451461795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2087084796147575741129573 391328399277670451461795)
                  ·
                    rfl

theorem cell20_857373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 2, 1, 4].length) (baseStart_857373 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_857373 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_857373 prefixEnd_857373 := by exact prefixLift 857373
  have htrace : WordTrace (prefixWord ++ tailWord_857373) baseStart_857373 baseEnd_857373 := by
    simpa [prefixWord, tailWord_857373, baseEnd_857373] using wordTrace_append hprefix tailTrace_857373
  have hstable : (prefixWord ++ tailWord_857373).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857373).length < 2 ^ (prefixWord ++ tailWord_857373).sum := by decide
  have hdescent : baseEnd_857373 < baseStart_857373 := by decide
  rcases family_descends (prefixWord ++ tailWord_857373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857394 : List Nat := [3, 2, 1, 1, 4, 1, 2, 2, 4]
def baseStart_857394 : Nat := 118140960795 + 857394 * 2 ^ 59
def prefixEnd_857394 : Nat := 4983230072969 + 3 ^ 40 * 857394 * 2
def baseEnd_857394 : Nat := 391337984249887711761709

theorem tailTrace_857394 : CollatzResearch.WordTrace tailWord_857394 prefixEnd_857394 391337984249887711761709 := by
  unfold tailWord_857394
  simp only [CollatzResearch.WordTrace]
  refine ⟨7817932063953861020580809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20847818837210296054882157 7817932063953861020580809)
  ·
    refine ⟨5863449047965395765435607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7817932063953861020580809 5863449047965395765435607)
    ·
      refine ⟨8795173571948093648153411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5863449047965395765435607 8795173571948093648153411)
      ·
        refine ⟨13192760357922140472230117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8795173571948093648153411 13192760357922140472230117)
        ·
          refine ⟨2473642567110401338543147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13192760357922140472230117 2473642567110401338543147)
          ·
            refine ⟨3710463850665602007814721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2473642567110401338543147 3710463850665602007814721)
            ·
              refine ⟨2782847887999201505861041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3710463850665602007814721 2782847887999201505861041)
              ·
                refine ⟨2087135915999401129395781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2782847887999201505861041 2087135915999401129395781)
                ·
                  refine ⟨391337984249887711761709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2087135915999401129395781 391337984249887711761709)
                  ·
                    rfl

theorem cell20_857394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 2, 4].length) (baseStart_857394 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_857394 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_857394 prefixEnd_857394 := by exact prefixLift 857394
  have htrace : WordTrace (prefixWord ++ tailWord_857394) baseStart_857394 baseEnd_857394 := by
    simpa [prefixWord, tailWord_857394, baseEnd_857394] using wordTrace_append hprefix tailTrace_857394
  have hstable : (prefixWord ++ tailWord_857394).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857394).length < 2 ^ (prefixWord ++ tailWord_857394).sum := by decide
  have hdescent : baseEnd_857394 < baseStart_857394 := by decide
  rcases family_descends (prefixWord ++ tailWord_857394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857414 : List Nat := [6, 1, 1, 3, 1, 2, 6]
def baseStart_857414 : Nat := 118140960795 + 857414 * 2 ^ 59
def prefixEnd_857414 : Nat := 4983230072969 + 3 ^ 40 * 857414 * 2
def baseEnd_857414 : Nat := 43483012532761836788329

theorem tailTrace_857414 : CollatzResearch.WordTrace tailWord_857414 prefixEnd_857414 43483012532761836788329 := by
  unfold tailWord_857414
  simp only [CollatzResearch.WordTrace]
  refine ⟨977264303616968359314103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 20848305143828658332034197 977264303616968359314103)
  ·
    refine ⟨1465896455425452538971155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 977264303616968359314103 1465896455425452538971155)
    ·
      refine ⟨2198844683138178808456733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1465896455425452538971155 2198844683138178808456733)
      ·
        refine ⟨824566756176817053171275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2198844683138178808456733 824566756176817053171275)
        ·
          refine ⟨1236850134265225579756913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 824566756176817053171275 1236850134265225579756913)
          ·
            refine ⟨927637600698919184817685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1236850134265225579756913 927637600698919184817685)
            ·
              refine ⟨43483012532761836788329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 927637600698919184817685 43483012532761836788329)
              ·
                rfl

theorem cell20_857414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 6].length) (baseStart_857414 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_857414 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_857414 prefixEnd_857414 := by exact prefixLift 857414
  have htrace : WordTrace (prefixWord ++ tailWord_857414) baseStart_857414 baseEnd_857414 := by
    simpa [prefixWord, tailWord_857414, baseEnd_857414] using wordTrace_append hprefix tailTrace_857414
  have hstable : (prefixWord ++ tailWord_857414).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857414).length < 2 ^ (prefixWord ++ tailWord_857414).sum := by decide
  have hdescent : baseEnd_857414 < baseStart_857414 := by decide
  rcases family_descends (prefixWord ++ tailWord_857414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857428 : List Nat := [2, 4, 1, 1, 2, 1, 5, 2, 2]
def baseStart_857428 : Nat := 118140960795 + 857428 * 2 ^ 59
def prefixEnd_857428 : Nat := 4983230072969 + 3 ^ 40 * 857428 * 2
def baseEnd_857428 : Nat := 391353502776334704628237

theorem tailTrace_857428 : CollatzResearch.WordTrace tailWord_857428 prefixEnd_857428 391353502776334704628237 := by
  unfold tailWord_857428
  simp only [CollatzResearch.WordTrace]
  refine ⟨15636484168846133944530469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20848645558461511926040625 15636484168846133944530469)
  ·
    refine ⟨2931840781658650114599463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15636484168846133944530469 2931840781658650114599463)
    ·
      refine ⟨4397761172487975171899195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2931840781658650114599463 4397761172487975171899195)
      ·
        refine ⟨6596641758731962757848793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4397761172487975171899195 6596641758731962757848793)
        ·
          refine ⟨4947481319048972068386595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6596641758731962757848793 4947481319048972068386595)
          ·
            refine ⟨7421221978573458102579893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4947481319048972068386595 7421221978573458102579893)
            ·
              refine ⟨695739560491261697116865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7421221978573458102579893 695739560491261697116865)
              ·
                refine ⟨521804670368446272837649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 695739560491261697116865 521804670368446272837649)
                ·
                  refine ⟨391353502776334704628237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 521804670368446272837649 391353502776334704628237)
                  ·
                    rfl

theorem cell20_857428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 5, 2, 2].length) (baseStart_857428 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_857428 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_857428 prefixEnd_857428 := by exact prefixLift 857428
  have htrace : WordTrace (prefixWord ++ tailWord_857428) baseStart_857428 baseEnd_857428 := by
    simpa [prefixWord, tailWord_857428, baseEnd_857428] using wordTrace_append hprefix tailTrace_857428
  have hstable : (prefixWord ++ tailWord_857428).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857428).length < 2 ^ (prefixWord ++ tailWord_857428).sum := by decide
  have hdescent : baseEnd_857428 < baseStart_857428 := by decide
  rcases family_descends (prefixWord ++ tailWord_857428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_857490 : List Nat := [3, 2, 3, 3, 2, 1, 1, 5]
def baseStart_857490 : Nat := 118140960795 + 857490 * 2 ^ 59
def prefixEnd_857490 : Nat := 4983230072969 + 3 ^ 40 * 857490 * 2
def baseEnd_857490 : Nat := 130460600421912681520439

theorem tailTrace_857490 : CollatzResearch.WordTrace tailWord_857490 prefixEnd_857490 130460600421912681520439 := by
  unfold tailWord_857490
  simp only [CollatzResearch.WordTrace]
  refine ⟨7818807415866913119454481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20850153108978434985211949 7818807415866913119454481)
  ·
    refine ⟨5864105561900184839590861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7818807415866913119454481 5864105561900184839590861)
    ·
      refine ⟨2199039585712569314846573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5864105561900184839590861 2199039585712569314846573)
      ·
        refine ⟨824639844642213493067465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2199039585712569314846573 824639844642213493067465)
        ·
          refine ⟨618479883481660119800599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 824639844642213493067465 618479883481660119800599)
          ·
            refine ⟨927719825222490179700899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 618479883481660119800599 927719825222490179700899)
            ·
              refine ⟨1391579737833735269551349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 927719825222490179700899 1391579737833735269551349)
              ·
                refine ⟨130460600421912681520439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1391579737833735269551349 130460600421912681520439)
                ·
                  rfl

theorem cell20_857490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 1, 5].length) (baseStart_857490 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_857490 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_857490 prefixEnd_857490 := by exact prefixLift 857490
  have htrace : WordTrace (prefixWord ++ tailWord_857490) baseStart_857490 baseEnd_857490 := by
    simpa [prefixWord, tailWord_857490, baseEnd_857490] using wordTrace_append hprefix tailTrace_857490
  have hstable : (prefixWord ++ tailWord_857490).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_857490).length < 2 ^ (prefixWord ++ tailWord_857490).sum := by decide
  have hdescent : baseEnd_857490 < baseStart_857490 := by decide
  rcases family_descends (prefixWord ++ tailWord_857490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
