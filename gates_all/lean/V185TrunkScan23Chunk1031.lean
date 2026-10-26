import V185TrunkScan23Chunk1030

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6103529 : List Nat := [1, 2, 1, 1, 1, 2, 1, 7, 1, 4, 2]
def baseStart_6103529 : Nat := 118140960795 + 6103529 * 2 ^ 59
def prefixEnd_6103529 : Nat := 4983230072969 + 3 ^ 40 * 6103529 * 2
def baseEnd_6103529 : Nat := 3134044065655955648417887

theorem tailTrace_6103529 : CollatzResearch.WordTrace tailWord_6103529 prefixEnd_6103529 3134044065655955648417887 := by
  unfold tailWord_6103529
  simp only [CollatzResearch.WordTrace]
  refine ⟨222613991104964307608625641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148409327403309538405750427 222613991104964307608625641)
  ·
    refine ⟨166960493328723230706469231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222613991104964307608625641 166960493328723230706469231)
    ·
      refine ⟨250440739993084846059703847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166960493328723230706469231 250440739993084846059703847)
      ·
        refine ⟨375661109989627269089555771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250440739993084846059703847 375661109989627269089555771)
        ·
          refine ⟨563491664984440903634333657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 375661109989627269089555771 563491664984440903634333657)
          ·
            refine ⟨422618748738330677725750243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 563491664984440903634333657 422618748738330677725750243)
            ·
              refine ⟨633928123107496016588625365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 422618748738330677725750243 633928123107496016588625365)
              ·
                refine ⟨14857690385331937888795907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 633928123107496016588625365 14857690385331937888795907)
                ·
                  refine ⟨22286535577997906833193861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14857690385331937888795907 22286535577997906833193861)
                  ·
                    refine ⟨4178725420874607531223849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22286535577997906833193861 4178725420874607531223849)
                    ·
                      refine ⟨3134044065655955648417887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4178725420874607531223849 3134044065655955648417887)
                      ·
                        rfl

theorem cell23_6103529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 7, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 7, 1, 4, 2].length) (baseStart_6103529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6103529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6103529 prefixEnd_6103529 := by exact prefixLift 6103529
  have htrace : WordTrace (prefixWord ++ tailWord_6103529) baseStart_6103529 baseEnd_6103529 := by
    simpa [prefixWord, tailWord_6103529, baseEnd_6103529] using wordTrace_append hprefix tailTrace_6103529
  have hstable : (prefixWord ++ tailWord_6103529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6103529).length < 2 ^ (prefixWord ++ tailWord_6103529).sum := by decide
  have hdescent : baseEnd_6103529 < baseStart_6103529 := by decide
  rcases family_descends (prefixWord ++ tailWord_6103529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6103532 : List Nat := [2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 5]
def baseStart_6103532 : Nat := 118140960795 + 6103532 * 2 ^ 59
def prefixEnd_6103532 : Nat := 4983230072969 + 3 ^ 40 * 6103532 * 2
def baseEnd_6103532 : Nat := 3134045606097919136680373

theorem tailTrace_6103532 : CollatzResearch.WordTrace tailWord_6103532 prefixEnd_6103532 3134045606097919136680373 := by
  unfold tailWord_6103532
  simp only [CollatzResearch.WordTrace]
  refine ⟨111307050261976719560492425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148409400349302292747323233 111307050261976719560492425)
  ·
    refine ⟨83480287696482539670369319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111307050261976719560492425 83480287696482539670369319)
    ·
      refine ⟨125220431544723809505553979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83480287696482539670369319 125220431544723809505553979)
      ·
        refine ⟨187830647317085714258330969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125220431544723809505553979 187830647317085714258330969)
        ·
          refine ⟨140872985487814285693748227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187830647317085714258330969 140872985487814285693748227)
          ·
            refine ⟨211309478231721428540622341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140872985487814285693748227 211309478231721428540622341)
            ·
              refine ⟨39620527168447767851366689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 211309478231721428540622341 39620527168447767851366689)
              ·
                refine ⟨29715395376335825888525017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39620527168447767851366689 29715395376335825888525017)
                ·
                  refine ⟨22286546532251869416393763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29715395376335825888525017 22286546532251869416393763)
                  ·
                    refine ⟨33429819798377804124590645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22286546532251869416393763 33429819798377804124590645)
                    ·
                      refine ⟨3134045606097919136680373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33429819798377804124590645 3134045606097919136680373)
                      ·
                        rfl

theorem cell23_6103532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 5].length) (baseStart_6103532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6103532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6103532 prefixEnd_6103532 := by exact prefixLift 6103532
  have htrace : WordTrace (prefixWord ++ tailWord_6103532) baseStart_6103532 baseEnd_6103532 := by
    simpa [prefixWord, tailWord_6103532, baseEnd_6103532] using wordTrace_append hprefix tailTrace_6103532
  have hstable : (prefixWord ++ tailWord_6103532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6103532).length < 2 ^ (prefixWord ++ tailWord_6103532).sum := by decide
  have hdescent : baseEnd_6103532 < baseStart_6103532 := by decide
  rcases family_descends (prefixWord ++ tailWord_6103532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6103533 : List Nat := [1, 5, 1, 3, 1, 1, 1, 4, 1, 3, 2]
def baseStart_6103533 : Nat := 118140960795 + 6103533 * 2 ^ 59
def prefixEnd_6103533 : Nat := 4983230072969 + 3 ^ 40 * 6103533 * 2
def baseEnd_6103533 : Nat := 3134046119578573632767869

theorem tailTrace_6103533 : CollatzResearch.WordTrace tailWord_6103533 prefixEnd_6103533 3134046119578573632767869 := by
  unfold tailWord_6103533
  simp only [CollatzResearch.WordTrace]
  refine ⟨222614136996949816291771253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148409424664633210861180835 222614136996949816291771253)
  ·
    refine ⟨20870075343464045277353555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 222614136996949816291771253 20870075343464045277353555)
    ·
      refine ⟨31305113015196067916030333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20870075343464045277353555 31305113015196067916030333)
      ·
        refine ⟨11739417380698525468511375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31305113015196067916030333 11739417380698525468511375)
        ·
          refine ⟨17609126071047788202767063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11739417380698525468511375 17609126071047788202767063)
          ·
            refine ⟨26413689106571682304150595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17609126071047788202767063 26413689106571682304150595)
            ·
              refine ⟨39620533659857523456225893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26413689106571682304150595 39620533659857523456225893)
              ·
                refine ⟨7428850061223285648042355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39620533659857523456225893 7428850061223285648042355)
                ·
                  refine ⟨11143275091834928472063533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7428850061223285648042355 11143275091834928472063533)
                  ·
                    refine ⟨4178728159438098177023825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11143275091834928472063533 4178728159438098177023825)
                    ·
                      refine ⟨3134046119578573632767869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4178728159438098177023825 3134046119578573632767869)
                      ·
                        rfl

theorem cell23_6103533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 4, 1, 3, 2].length) (baseStart_6103533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6103533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6103533 prefixEnd_6103533 := by exact prefixLift 6103533
  have htrace : WordTrace (prefixWord ++ tailWord_6103533) baseStart_6103533 baseEnd_6103533 := by
    simpa [prefixWord, tailWord_6103533, baseEnd_6103533] using wordTrace_append hprefix tailTrace_6103533
  have hstable : (prefixWord ++ tailWord_6103533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6103533).length < 2 ^ (prefixWord ++ tailWord_6103533).sum := by decide
  have hdescent : baseEnd_6103533 < baseStart_6103533 := by decide
  rcases family_descends (prefixWord ++ tailWord_6103533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6103562 : List Nat := [3, 1, 2, 2, 2, 1, 1, 1, 1, 2, 7]
def baseStart_6103562 : Nat := 118140960795 + 6103562 * 2 ^ 59
def prefixEnd_6103562 : Nat := 4983230072969 + 3 ^ 40 * 6103562 * 2
def baseEnd_6103562 : Nat := 3134061010517554019305235

theorem tailTrace_6103562 : CollatzResearch.WordTrace tailWord_6103562 prefixEnd_6103562 3134061010517554019305235 := by
  unfold tailWord_6103562
  simp only [CollatzResearch.WordTrace]
  refine ⟨55653798678461188561144235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148410129809229836163051293 55653798678461188561144235)
  ·
    refine ⟨83480698017691782841716353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55653798678461188561144235 83480698017691782841716353)
    ·
      refine ⟨62610523513268837131287265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83480698017691782841716353 62610523513268837131287265)
      ·
        refine ⟨46957892634951627848465449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62610523513268837131287265 46957892634951627848465449)
        ·
          refine ⟨35218419476213720886349087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46957892634951627848465449 35218419476213720886349087)
          ·
            refine ⟨52827629214320581329523631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35218419476213720886349087 52827629214320581329523631)
            ·
              refine ⟨79241443821480871994285447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52827629214320581329523631 79241443821480871994285447)
              ·
                refine ⟨118862165732221307991428171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79241443821480871994285447 118862165732221307991428171)
                ·
                  refine ⟨178293248598331961987142257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 118862165732221307991428171 178293248598331961987142257)
                  ·
                    refine ⟨133719936448748971490356693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 178293248598331961987142257 133719936448748971490356693)
                    ·
                      refine ⟨3134061010517554019305235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 133719936448748971490356693 3134061010517554019305235)
                      ·
                        rfl

theorem cell23_6103562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 1, 2, 7].length) (baseStart_6103562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6103562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6103562 prefixEnd_6103562 := by exact prefixLift 6103562
  have htrace : WordTrace (prefixWord ++ tailWord_6103562) baseStart_6103562 baseEnd_6103562 := by
    simpa [prefixWord, tailWord_6103562, baseEnd_6103562] using wordTrace_append hprefix tailTrace_6103562
  have hstable : (prefixWord ++ tailWord_6103562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6103562).length < 2 ^ (prefixWord ++ tailWord_6103562).sum := by decide
  have hdescent : baseEnd_6103562 < baseStart_6103562 := by decide
  rcases family_descends (prefixWord ++ tailWord_6103562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6103580 : List Nat := [2, 2, 3, 1, 2, 2, 4, 1, 2, 2, 2]
def baseStart_6103580 : Nat := 118140960795 + 6103580 * 2 ^ 59
def prefixEnd_6103580 : Nat := 4983230072969 + 3 ^ 40 * 6103580 * 2
def baseEnd_6103580 : Nat := 3134070253169334948880153

theorem tailTrace_6103580 : CollatzResearch.WordTrace tailWord_6103580 prefixEnd_6103580 3134070253169334948880153 := by
  unfold tailWord_6103580
  simp only [CollatzResearch.WordTrace]
  refine ⟨111307925613889771659366097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148410567485186362212488129 111307925613889771659366097)
  ·
    refine ⟨83480944210417328744524573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111307925613889771659366097 83480944210417328744524573)
    ·
      refine ⟨31305354078906498279196715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83480944210417328744524573 31305354078906498279196715)
      ·
        refine ⟨46958031118359747418795073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31305354078906498279196715 46958031118359747418795073)
        ·
          refine ⟨35218523338769810564096305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46958031118359747418795073 35218523338769810564096305)
          ·
            refine ⟨26413892504077357923072229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35218523338769810564096305 26413892504077357923072229)
            ·
              refine ⟨4952604844514504610576043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26413892504077357923072229 4952604844514504610576043)
              ·
                refine ⟨7428907266771756915864065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4952604844514504610576043 7428907266771756915864065)
                ·
                  refine ⟨5571680450078817686898049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7428907266771756915864065 5571680450078817686898049)
                  ·
                    refine ⟨4178760337559113265173537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5571680450078817686898049 4178760337559113265173537)
                    ·
                      refine ⟨3134070253169334948880153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4178760337559113265173537 3134070253169334948880153)
                      ·
                        rfl

theorem cell23_6103580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 4, 1, 2, 2, 2].length) (baseStart_6103580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6103580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6103580 prefixEnd_6103580 := by exact prefixLift 6103580
  have htrace : WordTrace (prefixWord ++ tailWord_6103580) baseStart_6103580 baseEnd_6103580 := by
    simpa [prefixWord, tailWord_6103580, baseEnd_6103580] using wordTrace_append hprefix tailTrace_6103580
  have hstable : (prefixWord ++ tailWord_6103580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6103580).length < 2 ^ (prefixWord ++ tailWord_6103580).sum := by decide
  have hdescent : baseEnd_6103580 < baseStart_6103580 := by decide
  rcases family_descends (prefixWord ++ tailWord_6103580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6103597 : List Nat := [1, 5, 4, 1, 1, 1, 1, 2, 1, 4, 2]
def baseStart_6103597 : Nat := 118140960795 + 6103597 * 2 ^ 59
def prefixEnd_6103597 : Nat := 4983230072969 + 3 ^ 40 * 6103597 * 2
def baseEnd_6103597 : Nat := 3134078982340461382367575

theorem tailTrace_6103597 : CollatzResearch.WordTrace tailWord_6103597 prefixEnd_6103597 3134078982340461382367575 := by
  unfold tailWord_6103597
  simp only [CollatzResearch.WordTrace]
  refine ⟨222616471268717955222101045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148410980845811970148067363 222616471268717955222101045)
  ·
    refine ⟨20870294181442308302071973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 222616471268717955222101045 20870294181442308302071973)
    ·
      refine ⟨3913180159020432806638495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20870294181442308302071973 3913180159020432806638495)
      ·
        refine ⟨5869770238530649209957743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3913180159020432806638495 5869770238530649209957743)
        ·
          refine ⟨8804655357795973814936615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5869770238530649209957743 8804655357795973814936615)
          ·
            refine ⟨13206983036693960722404923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8804655357795973814936615 13206983036693960722404923)
            ·
              refine ⟨19810474555040941083607385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13206983036693960722404923 19810474555040941083607385)
              ·
                refine ⟨14857855916280705812705539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19810474555040941083607385 14857855916280705812705539)
                ·
                  refine ⟨22286783874421058719058309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14857855916280705812705539 22286783874421058719058309)
                  ·
                    refine ⟨4178771976453948509823433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22286783874421058719058309 4178771976453948509823433)
                    ·
                      refine ⟨3134078982340461382367575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4178771976453948509823433 3134078982340461382367575)
                      ·
                        rfl

theorem cell23_6103597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_6103597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6103597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6103597 prefixEnd_6103597 := by exact prefixLift 6103597
  have htrace : WordTrace (prefixWord ++ tailWord_6103597) baseStart_6103597 baseEnd_6103597 := by
    simpa [prefixWord, tailWord_6103597, baseEnd_6103597] using wordTrace_append hprefix tailTrace_6103597
  have hstable : (prefixWord ++ tailWord_6103597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6103597).length < 2 ^ (prefixWord ++ tailWord_6103597).sum := by decide
  have hdescent : baseEnd_6103597 < baseStart_6103597 := by decide
  rcases family_descends (prefixWord ++ tailWord_6103597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6103619 : List Nat := [1, 1, 1, 3, 1, 2, 1, 2, 3, 6, 2]
def baseStart_6103619 : Nat := 118140960795 + 6103619 * 2 ^ 59
def prefixEnd_6103619 : Nat := 4983230072969 + 3 ^ 40 * 6103619 * 2
def baseEnd_6103619 : Nat := 3134090278914860296292473

theorem tailTrace_6103619 : CollatzResearch.WordTrace tailWord_6103619 prefixEnd_6103619 3134090278914860296292473 := by
  unfold tailWord_6103619
  simp only [CollatzResearch.WordTrace]
  refine ⟨222617273674638252979401911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148411515783092168652934607 222617273674638252979401911)
  ·
    refine ⟨333925910511957379469102867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222617273674638252979401911 333925910511957379469102867)
    ·
      refine ⟨500888865767936069203654301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 333925910511957379469102867 500888865767936069203654301)
      ·
        refine ⟨187833324662976025951370363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 500888865767936069203654301 187833324662976025951370363)
        ·
          refine ⟨281749986994464038927055545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187833324662976025951370363 281749986994464038927055545)
          ·
            refine ⟨211312490245848029195291659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 281749986994464038927055545 211312490245848029195291659)
            ·
              refine ⟨316968735368772043792937489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 211312490245848029195291659 316968735368772043792937489)
              ·
                refine ⟨237726551526579032844703117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 316968735368772043792937489 237726551526579032844703117)
                ·
                  refine ⟨89147456822467137316763669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 237726551526579032844703117 89147456822467137316763669)
                  ·
                    refine ⟨4178787038553147061723297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 89147456822467137316763669 4178787038553147061723297)
                    ·
                      refine ⟨3134090278914860296292473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4178787038553147061723297 3134090278914860296292473)
                      ·
                        rfl

theorem cell23_6103619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 3, 6, 2].length) (baseStart_6103619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6103619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6103619 prefixEnd_6103619 := by exact prefixLift 6103619
  have htrace : WordTrace (prefixWord ++ tailWord_6103619) baseStart_6103619 baseEnd_6103619 := by
    simpa [prefixWord, tailWord_6103619, baseEnd_6103619] using wordTrace_append hprefix tailTrace_6103619
  have hstable : (prefixWord ++ tailWord_6103619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6103619).length < 2 ^ (prefixWord ++ tailWord_6103619).sum := by decide
  have hdescent : baseEnd_6103619 < baseStart_6103619 := by decide
  rcases family_descends (prefixWord ++ tailWord_6103619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6103632 : List Nat := [2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 6]
def baseStart_6103632 : Nat := 118140960795 + 6103632 * 2 ^ 59
def prefixEnd_6103632 : Nat := 4983230072969 + 3 ^ 40 * 6103632 * 2
def baseEnd_6103632 : Nat := 3134096954163368745429913

theorem tailTrace_6103632 : CollatzResearch.WordTrace tailWord_6103632 prefixEnd_6103632 3134096954163368745429913 := by
  unfold tailWord_6103632
  simp only [CollatzResearch.WordTrace]
  refine ⟨111308873911795578099812575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148411831882394104133083433 111308873911795578099812575)
  ·
    refine ⟨166963310867693367149718863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111308873911795578099812575 166963310867693367149718863)
    ·
      refine ⟨250444966301540050724578295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166963310867693367149718863 250444966301540050724578295)
      ·
        refine ⟨375667449452310076086867443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250444966301540050724578295 375667449452310076086867443)
        ·
          refine ⟨563501174178465114130301165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 375667449452310076086867443 563501174178465114130301165)
          ·
            refine ⟨211312940316924417798862937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 563501174178465114130301165 211312940316924417798862937)
            ·
              refine ⟨158484705237693313349147203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 211312940316924417798862937 158484705237693313349147203)
              ·
                refine ⟨237727057856539970023720805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 158484705237693313349147203 237727057856539970023720805)
                ·
                  refine ⟨44573823348101244379447651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 237727057856539970023720805 44573823348101244379447651)
                  ·
                    refine ⟨66860735022151866569171477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44573823348101244379447651 66860735022151866569171477)
                    ·
                      refine ⟨3134096954163368745429913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66860735022151866569171477 3134096954163368745429913)
                      ·
                        rfl

theorem cell23_6103632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 6].length) (baseStart_6103632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6103632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6103632 prefixEnd_6103632 := by exact prefixLift 6103632
  have htrace : WordTrace (prefixWord ++ tailWord_6103632) baseStart_6103632 baseEnd_6103632 := by
    simpa [prefixWord, tailWord_6103632, baseEnd_6103632] using wordTrace_append hprefix tailTrace_6103632
  have hstable : (prefixWord ++ tailWord_6103632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6103632).length < 2 ^ (prefixWord ++ tailWord_6103632).sum := by decide
  have hdescent : baseEnd_6103632 < baseStart_6103632 := by decide
  rcases family_descends (prefixWord ++ tailWord_6103632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6103636 : List Nat := [2, 4, 1, 1, 1, 3, 1, 1, 1, 6, 2]
def baseStart_6103636 : Nat := 118140960795 + 6103636 * 2 ^ 59
def prefixEnd_6103636 : Nat := 4983230072969 + 3 ^ 40 * 6103636 * 2
def baseEnd_6103636 : Nat := 3134099008085986729779895

theorem tailTrace_6103636 : CollatzResearch.WordTrace tailWord_6103636 prefixEnd_6103636 3134099008085986729779895 := by
  unfold tailWord_6103636
  simp only [CollatzResearch.WordTrace]
  refine ⟨111308946857788332441385381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148411929143717776588513841 111308946857788332441385381)
  ·
    refine ⟨20870427535835312332759759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111308946857788332441385381 20870427535835312332759759)
    ·
      refine ⟨31305641303752968499139639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20870427535835312332759759 31305641303752968499139639)
      ·
        refine ⟨46958461955629452748709459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31305641303752968499139639 46958461955629452748709459)
        ·
          refine ⟨70437692933444179123064189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46958461955629452748709459 70437692933444179123064189)
          ·
            refine ⟨26414134850041567171149071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70437692933444179123064189 26414134850041567171149071)
            ·
              refine ⟨39621202275062350756723607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26414134850041567171149071 39621202275062350756723607)
              ·
                refine ⟨59431803412593526135085411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39621202275062350756723607 59431803412593526135085411)
                ·
                  refine ⟨89147705118890289202628117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59431803412593526135085411 89147705118890289202628117)
                  ·
                    refine ⟨4178798677447982306373193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 89147705118890289202628117 4178798677447982306373193)
                    ·
                      refine ⟨3134099008085986729779895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4178798677447982306373193 3134099008085986729779895)
                      ·
                        rfl

theorem cell23_6103636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 1, 1, 6, 2].length) (baseStart_6103636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6103636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6103636 prefixEnd_6103636 := by exact prefixLift 6103636
  have htrace : WordTrace (prefixWord ++ tailWord_6103636) baseStart_6103636 baseEnd_6103636 := by
    simpa [prefixWord, tailWord_6103636, baseEnd_6103636] using wordTrace_append hprefix tailTrace_6103636
  have hstable : (prefixWord ++ tailWord_6103636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6103636).length < 2 ^ (prefixWord ++ tailWord_6103636).sum := by decide
  have hdescent : baseEnd_6103636 < baseStart_6103636 := by decide
  rcases family_descends (prefixWord ++ tailWord_6103636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6103639 : List Nat := [1, 1, 3, 2, 2, 2, 2, 2, 1, 4, 3]
def baseStart_6103639 : Nat := 118140960795 + 6103639 * 2 ^ 59
def prefixEnd_6103639 : Nat := 4983230072969 + 3 ^ 40 * 6103639 * 2
def baseEnd_6103639 : Nat := 3134100548527950218042381

theorem tailTrace_6103639 : CollatzResearch.WordTrace tailWord_6103639 prefixEnd_6103639 3134100548527950218042381 := by
  unfold tailWord_6103639
  simp only [CollatzResearch.WordTrace]
  refine ⟨222618003134565796395129971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148412002089710530930086647 222618003134565796395129971)
  ·
    refine ⟨333927004701848694592694957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222618003134565796395129971 333927004701848694592694957)
    ·
      refine ⟨125222626763193260472260609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 333927004701848694592694957 125222626763193260472260609)
      ·
        refine ⟨93916970072394945354195457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125222626763193260472260609 93916970072394945354195457)
        ·
          refine ⟨70437727554296209015646593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93916970072394945354195457 70437727554296209015646593)
          ·
            refine ⟨52828295665722156761734945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70437727554296209015646593 52828295665722156761734945)
            ·
              refine ⟨39621221749291617571301209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52828295665722156761734945 39621221749291617571301209)
              ·
                refine ⟨29715916311968713178475907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39621221749291617571301209 29715916311968713178475907)
                ·
                  refine ⟨44573874467953069767713861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29715916311968713178475907 44573874467953069767713861)
                  ·
                    refine ⟨8357601462741200581446349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44573874467953069767713861 8357601462741200581446349)
                    ·
                      refine ⟨3134100548527950218042381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8357601462741200581446349 3134100548527950218042381)
                      ·
                        rfl

theorem cell23_6103639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 2, 1, 4, 3].length) (baseStart_6103639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6103639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6103639 prefixEnd_6103639 := by exact prefixLift 6103639
  have htrace : WordTrace (prefixWord ++ tailWord_6103639) baseStart_6103639 baseEnd_6103639 := by
    simpa [prefixWord, tailWord_6103639, baseEnd_6103639] using wordTrace_append hprefix tailTrace_6103639
  have hstable : (prefixWord ++ tailWord_6103639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6103639).length < 2 ^ (prefixWord ++ tailWord_6103639).sum := by decide
  have hdescent : baseEnd_6103639 < baseStart_6103639 := by decide
  rcases family_descends (prefixWord ++ tailWord_6103639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6103642 : List Nat := [3, 1, 1, 2, 1, 1, 1, 1, 12]
def baseStart_6103642 : Nat := 118140960795 + 6103642 * 2 ^ 59
def prefixEnd_6103642 : Nat := 4983230072969 + 3 ^ 40 * 6103642 * 2
def baseEnd_6103642 : Nat := 348233565441101522922763

theorem tailTrace_6103642 : CollatzResearch.WordTrace tailWord_6103642 prefixEnd_6103642 348233565441101522922763 := by
  unfold tailWord_6103642
  simp only [CollatzResearch.WordTrace]
  refine ⟨55654528138388731976872295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148412075035703285271659453 55654528138388731976872295)
  ·
    refine ⟨83481792207583097965308443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55654528138388731976872295 83481792207583097965308443)
    ·
      refine ⟨125222688311374646947962665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83481792207583097965308443 125222688311374646947962665)
      ·
        refine ⟨93917016233530985210971999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125222688311374646947962665 93917016233530985210971999)
        ·
          refine ⟨140875524350296477816457999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93917016233530985210971999 140875524350296477816457999)
          ·
            refine ⟨211313286525444716724686999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140875524350296477816457999 211313286525444716724686999)
            ·
              refine ⟨316969929788167075087030499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 211313286525444716724686999 316969929788167075087030499)
              ·
                refine ⟨475454894682250612630545749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 316969929788167075087030499 475454894682250612630545749)
                ·
                  refine ⟨348233565441101522922763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 475454894682250612630545749 348233565441101522922763)
                  ·
                    rfl

theorem cell23_6103642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 12].length) (baseStart_6103642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6103642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6103642 prefixEnd_6103642 := by exact prefixLift 6103642
  have htrace : WordTrace (prefixWord ++ tailWord_6103642) baseStart_6103642 baseEnd_6103642 := by
    simpa [prefixWord, tailWord_6103642, baseEnd_6103642] using wordTrace_append hprefix tailTrace_6103642
  have hstable : (prefixWord ++ tailWord_6103642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6103642).length < 2 ^ (prefixWord ++ tailWord_6103642).sum := by decide
  have hdescent : baseEnd_6103642 < baseStart_6103642 := by decide
  rcases family_descends (prefixWord ++ tailWord_6103642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6103650 : List Nat := [3, 3, 2, 3, 1, 2, 1, 1, 2, 5]
def baseStart_6103650 : Nat := 118140960795 + 6103650 * 2 ^ 59
def prefixEnd_6103650 : Nat := 4983230072969 + 3 ^ 40 * 6103650 * 2
def baseEnd_6103650 : Nat := 1044702065605049891668277

theorem tailTrace_6103650 : CollatzResearch.WordTrace tailWord_6103650 prefixEnd_6103650 1044702065605049891668277 := by
  unfold tailWord_6103650
  simp only [CollatzResearch.WordTrace]
  refine ⟨55654601084381486318445101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148412269558350630182520269 55654601084381486318445101)
  ·
    refine ⟨20870475406643057369416913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55654601084381486318445101 20870475406643057369416913)
    ·
      refine ⟨15652856554982293027062685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20870475406643057369416913 15652856554982293027062685)
      ·
        refine ⟨5869821208118359885148507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15652856554982293027062685 5869821208118359885148507)
        ·
          refine ⟨8804731812177539827722761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5869821208118359885148507 8804731812177539827722761)
          ·
            refine ⟨6603548859133154870792071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8804731812177539827722761 6603548859133154870792071)
            ·
              refine ⟨9905323288699732306188107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6603548859133154870792071 9905323288699732306188107)
              ·
                refine ⟨14857984933049598459282161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9905323288699732306188107 14857984933049598459282161)
                ·
                  refine ⟨11143488699787198844461621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14857984933049598459282161 11143488699787198844461621)
                  ·
                    refine ⟨1044702065605049891668277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11143488699787198844461621 1044702065605049891668277)
                    ·
                      rfl

theorem cell23_6103650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 1, 1, 2, 5].length) (baseStart_6103650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6103650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6103650 prefixEnd_6103650 := by exact prefixLift 6103650
  have htrace : WordTrace (prefixWord ++ tailWord_6103650) baseStart_6103650 baseEnd_6103650 := by
    simpa [prefixWord, tailWord_6103650, baseEnd_6103650] using wordTrace_append hprefix tailTrace_6103650
  have hstable : (prefixWord ++ tailWord_6103650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6103650).length < 2 ^ (prefixWord ++ tailWord_6103650).sum := by decide
  have hdescent : baseEnd_6103650 < baseStart_6103650 := by decide
  rcases family_descends (prefixWord ++ tailWord_6103650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6103653 : List Nat := [1, 3, 1, 3, 4, 2, 1, 1, 2, 1, 4]
def baseStart_6103653 : Nat := 118140960795 + 6103653 * 2 ^ 59
def prefixEnd_6103653 : Nat := 4983230072969 + 3 ^ 40 * 6103653 * 2
def baseEnd_6103653 : Nat := 3134107737257113163267317

theorem tailTrace_6103653 : CollatzResearch.WordTrace tailWord_6103653 prefixEnd_6103653 3134107737257113163267317 := by
  unfold tailWord_6103653
  simp only [CollatzResearch.WordTrace]
  refine ⟨222618513756515076786139613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148412342504343384524093075 222618513756515076786139613)
  ·
    refine ⟨83481942658693153794802355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 222618513756515076786139613 83481942658693153794802355)
    ·
      refine ⟨125222913988039730692203533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83481942658693153794802355 125222913988039730692203533)
      ·
        refine ⟨46958592745514899009576325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125222913988039730692203533 46958592745514899009576325)
        ·
          refine ⟨8804736139784043564295561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46958592745514899009576325 8804736139784043564295561)
          ·
            refine ⟨6603552104838032673221671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8804736139784043564295561 6603552104838032673221671)
            ·
              refine ⟨9905328157257049009832507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6603552104838032673221671 9905328157257049009832507)
              ·
                refine ⟨14857992235885573514748761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9905328157257049009832507 14857992235885573514748761)
                ·
                  refine ⟨11143494176914180136061571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14857992235885573514748761 11143494176914180136061571)
                  ·
                    refine ⟨16715241265371270204092357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11143494176914180136061571 16715241265371270204092357)
                    ·
                      refine ⟨3134107737257113163267317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16715241265371270204092357 3134107737257113163267317)
                      ·
                        rfl

theorem cell23_6103653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 1, 1, 2, 1, 4].length) (baseStart_6103653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6103653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6103653 prefixEnd_6103653 := by exact prefixLift 6103653
  have htrace : WordTrace (prefixWord ++ tailWord_6103653) baseStart_6103653 baseEnd_6103653 := by
    simpa [prefixWord, tailWord_6103653, baseEnd_6103653] using wordTrace_append hprefix tailTrace_6103653
  have hstable : (prefixWord ++ tailWord_6103653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6103653).length < 2 ^ (prefixWord ++ tailWord_6103653).sum := by decide
  have hdescent : baseEnd_6103653 < baseStart_6103653 := by decide
  rcases family_descends (prefixWord ++ tailWord_6103653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6103756 : List Nat := [2, 2, 1, 5, 1, 1, 2, 1, 1, 1, 6]
def baseStart_6103756 : Nat := 118140960795 + 6103756 * 2 ^ 59
def prefixEnd_6103756 : Nat := 4983230072969 + 3 ^ 40 * 6103756 * 2
def baseEnd_6103756 : Nat := 3134160625764526260279343

theorem tailTrace_6103756 : CollatzResearch.WordTrace tailWord_6103756 prefixEnd_6103756 3134160625764526260279343 := by
  unfold tailWord_6103756
  simp only [CollatzResearch.WordTrace]
  refine ⟨111311135237570962688569561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148414846983427950251426081 111311135237570962688569561)
  ·
    refine ⟨83483351428178222016427171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111311135237570962688569561 83483351428178222016427171)
    ·
      refine ⟨125225027142267333024640757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83483351428178222016427171 125225027142267333024640757)
      ·
        refine ⟨11739846294587562471060071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 125225027142267333024640757 11739846294587562471060071)
        ·
          refine ⟨17609769441881343706590107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11739846294587562471060071 17609769441881343706590107)
          ·
            refine ⟨26414654162822015559885161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17609769441881343706590107 26414654162822015559885161)
            ·
              refine ⟨19810990622116511669913871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26414654162822015559885161 19810990622116511669913871)
              ·
                refine ⟨29716485933174767504870807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19810990622116511669913871 29716485933174767504870807)
                ·
                  refine ⟨44574728899762151257306211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29716485933174767504870807 44574728899762151257306211)
                  ·
                    refine ⟨66862093349643226885959317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44574728899762151257306211 66862093349643226885959317)
                    ·
                      refine ⟨3134160625764526260279343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66862093349643226885959317 3134160625764526260279343)
                      ·
                        rfl

theorem cell23_6103756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_6103756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6103756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6103756 prefixEnd_6103756 := by exact prefixLift 6103756
  have htrace : WordTrace (prefixWord ++ tailWord_6103756) baseStart_6103756 baseEnd_6103756 := by
    simpa [prefixWord, tailWord_6103756, baseEnd_6103756] using wordTrace_append hprefix tailTrace_6103756
  have hstable : (prefixWord ++ tailWord_6103756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6103756).length < 2 ^ (prefixWord ++ tailWord_6103756).sum := by decide
  have hdescent : baseEnd_6103756 < baseStart_6103756 := by decide
  rcases family_descends (prefixWord ++ tailWord_6103756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6103757 : List Nat := [1, 6, 2, 1, 2, 2, 1, 2, 1, 5]
def baseStart_6103757 : Nat := 118140960795 + 6103757 * 2 ^ 59
def prefixEnd_6103757 : Nat := 4983230072969 + 3 ^ 40 * 6103757 * 2
def baseEnd_6103757 : Nat := 1044720379748393585455613

theorem tailTrace_6103757 : CollatzResearch.WordTrace tailWord_6103757 prefixEnd_6103757 1044720379748393585455613 := by
  unfold tailWord_6103757
  simp only [CollatzResearch.WordTrace]
  refine ⟨222622306948138302547925525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148414871298758868365283683 222622306948138302547925525)
  ·
    refine ⟨10435420638193982931934009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 222622306948138302547925525 10435420638193982931934009)
    ·
      refine ⟨7826565478645487198950507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10435420638193982931934009 7826565478645487198950507)
      ·
        refine ⟨11739848217968230798425761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7826565478645487198950507 11739848217968230798425761)
        ·
          refine ⟨8804886163476173098819321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11739848217968230798425761 8804886163476173098819321)
          ·
            refine ⟨6603664622607129824114491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8804886163476173098819321 6603664622607129824114491)
            ·
              refine ⟨9905496933910694736171737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6603664622607129824114491 9905496933910694736171737)
              ·
                refine ⟨7429122700433021052128803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9905496933910694736171737 7429122700433021052128803)
                ·
                  refine ⟨11143684050649531578193205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7429122700433021052128803 11143684050649531578193205)
                  ·
                    refine ⟨1044720379748393585455613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11143684050649531578193205 1044720379748393585455613)
                    ·
                      rfl

theorem cell23_6103757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_6103757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6103757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6103757 prefixEnd_6103757 := by exact prefixLift 6103757
  have htrace : WordTrace (prefixWord ++ tailWord_6103757) baseStart_6103757 baseEnd_6103757 := by
    simpa [prefixWord, tailWord_6103757, baseEnd_6103757] using wordTrace_append hprefix tailTrace_6103757
  have hstable : (prefixWord ++ tailWord_6103757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6103757).length < 2 ^ (prefixWord ++ tailWord_6103757).sum := by decide
  have hdescent : baseEnd_6103757 < baseStart_6103757 := by decide
  rcases family_descends (prefixWord ++ tailWord_6103757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6103780 : List Nat := [2, 3, 1, 1, 1, 5, 3, 1, 1, 2, 3]
def baseStart_6103780 : Nat := 118140960795 + 6103780 * 2 ^ 59
def prefixEnd_6103780 : Nat := 4983230072969 + 3 ^ 40 * 6103780 * 2
def baseEnd_6103780 : Nat := 3134172949300234166379233

theorem tailTrace_6103780 : CollatzResearch.WordTrace tailWord_6103780 prefixEnd_6103780 3134172949300234166379233 := by
  unfold tailWord_6103780
  simp only [CollatzResearch.WordTrace]
  refine ⟨111311572913527488738006397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148415430551369984984008529 111311572913527488738006397)
  ·
    refine ⟨41741839842572808276752399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111311572913527488738006397 41741839842572808276752399)
    ·
      refine ⟨62612759763859212415128599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41741839842572808276752399 62612759763859212415128599)
      ·
        refine ⟨93919139645788818622692899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62612759763859212415128599 93919139645788818622692899)
        ·
          refine ⟨140878709468683227934039349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93919139645788818622692899 140878709468683227934039349)
          ·
            refine ⟨13207379012689052618816189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 140878709468683227934039349 13207379012689052618816189)
            ·
              refine ⟨4952767129758394732056071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13207379012689052618816189 4952767129758394732056071)
              ·
                refine ⟨7429150694637592098084107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4952767129758394732056071 7429150694637592098084107)
                ·
                  refine ⟨11143726041956388147126161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7429150694637592098084107 11143726041956388147126161)
                  ·
                    refine ⟨8357794531467291110344621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11143726041956388147126161 8357794531467291110344621)
                    ·
                      refine ⟨3134172949300234166379233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8357794531467291110344621 3134172949300234166379233)
                      ·
                        rfl

theorem cell23_6103780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 3, 1, 1, 2, 3].length) (baseStart_6103780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6103780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6103780 prefixEnd_6103780 := by exact prefixLift 6103780
  have htrace : WordTrace (prefixWord ++ tailWord_6103780) baseStart_6103780 baseEnd_6103780 := by
    simpa [prefixWord, tailWord_6103780, baseEnd_6103780] using wordTrace_append hprefix tailTrace_6103780
  have hstable : (prefixWord ++ tailWord_6103780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6103780).length < 2 ^ (prefixWord ++ tailWord_6103780).sum := by decide
  have hdescent : baseEnd_6103780 < baseStart_6103780 := by decide
  rcases family_descends (prefixWord ++ tailWord_6103780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6103794 : List Nat := [3, 2, 1, 3, 1, 2, 4, 2, 1, 2, 2]
def baseStart_6103794 : Nat := 118140960795 + 6103794 * 2 ^ 59
def prefixEnd_6103794 : Nat := 4983230072969 + 3 ^ 40 * 6103794 * 2
def baseEnd_6103794 : Nat := 3134180138029397111604169

theorem tailTrace_6103794 : CollatzResearch.WordTrace tailWord_6103794 prefixEnd_6103794 3134180138029397111604169 := by
  unfold tailWord_6103794
  simp only [CollatzResearch.WordTrace]
  refine ⟨55655914112251064466755609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148415770966002838578014957 55655914112251064466755609)
  ·
    refine ⟨41741935584188298350066707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55655914112251064466755609 41741935584188298350066707)
    ·
      refine ⟨62612903376282447525100061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41741935584188298350066707 62612903376282447525100061)
      ·
        refine ⟨23479838766105917821912523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62612903376282447525100061 23479838766105917821912523)
        ·
          refine ⟨35219758149158876732868785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23479838766105917821912523 35219758149158876732868785)
          ·
            refine ⟨26414818611869157549651589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35219758149158876732868785 26414818611869157549651589)
            ·
              refine ⟨4952778489725467040559673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26414818611869157549651589 4952778489725467040559673)
              ·
                refine ⟨3714583867294100280419755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4952778489725467040559673 3714583867294100280419755)
                ·
                  refine ⟨5571875800941150420629633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3714583867294100280419755 5571875800941150420629633)
                  ·
                    refine ⟨4178906850705862815472225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5571875800941150420629633 4178906850705862815472225)
                    ·
                      refine ⟨3134180138029397111604169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4178906850705862815472225 3134180138029397111604169)
                      ·
                        rfl

theorem cell23_6103794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 4, 2, 1, 2, 2].length) (baseStart_6103794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6103794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6103794 prefixEnd_6103794 := by exact prefixLift 6103794
  have htrace : WordTrace (prefixWord ++ tailWord_6103794) baseStart_6103794 baseEnd_6103794 := by
    simpa [prefixWord, tailWord_6103794, baseEnd_6103794] using wordTrace_append hprefix tailTrace_6103794
  have hstable : (prefixWord ++ tailWord_6103794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6103794).length < 2 ^ (prefixWord ++ tailWord_6103794).sum := by decide
  have hdescent : baseEnd_6103794 < baseStart_6103794 := by decide
  rcases family_descends (prefixWord ++ tailWord_6103794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6103810 : List Nat := [3, 4, 1, 1, 1, 3, 2, 1, 1, 3, 3]
def baseStart_6103810 : Nat := 118140960795 + 6103810 * 2 ^ 59
def prefixEnd_6103810 : Nat := 4983230072969 + 3 ^ 40 * 6103810 * 2
def baseEnd_6103810 : Nat := 3134188353719869049004095

theorem tailTrace_6103810 : CollatzResearch.WordTrace tailWord_6103810 prefixEnd_6103810 3134188353719869049004095 := by
  unfold tailWord_6103810
  simp only [CollatzResearch.WordTrace]
  refine ⟨55656060004236573149901221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148416160011297528399736589 55656060004236573149901221)
  ·
    refine ⟨10435511250794357465606479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55656060004236573149901221 10435511250794357465606479)
    ·
      refine ⟨15653266876191536198409719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10435511250794357465606479 15653266876191536198409719)
      ·
        refine ⟨23479900314287304297614579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15653266876191536198409719 23479900314287304297614579)
        ·
          refine ⟨35219850471430956446421869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23479900314287304297614579 35219850471430956446421869)
          ·
            refine ⟨13207443926786608667408201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35219850471430956446421869 13207443926786608667408201)
            ·
              refine ⟨9905582945089956500556151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13207443926786608667408201 9905582945089956500556151)
              ·
                refine ⟨14858374417634934750834227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9905582945089956500556151 14858374417634934750834227)
                ·
                  refine ⟨22287561626452402126251341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14858374417634934750834227 22287561626452402126251341)
                  ·
                    refine ⟨8357835609919650797344253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22287561626452402126251341 8357835609919650797344253)
                    ·
                      refine ⟨3134188353719869049004095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8357835609919650797344253 3134188353719869049004095)
                      ·
                        rfl

theorem cell23_6103810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 2, 1, 1, 3, 3].length) (baseStart_6103810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6103810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6103810 prefixEnd_6103810 := by exact prefixLift 6103810
  have htrace : WordTrace (prefixWord ++ tailWord_6103810) baseStart_6103810 baseEnd_6103810 := by
    simpa [prefixWord, tailWord_6103810, baseEnd_6103810] using wordTrace_append hprefix tailTrace_6103810
  have hstable : (prefixWord ++ tailWord_6103810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6103810).length < 2 ^ (prefixWord ++ tailWord_6103810).sum := by decide
  have hdescent : baseEnd_6103810 < baseStart_6103810 := by decide
  rcases family_descends (prefixWord ++ tailWord_6103810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6103844 : List Nat := [2, 3, 1, 3, 4, 1, 1, 2, 2, 1, 3]
def baseStart_6103844 : Nat := 118140960795 + 6103844 * 2 ^ 59
def prefixEnd_6103844 : Nat := 4983230072969 + 3 ^ 40 * 6103844 * 2
def baseEnd_6103844 : Nat := 3134205812062121915978939

theorem tailTrace_6103844 : CollatzResearch.WordTrace tailWord_6103844 prefixEnd_6103844 3134205812062121915978939 := by
  unfold tailWord_6103844
  simp only [CollatzResearch.WordTrace]
  refine ⟨111312740049411558203171293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148416986732548744270895057 111312740049411558203171293)
  ·
    refine ⟨41742277518529334326189235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111312740049411558203171293 41742277518529334326189235)
    ·
      refine ⟨62613416277794001489283853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41742277518529334326189235 62613416277794001489283853)
      ·
        refine ⟨23480031104172750558481445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62613416277794001489283853 23480031104172750558481445)
        ·
          refine ⟨4402505832032390729715271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23480031104172750558481445 4402505832032390729715271)
          ·
            refine ⟨6603758748048586094572907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4402505832032390729715271 6603758748048586094572907)
            ·
              refine ⟨9905638122072879141859361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6603758748048586094572907 9905638122072879141859361)
              ·
                refine ⟨7429228591554659356394521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9905638122072879141859361 7429228591554659356394521)
                ·
                  refine ⟨5571921443665994517295891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7429228591554659356394521 5571921443665994517295891)
                  ·
                    refine ⟨8357882165498991775943837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5571921443665994517295891 8357882165498991775943837)
                    ·
                      refine ⟨3134205812062121915978939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8357882165498991775943837 3134205812062121915978939)
                      ·
                        rfl

theorem cell23_6103844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 1, 2, 2, 1, 3].length) (baseStart_6103844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6103844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6103844 prefixEnd_6103844 := by exact prefixLift 6103844
  have htrace : WordTrace (prefixWord ++ tailWord_6103844) baseStart_6103844 baseEnd_6103844 := by
    simpa [prefixWord, tailWord_6103844, baseEnd_6103844] using wordTrace_append hprefix tailTrace_6103844
  have hstable : (prefixWord ++ tailWord_6103844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6103844).length < 2 ^ (prefixWord ++ tailWord_6103844).sum := by decide
  have hdescent : baseEnd_6103844 < baseStart_6103844 := by decide
  rcases family_descends (prefixWord ++ tailWord_6103844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6103849 : List Nat := [1, 2, 1, 1, 1, 1, 1, 5, 1, 2, 7]
def baseStart_6103849 : Nat := 118140960795 + 6103849 * 2 ^ 59
def prefixEnd_6103849 : Nat := 4983230072969 + 3 ^ 40 * 6103849 * 2
def baseEnd_6103849 : Nat := 3134208379465394396416415

theorem tailTrace_6103849 : CollatzResearch.WordTrace tailWord_6103849 prefixEnd_6103849 3134208379465394396416415 := by
  unfold tailWord_6103849
  simp only [CollatzResearch.WordTrace]
  refine ⟨222625662463805002260274601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148417108309203334840183067 222625662463805002260274601)
  ·
    refine ⟨166969246847853751695205951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222625662463805002260274601 166969246847853751695205951)
    ·
      refine ⟨250453870271780627542808927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166969246847853751695205951 250453870271780627542808927)
      ·
        refine ⟨375680805407670941314213391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250453870271780627542808927 375680805407670941314213391)
        ·
          refine ⟨563521208111506411971320087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 375680805407670941314213391 563521208111506411971320087)
          ·
            refine ⟨845281812167259617956980131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 563521208111506411971320087 845281812167259617956980131)
            ·
              refine ⟨1267922718250889426935470197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 845281812167259617956980131 1267922718250889426935470197)
              ·
                refine ⟨118867754836020883775200331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1267922718250889426935470197 118867754836020883775200331)
                ·
                  refine ⟨178301632254031325662800497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 118867754836020883775200331 178301632254031325662800497)
                  ·
                    refine ⟨133726224190523494247100373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 178301632254031325662800497 133726224190523494247100373)
                    ·
                      refine ⟨3134208379465394396416415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 133726224190523494247100373 3134208379465394396416415)
                      ·
                        rfl

theorem cell23_6103849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 2, 7].length) (baseStart_6103849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6103849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6103849 prefixEnd_6103849 := by exact prefixLift 6103849
  have htrace : WordTrace (prefixWord ++ tailWord_6103849) baseStart_6103849 baseEnd_6103849 := by
    simpa [prefixWord, tailWord_6103849, baseEnd_6103849] using wordTrace_append hprefix tailTrace_6103849
  have hstable : (prefixWord ++ tailWord_6103849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6103849).length < 2 ^ (prefixWord ++ tailWord_6103849).sum := by decide
  have hdescent : baseEnd_6103849 < baseStart_6103849 := by decide
  rcases family_descends (prefixWord ++ tailWord_6103849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6103886 : List Nat := [4, 1, 1, 1, 1, 1, 1, 2, 6, 5]
def baseStart_6103886 : Nat := 118140960795 + 6103886 * 2 ^ 59
def prefixEnd_6103886 : Nat := 4983230072969 + 3 ^ 40 * 6103886 * 2
def baseEnd_6103886 : Nat := 1044742459416536917217915

theorem tailTrace_6103886 : CollatzResearch.WordTrace tailWord_6103886 prefixEnd_6103886 1044742459416536917217915 := by
  unfold tailWord_6103886
  simp only [CollatzResearch.WordTrace]
  refine ⟨27828376495583869697421439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148418007976447305052914341 27828376495583869697421439)
  ·
    refine ⟨41742564743375804546132159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27828376495583869697421439 41742564743375804546132159)
    ·
      refine ⟨62613847115063706819198239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41742564743375804546132159 62613847115063706819198239)
      ·
        refine ⟨93920770672595560228797359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62613847115063706819198239 93920770672595560228797359)
        ·
          refine ⟨140881156008893340343196039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93920770672595560228797359 140881156008893340343196039)
          ·
            refine ⟨211321734013340010514794059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140881156008893340343196039 211321734013340010514794059)
            ·
              refine ⟨316982601020010015772191089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 211321734013340010514794059 316982601020010015772191089)
              ·
                refine ⟨237736950765007511829143317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 316982601020010015772191089 237736950765007511829143317)
                ·
                  refine ⟨11143919567109727116991093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 237736950765007511829143317 11143919567109727116991093)
                  ·
                    refine ⟨1044742459416536917217915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11143919567109727116991093 1044742459416536917217915)
                    ·
                      rfl

theorem cell23_6103886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 6, 5].length) (baseStart_6103886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6103886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6103886 prefixEnd_6103886 := by exact prefixLift 6103886
  have htrace : WordTrace (prefixWord ++ tailWord_6103886) baseStart_6103886 baseEnd_6103886 := by
    simpa [prefixWord, tailWord_6103886, baseEnd_6103886] using wordTrace_append hprefix tailTrace_6103886
  have hstable : (prefixWord ++ tailWord_6103886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6103886).length < 2 ^ (prefixWord ++ tailWord_6103886).sum := by decide
  have hdescent : baseEnd_6103886 < baseStart_6103886 := by decide
  rcases family_descends (prefixWord ++ tailWord_6103886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6103918 : List Nat := [4, 1, 2, 3, 3, 1, 2, 1, 2, 2, 2]
def baseStart_6103918 : Nat := 118140960795 + 6103918 * 2 ^ 59
def prefixEnd_6103918 : Nat := 4983230072969 + 3 ^ 40 * 6103918 * 2
def baseEnd_6103918 : Nat := 3134243809630554626453599

theorem tailTrace_6103918 : CollatzResearch.WordTrace tailWord_6103918 prefixEnd_6103918 3134243809630554626453599 := by
  unfold tailWord_6103918
  simp only [CollatzResearch.WordTrace]
  refine ⟨27828522387569378380567051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148418786067036684696357605 27828522387569378380567051)
  ·
    refine ⟨41742783581354067570850577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27828522387569378380567051 41742783581354067570850577)
    ·
      refine ⟨31307087686015550678137933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41742783581354067570850577 31307087686015550678137933)
      ·
        refine ⟨11740157882255831504301725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31307087686015550678137933 11740157882255831504301725)
        ·
          refine ⟨4402559205845936814113147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11740157882255831504301725 4402559205845936814113147)
          ·
            refine ⟨6603838808768905221169721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4402559205845936814113147 6603838808768905221169721)
            ·
              refine ⟨4952879106576678915877291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6603838808768905221169721 4952879106576678915877291)
              ·
                refine ⟨7429318659865018373815937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4952879106576678915877291 7429318659865018373815937)
                ·
                  refine ⟨5571988994898763780361953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7429318659865018373815937 5571988994898763780361953)
                  ·
                    refine ⟨4178991746174072835271465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5571988994898763780361953 4178991746174072835271465)
                    ·
                      refine ⟨3134243809630554626453599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4178991746174072835271465 3134243809630554626453599)
                      ·
                        rfl

theorem cell23_6103918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 2, 1, 2, 2, 2].length) (baseStart_6103918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6103918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6103918 prefixEnd_6103918 := by exact prefixLift 6103918
  have htrace : WordTrace (prefixWord ++ tailWord_6103918) baseStart_6103918 baseEnd_6103918 := by
    simpa [prefixWord, tailWord_6103918, baseEnd_6103918] using wordTrace_append hprefix tailTrace_6103918
  have hstable : (prefixWord ++ tailWord_6103918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6103918).length < 2 ^ (prefixWord ++ tailWord_6103918).sum := by decide
  have hdescent : baseEnd_6103918 < baseStart_6103918 := by decide
  rcases family_descends (prefixWord ++ tailWord_6103918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6103923 : List Nat := [1, 1, 1, 2, 2, 1, 4, 3, 2, 4, 2]
def baseStart_6103923 : Nat := 118140960795 + 6103923 * 2 ^ 59
def prefixEnd_6103923 : Nat := 4983230072969 + 3 ^ 40 * 6103923 * 2
def baseEnd_6103923 : Nat := 3134246377033827106891075

theorem tailTrace_6103923 : CollatzResearch.WordTrace tailWord_6103923 prefixEnd_6103923 3134246377033827106891075 := by
  unfold tailWord_6103923
  simp only [CollatzResearch.WordTrace]
  refine ⟨222628361465536912898468423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148418907643691275265645615 222628361465536912898468423)
  ·
    refine ⟨333942542198305369347702635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222628361465536912898468423 333942542198305369347702635)
    ·
      refine ⟨500913813297458054021553953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 333942542198305369347702635 500913813297458054021553953)
      ·
        refine ⟨375685359973093540516165465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 500913813297458054021553953 375685359973093540516165465)
        ·
          refine ⟨281764019979820155387124099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 375685359973093540516165465 281764019979820155387124099)
          ·
            refine ⟨422646029969730233080686149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 281764019979820155387124099 422646029969730233080686149)
            ·
              refine ⟨79246130619324418702628653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 422646029969730233080686149 79246130619324418702628653)
              ·
                refine ⟨29717298982246657013485745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79246130619324418702628653 29717298982246657013485745)
                ·
                  refine ⟨22287974236684992760114309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29717298982246657013485745 22287974236684992760114309)
                  ·
                    refine ⟨4178995169378436142521433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22287974236684992760114309 4178995169378436142521433)
                    ·
                      refine ⟨3134246377033827106891075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4178995169378436142521433 3134246377033827106891075)
                      ·
                        rfl

theorem cell23_6103923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 3, 2, 4, 2].length) (baseStart_6103923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6103923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6103923 prefixEnd_6103923 := by exact prefixLift 6103923
  have htrace : WordTrace (prefixWord ++ tailWord_6103923) baseStart_6103923 baseEnd_6103923 := by
    simpa [prefixWord, tailWord_6103923, baseEnd_6103923] using wordTrace_append hprefix tailTrace_6103923
  have hstable : (prefixWord ++ tailWord_6103923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6103923).length < 2 ^ (prefixWord ++ tailWord_6103923).sum := by decide
  have hdescent : baseEnd_6103923 < baseStart_6103923 := by decide
  rcases family_descends (prefixWord ++ tailWord_6103923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6103933 : List Nat := [1, 4, 1, 1, 2, 1, 2, 4, 3, 4]
def baseStart_6103933 : Nat := 118140960795 + 6103933 * 2 ^ 59
def prefixEnd_6103933 : Nat := 4983230072969 + 3 ^ 40 * 6103933 * 2
def baseEnd_6103933 : Nat := 1044750503946790689255343

theorem tailTrace_6103933 : CollatzResearch.WordTrace tailWord_6103933 prefixEnd_6103933 1044750503946790689255343 := by
  unfold tailWord_6103933
  simp only [CollatzResearch.WordTrace]
  refine ⟨222628726195500684606332453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148419150797000456404221635 222628726195500684606332453)
  ·
    refine ⟨41742886161656378363687335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 222628726195500684606332453 41742886161656378363687335)
    ·
      refine ⟨62614329242484567545531003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41742886161656378363687335 62614329242484567545531003)
      ·
        refine ⟨93921493863726851318296505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62614329242484567545531003 93921493863726851318296505)
        ·
          refine ⟨70441120397795138488722379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93921493863726851318296505 70441120397795138488722379)
          ·
            refine ⟨105661680596692707733083569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70441120397795138488722379 105661680596692707733083569)
            ·
              refine ⟨79246260447519530799812677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105661680596692707733083569 79246260447519530799812677)
              ·
                refine ⟨14858673833909912024964877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 79246260447519530799812677 14858673833909912024964877)
                ·
                  refine ⟨5572002687716217009361829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14858673833909912024964877 5572002687716217009361829)
                  ·
                    refine ⟨1044750503946790689255343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5572002687716217009361829 1044750503946790689255343)
                    ·
                      rfl

theorem cell23_6103933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 4, 3, 4].length) (baseStart_6103933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6103933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6103933 prefixEnd_6103933 := by exact prefixLift 6103933
  have htrace : WordTrace (prefixWord ++ tailWord_6103933) baseStart_6103933 baseEnd_6103933 := by
    simpa [prefixWord, tailWord_6103933, baseEnd_6103933] using wordTrace_append hprefix tailTrace_6103933
  have hstable : (prefixWord ++ tailWord_6103933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6103933).length < 2 ^ (prefixWord ++ tailWord_6103933).sum := by decide
  have hdescent : baseEnd_6103933 < baseStart_6103933 := by decide
  rcases family_descends (prefixWord ++ tailWord_6103933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6103967 : List Nat := [1, 1, 2, 5, 2, 2, 1, 4, 1, 4]
def baseStart_6103967 : Nat := 118140960795 + 6103967 * 2 ^ 59
def prefixEnd_6103967 : Nat := 4983230072969 + 3 ^ 40 * 6103967 * 2
def baseEnd_6103967 : Nat := 1044756323394208311580291

theorem tailTrace_6103967 : CollatzResearch.WordTrace tailWord_6103967 prefixEnd_6103967 1044756323394208311580291 := by
  unfold tailWord_6103967
  simp only [CollatzResearch.WordTrace]
  refine ⟨222629966277377508413070155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148419977518251672275380103 222629966277377508413070155)
  ·
    refine ⟨333944949416066262619605233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222629966277377508413070155 333944949416066262619605233)
    ·
      refine ⟨250458712062049696964703925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 333944949416066262619605233 250458712062049696964703925)
      ·
        refine ⟨23480504255817159090440993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 250458712062049696964703925 23480504255817159090440993)
        ·
          refine ⟨17610378191862869317830745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23480504255817159090440993 17610378191862869317830745)
          ·
            refine ⟨13207783643897151988373059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17610378191862869317830745 13207783643897151988373059)
            ·
              refine ⟨19811675465845727982559589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13207783643897151988373059 19811675465845727982559589)
              ·
                refine ⟨3714689149846073996729923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19811675465845727982559589 3714689149846073996729923)
                ·
                  refine ⟨5572033724769110995094885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3714689149846073996729923 5572033724769110995094885)
                  ·
                    refine ⟨1044756323394208311580291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5572033724769110995094885 1044756323394208311580291)
                    ·
                      rfl

theorem cell23_6103967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 4, 1, 4].length) (baseStart_6103967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6103967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6103967 prefixEnd_6103967 := by exact prefixLift 6103967
  have htrace : WordTrace (prefixWord ++ tailWord_6103967) baseStart_6103967 baseEnd_6103967 := by
    simpa [prefixWord, tailWord_6103967, baseEnd_6103967] using wordTrace_append hprefix tailTrace_6103967
  have hstable : (prefixWord ++ tailWord_6103967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6103967).length < 2 ^ (prefixWord ++ tailWord_6103967).sum := by decide
  have hdescent : baseEnd_6103967 < baseStart_6103967 := by decide
  rcases family_descends (prefixWord ++ tailWord_6103967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6103993 : List Nat := [1, 2, 1, 4, 2, 2, 2, 1, 3, 5]
def baseStart_6103993 : Nat := 118140960795 + 6103993 * 2 ^ 59
def prefixEnd_6103993 : Nat := 4983230072969 + 3 ^ 40 * 6103993 * 2
def baseEnd_6103993 : Nat := 1044760773559880611005251

theorem tailTrace_6103993 : CollatzResearch.WordTrace tailWord_6103993 prefixEnd_6103993 1044760773559880611005251 := by
  unfold tailWord_6103993
  simp only [CollatzResearch.WordTrace]
  refine ⟨222630914575283314853516633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148420609716855543235677755 222630914575283314853516633)
  ·
    refine ⟨166973185931462486140137475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222630914575283314853516633 166973185931462486140137475)
    ·
      refine ⟨250459778897193729210206213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166973185931462486140137475 250459778897193729210206213)
      ·
        refine ⟨46961208543223824226913665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 250459778897193729210206213 46961208543223824226913665)
        ·
          refine ⟨35220906407417868170185249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46961208543223824226913665 35220906407417868170185249)
          ·
            refine ⟨26415679805563401127638937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35220906407417868170185249 26415679805563401127638937)
            ·
              refine ⟨19811759854172550845729203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26415679805563401127638937 19811759854172550845729203)
              ·
                refine ⟨29717639781258826268593805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19811759854172550845729203 29717639781258826268593805)
                ·
                  refine ⟨11144114917972059850722677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29717639781258826268593805 11144114917972059850722677)
                  ·
                    refine ⟨1044760773559880611005251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11144114917972059850722677 1044760773559880611005251)
                    ·
                      rfl

theorem cell23_6103993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 1, 3, 5].length) (baseStart_6103993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6103993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6103993 prefixEnd_6103993 := by exact prefixLift 6103993
  have htrace : WordTrace (prefixWord ++ tailWord_6103993) baseStart_6103993 baseEnd_6103993 := by
    simpa [prefixWord, tailWord_6103993, baseEnd_6103993] using wordTrace_append hprefix tailTrace_6103993
  have hstable : (prefixWord ++ tailWord_6103993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6103993).length < 2 ^ (prefixWord ++ tailWord_6103993).sum := by decide
  have hdescent : baseEnd_6103993 < baseStart_6103993 := by decide
  rcases family_descends (prefixWord ++ tailWord_6103993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6104000 : List Nat := [2, 1, 1, 2, 3, 4, 1, 1, 1, 5, 2]
def baseStart_6104000 : Nat := 118140960795 + 6104000 * 2 ^ 59
def prefixEnd_6104000 : Nat := 4983230072969 + 3 ^ 40 * 6104000 * 2
def baseEnd_6104000 : Nat := 3134285915044223305628221

theorem tailTrace_6104000 : CollatzResearch.WordTrace tailWord_6104000 prefixEnd_6104000 3134285915044223305628221 := by
  unfold tailWord_6104000
  simp only [CollatzResearch.WordTrace]
  refine ⟨111315584943128977524510727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148420779924171970032680969 111315584943128977524510727)
  ·
    refine ⟨166973377414693466286766091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111315584943128977524510727 166973377414693466286766091)
    ·
      refine ⟨250460066122040199430149137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166973377414693466286766091 250460066122040199430149137)
      ·
        refine ⟨187845049591530149572611853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 250460066122040199430149137 187845049591530149572611853)
        ·
          refine ⟨70441893596823806089729445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 187845049591530149572611853 70441893596823806089729445)
          ·
            refine ⟨13207855049404463641824271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70441893596823806089729445 13207855049404463641824271)
            ·
              refine ⟨19811782574106695462736407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13207855049404463641824271 19811782574106695462736407)
              ·
                refine ⟨29717673861160043194104611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19811782574106695462736407 29717673861160043194104611)
                ·
                  refine ⟨44576510791740064791156917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29717673861160043194104611 44576510791740064791156917)
                  ·
                    refine ⟨4179047886725631074170961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44576510791740064791156917 4179047886725631074170961)
                    ·
                      refine ⟨3134285915044223305628221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4179047886725631074170961 3134285915044223305628221)
                      ·
                        rfl

theorem cell23_6104000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 1, 1, 5, 2].length) (baseStart_6104000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6104000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6104000 prefixEnd_6104000 := by exact prefixLift 6104000
  have htrace : WordTrace (prefixWord ++ tailWord_6104000) baseStart_6104000 baseEnd_6104000 := by
    simpa [prefixWord, tailWord_6104000, baseEnd_6104000] using wordTrace_append hprefix tailTrace_6104000
  have hstable : (prefixWord ++ tailWord_6104000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6104000).length < 2 ^ (prefixWord ++ tailWord_6104000).sum := by decide
  have hdescent : baseEnd_6104000 < baseStart_6104000 := by decide
  rcases family_descends (prefixWord ++ tailWord_6104000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6104007 : List Nat := [1, 1, 4, 1, 1, 2, 3, 5, 1, 1, 3]
def baseStart_6104007 : Nat := 118140960795 + 6104007 * 2 ^ 59
def prefixEnd_6104007 : Nat := 4983230072969 + 3 ^ 40 * 6104007 * 2
def baseEnd_6104007 : Nat := 3134289509408804778240689

theorem tailTrace_6104007 : CollatzResearch.WordTrace tailWord_6104007 prefixEnd_6104007 3134289509408804778240689 := by
  unfold tailWord_6104007
  simp only [CollatzResearch.WordTrace]
  refine ⟨222631425197232595244526275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148420950131488396829684183 222631425197232595244526275)
  ·
    refine ⟨333947137795848892866789413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222631425197232595244526275 333947137795848892866789413)
    ·
      refine ⟨62615088336721667412523015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 333947137795848892866789413 62615088336721667412523015)
      ·
        refine ⟨93922632505082501118784523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62615088336721667412523015 93922632505082501118784523)
        ·
          refine ⟨140883948757623751678176785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93922632505082501118784523 140883948757623751678176785)
          ·
            refine ⟨105662961568217813758632589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140883948757623751678176785 105662961568217813758632589)
            ·
              refine ⟨39623610588081680159487221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105662961568217813758632589 39623610588081680159487221)
              ·
                refine ⟨3714713492632657514951927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39623610588081680159487221 3714713492632657514951927)
                ·
                  refine ⟨5572070238948986272427891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3714713492632657514951927 5572070238948986272427891)
                  ·
                    refine ⟨8358105358423479408641837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5572070238948986272427891 8358105358423479408641837)
                    ·
                      refine ⟨3134289509408804778240689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8358105358423479408641837 3134289509408804778240689)
                      ·
                        rfl

theorem cell23_6104007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 5, 1, 1, 3].length) (baseStart_6104007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6104007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6104007 prefixEnd_6104007 := by exact prefixLift 6104007
  have htrace : WordTrace (prefixWord ++ tailWord_6104007) baseStart_6104007 baseEnd_6104007 := by
    simpa [prefixWord, tailWord_6104007, baseEnd_6104007] using wordTrace_append hprefix tailTrace_6104007
  have hstable : (prefixWord ++ tailWord_6104007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6104007).length < 2 ^ (prefixWord ++ tailWord_6104007).sum := by decide
  have hdescent : baseEnd_6104007 < baseStart_6104007 := by decide
  rcases family_descends (prefixWord ++ tailWord_6104007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6104040 : List Nat := [2, 1, 4, 1, 1, 1, 2, 5, 2, 4]
def baseStart_6104040 : Nat := 118140960795 + 6104040 * 2 ^ 59
def prefixEnd_6104040 : Nat := 4983230072969 + 3 ^ 40 * 6104040 * 2
def baseEnd_6104040 : Nat := 1044768818090134383042679

theorem tailTrace_6104040 : CollatzResearch.WordTrace tailWord_6104040 prefixEnd_6104040 1044768818090134383042679 := by
  unfold tailWord_6104040
  simp only [CollatzResearch.WordTrace]
  refine ⟨111316314403056520940238787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148421752537408694586985049 111316314403056520940238787)
  ·
    refine ⟨166974471604584781410358181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111316314403056520940238787 166974471604584781410358181)
    ·
      refine ⟨31307713425859646514442159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 166974471604584781410358181 31307713425859646514442159)
      ·
        refine ⟨46961570138789469771663239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31307713425859646514442159 46961570138789469771663239)
        ·
          refine ⟨70442355208184204657494859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46961570138789469771663239 70442355208184204657494859)
          ·
            refine ⟨105663532812276306986242289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70442355208184204657494859 105663532812276306986242289)
            ·
              refine ⟨79247649609207230239681717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105663532812276306986242289 79247649609207230239681717)
              ·
                refine ⟨7429467150863177834970161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 79247649609207230239681717 7429467150863177834970161)
                ·
                  refine ⟨5572100363147383376227621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7429467150863177834970161 5572100363147383376227621)
                  ·
                    refine ⟨1044768818090134383042679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5572100363147383376227621 1044768818090134383042679)
                    ·
                      rfl

theorem cell23_6104040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 5, 2, 4].length) (baseStart_6104040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6104040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6104040 prefixEnd_6104040 := by exact prefixLift 6104040
  have htrace : WordTrace (prefixWord ++ tailWord_6104040) baseStart_6104040 baseEnd_6104040 := by
    simpa [prefixWord, tailWord_6104040, baseEnd_6104040] using wordTrace_append hprefix tailTrace_6104040
  have hstable : (prefixWord ++ tailWord_6104040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6104040).length < 2 ^ (prefixWord ++ tailWord_6104040).sum := by decide
  have hdescent : baseEnd_6104040 < baseStart_6104040 := by decide
  rcases family_descends (prefixWord ++ tailWord_6104040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6104047 : List Nat := [1, 1, 2, 1, 4, 3, 2, 2, 3, 2, 2]
def baseStart_6104047 : Nat := 118140960795 + 6104047 * 2 ^ 59
def prefixEnd_6104047 : Nat := 4983230072969 + 3 ^ 40 * 6104047 * 2
def baseEnd_6104047 : Nat := 3134310048634984621740505

theorem tailTrace_6104047 : CollatzResearch.WordTrace tailWord_6104047 prefixEnd_6104047 3134310048634984621740505 := by
  unfold tailWord_6104047
  simp only [CollatzResearch.WordTrace]
  refine ⟨222632884117087682075982395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148421922744725121383988263 222632884117087682075982395)
  ·
    refine ⟨333949326175631523113973593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222632884117087682075982395 333949326175631523113973593)
    ·
      refine ⟨250461994631723642335480195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 333949326175631523113973593 250461994631723642335480195)
      ·
        refine ⟨375692991947585463503220293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250461994631723642335480195 375692991947585463503220293)
        ·
          refine ⟨70442435990172274406853805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 375692991947585463503220293 70442435990172274406853805)
          ·
            refine ⟨26415913496314602902570177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70442435990172274406853805 26415913496314602902570177)
            ·
              refine ⟨19811935122235952176927633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26415913496314602902570177 19811935122235952176927633)
              ·
                refine ⟨14858951341676964132695725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19811935122235952176927633 14858951341676964132695725)
                ·
                  refine ⟨5572106753128861549760897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14858951341676964132695725 5572106753128861549760897)
                  ·
                    refine ⟨4179080064846646162320673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5572106753128861549760897 4179080064846646162320673)
                    ·
                      refine ⟨3134310048634984621740505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4179080064846646162320673 3134310048634984621740505)
                      ·
                        rfl

theorem cell23_6104047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 2, 3, 2, 2].length) (baseStart_6104047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6104047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6104047 prefixEnd_6104047 := by exact prefixLift 6104047
  have htrace : WordTrace (prefixWord ++ tailWord_6104047) baseStart_6104047 baseEnd_6104047 := by
    simpa [prefixWord, tailWord_6104047, baseEnd_6104047] using wordTrace_append hprefix tailTrace_6104047
  have hstable : (prefixWord ++ tailWord_6104047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6104047).length < 2 ^ (prefixWord ++ tailWord_6104047).sum := by decide
  have hdescent : baseEnd_6104047 < baseStart_6104047 := by decide
  rcases family_descends (prefixWord ++ tailWord_6104047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6104052 : List Nat := [2, 6, 2, 1, 2, 1, 1, 3, 1, 4]
def baseStart_6104052 : Nat := 118140960795 + 6104052 * 2 ^ 59
def prefixEnd_6104052 : Nat := 4983230072969 + 3 ^ 40 * 6104052 * 2
def baseEnd_6104052 : Nat := 1044770872012752367392661

theorem tailTrace_6104052 : CollatzResearch.WordTrace tailWord_6104052 prefixEnd_6104052 1044770872012752367392661 := by
  unfold tailWord_6104052
  simp only [CollatzResearch.WordTrace]
  refine ⟨111316533241034783964957205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148422044321379711953276273 111316533241034783964957205)
  ·
    refine ⟨5217962495673505498357369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 111316533241034783964957205 5217962495673505498357369)
    ·
      refine ⟨3913471871755129123768027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5217962495673505498357369 3913471871755129123768027)
      ·
        refine ⟨5870207807632693685652041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3913471871755129123768027 5870207807632693685652041)
        ·
          refine ⟨4402655855724520264239031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5870207807632693685652041 4402655855724520264239031)
          ·
            refine ⟨6603983783586780396358547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4402655855724520264239031 6603983783586780396358547)
            ·
              refine ⟨9905975675380170594537821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6603983783586780396358547 9905975675380170594537821)
              ·
                refine ⟨3714740878267563972951683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9905975675380170594537821 3714740878267563972951683)
                ·
                  refine ⟨5572111317401345959427525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3714740878267563972951683 5572111317401345959427525)
                  ·
                    refine ⟨1044770872012752367392661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5572111317401345959427525 1044770872012752367392661)
                    ·
                      rfl

theorem cell23_6104052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_6104052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6104052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6104052 prefixEnd_6104052 := by exact prefixLift 6104052
  have htrace : WordTrace (prefixWord ++ tailWord_6104052) baseStart_6104052 baseEnd_6104052 := by
    simpa [prefixWord, tailWord_6104052, baseEnd_6104052] using wordTrace_append hprefix tailTrace_6104052
  have hstable : (prefixWord ++ tailWord_6104052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6104052).length < 2 ^ (prefixWord ++ tailWord_6104052).sum := by decide
  have hdescent : baseEnd_6104052 < baseStart_6104052 := by decide
  rcases family_descends (prefixWord ++ tailWord_6104052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6104123 : List Nat := [1, 1, 1, 1, 1, 2, 1, 3, 3, 6, 3]
def baseStart_6104123 : Nat := 118140960795 + 6104123 * 2 ^ 59
def prefixEnd_6104123 : Nat := 4983230072969 + 3 ^ 40 * 6104123 * 2
def baseEnd_6104123 : Nat := 3134349073164726324390155

theorem tailTrace_6104123 : CollatzResearch.WordTrace tailWord_6104123 prefixEnd_6104123 3134349073164726324390155 := by
  unfold tailWord_6104123
  simp only [CollatzResearch.WordTrace]
  refine ⟨222635656064812347055749023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148423770709874898037166015 222635656064812347055749023)
  ·
    refine ⟨333953484097218520583623535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222635656064812347055749023 333953484097218520583623535)
    ·
      refine ⟨500930226145827780875435303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 333953484097218520583623535 500930226145827780875435303)
      ·
        refine ⟨751395339218741671313152955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 500930226145827780875435303 751395339218741671313152955)
        ·
          refine ⟨1127093008828112506969729433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 751395339218741671313152955 1127093008828112506969729433)
          ·
            refine ⟨845319756621084380227297075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1127093008828112506969729433 845319756621084380227297075)
            ·
              refine ⟨1267979634931626570340945613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 845319756621084380227297075 1267979634931626570340945613)
              ·
                refine ⟨475492363099359963877854605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1267979634931626570340945613 475492363099359963877854605)
                ·
                  refine ⟨178309636162259986454195477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 475492363099359963877854605 178309636162259986454195477)
                  ·
                    refine ⟨8358264195105936865040413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 178309636162259986454195477 8358264195105936865040413)
                    ·
                      refine ⟨3134349073164726324390155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8358264195105936865040413 3134349073164726324390155)
                      ·
                        rfl

theorem cell23_6104123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 6, 3].length) (baseStart_6104123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6104123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6104123 prefixEnd_6104123 := by exact prefixLift 6104123
  have htrace : WordTrace (prefixWord ++ tailWord_6104123) baseStart_6104123 baseEnd_6104123 := by
    simpa [prefixWord, tailWord_6104123, baseEnd_6104123] using wordTrace_append hprefix tailTrace_6104123
  have hstable : (prefixWord ++ tailWord_6104123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6104123).length < 2 ^ (prefixWord ++ tailWord_6104123).sum := by decide
  have hdescent : baseEnd_6104123 < baseStart_6104123 := by decide
  rcases family_descends (prefixWord ++ tailWord_6104123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6104247 : List Nat := [1, 1, 3, 1, 4, 1, 3, 2, 2, 2, 3]
def baseStart_6104247 : Nat := 118140960795 + 6104247 * 2 ^ 59
def prefixEnd_6104247 : Nat := 4983230072969 + 3 ^ 40 * 6104247 * 2
def baseEnd_6104247 : Nat := 3134412744765883839239585

theorem tailTrace_6104247 : CollatzResearch.WordTrace tailWord_6104247 prefixEnd_6104247 3134412744765883839239585 := by
  unfold tailWord_6104247
  simp only [CollatzResearch.WordTrace]
  refine ⟨222640178716363116233262995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148426785810908744155508663 222640178716363116233262995)
  ·
    refine ⟨333960268074544674349894493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222640178716363116233262995 333960268074544674349894493)
    ·
      refine ⟨125235100527954252881210435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 333960268074544674349894493 125235100527954252881210435)
      ·
        refine ⟨187852650791931379321815653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125235100527954252881210435 187852650791931379321815653)
        ·
          refine ⟨35222372023487133622840435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 187852650791931379321815653 35222372023487133622840435)
          ·
            refine ⟨52833558035230700434260653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35222372023487133622840435 52833558035230700434260653)
            ·
              refine ⟨19812584263211512662847745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52833558035230700434260653 19812584263211512662847745)
              ·
                refine ⟨14859438197408634497135809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19812584263211512662847745 14859438197408634497135809)
                ·
                  refine ⟨11144578648056475872851857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14859438197408634497135809 11144578648056475872851857)
                  ·
                    refine ⟨8358433986042356904638893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11144578648056475872851857 8358433986042356904638893)
                    ·
                      refine ⟨3134412744765883839239585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8358433986042356904638893 3134412744765883839239585)
                      ·
                        rfl

theorem cell23_6104247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 2, 2, 2, 3].length) (baseStart_6104247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6104247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6104247 prefixEnd_6104247 := by exact prefixLift 6104247
  have htrace : WordTrace (prefixWord ++ tailWord_6104247) baseStart_6104247 baseEnd_6104247 := by
    simpa [prefixWord, tailWord_6104247, baseEnd_6104247] using wordTrace_append hprefix tailTrace_6104247
  have hstable : (prefixWord ++ tailWord_6104247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6104247).length < 2 ^ (prefixWord ++ tailWord_6104247).sum := by decide
  have hdescent : baseEnd_6104247 < baseStart_6104247 := by decide
  rcases family_descends (prefixWord ++ tailWord_6104247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6104250 : List Nat := [3, 1, 1, 1, 2, 2, 1, 6, 6]
def baseStart_6104250 : Nat := 118140960795 + 6104250 * 2 ^ 59
def prefixEnd_6104250 : Nat := 4983230072969 + 3 ^ 40 * 6104250 * 2
def baseEnd_6104250 : Nat := 348268253911983036389119

theorem tailTrace_6104250 : CollatzResearch.WordTrace tailWord_6104250 prefixEnd_6104250 348268253911983036389119 := by
  unfold tailWord_6104250
  simp only [CollatzResearch.WordTrace]
  refine ⟨55660072033838061936405551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148426858756901498497081469 55660072033838061936405551)
  ·
    refine ⟨83490108050757092904608327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55660072033838061936405551 83490108050757092904608327)
    ·
      refine ⟨125235162076135639356912491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83490108050757092904608327 125235162076135639356912491)
      ·
        refine ⟨187852743114203459035368737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125235162076135639356912491 187852743114203459035368737)
        ·
          refine ⟨140889557335652594276526553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187852743114203459035368737 140889557335652594276526553)
          ·
            refine ⟨105667168001739445707394915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140889557335652594276526553 105667168001739445707394915)
            ·
              refine ⟨158500752002609168561092373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105667168001739445707394915 158500752002609168561092373)
              ·
                refine ⟨7429722750122304776301205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 158500752002609168561092373 7429722750122304776301205)
                ·
                  refine ⟨348268253911983036389119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7429722750122304776301205 348268253911983036389119)
                  ·
                    rfl

theorem cell23_6104250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 6, 6].length) (baseStart_6104250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6104250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6104250 prefixEnd_6104250 := by exact prefixLift 6104250
  have htrace : WordTrace (prefixWord ++ tailWord_6104250) baseStart_6104250 baseEnd_6104250 := by
    simpa [prefixWord, tailWord_6104250, baseEnd_6104250] using wordTrace_append hprefix tailTrace_6104250
  have hstable : (prefixWord ++ tailWord_6104250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6104250).length < 2 ^ (prefixWord ++ tailWord_6104250).sum := by decide
  have hdescent : baseEnd_6104250 < baseStart_6104250 := by decide
  rcases family_descends (prefixWord ++ tailWord_6104250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6104254 : List Nat := [4, 2, 1, 1, 3, 1, 3, 1, 3, 4]
def baseStart_6104254 : Nat := 118140960795 + 6104254 * 2 ^ 59
def prefixEnd_6104254 : Nat := 4983230072969 + 3 ^ 40 * 6104254 * 2
def baseEnd_6104254 : Nat := 1044805446376821770617351

theorem tailTrace_6104254 : CollatzResearch.WordTrace tailWord_6104254 prefixEnd_6104254 1044805446376821770617351 := by
  unfold tailWord_6104254
  simp only [CollatzResearch.WordTrace]
  refine ⟨27830054253417219553595977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148426956018225170952511877 27830054253417219553595977)
  ·
    refine ⟨20872540690062914665196983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27830054253417219553595977 20872540690062914665196983)
    ·
      refine ⟨31308811035094371997795475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20872540690062914665196983 31308811035094371997795475)
      ·
        refine ⟨46963216552641557996693213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31308811035094371997795475 46963216552641557996693213)
        ·
          refine ⟨17611206207240584248759955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46963216552641557996693213 17611206207240584248759955)
          ·
            refine ⟨26416809310860876373139933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17611206207240584248759955 26416809310860876373139933)
            ·
              refine ⟨9906303491572828639927475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26416809310860876373139933 9906303491572828639927475)
              ·
                refine ⟨14859455237359242959891213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9906303491572828639927475 14859455237359242959891213)
                ·
                  refine ⟨5572295714009716109959205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14859455237359242959891213 5572295714009716109959205)
                  ·
                    refine ⟨1044805446376821770617351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5572295714009716109959205 1044805446376821770617351)
                    ·
                      rfl

theorem cell23_6104254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 3, 1, 3, 4].length) (baseStart_6104254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6104254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6104254 prefixEnd_6104254 := by exact prefixLift 6104254
  have htrace : WordTrace (prefixWord ++ tailWord_6104254) baseStart_6104254 baseEnd_6104254 := by
    simpa [prefixWord, tailWord_6104254, baseEnd_6104254] using wordTrace_append hprefix tailTrace_6104254
  have hstable : (prefixWord ++ tailWord_6104254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6104254).length < 2 ^ (prefixWord ++ tailWord_6104254).sum := by decide
  have hdescent : baseEnd_6104254 < baseStart_6104254 := by decide
  rcases family_descends (prefixWord ++ tailWord_6104254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6104287 : List Nat := [1, 1, 2, 3, 2, 1, 2, 3, 1, 5, 2]
def baseStart_6104287 : Nat := 118140960795 + 6104287 * 2 ^ 59
def prefixEnd_6104287 : Nat := 4983230072969 + 3 ^ 40 * 6104287 * 2
def baseEnd_6104287 : Nat := 3134433283992063682739401

theorem tailTrace_6104287 : CollatzResearch.WordTrace tailWord_6104287 prefixEnd_6104287 3134433283992063682739401 := by
  unfold tailWord_6104287
  simp only [CollatzResearch.WordTrace]
  refine ⟨222641637636218203064719115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148427758424145468709812743 222641637636218203064719115)
  ·
    refine ⟨333962456454327304597078673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222641637636218203064719115 333962456454327304597078673)
    ·
      refine ⟨250471842340745478447809005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 333962456454327304597078673 250471842340745478447809005)
      ·
        refine ⟨93926940877779554417928377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 250471842340745478447809005 93926940877779554417928377)
        ·
          refine ⟨70445205658334665813446283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93926940877779554417928377 70445205658334665813446283)
          ·
            refine ⟨105667808487501998720169425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70445205658334665813446283 105667808487501998720169425)
            ·
              refine ⟨79250856365626499040127069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105667808487501998720169425 79250856365626499040127069)
              ·
                refine ⟨29719071137109937140047651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79250856365626499040127069 29719071137109937140047651)
                ·
                  refine ⟨44578606705664905710071477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29719071137109937140047651 44578606705664905710071477)
                  ·
                    refine ⟨4179244378656084910319201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44578606705664905710071477 4179244378656084910319201)
                    ·
                      refine ⟨3134433283992063682739401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4179244378656084910319201 3134433283992063682739401)
                      ·
                        rfl

theorem cell23_6104287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 3, 1, 5, 2].length) (baseStart_6104287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6104287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6104287 prefixEnd_6104287 := by exact prefixLift 6104287
  have htrace : WordTrace (prefixWord ++ tailWord_6104287) baseStart_6104287 baseEnd_6104287 := by
    simpa [prefixWord, tailWord_6104287, baseEnd_6104287] using wordTrace_append hprefix tailTrace_6104287
  have hstable : (prefixWord ++ tailWord_6104287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6104287).length < 2 ^ (prefixWord ++ tailWord_6104287).sum := by decide
  have hdescent : baseEnd_6104287 < baseStart_6104287 := by decide
  rcases family_descends (prefixWord ++ tailWord_6104287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6104317 : List Nat := [1, 4, 1, 1, 1, 1, 1, 1, 4, 6, 2]
def baseStart_6104317 : Nat := 118140960795 + 6104317 * 2 ^ 59
def prefixEnd_6104317 : Nat := 4983230072969 + 3 ^ 40 * 6104317 * 2
def baseEnd_6104317 : Nat := 3134448688411698565364263

theorem tailTrace_6104317 : CollatzResearch.WordTrace tailWord_6104317 prefixEnd_6104317 3134448688411698565364263 := by
  unfold tailWord_6104317
  simp only [CollatzResearch.WordTrace]
  refine ⟨222642731826109518188311205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148428487884073012125540803 222642731826109518188311205)
  ·
    refine ⟨41745512217395534660308351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 222642731826109518188311205 41745512217395534660308351)
    ·
      refine ⟨62618268326093301990462527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41745512217395534660308351 62618268326093301990462527)
      ·
        refine ⟨93927402489139952985693791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62618268326093301990462527 93927402489139952985693791)
        ·
          refine ⟨140891103733709929478540687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93927402489139952985693791 140891103733709929478540687)
          ·
            refine ⟨211336655600564894217811031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140891103733709929478540687 211336655600564894217811031)
            ·
              refine ⟨317004983400847341326716547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 211336655600564894217811031 317004983400847341326716547)
              ·
                refine ⟨475507475101271011990074821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 317004983400847341326716547 475507475101271011990074821)
                ·
                  refine ⟨89157651581488314748139029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 475507475101271011990074821 89157651581488314748139029)
                  ·
                    refine ⟨4179264917882264753819017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 89157651581488314748139029 4179264917882264753819017)
                    ·
                      refine ⟨3134448688411698565364263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4179264917882264753819017 3134448688411698565364263)
                      ·
                        rfl

theorem cell23_6104317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 4, 6, 2].length) (baseStart_6104317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6104317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6104317 prefixEnd_6104317 := by exact prefixLift 6104317
  have htrace : WordTrace (prefixWord ++ tailWord_6104317) baseStart_6104317 baseEnd_6104317 := by
    simpa [prefixWord, tailWord_6104317, baseEnd_6104317] using wordTrace_append hprefix tailTrace_6104317
  have hstable : (prefixWord ++ tailWord_6104317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6104317).length < 2 ^ (prefixWord ++ tailWord_6104317).sum := by decide
  have hdescent : baseEnd_6104317 < baseStart_6104317 := by decide
  rcases family_descends (prefixWord ++ tailWord_6104317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6104320 : List Nat := [2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 5]
def baseStart_6104320 : Nat := 118140960795 + 6104320 * 2 ^ 59
def prefixEnd_6104320 : Nat := 4983230072969 + 3 ^ 40 * 6104320 * 2
def baseEnd_6104320 : Nat := 3134450228853662053626749

theorem tailTrace_6104320 : CollatzResearch.WordTrace tailWord_6104320 prefixEnd_6104320 3134450228853662053626749 := by
  unfold tailWord_6104320
  simp only [CollatzResearch.WordTrace]
  refine ⟨111321420622549324850335207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148428560830065766467113609 111321420622549324850335207)
  ·
    refine ⟨166982130933823987275502811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111321420622549324850335207 166982130933823987275502811)
    ·
      refine ⟨250473196400735980913254217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166982130933823987275502811 250473196400735980913254217)
      ·
        refine ⟨187854897300551985684940663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 250473196400735980913254217 187854897300551985684940663)
        ·
          refine ⟨281782345950827978527410995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187854897300551985684940663 281782345950827978527410995)
          ·
            refine ⟨422673518926241967791116493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 281782345950827978527410995 422673518926241967791116493)
            ·
              refine ⟨158502569597340737921668685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 422673518926241967791116493 158502569597340737921668685)
              ·
                refine ⟨59438463599002776720625757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 158502569597340737921668685 59438463599002776720625757)
                ·
                  refine ⟨22289423849626041270234659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59438463599002776720625757 22289423849626041270234659)
                  ·
                    refine ⟨33434135774439061905351989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22289423849626041270234659 33434135774439061905351989)
                    ·
                      refine ⟨3134450228853662053626749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33434135774439061905351989 3134450228853662053626749)
                      ·
                        rfl

theorem cell23_6104320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 5].length) (baseStart_6104320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6104320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6104320 prefixEnd_6104320 := by exact prefixLift 6104320
  have htrace : WordTrace (prefixWord ++ tailWord_6104320) baseStart_6104320 baseEnd_6104320 := by
    simpa [prefixWord, tailWord_6104320, baseEnd_6104320] using wordTrace_append hprefix tailTrace_6104320
  have hstable : (prefixWord ++ tailWord_6104320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6104320).length < 2 ^ (prefixWord ++ tailWord_6104320).sum := by decide
  have hdescent : baseEnd_6104320 < baseStart_6104320 := by decide
  rcases family_descends (prefixWord ++ tailWord_6104320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6104337 : List Nat := [1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 3]
def baseStart_6104337 : Nat := 118140960795 + 6104337 * 2 ^ 59
def prefixEnd_6104337 : Nat := 4983230072969 + 3 ^ 40 * 6104337 * 2
def baseEnd_6104337 : Nat := 3134458958024788487114171

theorem tailTrace_6104337 : CollatzResearch.WordTrace tailWord_6104337 prefixEnd_6104337 3134458958024788487114171 := by
  unfold tailWord_6104337
  simp only [CollatzResearch.WordTrace]
  refine ⟨222643461286037061604039265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148428974190691374402692843 222643461286037061604039265)
  ·
    refine ⟨166982595964527796203029449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222643461286037061604039265 166982595964527796203029449)
    ·
      refine ⟨125236946973395847152272087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 166982595964527796203029449 125236946973395847152272087)
      ·
        refine ⟨187855420460093770728408131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125236946973395847152272087 187855420460093770728408131)
        ·
          refine ⟨281783130690140656092612197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187855420460093770728408131 281783130690140656092612197)
          ·
            refine ⟨52834337004401373017364787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 281783130690140656092612197 52834337004401373017364787)
            ·
              refine ⟨79251505506602059526047181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52834337004401373017364787 79251505506602059526047181)
              ·
                refine ⟨29719314564975772322267693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79251505506602059526047181 29719314564975772322267693)
                ·
                  refine ⟨11144742961865914620850385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29719314564975772322267693 11144742961865914620850385)
                  ·
                    refine ⟨8358557221399435965637789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11144742961865914620850385 8358557221399435965637789)
                    ·
                      refine ⟨3134458958024788487114171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8358557221399435965637789 3134458958024788487114171)
                      ·
                        rfl

theorem cell23_6104337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 3].length) (baseStart_6104337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6104337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6104337 prefixEnd_6104337 := by exact prefixLift 6104337
  have htrace : WordTrace (prefixWord ++ tailWord_6104337) baseStart_6104337 baseEnd_6104337 := by
    simpa [prefixWord, tailWord_6104337, baseEnd_6104337] using wordTrace_append hprefix tailTrace_6104337
  have hstable : (prefixWord ++ tailWord_6104337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6104337).length < 2 ^ (prefixWord ++ tailWord_6104337).sum := by decide
  have hdescent : baseEnd_6104337 < baseStart_6104337 := by decide
  rcases family_descends (prefixWord ++ tailWord_6104337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6104338 : List Nat := [3, 2, 4, 2, 1, 1, 1, 1, 1, 5, 2]
def baseStart_6104338 : Nat := 118140960795 + 6104338 * 2 ^ 59
def prefixEnd_6104338 : Nat := 4983230072969 + 3 ^ 40 * 6104338 * 2
def baseEnd_6104338 : Nat := 3134459471505442983201667

theorem tailTrace_6104338 : CollatzResearch.WordTrace tailWord_6104338 prefixEnd_6104338 3134459471505442983201667 := by
  unfold tailWord_6104338
  simp only [CollatzResearch.WordTrace]
  refine ⟨55660874439758359693706417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148428998506022292516550445 55660874439758359693706417)
  ·
    refine ⟨41745655829818769770279813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55660874439758359693706417 41745655829818769770279813)
    ·
      refine ⟨7827310468091019331927465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41745655829818769770279813 7827310468091019331927465)
      ·
        refine ⟨5870482851068264498945599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7827310468091019331927465 5870482851068264498945599)
        ·
          refine ⟨8805724276602396748418399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5870482851068264498945599 8805724276602396748418399)
          ·
            refine ⟨13208586414903595122627599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8805724276602396748418399 13208586414903595122627599)
            ·
              refine ⟨19812879622355392683941399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13208586414903595122627599 19812879622355392683941399)
              ·
                refine ⟨29719319433533089025912099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19812879622355392683941399 29719319433533089025912099)
                ·
                  refine ⟨44578979150299633538868149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29719319433533089025912099 44578979150299633538868149)
                  ·
                    refine ⟨4179279295340590644268889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44578979150299633538868149 4179279295340590644268889)
                    ·
                      refine ⟨3134459471505442983201667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4179279295340590644268889 3134459471505442983201667)
                      ·
                        rfl

theorem cell23_6104338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_6104338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6104338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6104338 prefixEnd_6104338 := by exact prefixLift 6104338
  have htrace : WordTrace (prefixWord ++ tailWord_6104338) baseStart_6104338 baseEnd_6104338 := by
    simpa [prefixWord, tailWord_6104338, baseEnd_6104338] using wordTrace_append hprefix tailTrace_6104338
  have hstable : (prefixWord ++ tailWord_6104338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6104338).length < 2 ^ (prefixWord ++ tailWord_6104338).sum := by decide
  have hdescent : baseEnd_6104338 < baseStart_6104338 := by decide
  rcases family_descends (prefixWord ++ tailWord_6104338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6104388 : List Nat := [2, 3, 4, 1, 1, 2, 2, 2, 1, 2, 3]
def baseStart_6104388 : Nat := 118140960795 + 6104388 * 2 ^ 59
def prefixEnd_6104388 : Nat := 4983230072969 + 3 ^ 40 * 6104388 * 2
def baseEnd_6104388 : Nat := 3134485145538167787576437

theorem tailTrace_6104388 : CollatzResearch.WordTrace tailWord_6104388 prefixEnd_6104388 3134485145538167787576437 := by
  unfold tailWord_6104388
  simp only [CollatzResearch.WordTrace]
  refine ⟨111322660704426148657072909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148430214272568198209430545 111322660704426148657072909)
  ·
    refine ⟨41745997764159805746402341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111322660704426148657072909 41745997764159805746402341)
    ·
      refine ⟨7827374580779963577450439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41745997764159805746402341 7827374580779963577450439)
      ·
        refine ⟨11741061871169945366175659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7827374580779963577450439 11741061871169945366175659)
        ·
          refine ⟨17611592806754918049263489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11741061871169945366175659 17611592806754918049263489)
          ·
            refine ⟨13208694605066188536947617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17611592806754918049263489 13208694605066188536947617)
            ·
              refine ⟨9906520953799641402710713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13208694605066188536947617 9906520953799641402710713)
              ·
                refine ⟨7429890715349731052033035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9906520953799641402710713 7429890715349731052033035)
                ·
                  refine ⟨11144836073024596578049553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7429890715349731052033035 11144836073024596578049553)
                  ·
                    refine ⟨8358627054768447433537165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11144836073024596578049553 8358627054768447433537165)
                    ·
                      refine ⟨3134485145538167787576437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8358627054768447433537165 3134485145538167787576437)
                      ·
                        rfl

theorem cell23_6104388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_6104388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6104388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6104388 prefixEnd_6104388 := by exact prefixLift 6104388
  have htrace : WordTrace (prefixWord ++ tailWord_6104388) baseStart_6104388 baseEnd_6104388 := by
    simpa [prefixWord, tailWord_6104388, baseEnd_6104388] using wordTrace_append hprefix tailTrace_6104388
  have hstable : (prefixWord ++ tailWord_6104388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6104388).length < 2 ^ (prefixWord ++ tailWord_6104388).sum := by decide
  have hdescent : baseEnd_6104388 < baseStart_6104388 := by decide
  rcases family_descends (prefixWord ++ tailWord_6104388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6104394 : List Nat := [3, 1, 2, 1, 1, 1, 1, 5, 3, 3, 2]
def baseStart_6104394 : Nat := 118140960795 + 6104394 * 2 ^ 59
def prefixEnd_6104394 : Nat := 4983230072969 + 3 ^ 40 * 6104394 * 2
def baseEnd_6104394 : Nat := 3134488226422094764101409

theorem tailTrace_6104394 : CollatzResearch.WordTrace tailWord_6104394 prefixEnd_6104394 3134488226422094764101409 := by
  unfold tailWord_6104394
  simp only [CollatzResearch.WordTrace]
  refine ⟨55661385061707640084716059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148430360164553706892576157 55661385061707640084716059)
  ·
    refine ⟨83492077592561460127074089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55661385061707640084716059 83492077592561460127074089)
    ·
      refine ⟨62619058194421095095305567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83492077592561460127074089 62619058194421095095305567)
      ·
        refine ⟨93928587291631642642958351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62619058194421095095305567 93928587291631642642958351)
        ·
          refine ⟨140892880937447463964437527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93928587291631642642958351 140892880937447463964437527)
          ·
            refine ⟨211339321406171195946656291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140892880937447463964437527 211339321406171195946656291)
            ·
              refine ⟨317008982109256793919984437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 211339321406171195946656291 317008982109256793919984437)
              ·
                refine ⟨29719592072742824429998541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 317008982109256793919984437 29719592072742824429998541)
                ·
                  refine ⟨11144847027278559161249453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29719592072742824429998541 11144847027278559161249453)
                  ·
                    refine ⟨4179317635229459685468545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11144847027278559161249453 4179317635229459685468545)
                    ·
                      refine ⟨3134488226422094764101409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4179317635229459685468545 3134488226422094764101409)
                      ·
                        rfl

theorem cell23_6104394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 5, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 5, 3, 3, 2].length) (baseStart_6104394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6104394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6104394 prefixEnd_6104394 := by exact prefixLift 6104394
  have htrace : WordTrace (prefixWord ++ tailWord_6104394) baseStart_6104394 baseEnd_6104394 := by
    simpa [prefixWord, tailWord_6104394, baseEnd_6104394] using wordTrace_append hprefix tailTrace_6104394
  have hstable : (prefixWord ++ tailWord_6104394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6104394).length < 2 ^ (prefixWord ++ tailWord_6104394).sum := by decide
  have hdescent : baseEnd_6104394 < baseStart_6104394 := by decide
  rcases family_descends (prefixWord ++ tailWord_6104394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6104474 : List Nat := [3, 1, 1, 4, 1, 1, 2, 2, 2, 3, 3]
def baseStart_6104474 : Nat := 118140960795 + 6104474 * 2 ^ 59
def prefixEnd_6104474 : Nat := 4983230072969 + 3 ^ 40 * 6104474 * 2
def baseEnd_6104474 : Nat := 3134529304874454451101041

theorem tailTrace_6104474 : CollatzResearch.WordTrace tailWord_6104474 prefixEnd_6104474 3134529304874454451101041 := by
  unfold tailWord_6104474
  simp only [CollatzResearch.WordTrace]
  refine ⟨55662114521635183500444119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148432305391027156001184317 55662114521635183500444119)
  ·
    refine ⟨83493171782452775250666179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55662114521635183500444119 83493171782452775250666179)
    ·
      refine ⟨125239757673679162875999269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83493171782452775250666179 125239757673679162875999269)
      ·
        refine ⟨23482454563814843039249863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 125239757673679162875999269 23482454563814843039249863)
        ·
          refine ⟨35223681845722264558874795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23482454563814843039249863 35223681845722264558874795)
          ·
            refine ⟨52835522768583396838312193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35223681845722264558874795 52835522768583396838312193)
            ·
              refine ⟨39626642076437547628734145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52835522768583396838312193 39626642076437547628734145)
              ·
                refine ⟨29719981557328160721550609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39626642076437547628734145 29719981557328160721550609)
                ·
                  refine ⟨22289986167996120541162957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29719981557328160721550609 22289986167996120541162957)
                  ·
                    refine ⟨8358744812998545202936109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22289986167996120541162957 8358744812998545202936109)
                    ·
                      refine ⟨3134529304874454451101041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8358744812998545202936109 3134529304874454451101041)
                      ·
                        rfl

theorem cell23_6104474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 2, 2, 3, 3].length) (baseStart_6104474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6104474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6104474 prefixEnd_6104474 := by exact prefixLift 6104474
  have htrace : WordTrace (prefixWord ++ tailWord_6104474) baseStart_6104474 baseEnd_6104474 := by
    simpa [prefixWord, tailWord_6104474, baseEnd_6104474] using wordTrace_append hprefix tailTrace_6104474
  have hstable : (prefixWord ++ tailWord_6104474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6104474).length < 2 ^ (prefixWord ++ tailWord_6104474).sum := by decide
  have hdescent : baseEnd_6104474 < baseStart_6104474 := by decide
  rcases family_descends (prefixWord ++ tailWord_6104474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6104527 : List Nat := [1, 1, 2, 1, 1, 4, 3, 1, 2, 1, 6]
def baseStart_6104527 : Nat := 118140960795 + 6104527 * 2 ^ 59
def prefixEnd_6104527 : Nat := 4983230072969 + 3 ^ 40 * 6104527 * 2
def baseEnd_6104527 : Nat := 3134556519349142743738297

theorem tailTrace_6104527 : CollatzResearch.WordTrace tailWord_6104527 prefixEnd_6104527 3134556519349142743738297 := by
  unfold tailWord_6104527
  simp only [CollatzResearch.WordTrace]
  refine ⟨222650391155348724053455835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148433594103565816035637223 222650391155348724053455835)
  ·
    refine ⟨333975586733023086080183753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222650391155348724053455835 333975586733023086080183753)
    ·
      refine ⟨250481690049767314560137815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 333975586733023086080183753 250481690049767314560137815)
      ·
        refine ⟨375722535074650971840206723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250481690049767314560137815 375722535074650971840206723)
        ·
          refine ⟨563583802611976457760310085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 375722535074650971840206723 563583802611976457760310085)
          ·
            refine ⟨105671962989745585830058141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 563583802611976457760310085 105671962989745585830058141)
            ·
              refine ⟨39626986121154594686271803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105671962989745585830058141 39626986121154594686271803)
              ·
                refine ⟨59440479181731892029407705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39626986121154594686271803 59440479181731892029407705)
                ·
                  refine ⟨44580359386298919022055779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59440479181731892029407705 44580359386298919022055779)
                  ·
                    refine ⟨66870539079448378533083669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44580359386298919022055779 66870539079448378533083669)
                    ·
                      refine ⟨3134556519349142743738297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66870539079448378533083669 3134556519349142743738297)
                      ·
                        rfl

theorem cell23_6104527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 1, 2, 1, 6].length) (baseStart_6104527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6104527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6104527 prefixEnd_6104527 := by exact prefixLift 6104527
  have htrace : WordTrace (prefixWord ++ tailWord_6104527) baseStart_6104527 baseEnd_6104527 := by
    simpa [prefixWord, tailWord_6104527, baseEnd_6104527] using wordTrace_append hprefix tailTrace_6104527
  have hstable : (prefixWord ++ tailWord_6104527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6104527).length < 2 ^ (prefixWord ++ tailWord_6104527).sum := by decide
  have hdescent : baseEnd_6104527 < baseStart_6104527 := by decide
  rcases family_descends (prefixWord ++ tailWord_6104527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6104541 : List Nat := [1, 4, 3, 1, 1, 2, 1, 3, 3, 4]
def baseStart_6104541 : Nat := 118140960795 + 6104541 * 2 ^ 59
def prefixEnd_6104541 : Nat := 4983230072969 + 3 ^ 40 * 6104541 * 2
def baseEnd_6104541 : Nat := 1044854569359435229654411

theorem tailTrace_6104541 : CollatzResearch.WordTrace tailWord_6104541 prefixEnd_6104541 1044854569359435229654411 := by
  unfold tailWord_6104541
  simp only [CollatzResearch.WordTrace]
  refine ⟨222650901777298004444465477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148433934518198669629643651 222650901777298004444465477)
  ·
    refine ⟨41747044083243375833337277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 222650901777298004444465477 41747044083243375833337277)
    ·
      refine ⟨15655141531216265937501479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41747044083243375833337277 15655141531216265937501479)
      ·
        refine ⟨23482712296824398906252219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15655141531216265937501479 23482712296824398906252219)
        ·
          refine ⟨35224068445236598359378329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23482712296824398906252219 35224068445236598359378329)
          ·
            refine ⟨26418051333927448769533747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35224068445236598359378329 26418051333927448769533747)
            ·
              refine ⟨39627077000891173154300621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26418051333927448769533747 39627077000891173154300621)
              ·
                refine ⟨14860153875334189932862733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39627077000891173154300621 14860153875334189932862733)
                ·
                  refine ⟨5572557703250321224823525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14860153875334189932862733 5572557703250321224823525)
                  ·
                    refine ⟨1044854569359435229654411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5572557703250321224823525 1044854569359435229654411)
                    ·
                      rfl

theorem cell23_6104541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 3, 3, 4].length) (baseStart_6104541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6104541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6104541 prefixEnd_6104541 := by exact prefixLift 6104541
  have htrace : WordTrace (prefixWord ++ tailWord_6104541) baseStart_6104541 baseEnd_6104541 := by
    simpa [prefixWord, tailWord_6104541, baseEnd_6104541] using wordTrace_append hprefix tailTrace_6104541
  have hstable : (prefixWord ++ tailWord_6104541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6104541).length < 2 ^ (prefixWord ++ tailWord_6104541).sum := by decide
  have hdescent : baseEnd_6104541 < baseStart_6104541 := by decide
  rcases family_descends (prefixWord ++ tailWord_6104541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6104582 : List Nat := [6, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4]
def baseStart_6104582 : Nat := 118140960795 + 6104582 * 2 ^ 59
def prefixEnd_6104582 : Nat := 4983230072969 + 3 ^ 40 * 6104582 * 2
def baseEnd_6104582 : Nat := 3134584760785140028550545

theorem tailTrace_6104582 : CollatzResearch.WordTrace tailWord_6104582 prefixEnd_6104582 3134584760785140028550545 := by
  unfold tailWord_6104582
  simp only [CollatzResearch.WordTrace]
  refine ⟨6957887411567170888959625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 148434931446766312297805333 6957887411567170888959625)
  ·
    refine ⟨5218415558675378166719719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6957887411567170888959625 5218415558675378166719719)
    ·
      refine ⟨7827623338013067250079579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5218415558675378166719719 7827623338013067250079579)
      ·
        refine ⟨11741435007019600875119369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7827623338013067250079579 11741435007019600875119369)
        ·
          refine ⟨8806076255264700656339527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11741435007019600875119369 8806076255264700656339527)
          ·
            refine ⟨13209114382897050984509291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8806076255264700656339527 13209114382897050984509291)
            ·
              refine ⟨19813671574345576476763937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13209114382897050984509291 19813671574345576476763937)
              ·
                refine ⟨14860253680759182357572953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19813671574345576476763937 14860253680759182357572953)
                ·
                  refine ⟨11145190260569386768179715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14860253680759182357572953 11145190260569386768179715)
                  ·
                    refine ⟨16717785390854080152269573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11145190260569386768179715 16717785390854080152269573)
                    ·
                      refine ⟨3134584760785140028550545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16717785390854080152269573 3134584760785140028550545)
                      ·
                        rfl

theorem cell23_6104582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_6104582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6104582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6104582 prefixEnd_6104582 := by exact prefixLift 6104582
  have htrace : WordTrace (prefixWord ++ tailWord_6104582) baseStart_6104582 baseEnd_6104582 := by
    simpa [prefixWord, tailWord_6104582, baseEnd_6104582] using wordTrace_append hprefix tailTrace_6104582
  have hstable : (prefixWord ++ tailWord_6104582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6104582).length < 2 ^ (prefixWord ++ tailWord_6104582).sum := by decide
  have hdescent : baseEnd_6104582 < baseStart_6104582 := by decide
  rcases family_descends (prefixWord ++ tailWord_6104582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6104668 : List Nat := [2, 2, 4, 1, 2, 2, 2, 1, 1, 2, 4]
def baseStart_6104668 : Nat := 118140960795 + 6104668 * 2 ^ 59
def prefixEnd_6104668 : Nat := 4983230072969 + 3 ^ 40 * 6104668 * 2
def baseEnd_6104668 : Nat := 3134628920121426692075149

theorem tailTrace_6104668 : CollatzResearch.WordTrace tailWord_6104668 prefixEnd_6104668 3134628920121426692075149 := by
  unfold tailWord_6104668
  simp only [CollatzResearch.WordTrace]
  refine ⟨111327766923918952567169329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148437022565225270089559105 111327766923918952567169329)
  ·
    refine ⟨83495825192939214425376997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111327766923918952567169329 83495825192939214425376997)
    ·
      refine ⟨15655467223676102704758187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83495825192939214425376997 15655467223676102704758187)
      ·
        refine ⟨23483200835514154057137281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15655467223676102704758187 23483200835514154057137281)
        ·
          refine ⟨17612400626635615542852961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23483200835514154057137281 17612400626635615542852961)
          ·
            refine ⟨13209300469976711657139721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17612400626635615542852961 13209300469976711657139721)
            ·
              refine ⟨9906975352482533742854791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13209300469976711657139721 9906975352482533742854791)
              ·
                refine ⟨14860463028723800614282187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9906975352482533742854791 14860463028723800614282187)
                ·
                  refine ⟨22290694543085700921423281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14860463028723800614282187 22290694543085700921423281)
                  ·
                    refine ⟨16718020907314275691067461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22290694543085700921423281 16718020907314275691067461)
                    ·
                      refine ⟨3134628920121426692075149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16718020907314275691067461 3134628920121426692075149)
                      ·
                        rfl

theorem cell23_6104668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 2, 1, 1, 2, 4].length) (baseStart_6104668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6104668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6104668 prefixEnd_6104668 := by exact prefixLift 6104668
  have htrace : WordTrace (prefixWord ++ tailWord_6104668) baseStart_6104668 baseEnd_6104668 := by
    simpa [prefixWord, tailWord_6104668, baseEnd_6104668] using wordTrace_append hprefix tailTrace_6104668
  have hstable : (prefixWord ++ tailWord_6104668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6104668).length < 2 ^ (prefixWord ++ tailWord_6104668).sum := by decide
  have hdescent : baseEnd_6104668 < baseStart_6104668 := by decide
  rcases family_descends (prefixWord ++ tailWord_6104668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6104671 : List Nat := [1, 1, 2, 3, 1, 1, 1, 1, 8, 1, 3]
def baseStart_6104671 : Nat := 118140960795 + 6104671 * 2 ^ 59
def prefixEnd_6104671 : Nat := 4983230072969 + 3 ^ 40 * 6104671 * 2
def baseEnd_6104671 : Nat := 3134630460563390180337635

theorem tailTrace_6104671 : CollatzResearch.WordTrace tailWord_6104671 prefixEnd_6104671 3134630460563390180337635 := by
  unfold tailWord_6104671
  simp only [CollatzResearch.WordTrace]
  refine ⟨222655643266827036646697867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148437095511218024431131911 222655643266827036646697867)
  ·
    refine ⟨333983464900240554970046801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222655643266827036646697867 333983464900240554970046801)
    ·
      refine ⟨250487598675180416227535101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 333983464900240554970046801 250487598675180416227535101)
      ·
        refine ⟨93932849503192656085325663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 250487598675180416227535101 93932849503192656085325663)
        ·
          refine ⟨140899274254788984127988495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93932849503192656085325663 140899274254788984127988495)
          ·
            refine ⟨211348911382183476191982743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140899274254788984127988495 211348911382183476191982743)
            ·
              refine ⟨317023367073275214287974115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 211348911382183476191982743 317023367073275214287974115)
              ·
                refine ⟨475535050609912821431961173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 317023367073275214287974115 475535050609912821431961173)
                ·
                  refine ⟨5572676374334915876155795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 475535050609912821431961173 5572676374334915876155795)
                  ·
                    refine ⟨8359014561502373814233693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5572676374334915876155795 8359014561502373814233693)
                    ·
                      refine ⟨3134630460563390180337635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8359014561502373814233693 3134630460563390180337635)
                      ·
                        rfl

theorem cell23_6104671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 8, 1, 3].length) (baseStart_6104671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6104671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6104671 prefixEnd_6104671 := by exact prefixLift 6104671
  have htrace : WordTrace (prefixWord ++ tailWord_6104671) baseStart_6104671 baseEnd_6104671 := by
    simpa [prefixWord, tailWord_6104671, baseEnd_6104671] using wordTrace_append hprefix tailTrace_6104671
  have hstable : (prefixWord ++ tailWord_6104671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6104671).length < 2 ^ (prefixWord ++ tailWord_6104671).sum := by decide
  have hdescent : baseEnd_6104671 < baseStart_6104671 := by decide
  rcases family_descends (prefixWord ++ tailWord_6104671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6104684 : List Nat := [2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 5]
def baseStart_6104684 : Nat := 118140960795 + 6104684 * 2 ^ 59
def prefixEnd_6104684 : Nat := 4983230072969 + 3 ^ 40 * 6104684 * 2
def baseEnd_6104684 : Nat := 3134637135811898629475075

theorem tailTrace_6104684 : CollatzResearch.WordTrace tailWord_6104684 prefixEnd_6104684 3134637135811898629475075 := by
  unfold tailWord_6104684
  simp only [CollatzResearch.WordTrace]
  refine ⟨111328058707889969933460553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148437411610519959911280737 111328058707889969933460553)
  ·
    refine ⟨83496044030917477450095415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111328058707889969933460553 83496044030917477450095415)
    ·
      refine ⟨125244066046376216175143123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83496044030917477450095415 125244066046376216175143123)
      ·
        refine ⟨187866099069564324262714685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125244066046376216175143123 187866099069564324262714685)
        ·
          refine ⟨70449787151086621598518007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 187866099069564324262714685 70449787151086621598518007)
          ·
            refine ⟨105674680726629932397777011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70449787151086621598518007 105674680726629932397777011)
            ·
              refine ⟨158512021089944898596665517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105674680726629932397777011 158512021089944898596665517)
              ·
                refine ⟨59442007908729336973749569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 158512021089944898596665517 59442007908729336973749569)
                ·
                  refine ⟨44581505931547002730312177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59442007908729336973749569 44581505931547002730312177)
                  ·
                    refine ⟨33436129448660252047734133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44581505931547002730312177 33436129448660252047734133)
                    ·
                      refine ⟨3134637135811898629475075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33436129448660252047734133 3134637135811898629475075)
                      ·
                        rfl

theorem cell23_6104684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 5].length) (baseStart_6104684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6104684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6104684 prefixEnd_6104684 := by exact prefixLift 6104684
  have htrace : WordTrace (prefixWord ++ tailWord_6104684) baseStart_6104684 baseEnd_6104684 := by
    simpa [prefixWord, tailWord_6104684, baseEnd_6104684] using wordTrace_append hprefix tailTrace_6104684
  have hstable : (prefixWord ++ tailWord_6104684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6104684).length < 2 ^ (prefixWord ++ tailWord_6104684).sum := by decide
  have hdescent : baseEnd_6104684 < baseStart_6104684 := by decide
  rcases family_descends (prefixWord ++ tailWord_6104684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6104704 : List Nat := [2, 1, 1, 2, 1, 4, 1, 1, 4, 6]
def baseStart_6104704 : Nat := 118140960795 + 6104704 * 2 ^ 59
def prefixEnd_6104704 : Nat := 4983230072969 + 3 ^ 40 * 6104704 * 2
def baseEnd_6104704 : Nat := 1044882468474996183741661

theorem tailTrace_6104704 : CollatzResearch.WordTrace tailWord_6104704 prefixEnd_6104704 1044882468474996183741661 := by
  unfold tailWord_6104704
  simp only [CollatzResearch.WordTrace]
  refine ⟨111328423437853741641324583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148437897917138322188432777 111328423437853741641324583)
  ·
    refine ⟨166992635156780612461986875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111328423437853741641324583 166992635156780612461986875)
    ·
      refine ⟨250488952735170918692980313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166992635156780612461986875 250488952735170918692980313)
      ·
        refine ⟨187866714551378189019735235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 250488952735170918692980313 187866714551378189019735235)
        ·
          refine ⟨281800071827067283529602853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187866714551378189019735235 281800071827067283529602853)
          ·
            refine ⟨52837513467575115661800535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 281800071827067283529602853 52837513467575115661800535)
            ·
              refine ⟨79256270201362673492700803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52837513467575115661800535 79256270201362673492700803)
              ·
                refine ⟨118884405302044010239051205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79256270201362673492700803 118884405302044010239051205)
                ·
                  refine ⟨22290825994133251919822101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 118884405302044010239051205 22290825994133251919822101)
                  ·
                    refine ⟨1044882468474996183741661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22290825994133251919822101 1044882468474996183741661)
                    ·
                      rfl

theorem cell23_6104704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 4, 6].length) (baseStart_6104704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6104704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6104704 prefixEnd_6104704 := by exact prefixLift 6104704
  have htrace : WordTrace (prefixWord ++ tailWord_6104704) baseStart_6104704 baseEnd_6104704 := by
    simpa [prefixWord, tailWord_6104704, baseEnd_6104704] using wordTrace_append hprefix tailTrace_6104704
  have hstable : (prefixWord ++ tailWord_6104704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6104704).length < 2 ^ (prefixWord ++ tailWord_6104704).sum := by decide
  have hdescent : baseEnd_6104704 < baseStart_6104704 := by decide
  rcases family_descends (prefixWord ++ tailWord_6104704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6104705 : List Nat := [1, 2, 4, 2, 1, 2, 3, 2, 2, 1, 3]
def baseStart_6104705 : Nat := 118140960795 + 6104705 * 2 ^ 59
def prefixEnd_6104705 : Nat := 4983230072969 + 3 ^ 40 * 6104705 * 2
def baseEnd_6104705 : Nat := 3134647918905643047312479

theorem tailTrace_6104705 : CollatzResearch.WordTrace tailWord_6104705 prefixEnd_6104705 3134647918905643047312479 := by
  unfold tailWord_6104705
  simp only [CollatzResearch.WordTrace]
  refine ⟨222656883348703860453435569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148437922232469240302290379 222656883348703860453435569)
  ·
    refine ⟨166992662511527895340076677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222656883348703860453435569 166992662511527895340076677)
    ·
      refine ⟨31311124220911480376264377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 166992662511527895340076677 31311124220911480376264377)
      ·
        refine ⟨23483343165683610282198283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31311124220911480376264377 23483343165683610282198283)
        ·
          refine ⟨35225014748525415423297425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23483343165683610282198283 35225014748525415423297425)
          ·
            refine ⟨26418761061394061567473069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35225014748525415423297425 26418761061394061567473069)
            ·
              refine ⟨9907035398022773087802401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26418761061394061567473069 9907035398022773087802401)
              ·
                refine ⟨7430276548517079815851801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9907035398022773087802401 7430276548517079815851801)
                ·
                  refine ⟨5572707411387809861888851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7430276548517079815851801 5572707411387809861888851)
                  ·
                    refine ⟨8359061117081714792833277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5572707411387809861888851 8359061117081714792833277)
                    ·
                      refine ⟨3134647918905643047312479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8359061117081714792833277 3134647918905643047312479)
                      ·
                        rfl

theorem cell23_6104705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 3, 2, 2, 1, 3].length) (baseStart_6104705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6104705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6104705 prefixEnd_6104705 := by exact prefixLift 6104705
  have htrace : WordTrace (prefixWord ++ tailWord_6104705) baseStart_6104705 baseEnd_6104705 := by
    simpa [prefixWord, tailWord_6104705, baseEnd_6104705] using wordTrace_append hprefix tailTrace_6104705
  have hstable : (prefixWord ++ tailWord_6104705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6104705).length < 2 ^ (prefixWord ++ tailWord_6104705).sum := by decide
  have hdescent : baseEnd_6104705 < baseStart_6104705 := by decide
  rcases family_descends (prefixWord ++ tailWord_6104705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6104722 : List Nat := [3, 2, 3, 1, 4, 1, 1, 1, 1, 3, 3]
def baseStart_6104722 : Nat := 118140960795 + 6104722 * 2 ^ 59
def prefixEnd_6104722 : Nat := 4983230072969 + 3 ^ 40 * 6104722 * 2
def baseEnd_6104722 : Nat := 3134656648076769480799901

theorem tailTrace_6104722 : CollatzResearch.WordTrace tailWord_6104722 prefixEnd_6104722 3134656648076769480799901 := by
  unfold tailWord_6104722
  simp only [CollatzResearch.WordTrace]
  refine ⟨55664375847410568089201105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148438335593094848237869613 55664375847410568089201105)
  ·
    refine ⟨41748281885557926066900829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55664375847410568089201105 41748281885557926066900829)
    ·
      refine ⟨15655605707084222275087811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41748281885557926066900829 15655605707084222275087811)
      ·
        refine ⟨23483408560626333412631717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15655605707084222275087811 23483408560626333412631717)
        ·
          refine ⟨4403139105117437514868447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23483408560626333412631717 4403139105117437514868447)
          ·
            refine ⟨6604708657676156272302671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4403139105117437514868447 6604708657676156272302671)
            ·
              refine ⟨9907062986514234408454007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6604708657676156272302671 9907062986514234408454007)
              ·
                refine ⟨14860594479771351612681011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9907062986514234408454007 14860594479771351612681011)
                ·
                  refine ⟨22290891719657027419021517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14860594479771351612681011 22290891719657027419021517)
                  ·
                    refine ⟨8359084394871385282133069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22290891719657027419021517 8359084394871385282133069)
                    ·
                      refine ⟨3134656648076769480799901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8359084394871385282133069 3134656648076769480799901)
                      ·
                        rfl

theorem cell23_6104722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 1, 1, 1, 3, 3].length) (baseStart_6104722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6104722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6104722 prefixEnd_6104722 := by exact prefixLift 6104722
  have htrace : WordTrace (prefixWord ++ tailWord_6104722) baseStart_6104722 baseEnd_6104722 := by
    simpa [prefixWord, tailWord_6104722, baseEnd_6104722] using wordTrace_append hprefix tailTrace_6104722
  have hstable : (prefixWord ++ tailWord_6104722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6104722).length < 2 ^ (prefixWord ++ tailWord_6104722).sum := by decide
  have hdescent : baseEnd_6104722 < baseStart_6104722 := by decide
  rcases family_descends (prefixWord ++ tailWord_6104722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6104732 : List Nat := [2, 2, 3, 2, 3, 1, 2, 2, 1, 3, 2]
def baseStart_6104732 : Nat := 118140960795 + 6104732 * 2 ^ 59
def prefixEnd_6104732 : Nat := 4983230072969 + 3 ^ 40 * 6104732 * 2
def baseEnd_6104732 : Nat := 3134661782883314441674855

theorem tailTrace_6104732 : CollatzResearch.WordTrace tailWord_6104732 prefixEnd_6104732 3134661782883314441674855 := by
  unfold tailWord_6104732
  simp only [CollatzResearch.WordTrace]
  refine ⟨111328934059803022032334225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148438578746404029376445633 111328934059803022032334225)
  ·
    refine ⟨83496700544852266524250669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111328934059803022032334225 83496700544852266524250669)
    ·
      refine ⟨31311262704319599946594001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83496700544852266524250669 31311262704319599946594001)
      ·
        refine ⟨23483447028239699959945501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31311262704319599946594001 23483447028239699959945501)
        ·
          refine ⟨8806292635589887484979563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23483447028239699959945501 8806292635589887484979563)
          ·
            refine ⟨13209438953384831227469345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8806292635589887484979563 13209438953384831227469345)
            ·
              refine ⟨9907079215038623420602009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13209438953384831227469345 9907079215038623420602009)
              ·
                refine ⟨7430309411278967565451507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9907079215038623420602009 7430309411278967565451507)
                ·
                  refine ⟨11145464116918451348177261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7430309411278967565451507 11145464116918451348177261)
                  ·
                    refine ⟨4179549043844419255566473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11145464116918451348177261 4179549043844419255566473)
                    ·
                      refine ⟨3134661782883314441674855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4179549043844419255566473 3134661782883314441674855)
                      ·
                        rfl

theorem cell23_6104732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 2, 2, 1, 3, 2].length) (baseStart_6104732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6104732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6104732 prefixEnd_6104732 := by exact prefixLift 6104732
  have htrace : WordTrace (prefixWord ++ tailWord_6104732) baseStart_6104732 baseEnd_6104732 := by
    simpa [prefixWord, tailWord_6104732, baseEnd_6104732] using wordTrace_append hprefix tailTrace_6104732
  have hstable : (prefixWord ++ tailWord_6104732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6104732).length < 2 ^ (prefixWord ++ tailWord_6104732).sum := by decide
  have hdescent : baseEnd_6104732 < baseStart_6104732 := by decide
  rcases family_descends (prefixWord ++ tailWord_6104732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6104761 : List Nat := [1, 2, 1, 4, 1, 1, 2, 1, 4, 3, 3]
def baseStart_6104761 : Nat := 118140960795 + 6104761 * 2 ^ 59
def prefixEnd_6104761 : Nat := 4983230072969 + 3 ^ 40 * 6104761 * 2
def baseEnd_6104761 : Nat := 3134676673822294828212221

theorem tailTrace_6104761 : CollatzResearch.WordTrace tailWord_6104761 prefixEnd_6104761 3134676673822294828212221 := by
  unfold tailWord_6104761
  simp only [CollatzResearch.WordTrace]
  refine ⟨222658925836500982017474137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148439283891000654678316091 222658925836500982017474137)
  ·
    refine ⟨166994194377375736513105603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222658925836500982017474137 166994194377375736513105603)
    ·
      refine ⟨250491291566063604769658405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166994194377375736513105603 250491291566063604769658405)
      ·
        refine ⟨46967117168636925894310951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 250491291566063604769658405 46967117168636925894310951)
        ·
          refine ⟨70450675752955388841466427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46967117168636925894310951 70450675752955388841466427)
          ·
            refine ⟨105676013629433083262199641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70450675752955388841466427 105676013629433083262199641)
            ·
              refine ⟨79257010222074812446649731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105676013629433083262199641 79257010222074812446649731)
              ·
                refine ⟨118885515333112218669974597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79257010222074812446649731 118885515333112218669974597)
                ·
                  refine ⟨22291034124958541000620237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 118885515333112218669974597 22291034124958541000620237)
                  ·
                    refine ⟨8359137796859452875232589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22291034124958541000620237 8359137796859452875232589)
                    ·
                      refine ⟨3134676673822294828212221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8359137796859452875232589 3134676673822294828212221)
                      ·
                        rfl

theorem cell23_6104761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 4, 3, 3].length) (baseStart_6104761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6104761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6104761 prefixEnd_6104761 := by exact prefixLift 6104761
  have htrace : WordTrace (prefixWord ++ tailWord_6104761) baseStart_6104761 baseEnd_6104761 := by
    simpa [prefixWord, tailWord_6104761, baseEnd_6104761] using wordTrace_append hprefix tailTrace_6104761
  have hstable : (prefixWord ++ tailWord_6104761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6104761).length < 2 ^ (prefixWord ++ tailWord_6104761).sum := by decide
  have hdescent : baseEnd_6104761 < baseStart_6104761 := by decide
  rcases family_descends (prefixWord ++ tailWord_6104761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6104818 : List Nat := [3, 2, 1, 3, 1, 1, 1, 4, 2, 1, 4]
def baseStart_6104818 : Nat := 118140960795 + 6104818 * 2 ^ 59
def prefixEnd_6104818 : Nat := 4983230072969 + 3 ^ 40 * 6104818 * 2
def baseEnd_6104818 : Nat := 3134705942219601105199459

theorem tailTrace_6104818 : CollatzResearch.WordTrace tailWord_6104818 prefixEnd_6104818 3134705942219601105199459 := by
  unfold tailWord_6104818
  simp only [CollatzResearch.WordTrace]
  refine ⟨55665251199323620188074777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148440669864862987168199405 55665251199323620188074777)
  ·
    refine ⟨41748938399492715141056083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55665251199323620188074777 41748938399492715141056083)
    ·
      refine ⟨62623407599239072711584125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41748938399492715141056083 62623407599239072711584125)
      ·
        refine ⟨23483777849714652266844047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62623407599239072711584125 23483777849714652266844047)
        ·
          refine ⟨35225666774571978400266071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23483777849714652266844047 35225666774571978400266071)
          ·
            refine ⟨52838500161857967600399107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35225666774571978400266071 52838500161857967600399107)
            ·
              refine ⟨79257750242786951400598661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52838500161857967600399107 79257750242786951400598661)
              ·
                refine ⟨14860828170522553387612249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 79257750242786951400598661 14860828170522553387612249)
                ·
                  refine ⟨11145621127891915040709187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14860828170522553387612249 11145621127891915040709187)
                  ·
                    refine ⟨16718431691837872561063781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11145621127891915040709187 16718431691837872561063781)
                    ·
                      refine ⟨3134705942219601105199459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16718431691837872561063781 3134705942219601105199459)
                      ·
                        rfl

theorem cell23_6104818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_6104818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6104818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6104818 prefixEnd_6104818 := by exact prefixLift 6104818
  have htrace : WordTrace (prefixWord ++ tailWord_6104818) baseStart_6104818 baseEnd_6104818 := by
    simpa [prefixWord, tailWord_6104818, baseEnd_6104818] using wordTrace_append hprefix tailTrace_6104818
  have hstable : (prefixWord ++ tailWord_6104818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6104818).length < 2 ^ (prefixWord ++ tailWord_6104818).sum := by decide
  have hdescent : baseEnd_6104818 < baseStart_6104818 := by decide
  rcases family_descends (prefixWord ++ tailWord_6104818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6104828 : List Nat := [2, 2, 2, 1, 3, 1, 2, 3, 3, 4]
def baseStart_6104828 : Nat := 118140960795 + 6104828 * 2 ^ 59
def prefixEnd_6104828 : Nat := 4983230072969 + 3 ^ 40 * 6104828 * 2
def baseEnd_6104828 : Nat := 1044903692342048688691471

theorem tailTrace_6104828 : CollatzResearch.WordTrace tailWord_6104828 prefixEnd_6104828 1044903692342048688691471 := by
  unfold tailWord_6104828
  simp only [CollatzResearch.WordTrace]
  refine ⟨111330684763629126230081569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148440913018172168306775425 111330684763629126230081569)
  ·
    refine ⟨83498013572721844672561177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111330684763629126230081569 83498013572721844672561177)
    ·
      refine ⟨62623510179541383504420883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83498013572721844672561177 62623510179541383504420883)
      ·
        refine ⟨93935265269312075256631325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62623510179541383504420883 93935265269312075256631325)
        ·
          refine ⟨35225724475992028221236747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93935265269312075256631325 35225724475992028221236747)
          ·
            refine ⟨52838586713988042331855121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35225724475992028221236747 52838586713988042331855121)
            ·
              refine ⟨39628940035491031748891341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52838586713988042331855121 39628940035491031748891341)
              ·
                refine ⟨14860852513309136905834253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39628940035491031748891341 14860852513309136905834253)
                ·
                  refine ⟨5572819692490926339687845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14860852513309136905834253 5572819692490926339687845)
                  ·
                    refine ⟨1044903692342048688691471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5572819692490926339687845 1044903692342048688691471)
                    ·
                      rfl

theorem cell23_6104828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 3, 3, 4].length) (baseStart_6104828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6104828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6104828 prefixEnd_6104828 := by exact prefixLift 6104828
  have htrace : WordTrace (prefixWord ++ tailWord_6104828) baseStart_6104828 baseEnd_6104828 := by
    simpa [prefixWord, tailWord_6104828, baseEnd_6104828] using wordTrace_append hprefix tailTrace_6104828
  have hstable : (prefixWord ++ tailWord_6104828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6104828).length < 2 ^ (prefixWord ++ tailWord_6104828).sum := by decide
  have hdescent : baseEnd_6104828 < baseStart_6104828 := by decide
  rcases family_descends (prefixWord ++ tailWord_6104828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6104851 : List Nat := [1, 1, 1, 2, 1, 3, 2, 1, 1, 7, 3]
def baseStart_6104851 : Nat := 118140960795 + 6104851 * 2 ^ 59
def prefixEnd_6104851 : Nat := 4983230072969 + 3 ^ 40 * 6104851 * 2
def baseEnd_6104851 : Nat := 3134722887081199476086807

theorem tailTrace_6104851 : CollatzResearch.WordTrace tailWord_6104851 prefixEnd_6104851 3134722887081199476086807 := by
  unfold tailWord_6104851
  simp only [CollatzResearch.WordTrace]
  refine ⟨222662208406174927388250407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148441472270783284925500271 222662208406174927388250407)
  ·
    refine ⟨333993312609262391082375611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222662208406174927388250407 333993312609262391082375611)
    ·
      refine ⟨500989968913893586623563417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 333993312609262391082375611 500989968913893586623563417)
      ·
        refine ⟨375742476685420189967672563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 500989968913893586623563417 375742476685420189967672563)
        ·
          refine ⟨563613715028130284951508845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 375742476685420189967672563 563613715028130284951508845)
          ·
            refine ⟨211355143135548856856815817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 563613715028130284951508845 211355143135548856856815817)
            ·
              refine ⟨158516357351661642642611863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 211355143135548856856815817 158516357351661642642611863)
              ·
                refine ⟨237774536027492463963917795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 158516357351661642642611863 237774536027492463963917795)
                ·
                  refine ⟨356661804041238695945876693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 237774536027492463963917795 356661804041238695945876693)
                  ·
                    refine ⟨8359261032216531936231485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 356661804041238695945876693 8359261032216531936231485)
                    ·
                      refine ⟨3134722887081199476086807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8359261032216531936231485 3134722887081199476086807)
                      ·
                        rfl

theorem cell23_6104851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 7, 3].length) (baseStart_6104851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6104851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6104851 prefixEnd_6104851 := by exact prefixLift 6104851
  have htrace : WordTrace (prefixWord ++ tailWord_6104851) baseStart_6104851 baseEnd_6104851 := by
    simpa [prefixWord, tailWord_6104851, baseEnd_6104851] using wordTrace_append hprefix tailTrace_6104851
  have hstable : (prefixWord ++ tailWord_6104851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6104851).length < 2 ^ (prefixWord ++ tailWord_6104851).sum := by decide
  have hdescent : baseEnd_6104851 < baseStart_6104851 := by decide
  rcases family_descends (prefixWord ++ tailWord_6104851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6104855 : List Nat := [1, 1, 3, 4, 2, 1, 3, 1, 2, 2, 3]
def baseStart_6104855 : Nat := 118140960795 + 6104855 * 2 ^ 59
def prefixEnd_6104855 : Nat := 4983230072969 + 3 ^ 40 * 6104855 * 2
def baseEnd_6104855 : Nat := 3134724941003817460436789

theorem tailTrace_6104855 : CollatzResearch.WordTrace tailWord_6104855 prefixEnd_6104855 3134724941003817460436789 := by
  unfold tailWord_6104855
  simp only [CollatzResearch.WordTrace]
  refine ⟨222662354298160436071396019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148441569532106957380930679 222662354298160436071396019)
  ·
    refine ⟨333993531447240654107094029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222662354298160436071396019 333993531447240654107094029)
    ·
      refine ⟨125247574292715245290160261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 333993531447240654107094029 125247574292715245290160261)
      ·
        refine ⟨23483920179884108491905049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 125247574292715245290160261 23483920179884108491905049)
        ·
          refine ⟨17612940134913081368928787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23483920179884108491905049 17612940134913081368928787)
          ·
            refine ⟨26419410202369622053393181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17612940134913081368928787 26419410202369622053393181)
            ·
              refine ⟨9907278825888608270022443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26419410202369622053393181 9907278825888608270022443)
              ·
                refine ⟨14860918238832912405033665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9907278825888608270022443 14860918238832912405033665)
                ·
                  refine ⟨11145688679124684303775249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14860918238832912405033665 11145688679124684303775249)
                  ·
                    refine ⟨8359266509343513227831437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11145688679124684303775249 8359266509343513227831437)
                    ·
                      refine ⟨3134724941003817460436789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8359266509343513227831437 3134724941003817460436789)
                      ·
                        rfl

theorem cell23_6104855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 3, 1, 2, 2, 3].length) (baseStart_6104855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6104855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6104855 prefixEnd_6104855 := by exact prefixLift 6104855
  have htrace : WordTrace (prefixWord ++ tailWord_6104855) baseStart_6104855 baseEnd_6104855 := by
    simpa [prefixWord, tailWord_6104855, baseEnd_6104855] using wordTrace_append hprefix tailTrace_6104855
  have hstable : (prefixWord ++ tailWord_6104855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6104855).length < 2 ^ (prefixWord ++ tailWord_6104855).sum := by decide
  have hdescent : baseEnd_6104855 < baseStart_6104855 := by decide
  rcases family_descends (prefixWord ++ tailWord_6104855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6104928 : List Nat := [2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 5]
def baseStart_6104928 : Nat := 118140960795 + 6104928 * 2 ^ 59
def prefixEnd_6104928 : Nat := 4983230072969 + 3 ^ 40 * 6104928 * 2
def baseEnd_6104928 : Nat := 3134762425091595674823953

theorem tailTrace_6104928 : CollatzResearch.WordTrace tailWord_6104928 prefixEnd_6104928 3134762425091595674823953 := by
  unfold tailWord_6104928
  simp only [CollatzResearch.WordTrace]
  refine ⟨111332508413447984769401719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148443344551263979692535625 111332508413447984769401719)
  ·
    refine ⟨166998762620171977154102579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111332508413447984769401719 166998762620171977154102579)
    ·
      refine ⟨250498143930257965731153869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 166998762620171977154102579 250498143930257965731153869)
      ·
        refine ⟨93936803973846737149182701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 250498143930257965731153869 93936803973846737149182701)
        ·
          refine ⟨35226301490192526430943513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93936803973846737149182701 35226301490192526430943513)
          ·
            refine ⟨26419726117644394823207635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35226301490192526430943513 26419726117644394823207635)
            ·
              refine ⟨39629589176466592234811453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26419726117644394823207635 39629589176466592234811453)
              ·
                refine ⟨14861095941174972088054295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39629589176466592234811453 14861095941174972088054295)
                ·
                  refine ⟨22291643911762458132081443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14861095941174972088054295 22291643911762458132081443)
                  ·
                    refine ⟨33437465867643687198122165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22291643911762458132081443 33437465867643687198122165)
                    ·
                      refine ⟨3134762425091595674823953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33437465867643687198122165 3134762425091595674823953)
                      ·
                        rfl

theorem cell23_6104928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 5].length) (baseStart_6104928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6104928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6104928 prefixEnd_6104928 := by exact prefixLift 6104928
  have htrace : WordTrace (prefixWord ++ tailWord_6104928) baseStart_6104928 baseEnd_6104928 := by
    simpa [prefixWord, tailWord_6104928, baseEnd_6104928] using wordTrace_append hprefix tailTrace_6104928
  have hstable : (prefixWord ++ tailWord_6104928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6104928).length < 2 ^ (prefixWord ++ tailWord_6104928).sum := by decide
  have hdescent : baseEnd_6104928 < baseStart_6104928 := by decide
  rcases family_descends (prefixWord ++ tailWord_6104928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6104935 : List Nat := [1, 1, 5, 1, 2, 1, 2, 4, 2, 4]
def baseStart_6104935 : Nat := 118140960795 + 6104935 * 2 ^ 59
def prefixEnd_6104935 : Nat := 4983230072969 + 3 ^ 40 * 6104935 * 2
def baseEnd_6104935 : Nat := 1044922006485392382478807

theorem tailTrace_6104935 : CollatzResearch.WordTrace tailWord_6104935 prefixEnd_6104935 1044922006485392382478807 := by
  unfold tailWord_6104935
  simp only [CollatzResearch.WordTrace]
  refine ⟨222665272137870609734308259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148443514758580406489538839 222665272137870609734308259)
  ·
    refine ⟨333997908206805914601462389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222665272137870609734308259 333997908206805914601462389)
    ·
      refine ⟨31312303894388054493887099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 333997908206805914601462389 31312303894388054493887099)
      ·
        refine ⟨46968455841582081740830649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31312303894388054493887099 46968455841582081740830649)
        ·
          refine ⟨35226341881186561305622987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46968455841582081740830649 35226341881186561305622987)
          ·
            refine ⟨52839512821779841958434481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35226341881186561305622987 52839512821779841958434481)
            ·
              refine ⟨39629634616334881468825861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52839512821779841958434481 39629634616334881468825861)
              ·
                refine ⟨7430556490562790275404849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39629634616334881468825861 7430556490562790275404849)
                ·
                  refine ⟨5572917367922092706553637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7430556490562790275404849 5572917367922092706553637)
                  ·
                    refine ⟨1044922006485392382478807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5572917367922092706553637 1044922006485392382478807)
                    ·
                      rfl

theorem cell23_6104935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 4, 2, 4].length) (baseStart_6104935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6104935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6104935 prefixEnd_6104935 := by exact prefixLift 6104935
  have htrace : WordTrace (prefixWord ++ tailWord_6104935) baseStart_6104935 baseEnd_6104935 := by
    simpa [prefixWord, tailWord_6104935, baseEnd_6104935] using wordTrace_append hprefix tailTrace_6104935
  have hstable : (prefixWord ++ tailWord_6104935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6104935).length < 2 ^ (prefixWord ++ tailWord_6104935).sum := by decide
  have hdescent : baseEnd_6104935 < baseStart_6104935 := by decide
  rcases family_descends (prefixWord ++ tailWord_6104935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6104982 : List Nat := [5, 3, 1, 1, 2, 11]
def baseStart_6104982 : Nat := 118140960795 + 6104982 * 2 ^ 59
def prefixEnd_6104982 : Nat := 4983230072969 + 3 ^ 40 * 6104982 * 2
def baseEnd_6104982 : Nat := 12900371000193162401435

theorem tailTrace_6104982 : CollatzResearch.WordTrace tailWord_6104982 prefixEnd_6104982 12900371000193162401435 := by
  unfold tailWord_6104982
  simp only [CollatzResearch.WordTrace]
  refine ⟨13916686648043771047579325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 148444657579133557840846133 13916686648043771047579325)
  ·
    refine ⟨5218757493016414142842247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13916686648043771047579325 5218757493016414142842247)
    ·
      refine ⟨7828136239524621214263371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5218757493016414142842247 7828136239524621214263371)
      ·
        refine ⟨11742204359286931821395057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7828136239524621214263371 11742204359286931821395057)
        ·
          refine ⟨8806653269465198866046293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11742204359286931821395057 8806653269465198866046293)
          ·
            refine ⟨12900371000193162401435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 8806653269465198866046293 12900371000193162401435)
            ·
              rfl

theorem cell23_6104982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 11].length) (baseStart_6104982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6104982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6104982 prefixEnd_6104982 := by exact prefixLift 6104982
  have htrace : WordTrace (prefixWord ++ tailWord_6104982) baseStart_6104982 baseEnd_6104982 := by
    simpa [prefixWord, tailWord_6104982, baseEnd_6104982] using wordTrace_append hprefix tailTrace_6104982
  have hstable : (prefixWord ++ tailWord_6104982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6104982).length < 2 ^ (prefixWord ++ tailWord_6104982).sum := by decide
  have hdescent : baseEnd_6104982 < baseStart_6104982 := by decide
  rcases family_descends (prefixWord ++ tailWord_6104982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6105006 : List Nat := [4, 1, 5, 1, 1, 1, 2, 1, 1, 2, 4]
def baseStart_6105006 : Nat := 118140960795 + 6105006 * 2 ^ 59
def prefixEnd_6105006 : Nat := 4983230072969 + 3 ^ 40 * 6105006 * 2
def baseEnd_6105006 : Nat := 3134802476582646369648595

theorem tailTrace_6105006 : CollatzResearch.WordTrace tailWord_6105006 prefixEnd_6105006 3134802476582646369648595 := by
  unfold tailWord_6105006
  simp only [CollatzResearch.WordTrace]
  refine ⟨27833482715076673607517859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148445241147075592573428581 27833482715076673607517859)
  ·
    refine ⟨41750224072615010411276789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27833482715076673607517859 41750224072615010411276789)
    ·
      refine ⟨3914083506807657226057199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 41750224072615010411276789 3914083506807657226057199)
      ·
        refine ⟨5871125260211485839085799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3914083506807657226057199 5871125260211485839085799)
        ·
          refine ⟨8806687890317228758628699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5871125260211485839085799 8806687890317228758628699)
          ·
            refine ⟨13210031835475843137943049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8806687890317228758628699 13210031835475843137943049)
            ·
              refine ⟨9907523876606882353457287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13210031835475843137943049 9907523876606882353457287)
              ·
                refine ⟨14861285814910323530185931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9907523876606882353457287 14861285814910323530185931)
                ·
                  refine ⟨22291928722365485295278897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14861285814910323530185931 22291928722365485295278897)
                  ·
                    refine ⟨16718946541774113971459173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22291928722365485295278897 16718946541774113971459173)
                    ·
                      refine ⟨3134802476582646369648595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16718946541774113971459173 3134802476582646369648595)
                      ·
                        rfl

theorem cell23_6105006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_6105006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6105006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6105006 prefixEnd_6105006 := by exact prefixLift 6105006
  have htrace : WordTrace (prefixWord ++ tailWord_6105006) baseStart_6105006 baseEnd_6105006 := by
    simpa [prefixWord, tailWord_6105006, baseEnd_6105006] using wordTrace_append hprefix tailTrace_6105006
  have hstable : (prefixWord ++ tailWord_6105006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6105006).length < 2 ^ (prefixWord ++ tailWord_6105006).sum := by decide
  have hdescent : baseEnd_6105006 < baseStart_6105006 := by decide
  rcases family_descends (prefixWord ++ tailWord_6105006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6105018 : List Nat := [3, 1, 1, 1, 2, 1, 2, 4, 2, 1, 5]
def baseStart_6105018 : Nat := 118140960795 + 6105018 * 2 ^ 59
def prefixEnd_6105018 : Nat := 4983230072969 + 3 ^ 40 * 6105018 * 2
def baseEnd_6105018 : Nat := 3134808638350500322698539

theorem tailTrace_6105018 : CollatzResearch.WordTrace tailWord_6105018 prefixEnd_6105018 3134808638350500322698539 := by
  unfold tailWord_6105018
  simp only [CollatzResearch.WordTrace]
  refine ⟨55667074849142478727394927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148445532931046609939719805 55667074849142478727394927)
  ·
    refine ⟨83500612273713718091092391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55667074849142478727394927 83500612273713718091092391)
    ·
      refine ⟨125250918410570577136638587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83500612273713718091092391 125250918410570577136638587)
      ·
        refine ⟨187876377615855865704957881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125250918410570577136638587 187876377615855865704957881)
        ·
          refine ⟨140907283211891899278718411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187876377615855865704957881 140907283211891899278718411)
          ·
            refine ⟨211360924817837848918077617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140907283211891899278718411 211360924817837848918077617)
            ·
              refine ⟨158520693613378386688558213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 211360924817837848918077617 158520693613378386688558213)
              ·
                refine ⟨29722630052508447504104665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 158520693613378386688558213 29722630052508447504104665)
                ·
                  refine ⟨22291972539381335628078499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29722630052508447504104665 22291972539381335628078499)
                  ·
                    refine ⟨33437958809072003442117749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22291972539381335628078499 33437958809072003442117749)
                    ·
                      refine ⟨3134808638350500322698539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33437958809072003442117749 3134808638350500322698539)
                      ·
                        rfl

theorem cell23_6105018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 4, 2, 1, 5].length) (baseStart_6105018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6105018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6105018 prefixEnd_6105018 := by exact prefixLift 6105018
  have htrace : WordTrace (prefixWord ++ tailWord_6105018) baseStart_6105018 baseEnd_6105018 := by
    simpa [prefixWord, tailWord_6105018, baseEnd_6105018] using wordTrace_append hprefix tailTrace_6105018
  have hstable : (prefixWord ++ tailWord_6105018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6105018).length < 2 ^ (prefixWord ++ tailWord_6105018).sum := by decide
  have hdescent : baseEnd_6105018 < baseStart_6105018 := by decide
  rcases family_descends (prefixWord ++ tailWord_6105018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6105032 : List Nat := [2, 1, 3, 1, 4, 1, 2, 2, 1, 4, 2]
def baseStart_6105032 : Nat := 118140960795 + 6105032 * 2 ^ 59
def prefixEnd_6105032 : Nat := 4983230072969 + 3 ^ 40 * 6105032 * 2
def baseEnd_6105032 : Nat := 3134815827079663267923475

theorem tailTrace_6105032 : CollatzResearch.WordTrace tailWord_6105032 prefixEnd_6105032 3134815827079663267923475 := by
  unfold tailWord_6105032
  simp only [CollatzResearch.WordTrace]
  refine ⟨111334405009259597650294675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148445873345679463533726233 111334405009259597650294675)
  ·
    refine ⟨167001607513889396475442013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111334405009259597650294675 167001607513889396475442013)
    ·
      refine ⟨62625602817708523678290755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167001607513889396475442013 62625602817708523678290755)
      ·
        refine ⟨93938404226562785517436133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62625602817708523678290755 93938404226562785517436133)
        ·
          refine ⟨17613450792480522284519275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93938404226562785517436133 17613450792480522284519275)
          ·
            refine ⟨26420176188720783426778913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17613450792480522284519275 26420176188720783426778913)
            ·
              refine ⟨19815132141540587570084185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26420176188720783426778913 19815132141540587570084185)
              ·
                refine ⟨14861349106155440677563139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19815132141540587570084185 14861349106155440677563139)
                ·
                  refine ⟨22292023659233161016344709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14861349106155440677563139 22292023659233161016344709)
                  ·
                    refine ⟨4179754436106217690564633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22292023659233161016344709 4179754436106217690564633)
                    ·
                      refine ⟨3134815827079663267923475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4179754436106217690564633 3134815827079663267923475)
                      ·
                        rfl

theorem cell23_6105032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 2, 1, 4, 2].length) (baseStart_6105032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6105032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6105032 prefixEnd_6105032 := by exact prefixLift 6105032
  have htrace : WordTrace (prefixWord ++ tailWord_6105032) baseStart_6105032 baseEnd_6105032 := by
    simpa [prefixWord, tailWord_6105032, baseEnd_6105032] using wordTrace_append hprefix tailTrace_6105032
  have hstable : (prefixWord ++ tailWord_6105032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6105032).length < 2 ^ (prefixWord ++ tailWord_6105032).sum := by decide
  have hdescent : baseEnd_6105032 < baseStart_6105032 := by decide
  rcases family_descends (prefixWord ++ tailWord_6105032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6105036 : List Nat := [2, 2, 1, 4, 1, 4, 2, 1, 1, 3, 2]
def baseStart_6105036 : Nat := 118140960795 + 6105036 * 2 ^ 59
def prefixEnd_6105036 : Nat := 4983230072969 + 3 ^ 40 * 6105036 * 2
def baseEnd_6105036 : Nat := 3134817881002281252273457

theorem tailTrace_6105036 : CollatzResearch.WordTrace tailWord_6105036 prefixEnd_6105036 3134817881002281252273457 := by
  unfold tailWord_6105036
  simp only [CollatzResearch.WordTrace]
  refine ⟨111334477955252351991867481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148445970607003135989156641 111334477955252351991867481)
  ·
    refine ⟨83500858466439263993900611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111334477955252351991867481 83500858466439263993900611)
    ·
      refine ⟨125251287699658895990850917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83500858466439263993900611 125251287699658895990850917)
      ·
        refine ⟨23484616443686042998284547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 125251287699658895990850917 23484616443686042998284547)
        ·
          refine ⟨35226924665529064497426821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23484616443686042998284547 35226924665529064497426821)
          ·
            refine ⟨6605048374786699593267529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35226924665529064497426821 6605048374786699593267529)
            ·
              refine ⟨4953786281090024694950647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6605048374786699593267529 4953786281090024694950647)
              ·
                refine ⟨7430679421635037042425971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4953786281090024694950647 7430679421635037042425971)
                ·
                  refine ⟨11146019132452555563638957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7430679421635037042425971 11146019132452555563638957)
                  ·
                    refine ⟨4179757174669708336364609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11146019132452555563638957 4179757174669708336364609)
                    ·
                      refine ⟨3134817881002281252273457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4179757174669708336364609 3134817881002281252273457)
                      ·
                        rfl

theorem cell23_6105036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 2, 1, 1, 3, 2].length) (baseStart_6105036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6105036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6105036 prefixEnd_6105036 := by exact prefixLift 6105036
  have htrace : WordTrace (prefixWord ++ tailWord_6105036) baseStart_6105036 baseEnd_6105036 := by
    simpa [prefixWord, tailWord_6105036, baseEnd_6105036] using wordTrace_append hprefix tailTrace_6105036
  have hstable : (prefixWord ++ tailWord_6105036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6105036).length < 2 ^ (prefixWord ++ tailWord_6105036).sum := by decide
  have hdescent : baseEnd_6105036 < baseStart_6105036 := by decide
  rcases family_descends (prefixWord ++ tailWord_6105036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6105038 : List Nat := [4, 1, 1, 1, 2, 2, 1, 2, 9]
def baseStart_6105038 : Nat := 118140960795 + 6105038 * 2 ^ 59
def prefixEnd_6105038 : Nat := 4983230072969 + 3 ^ 40 * 6105038 * 2
def baseEnd_6105038 : Nat := 348313211995954471605383

theorem tailTrace_6105038 : CollatzResearch.WordTrace tailWord_6105038 prefixEnd_6105038 348313211995954471605383 := by
  unfold tailWord_6105038
  simp only [CollatzResearch.WordTrace]
  refine ⟨27833628607062182290663471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148446019237664972216871845 27833628607062182290663471)
  ·
    refine ⟨41750442910593273435995207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27833628607062182290663471 41750442910593273435995207)
    ·
      refine ⟨62625664365889910153992811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41750442910593273435995207 62625664365889910153992811)
      ·
        refine ⟨93938496548834865230989217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62625664365889910153992811 93938496548834865230989217)
        ·
          refine ⟨70453872411626148923241913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93938496548834865230989217 70453872411626148923241913)
          ·
            refine ⟨52840404308719611692431435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70453872411626148923241913 52840404308719611692431435)
            ·
              refine ⟨79260606463079417538647153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52840404308719611692431435 79260606463079417538647153)
              ·
                refine ⟨59445454847309563153985365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79260606463079417538647153 59445454847309563153985365)
                ·
                  refine ⟨348313211995954471605383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 59445454847309563153985365 348313211995954471605383)
                  ·
                    rfl

theorem cell23_6105038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 2, 9].length) (baseStart_6105038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6105038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6105038 prefixEnd_6105038 := by exact prefixLift 6105038
  have htrace : WordTrace (prefixWord ++ tailWord_6105038) baseStart_6105038 baseEnd_6105038 := by
    simpa [prefixWord, tailWord_6105038, baseEnd_6105038] using wordTrace_append hprefix tailTrace_6105038
  have hstable : (prefixWord ++ tailWord_6105038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6105038).length < 2 ^ (prefixWord ++ tailWord_6105038).sum := by decide
  have hdescent : baseEnd_6105038 < baseStart_6105038 := by decide
  rcases family_descends (prefixWord ++ tailWord_6105038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6105045 : List Nat := [1, 3, 2, 3, 2, 1, 1, 2, 2, 2, 4]
def baseStart_6105045 : Nat := 118140960795 + 6105045 * 2 ^ 59
def prefixEnd_6105045 : Nat := 4983230072969 + 3 ^ 40 * 6105045 * 2
def baseEnd_6105045 : Nat := 3134822502328171717060915

theorem tailTrace_6105045 : CollatzResearch.WordTrace tailWord_6105045 prefixEnd_6105045 3134822502328171717060915 := by
  unfold tailWord_6105045
  simp only [CollatzResearch.WordTrace]
  refine ⟨222669284167472098520812589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148446189444981399013875059 222669284167472098520812589)
  ·
    refine ⟨83500981562802036945304721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 222669284167472098520812589 83500981562802036945304721)
    ·
      refine ⟨62625736172101527708978541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83500981562802036945304721 62625736172101527708978541)
      ·
        refine ⟨23484651064538072890866953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62625736172101527708978541 23484651064538072890866953)
        ·
          refine ⟨17613488298403554668150215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23484651064538072890866953 17613488298403554668150215)
          ·
            refine ⟨26420232447605332002225323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17613488298403554668150215 26420232447605332002225323)
            ·
              refine ⟨39630348671407998003337985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26420232447605332002225323 39630348671407998003337985)
              ·
                refine ⟨29722761503555998502503489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39630348671407998003337985 29722761503555998502503489)
                ·
                  refine ⟨22292071127666998876877617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29722761503555998502503489 22292071127666998876877617)
                  ·
                    refine ⟨16719053345750249157658213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22292071127666998876877617 16719053345750249157658213)
                    ·
                      refine ⟨3134822502328171717060915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16719053345750249157658213 3134822502328171717060915)
                      ·
                        rfl

theorem cell23_6105045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_6105045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6105045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6105045 prefixEnd_6105045 := by exact prefixLift 6105045
  have htrace : WordTrace (prefixWord ++ tailWord_6105045) baseStart_6105045 baseEnd_6105045 := by
    simpa [prefixWord, tailWord_6105045, baseEnd_6105045] using wordTrace_append hprefix tailTrace_6105045
  have hstable : (prefixWord ++ tailWord_6105045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6105045).length < 2 ^ (prefixWord ++ tailWord_6105045).sum := by decide
  have hdescent : baseEnd_6105045 < baseStart_6105045 := by decide
  rcases family_descends (prefixWord ++ tailWord_6105045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6105049 : List Nat := [1, 2, 1, 2, 6, 1, 1, 1, 4, 2, 2]
def baseStart_6105049 : Nat := 118140960795 + 6105049 * 2 ^ 59
def prefixEnd_6105049 : Nat := 4983230072969 + 3 ^ 40 * 6105049 * 2
def baseEnd_6105049 : Nat := 3134824556250789701410897

theorem tailTrace_6105049 : CollatzResearch.WordTrace tailWord_6105049 prefixEnd_6105049 3134824556250789701410897 := by
  unfold tailWord_6105049
  simp only [CollatzResearch.WordTrace]
  refine ⟨222669430059457607203958201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148446286706305071469305467 222669430059457607203958201)
  ·
    refine ⟨167002072544593205402968651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222669430059457607203958201 167002072544593205402968651)
    ·
      refine ⟨250503108816889808104452977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167002072544593205402968651 250503108816889808104452977)
      ·
        refine ⟨187877331612667356078339733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 250503108816889808104452977 187877331612667356078339733)
        ·
          refine ⟨8806749919343782316172175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 187877331612667356078339733 8806749919343782316172175)
          ·
            refine ⟨13210124879015673474258263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8806749919343782316172175 13210124879015673474258263)
            ·
              refine ⟨19815187318523510211387395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13210124879015673474258263 19815187318523510211387395)
              ·
                refine ⟨29722780977785265317081093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19815187318523510211387395 29722780977785265317081093)
                ·
                  refine ⟨5573021433334737246952705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29722780977785265317081093 5573021433334737246952705)
                  ·
                    refine ⟨4179766075001052935214529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5573021433334737246952705 4179766075001052935214529)
                    ·
                      refine ⟨3134824556250789701410897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4179766075001052935214529 3134824556250789701410897)
                      ·
                        rfl

theorem cell23_6105049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 1, 4, 2, 2].length) (baseStart_6105049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6105049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6105049 prefixEnd_6105049 := by exact prefixLift 6105049
  have htrace : WordTrace (prefixWord ++ tailWord_6105049) baseStart_6105049 baseEnd_6105049 := by
    simpa [prefixWord, tailWord_6105049, baseEnd_6105049] using wordTrace_append hprefix tailTrace_6105049
  have hstable : (prefixWord ++ tailWord_6105049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6105049).length < 2 ^ (prefixWord ++ tailWord_6105049).sum := by decide
  have hdescent : baseEnd_6105049 < baseStart_6105049 := by decide
  rcases family_descends (prefixWord ++ tailWord_6105049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6105055 : List Nat := [1, 1, 2, 3, 4, 2, 2, 1, 7]
def baseStart_6105055 : Nat := 118140960795 + 6105055 * 2 ^ 59
def prefixEnd_6105055 : Nat := 4983230072969 + 3 ^ 40 * 6105055 * 2
def baseEnd_6105055 : Nat := 348314181903857408659541

theorem tailTrace_6105055 : CollatzResearch.WordTrace tailWord_6105055 prefixEnd_6105055 348314181903857408659541 := by
  unfold tailWord_6105055
  simp only [CollatzResearch.WordTrace]
  refine ⟨222669648897435870228676619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148446432598290580152451079 222669648897435870228676619)
  ·
    refine ⟨334004473346153805343014929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222669648897435870228676619 334004473346153805343014929)
    ·
      refine ⟨250503355009615354007261197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 334004473346153805343014929 250503355009615354007261197)
      ·
        refine ⟨93938758128605757752722949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 250503355009615354007261197 93938758128605757752722949)
        ·
          refine ⟨17613517149113579578635553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93938758128605757752722949 17613517149113579578635553)
          ·
            refine ⟨13210137861835184683976665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17613517149113579578635553 13210137861835184683976665)
            ·
              refine ⟨9907603396376388512982499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13210137861835184683976665 9907603396376388512982499)
              ·
                refine ⟨14861405094564582769473749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9907603396376388512982499 14861405094564582769473749)
                ·
                  refine ⟨348314181903857408659541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14861405094564582769473749 348314181903857408659541)
                  ·
                    rfl

theorem cell23_6105055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 2, 1, 7].length) (baseStart_6105055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6105055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6105055 prefixEnd_6105055 := by exact prefixLift 6105055
  have htrace : WordTrace (prefixWord ++ tailWord_6105055) baseStart_6105055 baseEnd_6105055 := by
    simpa [prefixWord, tailWord_6105055, baseEnd_6105055] using wordTrace_append hprefix tailTrace_6105055
  have hstable : (prefixWord ++ tailWord_6105055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6105055).length < 2 ^ (prefixWord ++ tailWord_6105055).sum := by decide
  have hdescent : baseEnd_6105055 < baseStart_6105055 := by decide
  rcases family_descends (prefixWord ++ tailWord_6105055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6105066 : List Nat := [3, 1, 3, 1, 2, 1, 5, 1, 2, 2, 2]
def baseStart_6105066 : Nat := 118140960795 + 6105066 * 2 ^ 59
def prefixEnd_6105066 : Nat := 4983230072969 + 3 ^ 40 * 6105066 * 2
def baseEnd_6105066 : Nat := 3134833285421916134898319

theorem tailTrace_6105066 : CollatzResearch.WordTrace tailWord_6105066 prefixEnd_6105066 3134833285421916134898319 := by
  unfold tailWord_6105066
  simp only [CollatzResearch.WordTrace]
  refine ⟨55667512525099004776831763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148446700066930679404884701 55667512525099004776831763)
  ·
    refine ⟨83501268787648507165247645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55667512525099004776831763 83501268787648507165247645)
    ·
      refine ⟨31312975795368190186967867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83501268787648507165247645 31312975795368190186967867)
      ·
        refine ⟨46969463693052285280451801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31312975795368190186967867 46969463693052285280451801)
        ·
          refine ⟨35227097769789213960338851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46969463693052285280451801 35227097769789213960338851)
          ·
            refine ⟨52840646654683820940508277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35227097769789213960338851 52840646654683820940508277)
            ·
              refine ⟨4953810623876608213172651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52840646654683820940508277 4953810623876608213172651)
              ·
                refine ⟨7430715935814912319758977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4953810623876608213172651 7430715935814912319758977)
                ·
                  refine ⟨5573036951861184239819233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7430715935814912319758977 5573036951861184239819233)
                  ·
                    refine ⟨4179777713895888179864425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5573036951861184239819233 4179777713895888179864425)
                    ·
                      refine ⟨3134833285421916134898319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4179777713895888179864425 3134833285421916134898319)
                      ·
                        rfl

theorem cell23_6105066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 5, 1, 2, 2, 2].length) (baseStart_6105066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6105066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6105066 prefixEnd_6105066 := by exact prefixLift 6105066
  have htrace : WordTrace (prefixWord ++ tailWord_6105066) baseStart_6105066 baseEnd_6105066 := by
    simpa [prefixWord, tailWord_6105066, baseEnd_6105066] using wordTrace_append hprefix tailTrace_6105066
  have hstable : (prefixWord ++ tailWord_6105066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6105066).length < 2 ^ (prefixWord ++ tailWord_6105066).sum := by decide
  have hdescent : baseEnd_6105066 < baseStart_6105066 := by decide
  rcases family_descends (prefixWord ++ tailWord_6105066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6105075 : List Nat := [1, 1, 1, 2, 2, 2, 1, 4, 2, 5, 2]
def baseStart_6105075 : Nat := 118140960795 + 6105075 * 2 ^ 59
def prefixEnd_6105075 : Nat := 4983230072969 + 3 ^ 40 * 6105075 * 2
def baseEnd_6105075 : Nat := 3134837906747806599685777

theorem tailTrace_6105075 : CollatzResearch.WordTrace tailWord_6105075 prefixEnd_6105075 3134837906747806599685777 := by
  unfold tailWord_6105075
  simp only [CollatzResearch.WordTrace]
  refine ⟨222670378357363413644404679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148446918904908942429603119 222670378357363413644404679)
  ·
    refine ⟨334005567536045120466607019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222670378357363413644404679 334005567536045120466607019)
    ·
      refine ⟨501008351304067680699910529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 334005567536045120466607019 501008351304067680699910529)
      ·
        refine ⟨375756263478050760524932897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 501008351304067680699910529 375756263478050760524932897)
        ·
          refine ⟨281817197608538070393699673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 375756263478050760524932897 281817197608538070393699673)
          ·
            refine ⟨211362898206403552795274755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 281817197608538070393699673 211362898206403552795274755)
            ·
              refine ⟨317044347309605329192912133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 211362898206403552795274755 317044347309605329192912133)
              ·
                refine ⟨59445815120550999223671025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 317044347309605329192912133 59445815120550999223671025)
                ·
                  refine ⟨44584361340413249417753269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59445815120550999223671025 44584361340413249417753269)
                  ·
                    refine ⟨4179783875663742132914369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44584361340413249417753269 4179783875663742132914369)
                    ·
                      refine ⟨3134837906747806599685777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4179783875663742132914369 3134837906747806599685777)
                      ·
                        rfl

theorem cell23_6105075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 4, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 4, 2, 5, 2].length) (baseStart_6105075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6105075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6105075 prefixEnd_6105075 := by exact prefixLift 6105075
  have htrace : WordTrace (prefixWord ++ tailWord_6105075) baseStart_6105075 baseEnd_6105075 := by
    simpa [prefixWord, tailWord_6105075, baseEnd_6105075] using wordTrace_append hprefix tailTrace_6105075
  have hstable : (prefixWord ++ tailWord_6105075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6105075).length < 2 ^ (prefixWord ++ tailWord_6105075).sum := by decide
  have hdescent : baseEnd_6105075 < baseStart_6105075 := by decide
  rcases family_descends (prefixWord ++ tailWord_6105075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6105115 : List Nat := [1, 1, 1, 1, 1, 1, 3, 7, 3, 4]
def baseStart_6105115 : Nat := 118140960795 + 6105115 * 2 ^ 59
def prefixEnd_6105115 : Nat := 4983230072969 + 3 ^ 40 * 6105115 * 2
def baseEnd_6105115 : Nat := 1044952815324662147728531

theorem tailTrace_6105115 : CollatzResearch.WordTrace tailWord_6105115 prefixEnd_6105115 1044952815324662147728531 := by
  unfold tailWord_6105115
  simp only [CollatzResearch.WordTrace]
  refine ⟨222671837277218500475860799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148447891518145666983907199 222671837277218500475860799)
  ·
    refine ⟨334007755915827750713791199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222671837277218500475860799 334007755915827750713791199)
    ·
      refine ⟨501011633873741626070686799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 334007755915827750713791199 501011633873741626070686799)
      ·
        refine ⟨751517450810612439106030199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 501011633873741626070686799 751517450810612439106030199)
        ·
          refine ⟨1127276176215918658659045299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 751517450810612439106030199 1127276176215918658659045299)
          ·
            refine ⟨1690914264323877987988567949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1127276176215918658659045299 1690914264323877987988567949)
            ·
              refine ⟨634092849121454245495712981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1690914264323877987988567949 634092849121454245495712981)
              ·
                refine ⟨14861551151284083878805773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 634092849121454245495712981 14861551151284083878805773)
                ·
                  refine ⟨5573081681731531454552165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14861551151284083878805773 5573081681731531454552165)
                  ·
                    refine ⟨1044952815324662147728531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5573081681731531454552165 1044952815324662147728531)
                    ·
                      rfl

theorem cell23_6105115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 7, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 7, 3, 4].length) (baseStart_6105115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6105115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6105115 prefixEnd_6105115 := by exact prefixLift 6105115
  have htrace : WordTrace (prefixWord ++ tailWord_6105115) baseStart_6105115 baseEnd_6105115 := by
    simpa [prefixWord, tailWord_6105115, baseEnd_6105115] using wordTrace_append hprefix tailTrace_6105115
  have hstable : (prefixWord ++ tailWord_6105115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6105115).length < 2 ^ (prefixWord ++ tailWord_6105115).sum := by decide
  have hdescent : baseEnd_6105115 < baseStart_6105115 := by decide
  rcases family_descends (prefixWord ++ tailWord_6105115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6105122 : List Nat := [3, 3, 1, 1, 1, 2, 2, 1, 1, 6, 2]
def baseStart_6105122 : Nat := 118140960795 + 6105122 * 2 ^ 59
def prefixEnd_6105122 : Nat := 4983230072969 + 3 ^ 40 * 6105122 * 2
def baseEnd_6105122 : Nat := 3134862040338567915798061

theorem tailTrace_6105122 : CollatzResearch.WordTrace tailWord_6105122 prefixEnd_6105122 3134862040338567915798061 := by
  unfold tailWord_6105122
  simp only [CollatzResearch.WordTrace]
  refine ⟨55668023147048285167841405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148448061725462093780910413 55668023147048285167841405)
  ·
    refine ⟨20875508680143106937940527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55668023147048285167841405 20875508680143106937940527)
    ·
      refine ⟨31313263020214660406910791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20875508680143106937940527 31313263020214660406910791)
      ·
        refine ⟨46969894530321990610366187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31313263020214660406910791 46969894530321990610366187)
        ·
          refine ⟨70454841795482985915549281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46969894530321990610366187 70454841795482985915549281)
          ·
            refine ⟨52841131346612239436661961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70454841795482985915549281 52841131346612239436661961)
            ·
              refine ⟨39630848509959179577496471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52841131346612239436661961 39630848509959179577496471)
              ·
                refine ⟨59446272764938769366244707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39630848509959179577496471 59446272764938769366244707)
                ·
                  refine ⟨89169409147408154049367061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59446272764938769366244707 89169409147408154049367061)
                  ·
                    refine ⟨4179816053784757221064081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 89169409147408154049367061 4179816053784757221064081)
                    ·
                      refine ⟨3134862040338567915798061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4179816053784757221064081 3134862040338567915798061)
                      ·
                        rfl

theorem cell23_6105122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 1, 1, 6, 2].length) (baseStart_6105122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6105122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6105122 prefixEnd_6105122 := by exact prefixLift 6105122
  have htrace : WordTrace (prefixWord ++ tailWord_6105122) baseStart_6105122 baseEnd_6105122 := by
    simpa [prefixWord, tailWord_6105122, baseEnd_6105122] using wordTrace_append hprefix tailTrace_6105122
  have hstable : (prefixWord ++ tailWord_6105122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6105122).length < 2 ^ (prefixWord ++ tailWord_6105122).sum := by decide
  have hdescent : baseEnd_6105122 < baseStart_6105122 := by decide
  rcases family_descends (prefixWord ++ tailWord_6105122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6105149 : List Nat := [1, 4, 1, 3, 1, 1, 2, 5, 1, 4]
def baseStart_6105149 : Nat := 118140960795 + 6105149 * 2 ^ 59
def prefixEnd_6105149 : Nat := 4983230072969 + 3 ^ 40 * 6105149 * 2
def baseEnd_6105149 : Nat := 1044958634772079770053479

theorem tailTrace_6105149 : CollatzResearch.WordTrace tailWord_6105149 prefixEnd_6105149 1044958634772079770053479 := by
  unfold tailWord_6105149
  simp only [CollatzResearch.WordTrace]
  refine ⟨222673077359095324282598501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148448718239396882855065667 222673077359095324282598501)
  ·
    refine ⟨41751202004830373302987219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 222673077359095324282598501 41751202004830373302987219)
    ·
      refine ⟨62626803007245559954480829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41751202004830373302987219 62626803007245559954480829)
      ·
        refine ⟨23485051127717084982930311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62626803007245559954480829 23485051127717084982930311)
        ·
          refine ⟨35227576691575627474395467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23485051127717084982930311 35227576691575627474395467)
          ·
            refine ⟨52841365037363441211593201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35227576691575627474395467 52841365037363441211593201)
            ·
              refine ⟨39631023778022580908694901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52841365037363441211593201 39631023778022580908694901)
              ·
                refine ⟨3715408479189616960190147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39631023778022580908694901 3715408479189616960190147)
                ·
                  refine ⟨5573112718784425440285221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3715408479189616960190147 5573112718784425440285221)
                  ·
                    refine ⟨1044958634772079770053479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5573112718784425440285221 1044958634772079770053479)
                    ·
                      rfl

theorem cell23_6105149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 5, 1, 4].length) (baseStart_6105149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6105149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6105149 prefixEnd_6105149 := by exact prefixLift 6105149
  have htrace : WordTrace (prefixWord ++ tailWord_6105149) baseStart_6105149 baseEnd_6105149 := by
    simpa [prefixWord, tailWord_6105149, baseEnd_6105149] using wordTrace_append hprefix tailTrace_6105149
  have hstable : (prefixWord ++ tailWord_6105149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6105149).length < 2 ^ (prefixWord ++ tailWord_6105149).sum := by decide
  have hdescent : baseEnd_6105149 < baseStart_6105149 := by decide
  rcases family_descends (prefixWord ++ tailWord_6105149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6105166 : List Nat := [4, 1, 1, 1, 1, 4, 4, 2, 1, 4]
def baseStart_6105166 : Nat := 118140960795 + 6105166 * 2 ^ 59
def prefixEnd_6105166 : Nat := 4983230072969 + 3 ^ 40 * 6105166 * 2
def baseEnd_6105166 : Nat := 1044961544495788581215953

theorem tailTrace_6105166 : CollatzResearch.WordTrace tailWord_6105166 prefixEnd_6105166 1044961544495788581215953 := by
  unfold tailWord_6105166
  simp only [CollatzResearch.WordTrace]
  refine ⟨27834212175004217023245919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148449131600022490790644901 27834212175004217023245919)
  ·
    refine ⟨41751318262506325534868879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27834212175004217023245919 41751318262506325534868879)
    ·
      refine ⟨62626977393759488302303319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41751318262506325534868879 62626977393759488302303319)
      ·
        refine ⟨93940466090639232453454979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62626977393759488302303319 93940466090639232453454979)
        ·
          refine ⟨140910699135958848680182469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93940466090639232453454979 140910699135958848680182469)
          ·
            refine ⟨26420756087992284127534213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 140910699135958848680182469 26420756087992284127534213)
            ·
              refine ⟨4953891766498553273912665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26420756087992284127534213 4953891766498553273912665)
              ·
                refine ⟨3715418824873914955434499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4953891766498553273912665 3715418824873914955434499)
                ·
                  refine ⟨5573128237310872433151749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3715418824873914955434499 5573128237310872433151749)
                  ·
                    refine ⟨1044961544495788581215953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5573128237310872433151749 1044961544495788581215953)
                    ·
                      rfl

theorem cell23_6105166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 4, 2, 1, 4].length) (baseStart_6105166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6105166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6105166 prefixEnd_6105166 := by exact prefixLift 6105166
  have htrace : WordTrace (prefixWord ++ tailWord_6105166) baseStart_6105166 baseEnd_6105166 := by
    simpa [prefixWord, tailWord_6105166, baseEnd_6105166] using wordTrace_append hprefix tailTrace_6105166
  have hstable : (prefixWord ++ tailWord_6105166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6105166).length < 2 ^ (prefixWord ++ tailWord_6105166).sum := by decide
  have hdescent : baseEnd_6105166 < baseStart_6105166 := by decide
  rcases family_descends (prefixWord ++ tailWord_6105166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6105175 : List Nat := [1, 1, 3, 2, 2, 1, 3, 2, 3, 5]
def baseStart_6105175 : Nat := 118140960795 + 6105175 * 2 ^ 59
def prefixEnd_6105175 : Nat := 4983230072969 + 3 ^ 40 * 6105175 * 2
def baseEnd_6105175 : Nat := 1044963084937752069478439

theorem tailTrace_6105175 : CollatzResearch.WordTrace tailWord_6105175 prefixEnd_6105175 1044963084937752069478439 := by
  unfold tailWord_6105175
  simp only [CollatzResearch.WordTrace]
  refine ⟨222674025657001130723044979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148449350438000753815363319 222674025657001130723044979)
  ·
    refine ⟨334011038485501696084567469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222674025657001130723044979 334011038485501696084567469)
    ·
      refine ⟨125254139432063136031712801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 334011038485501696084567469 125254139432063136031712801)
      ·
        refine ⟨93940604574047352023784601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125254139432063136031712801 93940604574047352023784601)
        ·
          refine ⟨70455453430535514017838451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93940604574047352023784601 70455453430535514017838451)
          ·
            refine ⟨105683180145803271026757677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70455453430535514017838451 105683180145803271026757677)
            ·
              refine ⟨39631192554676226635034129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105683180145803271026757677 39631192554676226635034129)
              ·
                refine ⟨29723394416007169976275597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39631192554676226635034129 29723394416007169976275597)
                ·
                  refine ⟨11146272906002688741103349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29723394416007169976275597 11146272906002688741103349)
                  ·
                    refine ⟨1044963084937752069478439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11146272906002688741103349 1044963084937752069478439)
                    ·
                      rfl

theorem cell23_6105175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 2, 3, 5].length) (baseStart_6105175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6105175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6105175 prefixEnd_6105175 := by exact prefixLift 6105175
  have htrace : WordTrace (prefixWord ++ tailWord_6105175) baseStart_6105175 baseEnd_6105175 := by
    simpa [prefixWord, tailWord_6105175, baseEnd_6105175] using wordTrace_append hprefix tailTrace_6105175
  have hstable : (prefixWord ++ tailWord_6105175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6105175).length < 2 ^ (prefixWord ++ tailWord_6105175).sum := by decide
  have hdescent : baseEnd_6105175 < baseStart_6105175 := by decide
  rcases family_descends (prefixWord ++ tailWord_6105175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6105189 : List Nat := [1, 3, 1, 3, 2, 3, 1, 2, 3, 1, 3]
def baseStart_6105189 : Nat := 118140960795 + 6105189 * 2 ^ 59
def prefixEnd_6105189 : Nat := 4983230072969 + 3 ^ 40 * 6105189 * 2
def baseEnd_6105189 : Nat := 3134896443542419153660253

theorem tailTrace_6105189 : CollatzResearch.WordTrace tailWord_6105189 prefixEnd_6105189 3134896443542419153660253 := by
  unfold tailWord_6105189
  simp only [CollatzResearch.WordTrace]
  refine ⟨222674536278950411114054621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148449690852633607409369747 222674536278950411114054621)
  ·
    refine ⟨83502951104606404167770483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 222674536278950411114054621 83502951104606404167770483)
    ·
      refine ⟨125254426656909606251655725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83502951104606404167770483 125254426656909606251655725)
      ·
        refine ⟨46970409996341102344370897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125254426656909606251655725 46970409996341102344370897)
        ·
          refine ⟨35227807497255826758278173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46970409996341102344370897 35227807497255826758278173)
          ·
            refine ⟨13210427811470935034354315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35227807497255826758278173 13210427811470935034354315)
            ·
              refine ⟨19815641717206402551531473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13210427811470935034354315 19815641717206402551531473)
              ·
                refine ⟨14861731287904801913648605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19815641717206402551531473 14861731287904801913648605)
                ·
                  refine ⟨5573149232964300717618227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14861731287904801913648605 5573149232964300717618227)
                  ·
                    refine ⟨8359723849446451076427341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5573149232964300717618227 8359723849446451076427341)
                    ·
                      refine ⟨3134896443542419153660253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8359723849446451076427341 3134896443542419153660253)
                      ·
                        rfl

theorem cell23_6105189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 2, 3, 1, 3].length) (baseStart_6105189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6105189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6105189 prefixEnd_6105189 := by exact prefixLift 6105189
  have htrace : WordTrace (prefixWord ++ tailWord_6105189) baseStart_6105189 baseEnd_6105189 := by
    simpa [prefixWord, tailWord_6105189, baseEnd_6105189] using wordTrace_append hprefix tailTrace_6105189
  have hstable : (prefixWord ++ tailWord_6105189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6105189).length < 2 ^ (prefixWord ++ tailWord_6105189).sum := by decide
  have hdescent : baseEnd_6105189 < baseStart_6105189 := by decide
  rcases family_descends (prefixWord ++ tailWord_6105189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6105199 : List Nat := [1, 1, 2, 1, 3, 4, 3, 1, 2, 3, 2]
def baseStart_6105199 : Nat := 118140960795 + 6105199 * 2 ^ 59
def prefixEnd_6105199 : Nat := 4983230072969 + 3 ^ 40 * 6105199 * 2
def baseEnd_6105199 : Nat := 3134901578348964114535207

theorem tailTrace_6105199 : CollatzResearch.WordTrace tailWord_6105199 prefixEnd_6105199 3134901578348964114535207 := by
  unfold tailWord_6105199
  simp only [CollatzResearch.WordTrace]
  refine ⟨222674901008914182821918651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148449934005942788547945767 222674901008914182821918651)
  ·
    refine ⟨334012351513371274232877977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222674901008914182821918651 334012351513371274232877977)
    ·
      refine ⟨250509263635028455674658483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 334012351513371274232877977 250509263635028455674658483)
      ·
        refine ⟨375763895452542683511987725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250509263635028455674658483 375763895452542683511987725)
        ·
          refine ⟨140911460794703506316995397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 375763895452542683511987725 140911460794703506316995397)
          ·
            refine ⟨26420898899006907434436637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 140911460794703506316995397 26420898899006907434436637)
            ·
              refine ⟨9907837087127590287913739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26420898899006907434436637 9907837087127590287913739)
              ·
                refine ⟨14861755630691385431870609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9907837087127590287913739 14861755630691385431870609)
                ·
                  refine ⟨11146316723018539073902957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14861755630691385431870609 11146316723018539073902957)
                  ·
                    refine ⟨4179868771131952152713609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11146316723018539073902957 4179868771131952152713609)
                    ·
                      refine ⟨3134901578348964114535207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4179868771131952152713609 3134901578348964114535207)
                      ·
                        rfl

theorem cell23_6105199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 3, 1, 2, 3, 2].length) (baseStart_6105199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6105199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6105199 prefixEnd_6105199 := by exact prefixLift 6105199
  have htrace : WordTrace (prefixWord ++ tailWord_6105199) baseStart_6105199 baseEnd_6105199 := by
    simpa [prefixWord, tailWord_6105199, baseEnd_6105199] using wordTrace_append hprefix tailTrace_6105199
  have hstable : (prefixWord ++ tailWord_6105199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6105199).length < 2 ^ (prefixWord ++ tailWord_6105199).sum := by decide
  have hdescent : baseEnd_6105199 < baseStart_6105199 := by decide
  rcases family_descends (prefixWord ++ tailWord_6105199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6105209 : List Nat := [1, 2, 1, 3, 4, 1, 4, 1, 1, 5]
def baseStart_6105209 : Nat := 118140960795 + 6105209 * 2 ^ 59
def prefixEnd_6105209 : Nat := 4983230072969 + 3 ^ 40 * 6105209 * 2
def baseEnd_6105209 : Nat := 1044968904385169691803387

theorem tailTrace_6105209 : CollatzResearch.WordTrace tailWord_6105209 prefixEnd_6105209 1044968904385169691803387 := by
  unfold tailWord_6105209
  simp only [CollatzResearch.WordTrace]
  refine ⟨222675265738877954529782681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148450177159251969686521787 222675265738877954529782681)
  ·
    refine ⟨167006449304158465897337011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222675265738877954529782681 167006449304158465897337011)
    ·
      refine ⟨250509673956237698846005517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167006449304158465897337011 250509673956237698846005517)
      ·
        refine ⟨93941127733589137067252069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 250509673956237698846005517 93941127733589137067252069)
        ·
          refine ⟨17613961450047963200109763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93941127733589137067252069 17613961450047963200109763)
          ·
            refine ⟨26420942175071944800164645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17613961450047963200109763 26420942175071944800164645)
            ·
              refine ⟨4953926657825989650030871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26420942175071944800164645 4953926657825989650030871)
              ·
                refine ⟨7430889986738984475046307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4953926657825989650030871 7430889986738984475046307)
                ·
                  refine ⟨11146334980108476712569461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7430889986738984475046307 11146334980108476712569461)
                  ·
                    refine ⟨1044968904385169691803387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11146334980108476712569461 1044968904385169691803387)
                    ·
                      rfl

theorem cell23_6105209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 4, 1, 1, 5].length) (baseStart_6105209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6105209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6105209 prefixEnd_6105209 := by exact prefixLift 6105209
  have htrace : WordTrace (prefixWord ++ tailWord_6105209) baseStart_6105209 baseEnd_6105209 := by
    simpa [prefixWord, tailWord_6105209, baseEnd_6105209] using wordTrace_append hprefix tailTrace_6105209
  have hstable : (prefixWord ++ tailWord_6105209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6105209).length < 2 ^ (prefixWord ++ tailWord_6105209).sum := by decide
  have hdescent : baseEnd_6105209 < baseStart_6105209 := by decide
  rcases family_descends (prefixWord ++ tailWord_6105209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6105225 : List Nat := [1, 2, 1, 1, 4, 2, 2, 2, 1, 1, 6]
def baseStart_6105225 : Nat := 118140960795 + 6105225 * 2 ^ 59
def prefixEnd_6105225 : Nat := 4983230072969 + 3 ^ 40 * 6105225 * 2
def baseEnd_6105225 : Nat := 3134914928845981012810087

theorem tailTrace_6105225 : CollatzResearch.WordTrace tailWord_6105225 prefixEnd_6105225 3134914928845981012810087 := by
  unfold tailWord_6105225
  simp only [CollatzResearch.WordTrace]
  refine ⟨222675849306819989262365129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148450566204546659508243419 222675849306819989262365129)
  ·
    refine ⟨167006886980114991946773847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222675849306819989262365129 167006886980114991946773847)
    ·
      refine ⟨250510330470172487920160771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167006886980114991946773847 250510330470172487920160771)
      ·
        refine ⟨375765495705258731880241157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250510330470172487920160771 375765495705258731880241157)
        ·
          refine ⟨70456030444736012227545217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 375765495705258731880241157 70456030444736012227545217)
          ·
            refine ⟨52842022833552009170658913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70456030444736012227545217 52842022833552009170658913)
            ·
              refine ⟨39631517125164006877994185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52842022833552009170658913 39631517125164006877994185)
              ·
                refine ⟨29723637843873005158495639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39631517125164006877994185 29723637843873005158495639)
                ·
                  refine ⟨44585456765809507737743459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29723637843873005158495639 44585456765809507737743459)
                  ·
                    refine ⟨66878185148714261606615189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44585456765809507737743459 66878185148714261606615189)
                    ·
                      refine ⟨3134914928845981012810087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66878185148714261606615189 3134914928845981012810087)
                      ·
                        rfl

theorem cell23_6105225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 2, 1, 1, 6].length) (baseStart_6105225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6105225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6105225 prefixEnd_6105225 := by exact prefixLift 6105225
  have htrace : WordTrace (prefixWord ++ tailWord_6105225) baseStart_6105225 baseEnd_6105225 := by
    simpa [prefixWord, tailWord_6105225, baseEnd_6105225] using wordTrace_append hprefix tailTrace_6105225
  have hstable : (prefixWord ++ tailWord_6105225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6105225).length < 2 ^ (prefixWord ++ tailWord_6105225).sum := by decide
  have hdescent : baseEnd_6105225 < baseStart_6105225 := by decide
  rcases family_descends (prefixWord ++ tailWord_6105225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6105239 : List Nat := [1, 1, 3, 3, 4, 2, 1, 1, 1, 6]
def baseStart_6105239 : Nat := 118140960795 + 6105239 * 2 ^ 59
def prefixEnd_6105239 : Nat := 4983230072969 + 3 ^ 40 * 6105239 * 2
def baseEnd_6105239 : Nat := 1044974039191714652678341

theorem tailTrace_6105239 : CollatzResearch.WordTrace tailWord_6105239 prefixEnd_6105239 1044974039191714652678341 := by
  unfold tailWord_6105239
  simp only [CollatzResearch.WordTrace]
  refine ⟨222676359928769269653374771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148450906619179513102249847 222676359928769269653374771)
  ·
    refine ⟨334014539893153904480062157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222676359928769269653374771 334014539893153904480062157)
    ·
      refine ⟨125255452459932714180023309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 334014539893153904480062157 125255452459932714180023309)
      ·
        refine ⟨46970794672474767817508741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125255452459932714180023309 46970794672474767817508741)
        ·
          refine ⟨8807024001089018965782889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46970794672474767817508741 8807024001089018965782889)
          ·
            refine ⟨6605268000816764224337167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8807024001089018965782889 6605268000816764224337167)
            ·
              refine ⟨9907902001225146336505751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6605268000816764224337167 9907902001225146336505751)
              ·
                refine ⟨14861853001837719504758627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9907902001225146336505751 14861853001837719504758627)
                ·
                  refine ⟨22292779502756579257137941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14861853001837719504758627 22292779502756579257137941)
                  ·
                    refine ⟨1044974039191714652678341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22292779502756579257137941 1044974039191714652678341)
                    ·
                      rfl

theorem cell23_6105239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 1, 1, 1, 6].length) (baseStart_6105239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6105239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6105239 prefixEnd_6105239 := by exact prefixLift 6105239
  have htrace : WordTrace (prefixWord ++ tailWord_6105239) baseStart_6105239 baseEnd_6105239 := by
    simpa [prefixWord, tailWord_6105239, baseEnd_6105239] using wordTrace_append hprefix tailTrace_6105239
  have hstable : (prefixWord ++ tailWord_6105239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6105239).length < 2 ^ (prefixWord ++ tailWord_6105239).sum := by decide
  have hdescent : baseEnd_6105239 < baseStart_6105239 := by decide
  rcases family_descends (prefixWord ++ tailWord_6105239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6105249 : List Nat := [1, 2, 3, 3, 1, 2, 1, 4, 1, 2, 3]
def baseStart_6105249 : Nat := 118140960795 + 6105249 * 2 ^ 59
def prefixEnd_6105249 : Nat := 4983230072969 + 3 ^ 40 * 6105249 * 2
def baseEnd_6105249 : Nat := 3134927252381688918909977

theorem tailTrace_6105249 : CollatzResearch.WordTrace tailWord_6105249 prefixEnd_6105249 3134927252381688918909977 := by
  unfold tailWord_6105249
  simp only [CollatzResearch.WordTrace]
  refine ⟨222676724658733041361238801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148451149772488694240825867 222676724658733041361238801)
  ·
    refine ⟨167007543494049781020929101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222676724658733041361238801 167007543494049781020929101)
    ·
      refine ⟨62627828810268667882848413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167007543494049781020929101 62627828810268667882848413)
      ·
        refine ⟨23485435803850750456068155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62627828810268667882848413 23485435803850750456068155)
        ·
          refine ⟨35228153705776125684102233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23485435803850750456068155 35228153705776125684102233)
          ·
            refine ⟨26421115279332094263076675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35228153705776125684102233 26421115279332094263076675)
            ·
              refine ⟨39631672918998141394615013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26421115279332094263076675 39631672918998141394615013)
              ·
                refine ⟨7430938672312151511490315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39631672918998141394615013 7430938672312151511490315)
                ·
                  refine ⟨11146408008468227267235473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7430938672312151511490315 11146408008468227267235473)
                  ·
                    refine ⟨8359806006351170450426605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11146408008468227267235473 8359806006351170450426605)
                    ·
                      refine ⟨3134927252381688918909977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8359806006351170450426605 3134927252381688918909977)
                      ·
                        rfl

theorem cell23_6105249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 4, 1, 2, 3].length) (baseStart_6105249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6105249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6105249 prefixEnd_6105249 := by exact prefixLift 6105249
  have htrace : WordTrace (prefixWord ++ tailWord_6105249) baseStart_6105249 baseEnd_6105249 := by
    simpa [prefixWord, tailWord_6105249, baseEnd_6105249] using wordTrace_append hprefix tailTrace_6105249
  have hstable : (prefixWord ++ tailWord_6105249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6105249).length < 2 ^ (prefixWord ++ tailWord_6105249).sum := by decide
  have hdescent : baseEnd_6105249 < baseStart_6105249 := by decide
  rcases family_descends (prefixWord ++ tailWord_6105249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6105252 : List Nat := [2, 3, 1, 2, 4, 1, 1, 9]
def baseStart_6105252 : Nat := 118140960795 + 6105252 * 2 ^ 59
def prefixEnd_6105252 : Nat := 4983230072969 + 3 ^ 40 * 6105252 * 2
def baseEnd_6105252 : Nat := 116108473808283422487869

theorem tailTrace_6105252 : CollatzResearch.WordTrace tailWord_6105252 prefixEnd_6105252 116108473808283422487869 := by
  unfold tailWord_6105252
  simp only [CollatzResearch.WordTrace]
  refine ⟨111338417038861086436799005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148451222718481448582398673 111338417038861086436799005)
  ·
    refine ⟨41751906389572907413799627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111338417038861086436799005 41751906389572907413799627)
    ·
      refine ⟨62627859584359361120699441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41751906389572907413799627 62627859584359361120699441)
      ·
        refine ⟨46970894688269520840524581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62627859584359361120699441 46970894688269520840524581)
        ·
          refine ⟨8807042754050535157598359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46970894688269520840524581 8807042754050535157598359)
          ·
            refine ⟨13210564131075802736397539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8807042754050535157598359 13210564131075802736397539)
            ·
              refine ⟨19815846196613704104596309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13210564131075802736397539 19815846196613704104596309)
              ·
                refine ⟨116108473808283422487869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19815846196613704104596309 116108473808283422487869)
                ·
                  rfl

theorem cell23_6105252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 9].length) (baseStart_6105252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6105252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6105252 prefixEnd_6105252 := by exact prefixLift 6105252
  have htrace : WordTrace (prefixWord ++ tailWord_6105252) baseStart_6105252 baseEnd_6105252 := by
    simpa [prefixWord, tailWord_6105252, baseEnd_6105252] using wordTrace_append hprefix tailTrace_6105252
  have hstable : (prefixWord ++ tailWord_6105252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6105252).length < 2 ^ (prefixWord ++ tailWord_6105252).sum := by decide
  have hdescent : baseEnd_6105252 < baseStart_6105252 := by decide
  rcases family_descends (prefixWord ++ tailWord_6105252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6105269 : List Nat := [1, 3, 3, 4, 1, 2, 9]
def baseStart_6105269 : Nat := 118140960795 + 6105269 * 2 ^ 59
def prefixEnd_6105269 : Nat := 4983230072969 + 3 ^ 40 * 6105269 * 2
def baseEnd_6105269 : Nat := 38702932370305911613085

theorem tailTrace_6105269 : CollatzResearch.WordTrace tailWord_6105269 prefixEnd_6105269 38702932370305911613085 := by
  unfold tailWord_6105269
  simp only [CollatzResearch.WordTrace]
  refine ⟨222677454118660584776966861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148451636079107056517977907 222677454118660584776966861)
  ·
    refine ⟨83504045294497719291362573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 222677454118660584776966861 83504045294497719291362573)
    ·
      refine ⟨31314016985436644734260965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83504045294497719291362573 31314016985436644734260965)
      ·
        refine ⟨5871378184769370887673931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31314016985436644734260965 5871378184769370887673931)
        ·
          refine ⟨8807067277154056331510897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5871378184769370887673931 8807067277154056331510897)
          ·
            refine ⟨6605300457865542248633173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8807067277154056331510897 6605300457865542248633173)
            ·
              refine ⟨38702932370305911613085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6605300457865542248633173 38702932370305911613085)
              ·
                rfl

theorem cell23_6105269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 9].length) (baseStart_6105269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6105269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6105269 prefixEnd_6105269 := by exact prefixLift 6105269
  have htrace : WordTrace (prefixWord ++ tailWord_6105269) baseStart_6105269 baseEnd_6105269 := by
    simpa [prefixWord, tailWord_6105269, baseEnd_6105269] using wordTrace_append hprefix tailTrace_6105269
  have hstable : (prefixWord ++ tailWord_6105269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6105269).length < 2 ^ (prefixWord ++ tailWord_6105269).sum := by decide
  have hdescent : baseEnd_6105269 < baseStart_6105269 := by decide
  rcases family_descends (prefixWord ++ tailWord_6105269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6105275 : List Nat := [1, 1, 1, 1, 1, 2, 5, 2, 2, 2, 5]
def baseStart_6105275 : Nat := 118140960795 + 6105275 * 2 ^ 59
def prefixEnd_6105275 : Nat := 4983230072969 + 3 ^ 40 * 6105275 * 2
def baseEnd_6105275 : Nat := 3134940602878705817184857

theorem tailTrace_6105275 : CollatzResearch.WordTrace tailWord_6105275 prefixEnd_6105275 3134940602878705817184857 := by
  unfold tailWord_6105275
  simp only [CollatzResearch.WordTrace]
  refine ⟨222677672956638847801685279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148451781971092565201123519 222677672956638847801685279)
  ·
    refine ⟨334016509434958271702527919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222677672956638847801685279 334016509434958271702527919)
    ·
      refine ⟨501024764152437407553791879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 334016509434958271702527919 501024764152437407553791879)
      ·
        refine ⟨751537146228656111330687819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 501024764152437407553791879 751537146228656111330687819)
        ·
          refine ⟨1127305719342984166996031729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 751537146228656111330687819 1127305719342984166996031729)
          ·
            refine ⟨845479289507238125247023797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1127305719342984166996031729 845479289507238125247023797)
            ·
              refine ⟨79263683391303574241908481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 845479289507238125247023797 79263683391303574241908481)
              ·
                refine ⟨59447762543477680681431361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79263683391303574241908481 59447762543477680681431361)
                ·
                  refine ⟨44585821907608260511073521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59447762543477680681431361 44585821907608260511073521)
                  ·
                    refine ⟨33439366430706195383305141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44585821907608260511073521 33439366430706195383305141)
                    ·
                      refine ⟨3134940602878705817184857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33439366430706195383305141 3134940602878705817184857)
                      ·
                        rfl

theorem cell23_6105275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 2, 2, 2, 5].length) (baseStart_6105275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6105275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6105275 prefixEnd_6105275 := by exact prefixLift 6105275
  have htrace : WordTrace (prefixWord ++ tailWord_6105275) baseStart_6105275 baseEnd_6105275 := by
    simpa [prefixWord, tailWord_6105275, baseEnd_6105275] using wordTrace_append hprefix tailTrace_6105275
  have hstable : (prefixWord ++ tailWord_6105275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6105275).length < 2 ^ (prefixWord ++ tailWord_6105275).sum := by decide
  have hdescent : baseEnd_6105275 < baseStart_6105275 := by decide
  rcases family_descends (prefixWord ++ tailWord_6105275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6105279 : List Nat := [1, 1, 2, 2, 2, 2, 1, 6, 2, 1, 3]
def baseStart_6105279 : Nat := 118140960795 + 6105279 * 2 ^ 59
def prefixEnd_6105279 : Nat := 4983230072969 + 3 ^ 40 * 6105279 * 2
def baseEnd_6105279 : Nat := 3134942656801323801534839

theorem tailTrace_6105279 : CollatzResearch.WordTrace tailWord_6105279 prefixEnd_6105279 3134942656801323801534839 := by
  unfold tailWord_6105279
  simp only [CollatzResearch.WordTrace]
  refine ⟨222677818848624356484830891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148451879232416237656553927 222677818848624356484830891)
  ·
    refine ⟨334016728272936534727246337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222677818848624356484830891 334016728272936534727246337)
    ·
      refine ⟨250512546204702401045434753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 334016728272936534727246337 250512546204702401045434753)
      ·
        refine ⟨187884409653526800784076065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 250512546204702401045434753 187884409653526800784076065)
        ·
          refine ⟨140913307240145100588057049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187884409653526800784076065 140913307240145100588057049)
          ·
            refine ⟨105684980430108825441042787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140913307240145100588057049 105684980430108825441042787)
            ·
              refine ⟨158527470645163238161564181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105684980430108825441042787 158527470645163238161564181)
              ·
                refine ⟨7430975186492026788823321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 158527470645163238161564181 7430975186492026788823321)
                ·
                  refine ⟨5573231389869020091617491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7430975186492026788823321 5573231389869020091617491)
                  ·
                    refine ⟨8359847084803530137426237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5573231389869020091617491 8359847084803530137426237)
                    ·
                      refine ⟨3134942656801323801534839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8359847084803530137426237 3134942656801323801534839)
                      ·
                        rfl

theorem cell23_6105279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 6, 2, 1, 3].length) (baseStart_6105279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6105279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6105279 prefixEnd_6105279 := by exact prefixLift 6105279
  have htrace : WordTrace (prefixWord ++ tailWord_6105279) baseStart_6105279 baseEnd_6105279 := by
    simpa [prefixWord, tailWord_6105279, baseEnd_6105279] using wordTrace_append hprefix tailTrace_6105279
  have hstable : (prefixWord ++ tailWord_6105279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6105279).length < 2 ^ (prefixWord ++ tailWord_6105279).sum := by decide
  have hdescent : baseEnd_6105279 < baseStart_6105279 := by decide
  rcases family_descends (prefixWord ++ tailWord_6105279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6105280 : List Nat := [2, 1, 1, 2, 5, 2, 3, 2, 1, 2, 2]
def baseStart_6105280 : Nat := 118140960795 + 6105280 * 2 ^ 59
def prefixEnd_6105280 : Nat := 4983230072969 + 3 ^ 40 * 6105280 * 2
def baseEnd_6105280 : Nat := 3134943170281978297622335

theorem tailTrace_6105280 : CollatzResearch.WordTrace tailWord_6105280 prefixEnd_6105280 3134943170281978297622335 := by
  unfold tailWord_6105280
  simp only [CollatzResearch.WordTrace]
  refine ⟨111338927660810366827808647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148451903547747155770411529 111338927660810366827808647)
  ·
    refine ⟨167008391491215550241712971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111338927660810366827808647 167008391491215550241712971)
    ·
      refine ⟨250512587236823325362569457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167008391491215550241712971 250512587236823325362569457)
      ·
        refine ⟨187884440427617494021927093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 250512587236823325362569457 187884440427617494021927093)
        ·
          refine ⟨17614166290089140064555665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 187884440427617494021927093 17614166290089140064555665)
          ·
            refine ⟨13210624717566855048416749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17614166290089140064555665 13210624717566855048416749)
            ·
              refine ⟨4953984269087570643156281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13210624717566855048416749 4953984269087570643156281)
              ·
                refine ⟨3715488201815677982367211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4953984269087570643156281 3715488201815677982367211)
                ·
                  refine ⟨5573232302723516973550817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3715488201815677982367211 5573232302723516973550817)
                  ·
                    refine ⟨4179924227042637730163113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5573232302723516973550817 4179924227042637730163113)
                    ·
                      refine ⟨3134943170281978297622335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4179924227042637730163113 3134943170281978297622335)
                      ·
                        rfl

theorem cell23_6105280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 3, 2, 1, 2, 2].length) (baseStart_6105280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6105280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6105280 prefixEnd_6105280 := by exact prefixLift 6105280
  have htrace : WordTrace (prefixWord ++ tailWord_6105280) baseStart_6105280 baseEnd_6105280 := by
    simpa [prefixWord, tailWord_6105280, baseEnd_6105280] using wordTrace_append hprefix tailTrace_6105280
  have hstable : (prefixWord ++ tailWord_6105280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6105280).length < 2 ^ (prefixWord ++ tailWord_6105280).sum := by decide
  have hdescent : baseEnd_6105280 < baseStart_6105280 := by decide
  rcases family_descends (prefixWord ++ tailWord_6105280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6105295 : List Nat := [1, 1, 2, 1, 1, 3, 4, 1, 1, 8]
def baseStart_6105295 : Nat := 118140960795 + 6105295 * 2 ^ 59
def prefixEnd_6105295 : Nat := 4983230072969 + 3 ^ 40 * 6105295 * 2
def baseEnd_6105295 : Nat := 1044983624163931912978255

theorem tailTrace_6105295 : CollatzResearch.WordTrace tailWord_6105295 prefixEnd_6105295 1044983624163931912978255 := by
  unfold tailWord_6105295
  simp only [CollatzResearch.WordTrace]
  refine ⟨222678402416566391217413339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148452268277710927478275559 222678402416566391217413339)
  ·
    refine ⟨334017603624849586826120009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222678402416566391217413339 334017603624849586826120009)
    ·
      refine ⟨250513202718637190119590007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 334017603624849586826120009 250513202718637190119590007)
      ·
        refine ⟨375769804077955785179385011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250513202718637190119590007 375769804077955785179385011)
        ·
          refine ⟨563654706116933677769077517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 375769804077955785179385011 563654706116933677769077517)
          ·
            refine ⟨211370514793850129163404069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 563654706116933677769077517 211370514793850129163404069)
            ·
              refine ⟨39631971523846899218138263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 211370514793850129163404069 39631971523846899218138263)
              ·
                refine ⟨59447957285770348827207395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39631971523846899218138263 59447957285770348827207395)
                ·
                  refine ⟨89171935928655523240811093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59447957285770348827207395 89171935928655523240811093)
                  ·
                    refine ⟨1044983624163931912978255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 89171935928655523240811093 1044983624163931912978255)
                    ·
                      rfl

theorem cell23_6105295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 1, 1, 8].length) (baseStart_6105295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6105295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6105295 prefixEnd_6105295 := by exact prefixLift 6105295
  have htrace : WordTrace (prefixWord ++ tailWord_6105295) baseStart_6105295 baseEnd_6105295 := by
    simpa [prefixWord, tailWord_6105295, baseEnd_6105295] using wordTrace_append hprefix tailTrace_6105295
  have hstable : (prefixWord ++ tailWord_6105295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6105295).length < 2 ^ (prefixWord ++ tailWord_6105295).sum := by decide
  have hdescent : baseEnd_6105295 < baseStart_6105295 := by decide
  rcases family_descends (prefixWord ++ tailWord_6105295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6105306 : List Nat := [3, 1, 1, 2, 2, 1, 5, 2, 1, 3, 2]
def baseStart_6105306 : Nat := 118140960795 + 6105306 * 2 ^ 59
def prefixEnd_6105306 : Nat := 4983230072969 + 3 ^ 40 * 6105306 * 2
def baseEnd_6105306 : Nat := 3134956520778995195897215

theorem tailTrace_6105306 : CollatzResearch.WordTrace tailWord_6105306 prefixEnd_6105306 3134956520778995195897215 := by
  unfold tailWord_6105306
  simp only [CollatzResearch.WordTrace]
  refine ⟨55669700904881635024015943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148452535746351026730709181 55669700904881635024015943)
  ·
    refine ⟨83504551357322452536023915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55669700904881635024015943 83504551357322452536023915)
    ·
      refine ⟨125256827035983678804035873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83504551357322452536023915 125256827035983678804035873)
      ·
        refine ⟨93942620276987759103026905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125256827035983678804035873 93942620276987759103026905)
        ·
          refine ⟨70456965207740819327270179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93942620276987759103026905 70456965207740819327270179)
          ·
            refine ⟨105685447811611228990905269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70456965207740819327270179 105685447811611228990905269)
            ·
              refine ⟨9908010732338552717897369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 105685447811611228990905269 9908010732338552717897369)
              ·
                refine ⟨7431008049253914538423027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9908010732338552717897369 7431008049253914538423027)
                ·
                  refine ⟨11146512073880871807634541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7431008049253914538423027 11146512073880871807634541)
                  ·
                    refine ⟨4179942027705326927862953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11146512073880871807634541 4179942027705326927862953)
                    ·
                      refine ⟨3134956520778995195897215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4179942027705326927862953 3134956520778995195897215)
                      ·
                        rfl

theorem cell23_6105306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 5, 2, 1, 3, 2].length) (baseStart_6105306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6105306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6105306 prefixEnd_6105306 := by exact prefixLift 6105306
  have htrace : WordTrace (prefixWord ++ tailWord_6105306) baseStart_6105306 baseEnd_6105306 := by
    simpa [prefixWord, tailWord_6105306, baseEnd_6105306] using wordTrace_append hprefix tailTrace_6105306
  have hstable : (prefixWord ++ tailWord_6105306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6105306).length < 2 ^ (prefixWord ++ tailWord_6105306).sum := by decide
  have hdescent : baseEnd_6105306 < baseStart_6105306 := by decide
  rcases family_descends (prefixWord ++ tailWord_6105306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6105322 : List Nat := [3, 1, 3, 1, 1, 2, 1, 3, 2, 1, 5]
def baseStart_6105322 : Nat := 118140960795 + 6105322 * 2 ^ 59
def prefixEnd_6105322 : Nat := 4983230072969 + 3 ^ 40 * 6105322 * 2
def baseEnd_6105322 : Nat := 3134964736469467133297141

theorem tailTrace_6105322 : CollatzResearch.WordTrace tailWord_6105322 prefixEnd_6105322 3134964736469467133297141 := by
  unfold tailWord_6105322
  simp only [CollatzResearch.WordTrace]
  refine ⟨55669846796867143707161555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148452924791645716552430813 55669846796867143707161555)
  ·
    refine ⟨83504770195300715560742333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55669846796867143707161555 83504770195300715560742333)
    ·
      refine ⟨31314288823237768335278375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83504770195300715560742333 31314288823237768335278375)
      ·
        refine ⟨46971433234856652502917563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31314288823237768335278375 46971433234856652502917563)
        ·
          refine ⟨70457149852284978754376345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46971433234856652502917563 70457149852284978754376345)
          ·
            refine ⟨52842862389213734065782259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70457149852284978754376345 52842862389213734065782259)
            ·
              refine ⟨79264293583820601098673389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52842862389213734065782259 79264293583820601098673389)
              ·
                refine ⟨29724110093932725412002521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79264293583820601098673389 29724110093932725412002521)
                ·
                  refine ⟨22293082570449544059001891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29724110093932725412002521 22293082570449544059001891)
                  ·
                    refine ⟨33439623855674316088502837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22293082570449544059001891 33439623855674316088502837)
                    ·
                      refine ⟨3134964736469467133297141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33439623855674316088502837 3134964736469467133297141)
                      ·
                        rfl

theorem cell23_6105322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 3, 2, 1, 5].length) (baseStart_6105322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6105322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6105322 prefixEnd_6105322 := by exact prefixLift 6105322
  have htrace : WordTrace (prefixWord ++ tailWord_6105322) baseStart_6105322 baseEnd_6105322 := by
    simpa [prefixWord, tailWord_6105322, baseEnd_6105322] using wordTrace_append hprefix tailTrace_6105322
  have hstable : (prefixWord ++ tailWord_6105322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6105322).length < 2 ^ (prefixWord ++ tailWord_6105322).sum := by decide
  have hdescent : baseEnd_6105322 < baseStart_6105322 := by decide
  rcases family_descends (prefixWord ++ tailWord_6105322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6105376 : List Nat := [2, 1, 1, 5, 2, 2, 2, 3, 5]
def baseStart_6105376 : Nat := 118140960795 + 6105376 * 2 ^ 59
def prefixEnd_6105376 : Nat := 4983230072969 + 3 ^ 40 * 6105376 * 2
def baseEnd_6105376 : Nat := 348332496047201102446877

theorem tailTrace_6105376 : CollatzResearch.WordTrace tailWord_6105376 prefixEnd_6105376 348332496047201102446877 := by
  unfold tailWord_6105376
  simp only [CollatzResearch.WordTrace]
  refine ⟨111340678364636471025555991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148454237819515294700741321 111340678364636471025555991)
  ·
    refine ⟨167011017546954706538333987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111340678364636471025555991 167011017546954706538333987)
    ·
      refine ⟨250516526320432059807500981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167011017546954706538333987 250516526320432059807500981)
      ·
        refine ⟨23485924342540505606953217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 250516526320432059807500981 23485924342540505606953217)
        ·
          refine ⟨17614443256905379205214913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23485924342540505606953217 17614443256905379205214913)
          ·
            refine ⟨13210832442679034403911185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17614443256905379205214913 13210832442679034403911185)
            ·
              refine ⟨9908124332009275802933389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13210832442679034403911185 9908124332009275802933389)
              ·
                refine ⟨3715546624503478426100021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9908124332009275802933389 3715546624503478426100021)
                ·
                  refine ⟨348332496047201102446877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3715546624503478426100021 348332496047201102446877)
                  ·
                    rfl

theorem cell23_6105376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 2, 3, 5].length) (baseStart_6105376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6105376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6105376 prefixEnd_6105376 := by exact prefixLift 6105376
  have htrace : WordTrace (prefixWord ++ tailWord_6105376) baseStart_6105376 baseEnd_6105376 := by
    simpa [prefixWord, tailWord_6105376, baseEnd_6105376] using wordTrace_append hprefix tailTrace_6105376
  have hstable : (prefixWord ++ tailWord_6105376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6105376).length < 2 ^ (prefixWord ++ tailWord_6105376).sum := by decide
  have hdescent : baseEnd_6105376 < baseStart_6105376 := by decide
  rcases family_descends (prefixWord ++ tailWord_6105376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6105422 : List Nat := [4, 1, 1, 1, 1, 1, 2, 2, 1, 3, 6]
def baseStart_6105422 : Nat := 118140960795 + 6105422 * 2 ^ 59
def prefixEnd_6105422 : Nat := 4983230072969 + 3 ^ 40 * 6105422 * 2
def baseEnd_6105422 : Nat := 3135016084534916742046681

theorem tailTrace_6105422 : CollatzResearch.WordTrace tailWord_6105422 prefixEnd_6105422 3135016084534916742046681 := by
  unfold tailWord_6105422
  simp only [CollatzResearch.WordTrace]
  refine ⟨27835379310888286488410815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148455356324737527938191013 27835379310888286488410815)
  ·
    refine ⟨41753068966332429732616223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27835379310888286488410815 41753068966332429732616223)
    ·
      refine ⟨62629603449498644598924335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41753068966332429732616223 62629603449498644598924335)
      ·
        refine ⟨93944405174247966898386503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62629603449498644598924335 93944405174247966898386503)
        ·
          refine ⟨140916607761371950347579755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93944405174247966898386503 140916607761371950347579755)
          ·
            refine ⟨211374911642057925521369633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140916607761371950347579755 211374911642057925521369633)
            ·
              refine ⟨158531183731543444141027225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 211374911642057925521369633 158531183731543444141027225)
              ·
                refine ⟨118898387798657583105770419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 158531183731543444141027225 118898387798657583105770419)
                ·
                  refine ⟨178347581697986374658655629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 118898387798657583105770419 178347581697986374658655629)
                  ·
                    refine ⟨66880343136744890496995861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 178347581697986374658655629 66880343136744890496995861)
                    ·
                      refine ⟨3135016084534916742046681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66880343136744890496995861 3135016084534916742046681)
                      ·
                        rfl

theorem cell23_6105422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 2, 1, 3, 6].length) (baseStart_6105422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6105422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6105422 prefixEnd_6105422 := by exact prefixLift 6105422
  have htrace : WordTrace (prefixWord ++ tailWord_6105422) baseStart_6105422 baseEnd_6105422 := by
    simpa [prefixWord, tailWord_6105422, baseEnd_6105422] using wordTrace_append hprefix tailTrace_6105422
  have hstable : (prefixWord ++ tailWord_6105422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6105422).length < 2 ^ (prefixWord ++ tailWord_6105422).sum := by decide
  have hdescent : baseEnd_6105422 < baseStart_6105422 := by decide
  rcases family_descends (prefixWord ++ tailWord_6105422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6105476 : List Nat := [2, 3, 2, 1, 1, 2, 2, 1, 5, 1, 3]
def baseStart_6105476 : Nat := 118140960795 + 6105476 * 2 ^ 59
def prefixEnd_6105476 : Nat := 4983230072969 + 3 ^ 40 * 6105476 * 2
def baseEnd_6105476 : Nat := 3135043812490259530771433

theorem tailTrace_6105476 : CollatzResearch.WordTrace tailWord_6105476 prefixEnd_6105476 3135043812490259530771433 := by
  unfold tailWord_6105476
  simp only [CollatzResearch.WordTrace]
  refine ⟨111342502014455329564876141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148456669352607106086501521 111342502014455329564876141)
  ·
    refine ⟨41753438255420748586828553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111342502014455329564876141 41753438255420748586828553)
    ·
      refine ⟨31315078691565561440121415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41753438255420748586828553 31315078691565561440121415)
      ·
        refine ⟨46972618037348342160182123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31315078691565561440121415 46972618037348342160182123)
        ·
          refine ⟨70458927056022513240273185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46972618037348342160182123 70458927056022513240273185)
          ·
            refine ⟨52844195292016884930204889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70458927056022513240273185 52844195292016884930204889)
            ·
              refine ⟨39633146469012663697653667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52844195292016884930204889 39633146469012663697653667)
              ·
                refine ⟨59449719703518995546480501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39633146469012663697653667 59449719703518995546480501)
                ·
                  refine ⟨5573411222204905832482547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59449719703518995546480501 5573411222204905832482547)
                  ·
                    refine ⟨8360116833307358748723821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5573411222204905832482547 8360116833307358748723821)
                    ·
                      refine ⟨3135043812490259530771433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8360116833307358748723821 3135043812490259530771433)
                      ·
                        rfl

theorem cell23_6105476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 1, 5, 1, 3].length) (baseStart_6105476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6105476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6105476 prefixEnd_6105476 := by exact prefixLift 6105476
  have htrace : WordTrace (prefixWord ++ tailWord_6105476) baseStart_6105476 baseEnd_6105476 := by
    simpa [prefixWord, tailWord_6105476, baseEnd_6105476] using wordTrace_append hprefix tailTrace_6105476
  have hstable : (prefixWord ++ tailWord_6105476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6105476).length < 2 ^ (prefixWord ++ tailWord_6105476).sum := by decide
  have hdescent : baseEnd_6105476 < baseStart_6105476 := by decide
  rcases family_descends (prefixWord ++ tailWord_6105476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6105479 : List Nat := [1, 1, 4, 2, 2, 1, 3, 1, 3, 5]
def baseStart_6105479 : Nat := 118140960795 + 6105479 * 2 ^ 59
def prefixEnd_6105479 : Nat := 4983230072969 + 3 ^ 40 * 6105479 * 2
def baseEnd_6105479 : Nat := 1045015117644074339677973

theorem tailTrace_6105479 : CollatzResearch.WordTrace tailWord_6105479 prefixEnd_6105479 1045015117644074339677973 := by
  unfold tailWord_6105479
  simp only [CollatzResearch.WordTrace]
  refine ⟨222685113447899790642111491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148456742298599860428074327 222685113447899790642111491)
  ·
    refine ⟨334027670171849685963167237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222685113447899790642111491 334027670171849685963167237)
    ·
      refine ⟨62630188157221816118093857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 334027670171849685963167237 62630188157221816118093857)
      ·
        refine ⟨46972641117916362088570393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62630188157221816118093857 46972641117916362088570393)
        ·
          refine ⟨35229480838437271566427795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46972641117916362088570393 35229480838437271566427795)
          ·
            refine ⟨52844221257655907349641693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35229480838437271566427795 52844221257655907349641693)
            ·
              refine ⟨19816582971620965256115635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52844221257655907349641693 19816582971620965256115635)
              ·
                refine ⟨29724874457431447884173453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19816582971620965256115635 29724874457431447884173453)
                ·
                  refine ⟨11146827921536792956565045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29724874457431447884173453 11146827921536792956565045)
                  ·
                    refine ⟨1045015117644074339677973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11146827921536792956565045 1045015117644074339677973)
                    ·
                      rfl

theorem cell23_6105479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 1, 3, 5].length) (baseStart_6105479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6105479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6105479 prefixEnd_6105479 := by exact prefixLift 6105479
  have htrace : WordTrace (prefixWord ++ tailWord_6105479) baseStart_6105479 baseEnd_6105479 := by
    simpa [prefixWord, tailWord_6105479, baseEnd_6105479] using wordTrace_append hprefix tailTrace_6105479
  have hstable : (prefixWord ++ tailWord_6105479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6105479).length < 2 ^ (prefixWord ++ tailWord_6105479).sum := by decide
  have hdescent : baseEnd_6105479 < baseStart_6105479 := by decide
  rcases family_descends (prefixWord ++ tailWord_6105479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6105493 : List Nat := [1, 3, 2, 1, 1, 2, 1, 7, 1, 1, 3]
def baseStart_6105493 : Nat := 118140960795 + 6105493 * 2 ^ 59
def prefixEnd_6105493 : Nat := 4983230072969 + 3 ^ 40 * 6105493 * 2
def baseEnd_6105493 : Nat := 3135052541661385964258855

theorem tailTrace_6105493 : CollatzResearch.WordTrace tailWord_6105493 prefixEnd_6105493 3135052541661385964258855 := by
  unfold tailWord_6105493
  simp only [CollatzResearch.WordTrace]
  refine ⟨222685624069849071033121133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148457082713232714022080755 222685624069849071033121133)
  ·
    refine ⟨83507109026193401637420425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 222685624069849071033121133 83507109026193401637420425)
    ·
      refine ⟨62630331769645051228065319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83507109026193401637420425 62630331769645051228065319)
      ·
        refine ⟨93945497654467576842097979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62630331769645051228065319 93945497654467576842097979)
        ·
          refine ⟨140918246481701365263146969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93945497654467576842097979 140918246481701365263146969)
          ·
            refine ⟨105688684861276023947360227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140918246481701365263146969 105688684861276023947360227)
            ·
              refine ⟨158533027291914035921040341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105688684861276023947360227 158533027291914035921040341)
              ·
                refine ⟨3715617827154235216899383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 158533027291914035921040341 3715617827154235216899383)
                ·
                  refine ⟨5573426740731352825349075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3715617827154235216899383 5573426740731352825349075)
                  ·
                    refine ⟨8360140111097029238023613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5573426740731352825349075 8360140111097029238023613)
                    ·
                      refine ⟨3135052541661385964258855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8360140111097029238023613 3135052541661385964258855)
                      ·
                        rfl

theorem cell23_6105493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 7, 1, 1, 3].length) (baseStart_6105493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6105493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6105493 prefixEnd_6105493 := by exact prefixLift 6105493
  have htrace : WordTrace (prefixWord ++ tailWord_6105493) baseStart_6105493 baseEnd_6105493 := by
    simpa [prefixWord, tailWord_6105493, baseEnd_6105493] using wordTrace_append hprefix tailTrace_6105493
  have hstable : (prefixWord ++ tailWord_6105493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6105493).length < 2 ^ (prefixWord ++ tailWord_6105493).sum := by decide
  have hdescent : baseEnd_6105493 < baseStart_6105493 := by decide
  rcases family_descends (prefixWord ++ tailWord_6105493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6105533 : List Nat := [1, 4, 1, 2, 2, 2, 1, 1, 5, 2, 2]
def baseStart_6105533 : Nat := 118140960795 + 6105533 * 2 ^ 59
def prefixEnd_6105533 : Nat := 4983230072969 + 3 ^ 40 * 6105533 * 2
def baseEnd_6105533 : Nat := 3135073080887565807758671

theorem tailTrace_6105533 : CollatzResearch.WordTrace tailWord_6105533 prefixEnd_6105533 3135073080887565807758671 := by
  unfold tailWord_6105533
  simp only [CollatzResearch.WordTrace]
  refine ⟨222687082989704157864577253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148458055326469438576384835 222687082989704157864577253)
  ·
    refine ⟨41753828060569529599608235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 222687082989704157864577253 41753828060569529599608235)
    ·
      refine ⟨62630742090854294399412353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41753828060569529599608235 62630742090854294399412353)
      ·
        refine ⟨46973056568140720799559265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62630742090854294399412353 46973056568140720799559265)
        ·
          refine ⟨35229792426105540599669449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46973056568140720799559265 35229792426105540599669449)
          ·
            refine ⟨26422344319579155449752087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35229792426105540599669449 26422344319579155449752087)
            ·
              refine ⟨39633516479368733174628131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26422344319579155449752087 39633516479368733174628131)
              ·
                refine ⟨59450274719053099761942197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39633516479368733174628131 59450274719053099761942197)
                ·
                  refine ⟨5573463254911228102682081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59450274719053099761942197 5573463254911228102682081)
                  ·
                    refine ⟨4180097441183421077011561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5573463254911228102682081 4180097441183421077011561)
                    ·
                      refine ⟨3135073080887565807758671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4180097441183421077011561 3135073080887565807758671)
                      ·
                        rfl

theorem cell23_6105533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 1, 5, 2, 2].length) (baseStart_6105533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6105533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6105533 prefixEnd_6105533 := by exact prefixLift 6105533
  have htrace : WordTrace (prefixWord ++ tailWord_6105533) baseStart_6105533 baseEnd_6105533 := by
    simpa [prefixWord, tailWord_6105533, baseEnd_6105533] using wordTrace_append hprefix tailTrace_6105533
  have hstable : (prefixWord ++ tailWord_6105533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6105533).length < 2 ^ (prefixWord ++ tailWord_6105533).sum := by decide
  have hdescent : baseEnd_6105533 < baseStart_6105533 := by decide
  rcases family_descends (prefixWord ++ tailWord_6105533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6105536 : List Nat := [2, 1, 1, 2, 3, 1, 1, 6, 1, 2, 3]
def baseStart_6105536 : Nat := 118140960795 + 6105536 * 2 ^ 59
def prefixEnd_6105536 : Nat := 4983230072969 + 3 ^ 40 * 6105536 * 2
def baseEnd_6105536 : Nat := 3135074621329529296021157

theorem tailTrace_6105536 : CollatzResearch.WordTrace tailWord_6105536 prefixEnd_6105536 3135074621329529296021157 := by
  unfold tailWord_6105536
  simp only [CollatzResearch.WordTrace]
  refine ⟨111343596204346644688468231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148458128272462192917957641 111343596204346644688468231)
  ·
    refine ⟨167015394306519967032702347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111343596204346644688468231 167015394306519967032702347)
    ·
      refine ⟨250523091459779950549053521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167015394306519967032702347 250523091459779950549053521)
      ·
        refine ⟨187892318594834962911790141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 250523091459779950549053521 187892318594834962911790141)
        ·
          refine ⟨70459619473063111091921303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 187892318594834962911790141 70459619473063111091921303)
          ·
            refine ⟨105689429209594666637881955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70459619473063111091921303 105689429209594666637881955)
            ·
              refine ⟨158534143814391999956822933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105689429209594666637881955 158534143814391999956822933)
              ·
                refine ⟨7431287991299624997976075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 158534143814391999956822933 7431287991299624997976075)
                ·
                  refine ⟨11146931986949437496964113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7431287991299624997976075 11146931986949437496964113)
                  ·
                    refine ⟨8360198990212078122723085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11146931986949437496964113 8360198990212078122723085)
                    ·
                      refine ⟨3135074621329529296021157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8360198990212078122723085 3135074621329529296021157)
                      ·
                        rfl

theorem cell23_6105536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 6, 1, 2, 3].length) (baseStart_6105536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6105536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6105536 prefixEnd_6105536 := by exact prefixLift 6105536
  have htrace : WordTrace (prefixWord ++ tailWord_6105536) baseStart_6105536 baseEnd_6105536 := by
    simpa [prefixWord, tailWord_6105536, baseEnd_6105536] using wordTrace_append hprefix tailTrace_6105536
  have hstable : (prefixWord ++ tailWord_6105536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6105536).length < 2 ^ (prefixWord ++ tailWord_6105536).sum := by decide
  have hdescent : baseEnd_6105536 < baseStart_6105536 := by decide
  rcases family_descends (prefixWord ++ tailWord_6105536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6105537 : List Nat := [1, 2, 7, 1, 1, 1, 1, 1, 1, 5, 2]
def baseStart_6105537 : Nat := 118140960795 + 6105537 * 2 ^ 59
def prefixEnd_6105537 : Nat := 4983230072969 + 3 ^ 40 * 6105537 * 2
def baseEnd_6105537 : Nat := 3135075134810183792108653

theorem tailTrace_6105537 : CollatzResearch.WordTrace tailWord_6105537 prefixEnd_6105537 3135075134810183792108653 := by
  unfold tailWord_6105537
  simp only [CollatzResearch.WordTrace]
  refine ⟨222687228881689666547722865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148458152587793111031815243 222687228881689666547722865)
  ·
    refine ⟨167015421661267249910792149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222687228881689666547722865 167015421661267249910792149)
    ·
      refine ⟨3914423945185951169784191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 167015421661267249910792149 3914423945185951169784191)
      ·
        refine ⟨5871635917778926754676287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3914423945185951169784191 5871635917778926754676287)
        ·
          refine ⟨8807453876668390132014431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5871635917778926754676287 8807453876668390132014431)
          ·
            refine ⟨13211180815002585198021647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8807453876668390132014431 13211180815002585198021647)
            ·
              refine ⟨19816771222503877797032471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13211180815002585198021647 19816771222503877797032471)
              ·
                refine ⟨29725156833755816695548707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19816771222503877797032471 29725156833755816695548707)
                ·
                  refine ⟨44587735250633725043323061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29725156833755816695548707 44587735250633725043323061)
                  ·
                    refine ⟨4180100179746911722811537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44587735250633725043323061 4180100179746911722811537)
                    ·
                      refine ⟨3135075134810183792108653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4180100179746911722811537 3135075134810183792108653)
                      ·
                        rfl

theorem cell23_6105537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_6105537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6105537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6105537 prefixEnd_6105537 := by exact prefixLift 6105537
  have htrace : WordTrace (prefixWord ++ tailWord_6105537) baseStart_6105537 baseEnd_6105537 := by
    simpa [prefixWord, tailWord_6105537, baseEnd_6105537] using wordTrace_append hprefix tailTrace_6105537
  have hstable : (prefixWord ++ tailWord_6105537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6105537).length < 2 ^ (prefixWord ++ tailWord_6105537).sum := by decide
  have hdescent : baseEnd_6105537 < baseStart_6105537 := by decide
  rcases family_descends (prefixWord ++ tailWord_6105537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6105570 : List Nat := [3, 3, 3, 2, 1, 1, 1, 2, 1, 1, 5]
def baseStart_6105570 : Nat := 118140960795 + 6105570 * 2 ^ 59
def prefixEnd_6105570 : Nat := 4983230072969 + 3 ^ 40 * 6105570 * 2
def baseEnd_6105570 : Nat := 3135092079671782162996001

theorem tailTrace_6105570 : CollatzResearch.WordTrace tailWord_6105570 prefixEnd_6105570 3135092079671782162996001 := by
  unfold tailWord_6105570
  simp only [CollatzResearch.WordTrace]
  refine ⟨55672108122642528295918541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148458954993713408789116109 55672108122642528295918541)
  ·
    refine ⟨20877040545990948110969453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55672108122642528295918541 20877040545990948110969453)
    ·
      refine ⟨7828890204746605541613545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20877040545990948110969453 7828890204746605541613545)
      ·
        refine ⟨5871667653559954156210159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7828890204746605541613545 5871667653559954156210159)
        ·
          refine ⟨8807501480339931234315239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5871667653559954156210159 8807501480339931234315239)
          ·
            refine ⟨13211252220509896851472859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8807501480339931234315239 13211252220509896851472859)
            ·
              refine ⟨19816878330764845277209289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13211252220509896851472859 19816878330764845277209289)
              ·
                refine ⟨14862658748073633957906967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19816878330764845277209289 14862658748073633957906967)
                ·
                  refine ⟨22293988122110450936860451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14862658748073633957906967 22293988122110450936860451)
                  ·
                    refine ⟨33440982183165676405290677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22293988122110450936860451 33440982183165676405290677)
                    ·
                      refine ⟨3135092079671782162996001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33440982183165676405290677 3135092079671782162996001)
                      ·
                        rfl

theorem cell23_6105570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_6105570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6105570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6105570 prefixEnd_6105570 := by exact prefixLift 6105570
  have htrace : WordTrace (prefixWord ++ tailWord_6105570) baseStart_6105570 baseEnd_6105570 := by
    simpa [prefixWord, tailWord_6105570, baseEnd_6105570] using wordTrace_append hprefix tailTrace_6105570
  have hstable : (prefixWord ++ tailWord_6105570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6105570).length < 2 ^ (prefixWord ++ tailWord_6105570).sum := by decide
  have hdescent : baseEnd_6105570 < baseStart_6105570 := by decide
  rcases family_descends (prefixWord ++ tailWord_6105570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6105593 : List Nat := [1, 2, 1, 3, 1, 2, 3, 4, 1, 3, 2]
def baseStart_6105593 : Nat := 118140960795 + 6105593 * 2 ^ 59
def prefixEnd_6105593 : Nat := 4983230072969 + 3 ^ 40 * 6105593 * 2
def baseEnd_6105593 : Nat := 3135103889726835573008395

theorem tailTrace_6105593 : CollatzResearch.WordTrace tailWord_6105593 prefixEnd_6105593 3135103889726835573008395 := by
  unfold tailWord_6105593
  simp only [CollatzResearch.WordTrace]
  refine ⟨222689271369486788111761433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148459514246324525407840955 222689271369486788111761433)
  ·
    refine ⟨167016953527115091083821075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222689271369486788111761433 167016953527115091083821075)
    ·
      refine ⟨250525430290672636625731613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167016953527115091083821075 250525430290672636625731613)
      ·
        refine ⟨93947036359002238734649355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 250525430290672636625731613 93947036359002238734649355)
        ·
          refine ⟨140920554538503358101974033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93947036359002238734649355 140920554538503358101974033)
          ·
            refine ⟨105690415903877518576480525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140920554538503358101974033 105690415903877518576480525)
            ·
              refine ⟨39633905963954069466180197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105690415903877518576480525 39633905963954069466180197)
              ·
                refine ⟨7431357368241388024908787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39633905963954069466180197 7431357368241388024908787)
                ·
                  refine ⟨11147036052362082037363181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7431357368241388024908787 11147036052362082037363181)
                  ·
                    refine ⟨4180138519635780764011193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11147036052362082037363181 4180138519635780764011193)
                    ·
                      refine ⟨3135103889726835573008395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4180138519635780764011193 3135103889726835573008395)
                      ·
                        rfl

theorem cell23_6105593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 4, 1, 3, 2].length) (baseStart_6105593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6105593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6105593 prefixEnd_6105593 := by exact prefixLift 6105593
  have htrace : WordTrace (prefixWord ++ tailWord_6105593) baseStart_6105593 baseEnd_6105593 := by
    simpa [prefixWord, tailWord_6105593, baseEnd_6105593] using wordTrace_append hprefix tailTrace_6105593
  have hstable : (prefixWord ++ tailWord_6105593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6105593).length < 2 ^ (prefixWord ++ tailWord_6105593).sum := by decide
  have hdescent : baseEnd_6105593 < baseStart_6105593 := by decide
  rcases family_descends (prefixWord ++ tailWord_6105593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6105676 : List Nat := [2, 2, 1, 3, 1, 2, 1, 4, 2, 5]
def baseStart_6105676 : Nat := 118140960795 + 6105676 * 2 ^ 59
def prefixEnd_6105676 : Nat := 4983230072969 + 3 ^ 40 * 6105676 * 2
def baseEnd_6105676 : Nat := 1045048836207052916090171

theorem tailTrace_6105676 : CollatzResearch.WordTrace tailWord_6105676 prefixEnd_6105676 1045048836207052916090171 := by
  unfold tailWord_6105676
  simp only [CollatzResearch.WordTrace]
  refine ⟨111346149314093046643516441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148461532418790728858021921 111346149314093046643516441)
  ·
    refine ⟨83509611985569784982637331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111346149314093046643516441 83509611985569784982637331)
    ·
      refine ⟨125264417978354677473955997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83509611985569784982637331 125264417978354677473955997)
      ·
        refine ⟨46974156741883004052733499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125264417978354677473955997 46974156741883004052733499)
        ·
          refine ⟨70461235112824506079100249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46974156741883004052733499 70461235112824506079100249)
          ·
            refine ⟨52845926334618379559325187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70461235112824506079100249 52845926334618379559325187)
            ·
              refine ⟨79268889501927569338987781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52845926334618379559325187 79268889501927569338987781)
              ·
                refine ⟨14862916781611419251060209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 79268889501927569338987781 14862916781611419251060209)
                ·
                  refine ⟨11147187586208564438295157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14862916781611419251060209 11147187586208564438295157)
                  ·
                    refine ⟨1045048836207052916090171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11147187586208564438295157 1045048836207052916090171)
                    ·
                      rfl

theorem cell23_6105676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 4, 2, 5].length) (baseStart_6105676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6105676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6105676 prefixEnd_6105676 := by exact prefixLift 6105676
  have htrace : WordTrace (prefixWord ++ tailWord_6105676) baseStart_6105676 baseEnd_6105676 := by
    simpa [prefixWord, tailWord_6105676, baseEnd_6105676] using wordTrace_append hprefix tailTrace_6105676
  have hstable : (prefixWord ++ tailWord_6105676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6105676).length < 2 ^ (prefixWord ++ tailWord_6105676).sum := by decide
  have hdescent : baseEnd_6105676 < baseStart_6105676 := by decide
  rcases family_descends (prefixWord ++ tailWord_6105676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6105689 : List Nat := [1, 2, 1, 2, 2, 1, 1, 1, 4, 8]
def baseStart_6105689 : Nat := 118140960795 + 6105689 * 2 ^ 59
def prefixEnd_6105689 : Nat := 4983230072969 + 3 ^ 40 * 6105689 * 2
def baseEnd_6105689 : Nat := 1045051061289889065802651

theorem tailTrace_6105689 : CollatzResearch.WordTrace tailWord_6105689 prefixEnd_6105689 1045051061289889065802651 := by
  unfold tailWord_6105689
  simp only [CollatzResearch.WordTrace]
  refine ⟨222692772777138996507256121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148461848518092664338170747 222692772777138996507256121)
  ·
    refine ⟨167019579582854247380442091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222692772777138996507256121 167019579582854247380442091)
    ·
      refine ⟨250529369374281371070663137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167019579582854247380442091 250529369374281371070663137)
      ·
        refine ⟨187897027030711028302997353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 250529369374281371070663137 187897027030711028302997353)
        ·
          refine ⟨140922770273033271227248015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187897027030711028302997353 140922770273033271227248015)
          ·
            refine ⟨211384155409549906840872023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140922770273033271227248015 211384155409549906840872023)
            ·
              refine ⟨317076233114324860261308035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 211384155409549906840872023 317076233114324860261308035)
              ·
                refine ⟨475614349671487290391962053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 317076233114324860261308035 475614349671487290391962053)
                ·
                  refine ⟨89177690563403866948492885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 475614349671487290391962053 89177690563403866948492885)
                  ·
                    refine ⟨1045051061289889065802651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 89177690563403866948492885 1045051061289889065802651)
                    ·
                      rfl

theorem cell23_6105689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 4, 8].length) (baseStart_6105689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6105689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6105689 prefixEnd_6105689 := by exact prefixLift 6105689
  have htrace : WordTrace (prefixWord ++ tailWord_6105689) baseStart_6105689 baseEnd_6105689 := by
    simpa [prefixWord, tailWord_6105689, baseEnd_6105689] using wordTrace_append hprefix tailTrace_6105689
  have hstable : (prefixWord ++ tailWord_6105689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6105689).length < 2 ^ (prefixWord ++ tailWord_6105689).sum := by decide
  have hdescent : baseEnd_6105689 < baseStart_6105689 := by decide
  rcases family_descends (prefixWord ++ tailWord_6105689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6105696 : List Nat := [2, 1, 1, 3, 2, 1, 2, 2, 4, 1, 4]
def baseStart_6105696 : Nat := 118140960795 + 6105696 * 2 ^ 59
def prefixEnd_6105696 : Nat := 4983230072969 + 3 ^ 40 * 6105696 * 2
def baseEnd_6105696 : Nat := 3135156778234248670020421

theorem tailTrace_6105696 : CollatzResearch.WordTrace tailWord_6105696 prefixEnd_6105696 3135156778234248670020421 := by
  unfold tailWord_6105696
  simp only [CollatzResearch.WordTrace]
  refine ⟨111346514044056818351380471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148462018725409091135173961 111346514044056818351380471)
  ·
    refine ⟨167019771066085227527070707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111346514044056818351380471 167019771066085227527070707)
    ·
      refine ⟨250529656599127841290606061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167019771066085227527070707 250529656599127841290606061)
      ·
        refine ⟨93948621224672940483977273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 250529656599127841290606061 93948621224672940483977273)
        ·
          refine ⟨70461465918504705362982955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93948621224672940483977273 70461465918504705362982955)
          ·
            refine ⟨105692198877757058044474433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70461465918504705362982955 105692198877757058044474433)
            ·
              refine ⟨79269149158317793533355825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105692198877757058044474433 79269149158317793533355825)
              ·
                refine ⟨59451861868738345150016869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79269149158317793533355825 59451861868738345150016869)
                ·
                  refine ⟨11147224100388439715628163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59451861868738345150016869 11147224100388439715628163)
                  ·
                    refine ⟨16720836150582659573442245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11147224100388439715628163 16720836150582659573442245)
                    ·
                      refine ⟨3135156778234248670020421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16720836150582659573442245 3135156778234248670020421)
                      ·
                        rfl

theorem cell23_6105696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 2, 4, 1, 4].length) (baseStart_6105696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6105696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6105696 prefixEnd_6105696 := by exact prefixLift 6105696
  have htrace : WordTrace (prefixWord ++ tailWord_6105696) baseStart_6105696 baseEnd_6105696 := by
    simpa [prefixWord, tailWord_6105696, baseEnd_6105696] using wordTrace_append hprefix tailTrace_6105696
  have hstable : (prefixWord ++ tailWord_6105696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6105696).length < 2 ^ (prefixWord ++ tailWord_6105696).sum := by decide
  have hdescent : baseEnd_6105696 < baseStart_6105696 := by decide
  rcases family_descends (prefixWord ++ tailWord_6105696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6105710 : List Nat := [4, 1, 2, 2, 2, 3, 1, 1, 2, 5]
def baseStart_6105710 : Nat := 118140960795 + 6105710 * 2 ^ 59
def prefixEnd_6105710 : Nat := 4983230072969 + 3 ^ 40 * 6105710 * 2
def baseEnd_6105710 : Nat := 1045054655654470538415119

theorem tailTrace_6105710 : CollatzResearch.WordTrace tailWord_6105710 prefixEnd_6105710 1045054655654470538415119 := by
  unfold tailWord_6105710
  simp only [CollatzResearch.WordTrace]
  refine ⟨27836692338757864636721323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148462359140041944729180389 27836692338757864636721323)
  ·
    refine ⟨41755038508136796955081985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27836692338757864636721323 41755038508136796955081985)
    ·
      refine ⟨31316278881102597716311489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41755038508136796955081985 31316278881102597716311489)
      ·
        refine ⟨23487209160826948287233617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31316278881102597716311489 23487209160826948287233617)
        ·
          refine ⟨17615406870620211215425213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23487209160826948287233617 17615406870620211215425213)
          ·
            refine ⟨6605777576482579205784455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17615406870620211215425213 6605777576482579205784455)
            ·
              refine ⟨9908666364723868808676683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6605777576482579205784455 9908666364723868808676683)
              ·
                refine ⟨14862999547085803213015025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9908666364723868808676683 14862999547085803213015025)
                ·
                  refine ⟨11147249660314352409761269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14862999547085803213015025 11147249660314352409761269)
                  ·
                    refine ⟨1045054655654470538415119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11147249660314352409761269 1045054655654470538415119)
                    ·
                      rfl

theorem cell23_6105710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 1, 1, 2, 5].length) (baseStart_6105710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6105710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6105710 prefixEnd_6105710 := by exact prefixLift 6105710
  have htrace : WordTrace (prefixWord ++ tailWord_6105710) baseStart_6105710 baseEnd_6105710 := by
    simpa [prefixWord, tailWord_6105710, baseEnd_6105710] using wordTrace_append hprefix tailTrace_6105710
  have hstable : (prefixWord ++ tailWord_6105710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6105710).length < 2 ^ (prefixWord ++ tailWord_6105710).sum := by decide
  have hdescent : baseEnd_6105710 < baseStart_6105710 := by decide
  rcases family_descends (prefixWord ++ tailWord_6105710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6105753 : List Nat := [1, 2, 1, 2, 1, 2, 7, 1, 6]
def baseStart_6105753 : Nat := 118140960795 + 6105753 * 2 ^ 59
def prefixEnd_6105753 : Nat := 4983230072969 + 3 ^ 40 * 6105753 * 2
def baseEnd_6105753 : Nat := 348354005181283883000851

theorem tailTrace_6105753 : CollatzResearch.WordTrace tailWord_6105753 prefixEnd_6105753 348354005181283883000851 := by
  unfold tailWord_6105753
  simp only [CollatzResearch.WordTrace]
  refine ⟨222695107048907135437585913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148463404699271423625057275 222695107048907135437585913)
  ·
    refine ⟨167021330286680351578189435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222695107048907135437585913 167021330286680351578189435)
    ·
      refine ⟨250531995430020527367284153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167021330286680351578189435 250531995430020527367284153)
      ·
        refine ⟨187898996572515395525463115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 250531995430020527367284153 187898996572515395525463115)
        ·
          refine ⟨281848494858773093288194673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187898996572515395525463115 281848494858773093288194673)
          ·
            refine ⟨211386371144079819966146005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 281848494858773093288194673 211386371144079819966146005)
            ·
              refine ⟨4954368073689370780456547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 211386371144079819966146005 4954368073689370780456547)
              ·
                refine ⟨7431552110534056170684821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4954368073689370780456547 7431552110534056170684821)
                ·
                  refine ⟨348354005181283883000851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7431552110534056170684821 348354005181283883000851)
                  ·
                    rfl

theorem cell23_6105753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 7, 1, 6].length) (baseStart_6105753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6105753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6105753 prefixEnd_6105753 := by exact prefixLift 6105753
  have htrace : WordTrace (prefixWord ++ tailWord_6105753) baseStart_6105753 baseEnd_6105753 := by
    simpa [prefixWord, tailWord_6105753, baseEnd_6105753] using wordTrace_append hprefix tailTrace_6105753
  have hstable : (prefixWord ++ tailWord_6105753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6105753).length < 2 ^ (prefixWord ++ tailWord_6105753).sum := by decide
  have hdescent : baseEnd_6105753 < baseStart_6105753 := by decide
  rcases family_descends (prefixWord ++ tailWord_6105753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6105763 : List Nat := [1, 1, 1, 4, 1, 1, 2, 3, 5, 1, 3]
def baseStart_6105763 : Nat := 118140960795 + 6105763 * 2 ^ 59
def prefixEnd_6105763 : Nat := 4983230072969 + 3 ^ 40 * 6105763 * 2
def baseEnd_6105763 : Nat := 3135191181438099907882613

theorem tailTrace_6105763 : CollatzResearch.WordTrace tailWord_6105763 prefixEnd_6105763 3135191181438099907882613 := by
  unfold tailWord_6105763
  simp only [CollatzResearch.WordTrace]
  refine ⟨222695471778870907145449943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148463647852580604763633295 222695471778870907145449943)
  ·
    refine ⟨334043207668306360718174915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222695471778870907145449943 334043207668306360718174915)
    ·
      refine ⟨501064811502459541077262373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 334043207668306360718174915 501064811502459541077262373)
      ·
        refine ⟨93949652156711163951986695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 501064811502459541077262373 93949652156711163951986695)
        ·
          refine ⟨140924478235066745927980043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93949652156711163951986695 140924478235066745927980043)
          ·
            refine ⟨211386717352600118891970065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140924478235066745927980043 211386717352600118891970065)
            ·
              refine ⟨158540038014450089168977549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 211386717352600118891970065 158540038014450089168977549)
              ·
                refine ⟨59452514255418783438366581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 158540038014450089168977549 59452514255418783438366581)
                ·
                  refine ⟨5573673211445510947346867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59452514255418783438366581 5573673211445510947346867)
                  ·
                    refine ⟨8360509817168266421020301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5573673211445510947346867 8360509817168266421020301)
                    ·
                      refine ⟨3135191181438099907882613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8360509817168266421020301 3135191181438099907882613)
                      ·
                        rfl

theorem cell23_6105763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 3, 5, 1, 3].length) (baseStart_6105763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6105763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6105763 prefixEnd_6105763 := by exact prefixLift 6105763
  have htrace : WordTrace (prefixWord ++ tailWord_6105763) baseStart_6105763 baseEnd_6105763 := by
    simpa [prefixWord, tailWord_6105763, baseEnd_6105763] using wordTrace_append hprefix tailTrace_6105763
  have hstable : (prefixWord ++ tailWord_6105763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6105763).length < 2 ^ (prefixWord ++ tailWord_6105763).sum := by decide
  have hdescent : baseEnd_6105763 < baseStart_6105763 := by decide
  rcases family_descends (prefixWord ++ tailWord_6105763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6105774 : List Nat := [4, 1, 4, 1, 1, 1, 3, 3, 1, 4]
def baseStart_6105774 : Nat := 118140960795 + 6105774 * 2 ^ 59
def prefixEnd_6105774 : Nat := 4983230072969 + 3 ^ 40 * 6105774 * 2
def baseEnd_6105774 : Nat := 1045065609908433121615021

theorem tailTrace_6105774 : CollatzResearch.WordTrace tailWord_6105774 prefixEnd_6105774 1045065609908433121615021 := by
  unfold tailWord_6105774
  simp only [CollatzResearch.WordTrace]
  refine ⟨27836984122728882003012547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148463915321220704016066917 27836984122728882003012547)
  ·
    refine ⟨41755476184093323004518821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27836984122728882003012547 41755476184093323004518821)
    ·
      refine ⟨7829151784517498063347279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41755476184093323004518821 7829151784517498063347279)
      ·
        refine ⟨11743727676776247095020919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7829151784517498063347279 11743727676776247095020919)
        ·
          refine ⟨17615591515164370642531379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11743727676776247095020919 17615591515164370642531379)
          ·
            refine ⟨26423387272746555963797069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17615591515164370642531379 26423387272746555963797069)
            ·
              refine ⟨9908770227279958486423901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26423387272746555963797069 9908770227279958486423901)
              ·
                refine ⟨3715788835229984432408963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9908770227279958486423901 3715788835229984432408963)
                ·
                  refine ⟨5573683252844976648613445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3715788835229984432408963 5573683252844976648613445)
                  ·
                    refine ⟨1045065609908433121615021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5573683252844976648613445 1045065609908433121615021)
                    ·
                      rfl

theorem cell23_6105774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_6105774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6105774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6105774 prefixEnd_6105774 := by exact prefixLift 6105774
  have htrace : WordTrace (prefixWord ++ tailWord_6105774) baseStart_6105774 baseEnd_6105774 := by
    simpa [prefixWord, tailWord_6105774, baseEnd_6105774] using wordTrace_append hprefix tailTrace_6105774
  have hstable : (prefixWord ++ tailWord_6105774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6105774).length < 2 ^ (prefixWord ++ tailWord_6105774).sum := by decide
  have hdescent : baseEnd_6105774 < baseStart_6105774 := by decide
  rcases family_descends (prefixWord ++ tailWord_6105774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6105837 : List Nat := [1, 5, 1, 2, 1, 1, 5, 1, 1, 1, 4]
def baseStart_6105837 : Nat := 118140960795 + 6105837 * 2 ^ 59
def prefixEnd_6105837 : Nat := 4983230072969 + 3 ^ 40 * 6105837 * 2
def baseEnd_6105837 : Nat := 3135229179006532618357273

theorem tailTrace_6105837 : CollatzResearch.WordTrace tailWord_6105837 prefixEnd_6105837 3135229179006532618357273 := by
  unfold tailWord_6105837
  simp only [CollatzResearch.WordTrace]
  refine ⟨222698170780602817783643765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148465447187068545189095843 222698170780602817783643765)
  ·
    refine ⟨20877953510681514167216603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 222698170780602817783643765 20877953510681514167216603)
    ·
      refine ⟨31316930266022271250824905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20877953510681514167216603 31316930266022271250824905)
      ·
        refine ⟨23487697699516703438118679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31316930266022271250824905 23487697699516703438118679)
        ·
          refine ⟨35231546549275055157178019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23487697699516703438118679 35231546549275055157178019)
          ·
            refine ⟨52847319823912582735767029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35231546549275055157178019 52847319823912582735767029)
            ·
              refine ⟨4954436233491804631478159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52847319823912582735767029 4954436233491804631478159)
              ·
                refine ⟨7431654350237706947217239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4954436233491804631478159 7431654350237706947217239)
                ·
                  refine ⟨11147481525356560420825859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7431654350237706947217239 11147481525356560420825859)
                  ·
                    refine ⟨16721222288034840631238789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11147481525356560420825859 16721222288034840631238789)
                    ·
                      refine ⟨3135229179006532618357273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16721222288034840631238789 3135229179006532618357273)
                      ·
                        rfl

theorem cell23_6105837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 5, 1, 1, 1, 4].length) (baseStart_6105837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6105837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6105837 prefixEnd_6105837 := by exact prefixLift 6105837
  have htrace : WordTrace (prefixWord ++ tailWord_6105837) baseStart_6105837 baseEnd_6105837 := by
    simpa [prefixWord, tailWord_6105837, baseEnd_6105837] using wordTrace_append hprefix tailTrace_6105837
  have hstable : (prefixWord ++ tailWord_6105837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6105837).length < 2 ^ (prefixWord ++ tailWord_6105837).sum := by decide
  have hdescent : baseEnd_6105837 < baseStart_6105837 := by decide
  rcases family_descends (prefixWord ++ tailWord_6105837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6105853 : List Nat := [1, 4, 1, 1, 1, 1, 3, 2, 3, 3, 3]
def baseStart_6105853 : Nat := 118140960795 + 6105853 * 2 ^ 59
def prefixEnd_6105853 : Nat := 4983230072969 + 3 ^ 40 * 6105853 * 2
def baseEnd_6105853 : Nat := 3135237394697004555757199

theorem tailTrace_6105853 : CollatzResearch.WordTrace tailWord_6105853 prefixEnd_6105853 3135237394697004555757199 := by
  unfold tailWord_6105853
  simp only [CollatzResearch.WordTrace]
  refine ⟨222698754348544852516226213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148465836232363235010817475 222698754348544852516226213)
  ·
    refine ⟨41756016440352159846792415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 222698754348544852516226213 41756016440352159846792415)
    ·
      refine ⟨62634024660528239770188623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41756016440352159846792415 62634024660528239770188623)
      ·
        refine ⟨93951036990792359655282935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62634024660528239770188623 93951036990792359655282935)
        ·
          refine ⟨140926555486188539482924403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93951036990792359655282935 140926555486188539482924403)
          ·
            refine ⟨211389833229282809224386605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140926555486188539482924403 211389833229282809224386605)
            ·
              refine ⟨79271187460981053459144977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 211389833229282809224386605 79271187460981053459144977)
              ·
                refine ⟨59453390595735790094358733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79271187460981053459144977 59453390595735790094358733)
                ·
                  refine ⟨22295021473400921285384525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59453390595735790094358733 22295021473400921285384525)
                  ·
                    refine ⟨8360633052525345482019197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22295021473400921285384525 8360633052525345482019197)
                    ·
                      refine ⟨3135237394697004555757199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8360633052525345482019197 3135237394697004555757199)
                      ·
                        rfl

theorem cell23_6105853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 2, 3, 3, 3].length) (baseStart_6105853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6105853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6105853 prefixEnd_6105853 := by exact prefixLift 6105853
  have htrace : WordTrace (prefixWord ++ tailWord_6105853) baseStart_6105853 baseEnd_6105853 := by
    simpa [prefixWord, tailWord_6105853, baseEnd_6105853] using wordTrace_append hprefix tailTrace_6105853
  have hstable : (prefixWord ++ tailWord_6105853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6105853).length < 2 ^ (prefixWord ++ tailWord_6105853).sum := by decide
  have hdescent : baseEnd_6105853 < baseStart_6105853 := by decide
  rcases family_descends (prefixWord ++ tailWord_6105853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6105870 : List Nat := [4, 1, 1, 2, 1, 1, 1, 2, 6, 1, 3]
def baseStart_6105870 : Nat := 118140960795 + 6105870 * 2 ^ 59
def prefixEnd_6105870 : Nat := 4983230072969 + 3 ^ 40 * 6105870 * 2
def baseEnd_6105870 : Nat := 3135246123868130989244621

theorem tailTrace_6105870 : CollatzResearch.WordTrace tailWord_6105870 prefixEnd_6105870 3135246123868130989244621 := by
  unfold tailWord_6105870
  simp only [CollatzResearch.WordTrace]
  refine ⟨27837421798685408052449383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148466249592988842946396709 27837421798685408052449383)
  ·
    refine ⟨41756132698028112078674075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27837421798685408052449383 41756132698028112078674075)
    ·
      refine ⟨62634199047042168118011113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41756132698028112078674075 62634199047042168118011113)
      ·
        refine ⟨46975649285281626088508335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62634199047042168118011113 46975649285281626088508335)
        ·
          refine ⟨70463473927922439132762503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46975649285281626088508335 70463473927922439132762503)
          ·
            refine ⟨105695210891883658699143755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70463473927922439132762503 105695210891883658699143755)
            ·
              refine ⟨158542816337825488048715633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105695210891883658699143755 158542816337825488048715633)
              ·
                refine ⟨118907112253369116036536725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 158542816337825488048715633 118907112253369116036536725)
                ·
                  refine ⟨5573770886876677314212659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 118907112253369116036536725 5573770886876677314212659)
                  ·
                    refine ⟨8360656330315015971318989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5573770886876677314212659 8360656330315015971318989)
                    ·
                      refine ⟨3135246123868130989244621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8360656330315015971318989 3135246123868130989244621)
                      ·
                        rfl

theorem cell23_6105870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 6, 1, 3].length) (baseStart_6105870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6105870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6105870 prefixEnd_6105870 := by exact prefixLift 6105870
  have htrace : WordTrace (prefixWord ++ tailWord_6105870) baseStart_6105870 baseEnd_6105870 := by
    simpa [prefixWord, tailWord_6105870, baseEnd_6105870] using wordTrace_append hprefix tailTrace_6105870
  have hstable : (prefixWord ++ tailWord_6105870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6105870).length < 2 ^ (prefixWord ++ tailWord_6105870).sum := by decide
  have hdescent : baseEnd_6105870 < baseStart_6105870 := by decide
  rcases family_descends (prefixWord ++ tailWord_6105870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6105921 : List Nat := [1, 2, 5, 3, 2, 1, 1, 1, 1, 3, 3]
def baseStart_6105921 : Nat := 118140960795 + 6105921 * 2 ^ 59
def prefixEnd_6105921 : Nat := 4983230072969 + 3 ^ 40 * 6105921 * 2
def baseEnd_6105921 : Nat := 3135272311381510289706887

theorem tailTrace_6105921 : CollatzResearch.WordTrace tailWord_6105921 prefixEnd_6105921 3135272311381510289706887 := by
  unfold tailWord_6105921
  simp only [CollatzResearch.WordTrace]
  refine ⟨222701234512298500129701617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148467489674865666753134411 222701234512298500129701617)
  ·
    refine ⟨167025925884223875097276213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222701234512298500129701617 167025925884223875097276213)
    ·
      refine ⟨15658680551645988290369645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 167025925884223875097276213 15658680551645988290369645)
      ·
        refine ⟨5872005206867245608888617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15658680551645988290369645 5872005206867245608888617)
        ·
          refine ⟨4404003905150434206666463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5872005206867245608888617 4404003905150434206666463)
          ·
            refine ⟨6606005857725651309999695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4404003905150434206666463 6606005857725651309999695)
            ·
              refine ⟨9909008786588476964999543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6606005857725651309999695 9909008786588476964999543)
              ·
                refine ⟨14863513179882715447499315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9909008786588476964999543 14863513179882715447499315)
                ·
                  refine ⟨22295269769824073171248973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14863513179882715447499315 22295269769824073171248973)
                  ·
                    refine ⟨8360726163684027439218365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22295269769824073171248973 8360726163684027439218365)
                    ·
                      refine ⟨3135272311381510289706887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8360726163684027439218365 3135272311381510289706887)
                      ·
                        rfl

theorem cell23_6105921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_6105921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6105921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6105921 prefixEnd_6105921 := by exact prefixLift 6105921
  have htrace : WordTrace (prefixWord ++ tailWord_6105921) baseStart_6105921 baseEnd_6105921 := by
    simpa [prefixWord, tailWord_6105921, baseEnd_6105921] using wordTrace_append hprefix tailTrace_6105921
  have hstable : (prefixWord ++ tailWord_6105921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6105921).length < 2 ^ (prefixWord ++ tailWord_6105921).sum := by decide
  have hdescent : baseEnd_6105921 < baseStart_6105921 := by decide
  rcases family_descends (prefixWord ++ tailWord_6105921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6105923 : List Nat := [1, 1, 1, 3, 1, 4, 1, 3, 2, 2, 4]
def baseStart_6105923 : Nat := 118140960795 + 6105923 * 2 ^ 59
def prefixEnd_6105923 : Nat := 4983230072969 + 3 ^ 40 * 6105923 * 2
def baseEnd_6105923 : Nat := 3135273338342819281881877

theorem tailTrace_6105923 : CollatzResearch.WordTrace tailWord_6105923 prefixEnd_6105923 3135273338342819281881877 := by
  unfold tailWord_6105923
  simp only [CollatzResearch.WordTrace]
  refine ⟨222701307458291254471274423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148467538305527502980849615 222701307458291254471274423)
  ·
    refine ⟨334051961187436881706911635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222701307458291254471274423 334051961187436881706911635)
    ·
      refine ⟨501077941781155322560367453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 334051961187436881706911635 501077941781155322560367453)
      ·
        refine ⟨187904228167933245960137795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 501077941781155322560367453 187904228167933245960137795)
        ·
          refine ⟨281856342251899868940206693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187904228167933245960137795 281856342251899868940206693)
          ·
            refine ⟨52848064172231225426288755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 281856342251899868940206693 52848064172231225426288755)
            ·
              refine ⟨79272096258346838139433133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52848064172231225426288755 79272096258346838139433133)
              ·
                refine ⟨29727036096880064302287425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79272096258346838139433133 29727036096880064302287425)
                ·
                  refine ⟨22295277072660048226715569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29727036096880064302287425 22295277072660048226715569)
                  ·
                    refine ⟨16721457804495036170036677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22295277072660048226715569 16721457804495036170036677)
                    ·
                      refine ⟨3135273338342819281881877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16721457804495036170036677 3135273338342819281881877)
                      ·
                        rfl

theorem cell23_6105923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 3, 2, 2, 4].length) (baseStart_6105923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6105923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6105923 prefixEnd_6105923 := by exact prefixLift 6105923
  have htrace : WordTrace (prefixWord ++ tailWord_6105923) baseStart_6105923 baseEnd_6105923 := by
    simpa [prefixWord, tailWord_6105923, baseEnd_6105923] using wordTrace_append hprefix tailTrace_6105923
  have hstable : (prefixWord ++ tailWord_6105923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6105923).length < 2 ^ (prefixWord ++ tailWord_6105923).sum := by decide
  have hdescent : baseEnd_6105923 < baseStart_6105923 := by decide
  rcases family_descends (prefixWord ++ tailWord_6105923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6105963 : List Nat := [1, 1, 1, 1, 2, 2, 5, 1, 4, 5]
def baseStart_6105963 : Nat := 118140960795 + 6105963 * 2 ^ 59
def prefixEnd_6105963 : Nat := 4983230072969 + 3 ^ 40 * 6105963 * 2
def baseEnd_6105963 : Nat := 1045097959189666375127231

theorem tailTrace_6105963 : CollatzResearch.WordTrace tailWord_6105963 prefixEnd_6105963 1045097959189666375127231 := by
  unfold tailWord_6105963
  simp only [CollatzResearch.WordTrace]
  refine ⟨222702766378146341302730543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148468510918764227535153695 222702766378146341302730543)
  ·
    refine ⟨334054149567219511954095815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222702766378146341302730543 334054149567219511954095815)
    ·
      refine ⟨501081224350829267931143723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 334054149567219511954095815 501081224350829267931143723)
      ·
        refine ⟨751621836526243901896715585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 501081224350829267931143723 751621836526243901896715585)
        ·
          refine ⟨563716377394682926422536689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 751621836526243901896715585 563716377394682926422536689)
          ·
            refine ⟨422787283046012194816902517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 563716377394682926422536689 422787283046012194816902517)
            ·
              refine ⟨39636307785563643264084611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 422787283046012194816902517 39636307785563643264084611)
              ·
                refine ⟨59454461678345464896126917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39636307785563643264084611 59454461678345464896126917)
                ·
                  refine ⟨11147711564689774668023797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59454461678345464896126917 11147711564689774668023797)
                  ·
                    refine ⟨1045097959189666375127231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11147711564689774668023797 1045097959189666375127231)
                    ·
                      rfl

theorem cell23_6105963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 1, 4, 5].length) (baseStart_6105963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6105963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6105963 prefixEnd_6105963 := by exact prefixLift 6105963
  have htrace : WordTrace (prefixWord ++ tailWord_6105963) baseStart_6105963 baseEnd_6105963 := by
    simpa [prefixWord, tailWord_6105963, baseEnd_6105963] using wordTrace_append hprefix tailTrace_6105963
  have hstable : (prefixWord ++ tailWord_6105963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6105963).length < 2 ^ (prefixWord ++ tailWord_6105963).sum := by decide
  have hdescent : baseEnd_6105963 < baseStart_6105963 := by decide
  rcases family_descends (prefixWord ++ tailWord_6105963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6105983 : List Nat := [1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 4]
def baseStart_6105983 : Nat := 118140960795 + 6105983 * 2 ^ 59
def prefixEnd_6105983 : Nat := 4983230072969 + 3 ^ 40 * 6105983 * 2
def baseEnd_6105983 : Nat := 3135304147182089047131601

theorem tailTrace_6105983 : CollatzResearch.WordTrace tailWord_6105983 prefixEnd_6105983 3135304147182089047131601 := by
  unfold tailWord_6105983
  simp only [CollatzResearch.WordTrace]
  refine ⟨222703495838073884718458603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148468997225382589812305735 222703495838073884718458603)
  ·
    refine ⟨334055243757110827077687905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222703495838073884718458603 334055243757110827077687905)
    ·
      refine ⟨250541432817833120308265929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 334055243757110827077687905 250541432817833120308265929)
      ·
        refine ⟨187906074613374840231199447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 250541432817833120308265929 187906074613374840231199447)
        ·
          refine ⟨281859111920062260346799171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187906074613374840231199447 281859111920062260346799171)
          ·
            refine ⟨422788667880093390520198757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 281859111920062260346799171 422788667880093390520198757)
            ·
              refine ⟨79272875227517510722537267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 422788667880093390520198757 79272875227517510722537267)
              ·
                refine ⟨118909312841276266083805901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79272875227517510722537267 118909312841276266083805901)
                ·
                  refine ⟨44590992315478599781427213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 118909312841276266083805901 44590992315478599781427213)
                  ·
                    refine ⟨16721622118304474918035205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44590992315478599781427213 16721622118304474918035205)
                    ·
                      refine ⟨3135304147182089047131601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16721622118304474918035205 3135304147182089047131601)
                      ·
                        rfl

theorem cell23_6105983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 4].length) (baseStart_6105983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6105983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6105983 prefixEnd_6105983 := by exact prefixLift 6105983
  have htrace : WordTrace (prefixWord ++ tailWord_6105983) baseStart_6105983 baseEnd_6105983 := by
    simpa [prefixWord, tailWord_6105983, baseEnd_6105983] using wordTrace_append hprefix tailTrace_6105983
  have hstable : (prefixWord ++ tailWord_6105983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6105983).length < 2 ^ (prefixWord ++ tailWord_6105983).sum := by decide
  have hdescent : baseEnd_6105983 < baseStart_6105983 := by decide
  rcases family_descends (prefixWord ++ tailWord_6105983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6106017 : List Nat := [1, 2, 3, 4, 1, 1, 2, 2, 2, 1, 4]
def baseStart_6106017 : Nat := 118140960795 + 6106017 * 2 ^ 59
def prefixEnd_6106017 : Nat := 4983230072969 + 3 ^ 40 * 6106017 * 2
def baseEnd_6106017 : Nat := 3135321605524341914106445

theorem tailTrace_6106017 : CollatzResearch.WordTrace tailWord_6106017 prefixEnd_6106017 3135321605524341914106445 := by
  unfold tailWord_6106017
  simp only [CollatzResearch.WordTrace]
  refine ⟨222704735919950708525196305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148469823946633805683464203 222704735919950708525196305)
  ·
    refine ⟨167028551939963031393897229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222704735919950708525196305 167028551939963031393897229)
    ·
      refine ⟨62635706977486136772711461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167028551939963031393897229 62635706977486136772711461)
      ·
        refine ⟨11744195058278650644883399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62635706977486136772711461 11744195058278650644883399)
        ·
          refine ⟨17616292587417975967325099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11744195058278650644883399 17616292587417975967325099)
          ·
            refine ⟨26424438881126963950987649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17616292587417975967325099 26424438881126963950987649)
            ·
              refine ⟨19818329160845222963240737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26424438881126963950987649 19818329160845222963240737)
              ·
                refine ⟨14863746870633917222430553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19818329160845222963240737 14863746870633917222430553)
                ·
                  refine ⟨11147810152975437916822915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14863746870633917222430553 11147810152975437916822915)
                  ·
                    refine ⟨16721715229463156875234373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11147810152975437916822915 16721715229463156875234373)
                    ·
                      refine ⟨3135321605524341914106445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16721715229463156875234373 3135321605524341914106445)
                      ·
                        rfl

theorem cell23_6106017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_6106017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6106017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6106017 prefixEnd_6106017 := by exact prefixLift 6106017
  have htrace : WordTrace (prefixWord ++ tailWord_6106017) baseStart_6106017 baseEnd_6106017 := by
    simpa [prefixWord, tailWord_6106017, baseEnd_6106017] using wordTrace_append hprefix tailTrace_6106017
  have hstable : (prefixWord ++ tailWord_6106017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6106017).length < 2 ^ (prefixWord ++ tailWord_6106017).sum := by decide
  have hdescent : baseEnd_6106017 < baseStart_6106017 := by decide
  rcases family_descends (prefixWord ++ tailWord_6106017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6106027 : List Nat := [1, 1, 1, 1, 2, 1, 1, 10, 1, 4]
def baseStart_6106027 : Nat := 118140960795 + 6106027 * 2 ^ 59
def prefixEnd_6106027 : Nat := 4983230072969 + 3 ^ 40 * 6106027 * 2
def baseEnd_6106027 : Nat := 1045108913443628958327133

theorem tailTrace_6106027 : CollatzResearch.WordTrace tailWord_6106027 prefixEnd_6106027 1045108913443628958327133 := by
  unfold tailWord_6106027
  simp only [CollatzResearch.WordTrace]
  refine ⟨222705100649914480233060335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148470067099942986822040223 222705100649914480233060335)
  ·
    refine ⟨334057650974871720349590503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222705100649914480233060335 334057650974871720349590503)
    ·
      refine ⟨501086476462307580524385755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 334057650974871720349590503 501086476462307580524385755)
      ·
        refine ⟨751629714693461370786578633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 501086476462307580524385755 751629714693461370786578633)
        ·
          refine ⟨563722286020096028089933975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 751629714693461370786578633 563722286020096028089933975)
          ·
            refine ⟨845583429030144042134900963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 563722286020096028089933975 845583429030144042134900963)
            ·
              refine ⟨1268375143545216063202351445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 845583429030144042134900963 1268375143545216063202351445)
              ·
                refine ⟨3715942803355125185163139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 1268375143545216063202351445 3715942803355125185163139)
                ·
                  refine ⟨5573914205032687777744709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3715942803355125185163139 5573914205032687777744709)
                  ·
                    refine ⟨1045108913443628958327133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5573914205032687777744709 1045108913443628958327133)
                    ·
                      rfl

theorem cell23_6106027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 10, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 10, 1, 4].length) (baseStart_6106027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6106027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6106027 prefixEnd_6106027 := by exact prefixLift 6106027
  have htrace : WordTrace (prefixWord ++ tailWord_6106027) baseStart_6106027 baseEnd_6106027 := by
    simpa [prefixWord, tailWord_6106027, baseEnd_6106027] using wordTrace_append hprefix tailTrace_6106027
  have hstable : (prefixWord ++ tailWord_6106027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6106027).length < 2 ^ (prefixWord ++ tailWord_6106027).sum := by decide
  have hdescent : baseEnd_6106027 < baseStart_6106027 := by decide
  rcases family_descends (prefixWord ++ tailWord_6106027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6106040 : List Nat := [2, 1, 2, 1, 2, 4, 2, 3, 6]
def baseStart_6106040 : Nat := 118140960795 + 6106040 * 2 ^ 59
def prefixEnd_6106040 : Nat := 4983230072969 + 3 ^ 40 * 6106040 * 2
def baseEnd_6106040 : Nat := 348370379508821702679871

theorem tailTrace_6106040 : CollatzResearch.WordTrace tailWord_6106040 prefixEnd_6106040 348370379508821702679871 := by
  unfold tailWord_6106040
  simp only [CollatzResearch.WordTrace]
  refine ⟨111352787399433691726641787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148470383199244922302189049 111352787399433691726641787)
  ·
    refine ⟨167029181099150537589962681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111352787399433691726641787 167029181099150537589962681)
    ·
      refine ⟨125271885824362903192472011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167029181099150537589962681 125271885824362903192472011)
      ·
        refine ⟨187907828736544354788708017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125271885824362903192472011 187907828736544354788708017)
        ·
          refine ⟨140930871552408266091531013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187907828736544354788708017 140930871552408266091531013)
          ·
            refine ⟨26424538416076549892162065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 140930871552408266091531013 26424538416076549892162065)
            ·
              refine ⟨19818403812057412419121549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26424538416076549892162065 19818403812057412419121549)
              ·
                refine ⟨7431901429521529657170581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19818403812057412419121549 7431901429521529657170581)
                ·
                  refine ⟨348370379508821702679871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7431901429521529657170581 348370379508821702679871)
                  ·
                    rfl

theorem cell23_6106040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 3, 6].length) (baseStart_6106040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6106040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6106040 prefixEnd_6106040 := by exact prefixLift 6106040
  have htrace : WordTrace (prefixWord ++ tailWord_6106040) baseStart_6106040 baseEnd_6106040 := by
    simpa [prefixWord, tailWord_6106040, baseEnd_6106040] using wordTrace_append hprefix tailTrace_6106040
  have hstable : (prefixWord ++ tailWord_6106040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6106040).length < 2 ^ (prefixWord ++ tailWord_6106040).sum := by decide
  have hdescent : baseEnd_6106040 < baseStart_6106040 := by decide
  rcases family_descends (prefixWord ++ tailWord_6106040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6106151 : List Nat := [1, 1, 7, 1, 1, 2, 1, 3, 2, 4]
def baseStart_6106151 : Nat := 118140960795 + 6106151 * 2 ^ 59
def prefixEnd_6106151 : Nat := 4983230072969 + 3 ^ 40 * 6106151 * 2
def baseEnd_6106151 : Nat := 1045130137310681463276943

theorem tailTrace_6106151 : CollatzResearch.WordTrace tailWord_6106151 prefixEnd_6106151 1045130137310681463276943 := by
  unfold tailWord_6106151
  simp only [CollatzResearch.WordTrace]
  refine ⟨222709623301465249410574307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148473082200976832940382871 222709623301465249410574307)
  ·
    refine ⟨334064434952197874115861461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222709623301465249410574307 334064434952197874115861461)
    ·
      refine ⟨7829635194192137674590503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 334064434952197874115861461 7829635194192137674590503)
      ·
        refine ⟨11744452791288206511885755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7829635194192137674590503 11744452791288206511885755)
        ·
          refine ⟨17616679186932309767828633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11744452791288206511885755 17616679186932309767828633)
          ·
            refine ⟨13212509390199232325871475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17616679186932309767828633 13212509390199232325871475)
            ·
              refine ⟨19818764085298848488807213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13212509390199232325871475 19818764085298848488807213)
              ·
                refine ⟨7432036531987068183302705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19818764085298848488807213 7432036531987068183302705)
                ·
                  refine ⟨5574027398990301137477029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7432036531987068183302705 5574027398990301137477029)
                  ·
                    refine ⟨1045130137310681463276943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5574027398990301137477029 1045130137310681463276943)
                    ·
                      rfl

theorem cell23_6106151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_6106151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6106151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6106151 prefixEnd_6106151 := by exact prefixLift 6106151
  have htrace : WordTrace (prefixWord ++ tailWord_6106151) baseStart_6106151 baseEnd_6106151 := by
    simpa [prefixWord, tailWord_6106151, baseEnd_6106151] using wordTrace_append hprefix tailTrace_6106151
  have hstable : (prefixWord ++ tailWord_6106151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6106151).length < 2 ^ (prefixWord ++ tailWord_6106151).sum := by decide
  have hdescent : baseEnd_6106151 < baseStart_6106151 := by decide
  rcases family_descends (prefixWord ++ tailWord_6106151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6106170 : List Nat := [3, 1, 1, 1, 3, 1, 2, 1, 1, 4, 5]
def baseStart_6106170 : Nat := 118140960795 + 6106170 * 2 ^ 59
def prefixEnd_6106170 : Nat := 4983230072969 + 3 ^ 40 * 6106170 * 2
def baseEnd_6106170 : Nat := 3135400168064479815493241

theorem tailTrace_6106170 : CollatzResearch.WordTrace tailWord_6106170 prefixEnd_6106170 3135400168064479815493241 := by
  unfold tailWord_6106170
  simp only [CollatzResearch.WordTrace]
  refine ⟨55677579072099103913878991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148473544192264277103677309 55677579072099103913878991)
  ·
    refine ⟨83516368608148655870818487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55677579072099103913878991 83516368608148655870818487)
    ·
      refine ⟨125274552912222983806227731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83516368608148655870818487 125274552912222983806227731)
      ·
        refine ⟨187911829368334475709341597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125274552912222983806227731 187911829368334475709341597)
        ·
          refine ⟨70466936013125428391003099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 187911829368334475709341597 70466936013125428391003099)
          ·
            refine ⟨105700404019688142586504649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70466936013125428391003099 105700404019688142586504649)
            ·
              refine ⟨79275303014766106939878487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105700404019688142586504649 79275303014766106939878487)
              ·
                refine ⟨118912954522149160409817731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79275303014766106939878487 118912954522149160409817731)
                ·
                  refine ⟨178369431783223740614726597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 118912954522149160409817731 178369431783223740614726597)
                  ·
                    refine ⟨33444268459354451365261237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 178369431783223740614726597 33444268459354451365261237)
                    ·
                      refine ⟨3135400168064479815493241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33444268459354451365261237 3135400168064479815493241)
                      ·
                        rfl

theorem cell23_6106170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 1, 4, 5].length) (baseStart_6106170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6106170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6106170 prefixEnd_6106170 := by exact prefixLift 6106170
  have htrace : WordTrace (prefixWord ++ tailWord_6106170) baseStart_6106170 baseEnd_6106170 := by
    simpa [prefixWord, tailWord_6106170, baseEnd_6106170] using wordTrace_append hprefix tailTrace_6106170
  have hstable : (prefixWord ++ tailWord_6106170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6106170).length < 2 ^ (prefixWord ++ tailWord_6106170).sum := by decide
  have hdescent : baseEnd_6106170 < baseStart_6106170 := by decide
  rcases family_descends (prefixWord ++ tailWord_6106170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6106174 : List Nat := [4, 2, 1, 3, 1, 1, 1, 1, 3, 3, 3]
def baseStart_6106174 : Nat := 118140960795 + 6106174 * 2 ^ 59
def prefixEnd_6106174 : Nat := 4983230072969 + 3 ^ 40 * 6106174 * 2
def baseEnd_6106174 : Nat := 3135402221987097799843223

theorem tailTrace_6106174 : CollatzResearch.WordTrace tailWord_6106174 prefixEnd_6106174 3135402221987097799843223 := by
  unfold tailWord_6106174
  simp only [CollatzResearch.WordTrace]
  refine ⟨27838807772547740542332697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148473641453587949559107717 27838807772547740542332697)
  ·
    refine ⟨20879105829410805406749523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27838807772547740542332697 20879105829410805406749523)
    ·
      refine ⟨31318658744116208110124285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20879105829410805406749523 31318658744116208110124285)
      ·
        refine ⟨11744497029043578041296607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31318658744116208110124285 11744497029043578041296607)
        ·
          refine ⟨17616745543565367061944911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11744497029043578041296607 17616745543565367061944911)
          ·
            refine ⟨26425118315348050592917367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17616745543565367061944911 26425118315348050592917367)
            ·
              refine ⟨39637677473022075889376051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26425118315348050592917367 39637677473022075889376051)
              ·
                refine ⟨59456516209533113834064077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39637677473022075889376051 59456516209533113834064077)
                ·
                  refine ⟨22296193578574917687774029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59456516209533113834064077 22296193578574917687774029)
                  ·
                    refine ⟨8361072591965594132915261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22296193578574917687774029 8361072591965594132915261)
                    ·
                      refine ⟨3135402221987097799843223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8361072591965594132915261 3135402221987097799843223)
                      ·
                        rfl

theorem cell23_6106174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_6106174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6106174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6106174 prefixEnd_6106174 := by exact prefixLift 6106174
  have htrace : WordTrace (prefixWord ++ tailWord_6106174) baseStart_6106174 baseEnd_6106174 := by
    simpa [prefixWord, tailWord_6106174, baseEnd_6106174] using wordTrace_append hprefix tailTrace_6106174
  have hstable : (prefixWord ++ tailWord_6106174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6106174).length < 2 ^ (prefixWord ++ tailWord_6106174).sum := by decide
  have hdescent : baseEnd_6106174 < baseStart_6106174 := by decide
  rcases family_descends (prefixWord ++ tailWord_6106174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6106198 : List Nat := [5, 2, 2, 1, 3, 1, 1, 8]
def baseStart_6106198 : Nat := 118140960795 + 6106198 * 2 ^ 59
def prefixEnd_6106198 : Nat := 4983230072969 + 3 ^ 40 * 6106198 * 2
def baseEnd_6106198 : Nat := 116126464648992803923819

theorem tailTrace_6106198 : CollatzResearch.WordTrace tailWord_6106198 prefixEnd_6106198 116126464648992803923819 := by
  unfold tailWord_6106198
  simp only [CollatzResearch.WordTrace]
  refine ⟨13919458595768436027345953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 148474225021529984291690165 13919458595768436027345953)
  ·
    refine ⟨10439593946826327020509465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13919458595768436027345953 10439593946826327020509465)
    ·
      refine ⟨7829695460119745265382099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10439593946826327020509465 7829695460119745265382099)
      ·
        refine ⟨11744543190179617898073149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7829695460119745265382099 11744543190179617898073149)
        ·
          refine ⟨4404203696317356711777431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11744543190179617898073149 4404203696317356711777431)
          ·
            refine ⟨6606305544476035067666147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4404203696317356711777431 6606305544476035067666147)
            ·
              refine ⟨9909458316714052601499221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6606305544476035067666147 9909458316714052601499221)
              ·
                refine ⟨116126464648992803923819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9909458316714052601499221 116126464648992803923819)
                ·
                  rfl

theorem cell23_6106198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 1, 8].length) (baseStart_6106198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6106198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6106198 prefixEnd_6106198 := by exact prefixLift 6106198
  have htrace : WordTrace (prefixWord ++ tailWord_6106198) baseStart_6106198 baseEnd_6106198 := by
    simpa [prefixWord, tailWord_6106198, baseEnd_6106198] using wordTrace_append hprefix tailTrace_6106198
  have hstable : (prefixWord ++ tailWord_6106198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6106198).length < 2 ^ (prefixWord ++ tailWord_6106198).sum := by decide
  have hdescent : baseEnd_6106198 < baseStart_6106198 := by decide
  rcases family_descends (prefixWord ++ tailWord_6106198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6106248 : List Nat := [2, 1, 3, 4, 2, 1, 1, 1, 4, 2, 2]
def baseStart_6106248 : Nat := 118140960795 + 6106248 * 2 ^ 59
def prefixEnd_6106248 : Nat := 4983230072969 + 3 ^ 40 * 6106248 * 2
def baseEnd_6106248 : Nat := 3135440219555530510317883

theorem tailTrace_6106248 : CollatzResearch.WordTrace tailWord_6106248 prefixEnd_6106248 3135440219555530510317883 := by
  unfold tailWord_6106248
  simp only [CollatzResearch.WordTrace]
  refine ⟨111356580591056917488427699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148475440788075889984570265 111356580591056917488427699)
  ·
    refine ⟨167034870886585376232641549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111356580591056917488427699 167034870886585376232641549)
    ·
      refine ⟨62638076582469516087240581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167034870886585376232641549 62638076582469516087240581)
      ·
        refine ⟨11744639359213034266357609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62638076582469516087240581 11744639359213034266357609)
        ·
          refine ⟨8808479519409775699768207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11744639359213034266357609 8808479519409775699768207)
          ·
            refine ⟨13212719279114663549652311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8808479519409775699768207 13212719279114663549652311)
            ·
              refine ⟨19819078918671995324478467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13212719279114663549652311 19819078918671995324478467)
              ·
                refine ⟨29728618378007992986717701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19819078918671995324478467 29728618378007992986717701)
                ·
                  refine ⟨5574115945876498685009569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29728618378007992986717701 5574115945876498685009569)
                  ·
                    refine ⟨4180586959407374013757177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5574115945876498685009569 4180586959407374013757177)
                    ·
                      refine ⟨3135440219555530510317883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4180586959407374013757177 3135440219555530510317883)
                      ·
                        rfl

theorem cell23_6106248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 1, 4, 2, 2].length) (baseStart_6106248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6106248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6106248 prefixEnd_6106248 := by exact prefixLift 6106248
  have htrace : WordTrace (prefixWord ++ tailWord_6106248) baseStart_6106248 baseEnd_6106248 := by
    simpa [prefixWord, tailWord_6106248, baseEnd_6106248] using wordTrace_append hprefix tailTrace_6106248
  have hstable : (prefixWord ++ tailWord_6106248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6106248).length < 2 ^ (prefixWord ++ tailWord_6106248).sum := by decide
  have hdescent : baseEnd_6106248 < baseStart_6106248 := by decide
  rcases family_descends (prefixWord ++ tailWord_6106248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6106254 : List Nat := [4, 1, 1, 3, 2, 2, 2, 1, 7]
def baseStart_6106254 : Nat := 118140960795 + 6106254 * 2 ^ 59
def prefixEnd_6106254 : Nat := 4983230072969 + 3 ^ 40 * 6106254 * 2
def baseEnd_6106254 : Nat := 348382588937717498538095

theorem tailTrace_6106254 : CollatzResearch.WordTrace tailWord_6106254 prefixEnd_6106254 348382588937717498538095 := by
  unfold tailWord_6106254
  simp only [CollatzResearch.WordTrace]
  refine ⟨27839172502511512250196727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148475586680061398667715877 27839172502511512250196727)
  ·
    refine ⟨41758758753767268375295091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27839172502511512250196727 41758758753767268375295091)
    ·
      refine ⟨62638138130650902562942637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41758758753767268375295091 62638138130650902562942637)
      ·
        refine ⟨23489301798994088461103489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62638138130650902562942637 23489301798994088461103489)
        ·
          refine ⟨17616976349245566345827617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23489301798994088461103489 17616976349245566345827617)
          ·
            refine ⟨13212732261934174759370713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17616976349245566345827617 13212732261934174759370713)
            ·
              refine ⟨9909549196450631069528035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13212732261934174759370713 9909549196450631069528035)
              ·
                refine ⟨14864323794675946604292053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9909549196450631069528035 14864323794675946604292053)
                ·
                  refine ⟨348382588937717498538095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14864323794675946604292053 348382588937717498538095)
                  ·
                    rfl

theorem cell23_6106254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 2, 1, 7].length) (baseStart_6106254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6106254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6106254 prefixEnd_6106254 := by exact prefixLift 6106254
  have htrace : WordTrace (prefixWord ++ tailWord_6106254) baseStart_6106254 baseEnd_6106254 := by
    simpa [prefixWord, tailWord_6106254, baseEnd_6106254] using wordTrace_append hprefix tailTrace_6106254
  have hstable : (prefixWord ++ tailWord_6106254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6106254).length < 2 ^ (prefixWord ++ tailWord_6106254).sum := by decide
  have hdescent : baseEnd_6106254 < baseStart_6106254 := by decide
  rcases family_descends (prefixWord ++ tailWord_6106254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6106264 : List Nat := [2, 1, 2, 4, 2, 1, 2, 1, 2, 3, 3]
def baseStart_6106264 : Nat := 118140960795 + 6106264 * 2 ^ 59
def prefixEnd_6106264 : Nat := 4983230072969 + 3 ^ 40 * 6106264 * 2
def baseEnd_6106264 : Nat := 3135448435246002447717809

theorem tailTrace_6106264 : CollatzResearch.WordTrace tailWord_6106264 prefixEnd_6106264 3135448435246002447717809 := by
  unfold tailWord_6106264
  simp only [CollatzResearch.WordTrace]
  refine ⟨111356872375027934854718923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148475829833370579806291897 111356872375027934854718923)
  ·
    refine ⟨167035308562541902282078385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111356872375027934854718923 167035308562541902282078385)
    ·
      refine ⟨125276481421906426711558789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167035308562541902282078385 125276481421906426711558789)
      ·
        refine ⟨23489340266607455008417273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 125276481421906426711558789 23489340266607455008417273)
        ·
          refine ⟨17617005199955591256312955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23489340266607455008417273 17617005199955591256312955)
          ·
            refine ⟨26425507799933386884469433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17617005199955591256312955 26425507799933386884469433)
            ·
              refine ⟨19819130849950040163352075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26425507799933386884469433 19819130849950040163352075)
              ·
                refine ⟨29728696274925060245028113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19819130849950040163352075 29728696274925060245028113)
                ·
                  refine ⟨22296522206193795183771085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29728696274925060245028113 22296522206193795183771085)
                  ·
                    refine ⟨8361195827322673193914157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22296522206193795183771085 8361195827322673193914157)
                    ·
                      refine ⟨3135448435246002447717809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8361195827322673193914157 3135448435246002447717809)
                      ·
                        rfl

theorem cell23_6106264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 1, 2, 3, 3].length) (baseStart_6106264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6106264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6106264 prefixEnd_6106264 := by exact prefixLift 6106264
  have htrace : WordTrace (prefixWord ++ tailWord_6106264) baseStart_6106264 baseEnd_6106264 := by
    simpa [prefixWord, tailWord_6106264, baseEnd_6106264] using wordTrace_append hprefix tailTrace_6106264
  have hstable : (prefixWord ++ tailWord_6106264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6106264).length < 2 ^ (prefixWord ++ tailWord_6106264).sum := by decide
  have hdescent : baseEnd_6106264 < baseStart_6106264 := by decide
  rcases family_descends (prefixWord ++ tailWord_6106264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6106287 : List Nat := [1, 1, 2, 1, 2, 3, 4, 1, 1, 3, 4]
def baseStart_6106287 : Nat := 118140960795 + 6106287 * 2 ^ 59
def prefixEnd_6106287 : Nat := 4983230072969 + 3 ^ 40 * 6106287 * 2
def baseEnd_6106287 : Nat := 3135460245301055857730203

theorem tailTrace_6106287 : CollatzResearch.WordTrace tailWord_6106287 prefixEnd_6106287 3135460245301055857730203 := by
  unfold tailWord_6106287
  simp only [CollatzResearch.WordTrace]
  refine ⟨222714583628972544637525115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148476389085981696425016743 222714583628972544637525115)
  ·
    refine ⟨334071875443458816956287673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222714583628972544637525115 334071875443458816956287673)
    ·
      refine ⟨250553906582594112717215755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 334071875443458816956287673 250553906582594112717215755)
      ·
        refine ⟨375830859873891169075823633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250553906582594112717215755 375830859873891169075823633)
        ·
          refine ⟨281873144905418376806867725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 375830859873891169075823633 281873144905418376806867725)
          ·
            refine ⟨105702429339531891302575397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 281873144905418376806867725 105702429339531891302575397)
            ·
              refine ⟨19819205501162229619232887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 105702429339531891302575397 19819205501162229619232887)
              ·
                refine ⟨29728808251743344428849331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19819205501162229619232887 29728808251743344428849331)
                ·
                  refine ⟨44593212377615016643273997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29728808251743344428849331 44593212377615016643273997)
                  ·
                    refine ⟨16722454641605631241227749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44593212377615016643273997 16722454641605631241227749)
                    ·
                      refine ⟨3135460245301055857730203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16722454641605631241227749 3135460245301055857730203)
                      ·
                        rfl

theorem cell23_6106287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 1, 1, 3, 4].length) (baseStart_6106287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6106287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6106287 prefixEnd_6106287 := by exact prefixLift 6106287
  have htrace : WordTrace (prefixWord ++ tailWord_6106287) baseStart_6106287 baseEnd_6106287 := by
    simpa [prefixWord, tailWord_6106287, baseEnd_6106287] using wordTrace_append hprefix tailTrace_6106287
  have hstable : (prefixWord ++ tailWord_6106287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6106287).length < 2 ^ (prefixWord ++ tailWord_6106287).sum := by decide
  have hdescent : baseEnd_6106287 < baseStart_6106287 := by decide
  rcases family_descends (prefixWord ++ tailWord_6106287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6106307 : List Nat := [1, 1, 1, 3, 1, 1, 1, 4, 3, 4, 3]
def baseStart_6106307 : Nat := 118140960795 + 6106307 * 2 ^ 59
def prefixEnd_6106307 : Nat := 4983230072969 + 3 ^ 40 * 6106307 * 2
def baseEnd_6106307 : Nat := 3135470514914145779480111

theorem tailTrace_6106307 : CollatzResearch.WordTrace tailWord_6106307 prefixEnd_6106307 3135470514914145779480111 := by
  unfold tailWord_6106307
  simp only [CollatzResearch.WordTrace]
  refine ⟨222715313088900088053253175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148476875392600058702168783 222715313088900088053253175)
  ·
    refine ⟨334072969633350132079879763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222715313088900088053253175 334072969633350132079879763)
    ·
      refine ⟨501109454450025198119819645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 334072969633350132079879763 501109454450025198119819645)
      ·
        refine ⟨187916045418759449294932367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 501109454450025198119819645 187916045418759449294932367)
        ·
          refine ⟨281874068128139173942398551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187916045418759449294932367 281874068128139173942398551)
          ·
            refine ⟨422811102192208760913597827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 281874068128139173942398551 422811102192208760913597827)
            ·
              refine ⟨634216653288313141370396741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 422811102192208760913597827 634216653288313141370396741)
              ·
                refine ⟨118915622491558714006949389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 634216653288313141370396741 118915622491558714006949389)
                ·
                  refine ⟨44593358434334517752606021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 118915622491558714006949389 44593358434334517752606021)
                  ·
                    refine ⟨8361254706437722078613629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44593358434334517752606021 8361254706437722078613629)
                    ·
                      refine ⟨3135470514914145779480111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8361254706437722078613629 3135470514914145779480111)
                      ·
                        rfl

theorem cell23_6106307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 3, 4, 3].length) (baseStart_6106307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6106307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6106307 prefixEnd_6106307 := by exact prefixLift 6106307
  have htrace : WordTrace (prefixWord ++ tailWord_6106307) baseStart_6106307 baseEnd_6106307 := by
    simpa [prefixWord, tailWord_6106307, baseEnd_6106307] using wordTrace_append hprefix tailTrace_6106307
  have hstable : (prefixWord ++ tailWord_6106307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6106307).length < 2 ^ (prefixWord ++ tailWord_6106307).sum := by decide
  have hdescent : baseEnd_6106307 < baseStart_6106307 := by decide
  rcases family_descends (prefixWord ++ tailWord_6106307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6106404 : List Nat := [2, 3, 1, 3, 1, 1, 1, 4, 1, 6]
def baseStart_6106404 : Nat := 118140960795 + 6106404 * 2 ^ 59
def prefixEnd_6106404 : Nat := 4983230072969 + 3 ^ 40 * 6106404 * 2
def baseEnd_6106404 : Nat := 1045173440845877299989055

theorem tailTrace_6106404 : CollatzResearch.WordTrace tailWord_6106404 prefixEnd_6106404 1045173440845877299989055 := by
  unfold tailWord_6106404
  simp only [CollatzResearch.WordTrace]
  refine ⟨111359425484774336809767133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148479233979699115746356177 111359425484774336809767133)
  ·
    refine ⟨41759784556790376303662675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111359425484774336809767133 41759784556790376303662675)
    ·
      refine ⟨62639676835185564455494013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41759784556790376303662675 62639676835185564455494013)
      ·
        refine ⟨23489878813194586670810255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62639676835185564455494013 23489878813194586670810255)
        ·
          refine ⟨35234818219791880006215383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23489878813194586670810255 35234818219791880006215383)
          ·
            refine ⟨52852227329687820009323075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35234818219791880006215383 52852227329687820009323075)
            ·
              refine ⟨79278340994531730013984613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52852227329687820009323075 79278340994531730013984613)
              ·
                refine ⟨14864688936474699377622115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 79278340994531730013984613 14864688936474699377622115)
                ·
                  refine ⟨22297033404712049066433173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14864688936474699377622115 22297033404712049066433173)
                  ·
                    refine ⟨1045173440845877299989055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22297033404712049066433173 1045173440845877299989055)
                    ·
                      rfl

theorem cell23_6106404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 4, 1, 6].length) (baseStart_6106404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6106404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6106404 prefixEnd_6106404 := by exact prefixLift 6106404
  have htrace : WordTrace (prefixWord ++ tailWord_6106404) baseStart_6106404 baseEnd_6106404 := by
    simpa [prefixWord, tailWord_6106404, baseEnd_6106404] using wordTrace_append hprefix tailTrace_6106404
  have hstable : (prefixWord ++ tailWord_6106404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6106404).length < 2 ^ (prefixWord ++ tailWord_6106404).sum := by decide
  have hdescent : baseEnd_6106404 < baseStart_6106404 := by decide
  rcases family_descends (prefixWord ++ tailWord_6106404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6106405 : List Nat := [1, 3, 1, 2, 4, 2, 2, 3, 1, 1, 3]
def baseStart_6106405 : Nat := 118140960795 + 6106405 * 2 ^ 59
def prefixEnd_6106405 : Nat := 4983230072969 + 3 ^ 40 * 6106405 * 2
def baseEnd_6106405 : Nat := 3135520836018286396054661

theorem tailTrace_6106405 : CollatzResearch.WordTrace tailWord_6106405 prefixEnd_6106405 3135520836018286396054661 := by
  unfold tailWord_6106405
  simp only [CollatzResearch.WordTrace]
  refine ⟨222718887442545050790320669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148479258295030033860213779 222718887442545050790320669)
  ·
    refine ⟨83519582790954394046370251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 222718887442545050790320669 83519582790954394046370251)
    ·
      refine ⟨125279374186431591069555377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83519582790954394046370251 125279374186431591069555377)
      ·
        refine ⟨93959530639823693302166533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125279374186431591069555377 93959530639823693302166533)
        ·
          refine ⟨17617411994966942494156225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93959530639823693302166533 17617411994966942494156225)
          ·
            refine ⟨13213058996225206870617169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17617411994966942494156225 13213058996225206870617169)
            ·
              refine ⟨9909794247168905152962877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13213058996225206870617169 9909794247168905152962877)
              ·
                refine ⟨3716172842688339432361079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9909794247168905152962877 3716172842688339432361079)
                ·
                  refine ⟨5574259264032509148541619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3716172842688339432361079 5574259264032509148541619)
                  ·
                    refine ⟨8361388896048763722812429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5574259264032509148541619 8361388896048763722812429)
                    ·
                      refine ⟨3135520836018286396054661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8361388896048763722812429 3135520836018286396054661)
                      ·
                        rfl

theorem cell23_6106405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 2, 3, 1, 1, 3].length) (baseStart_6106405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6106405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6106405 prefixEnd_6106405 := by exact prefixLift 6106405
  have htrace : WordTrace (prefixWord ++ tailWord_6106405) baseStart_6106405 baseEnd_6106405 := by
    simpa [prefixWord, tailWord_6106405, baseEnd_6106405] using wordTrace_append hprefix tailTrace_6106405
  have hstable : (prefixWord ++ tailWord_6106405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6106405).length < 2 ^ (prefixWord ++ tailWord_6106405).sum := by decide
  have hdescent : baseEnd_6106405 < baseStart_6106405 := by decide
  rcases family_descends (prefixWord ++ tailWord_6106405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6106408 : List Nat := [2, 1, 5, 1, 2, 1, 4, 1, 1, 5]
def baseStart_6106408 : Nat := 118140960795 + 6106408 * 2 ^ 59
def prefixEnd_6106408 : Nat := 4983230072969 + 3 ^ 40 * 6106408 * 2
def baseEnd_6106408 : Nat := 1045174125486749961439049

theorem tailTrace_6106408 : CollatzResearch.WordTrace tailWord_6106408 prefixEnd_6106408 1045174125486749961439049 := by
  unfold tailWord_6106408
  simp only [CollatzResearch.WordTrace]
  refine ⟨111359498430767091151339939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148479331241022788201786585 111359498430767091151339939)
  ·
    refine ⟨167039247646150636727009909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111359498430767091151339939 167039247646150636727009909)
    ·
      refine ⟨15659929466826622193157179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 167039247646150636727009909 15659929466826622193157179)
      ·
        refine ⟨23489894200239933289735769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15659929466826622193157179 23489894200239933289735769)
        ·
          refine ⟨17617420650179949967301827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23489894200239933289735769 17617420650179949967301827)
          ·
            refine ⟨26426130975269924950952741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17617420650179949967301827 26426130975269924950952741)
            ·
              refine ⟨4954899557863110928303639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26426130975269924950952741 4954899557863110928303639)
              ·
                refine ⟨7432349336794666392455459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4954899557863110928303639 7432349336794666392455459)
                ·
                  refine ⟨11148524005191999588683189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7432349336794666392455459 11148524005191999588683189)
                  ·
                    refine ⟨1045174125486749961439049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11148524005191999588683189 1045174125486749961439049)
                    ·
                      rfl

theorem cell23_6106408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 4, 1, 1, 5].length) (baseStart_6106408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6106408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6106408 prefixEnd_6106408 := by exact prefixLift 6106408
  have htrace : WordTrace (prefixWord ++ tailWord_6106408) baseStart_6106408 baseEnd_6106408 := by
    simpa [prefixWord, tailWord_6106408, baseEnd_6106408] using wordTrace_append hprefix tailTrace_6106408
  have hstable : (prefixWord ++ tailWord_6106408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6106408).length < 2 ^ (prefixWord ++ tailWord_6106408).sum := by decide
  have hdescent : baseEnd_6106408 < baseStart_6106408 := by decide
  rcases family_descends (prefixWord ++ tailWord_6106408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6106421 : List Nat := [1, 3, 3, 1, 2, 3, 1, 1, 4, 4]
def baseStart_6106421 : Nat := 118140960795 + 6106421 * 2 ^ 59
def prefixEnd_6106421 : Nat := 4983230072969 + 3 ^ 40 * 6106421 * 2
def baseEnd_6106421 : Nat := 1045176350569586111151529

theorem tailTrace_6106421 : CollatzResearch.WordTrace tailWord_6106421 prefixEnd_6106421 1045176350569586111151529 := by
  unfold tailWord_6106421
  simp only [CollatzResearch.WordTrace]
  refine ⟨222719471010487085522903117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148479647340324723681935411 222719471010487085522903117)
  ·
    refine ⟨83519801628932657071088669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 222719471010487085522903117 83519801628932657071088669)
    ·
      refine ⟨31319925610849746401658251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83519801628932657071088669 31319925610849746401658251)
      ·
        refine ⟨46979888416274619602487377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31319925610849746401658251 46979888416274619602487377)
        ·
          refine ⟨35234916312205964701865533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46979888416274619602487377 35234916312205964701865533)
          ·
            refine ⟨13213093617077236763199575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35234916312205964701865533 13213093617077236763199575)
            ·
              refine ⟨19819640425615855144799363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13213093617077236763199575 19819640425615855144799363)
              ·
                refine ⟨29729460638423782717199045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19819640425615855144799363 29729460638423782717199045)
                ·
                  refine ⟨5574273869704459259474821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29729460638423782717199045 5574273869704459259474821)
                  ·
                    refine ⟨1045176350569586111151529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5574273869704459259474821 1045176350569586111151529)
                    ·
                      rfl

theorem cell23_6106421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 1, 4, 4].length) (baseStart_6106421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6106421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6106421 prefixEnd_6106421 := by exact prefixLift 6106421
  have htrace : WordTrace (prefixWord ++ tailWord_6106421) baseStart_6106421 baseEnd_6106421 := by
    simpa [prefixWord, tailWord_6106421, baseEnd_6106421] using wordTrace_append hprefix tailTrace_6106421
  have hstable : (prefixWord ++ tailWord_6106421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6106421).length < 2 ^ (prefixWord ++ tailWord_6106421).sum := by decide
  have hdescent : baseEnd_6106421 < baseStart_6106421 := by decide
  rcases family_descends (prefixWord ++ tailWord_6106421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6106422 : List Nat := [5, 1, 2, 3, 1, 1, 2, 1, 3, 1, 3]
def baseStart_6106422 : Nat := 118140960795 + 6106422 * 2 ^ 59
def prefixEnd_6106422 : Nat := 4983230072969 + 3 ^ 40 * 6106422 * 2
def baseEnd_6106422 : Nat := 3135529565189412829542083

theorem tailTrace_6106422 : CollatzResearch.WordTrace tailWord_6106422 prefixEnd_6106422 3135529565189412829542083 := by
  unfold tailWord_6106422
  simp only [CollatzResearch.WordTrace]
  refine ⟨13919969217717716418355595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 148479671655655641795793013 13919969217717716418355595)
  ·
    refine ⟨20879953826576574627533393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13919969217717716418355595 20879953826576574627533393)
    ·
      refine ⟨15659965369932430970650045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20879953826576574627533393 15659965369932430970650045)
      ·
        refine ⟨5872487013724661613993767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15659965369932430970650045 5872487013724661613993767)
        ·
          refine ⟨8808730520586992420990651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5872487013724661613993767 8808730520586992420990651)
          ·
            refine ⟨13213095780880488631485977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8808730520586992420990651 13213095780880488631485977)
            ·
              refine ⟨9909821835660366473614483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13213095780880488631485977 9909821835660366473614483)
              ·
                refine ⟨14864732753490549710421725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9909821835660366473614483 14864732753490549710421725)
                ·
                  refine ⟨5574274782558956141408147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14864732753490549710421725 5574274782558956141408147)
                  ·
                    refine ⟨8361412173838434212112221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5574274782558956141408147 8361412173838434212112221)
                    ·
                      refine ⟨3135529565189412829542083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8361412173838434212112221 3135529565189412829542083)
                      ·
                        rfl

theorem cell23_6106422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_6106422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6106422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6106422 prefixEnd_6106422 := by exact prefixLift 6106422
  have htrace : WordTrace (prefixWord ++ tailWord_6106422) baseStart_6106422 baseEnd_6106422 := by
    simpa [prefixWord, tailWord_6106422, baseEnd_6106422] using wordTrace_append hprefix tailTrace_6106422
  have hstable : (prefixWord ++ tailWord_6106422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6106422).length < 2 ^ (prefixWord ++ tailWord_6106422).sum := by decide
  have hdescent : baseEnd_6106422 < baseStart_6106422 := by decide
  rcases family_descends (prefixWord ++ tailWord_6106422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6106428 : List Nat := [2, 2, 2, 2, 1, 3, 1, 3, 3, 2, 2]
def baseStart_6106428 : Nat := 118140960795 + 6106428 * 2 ^ 59
def prefixEnd_6106428 : Nat := 4983230072969 + 3 ^ 40 * 6106428 * 2
def baseEnd_6106428 : Nat := 3135532646073339806067055

theorem tailTrace_6106428 : CollatzResearch.WordTrace tailWord_6106428 prefixEnd_6106428 3135532646073339806067055 := by
  unfold tailWord_6106428
  simp only [CollatzResearch.WordTrace]
  refine ⟨111359863160730862859203969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148479817547641150478938625 111359863160730862859203969)
  ·
    refine ⟨83519897370548147144402977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111359863160730862859203969 83519897370548147144402977)
    ·
      refine ⟨62639923027911110358302233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83519897370548147144402977 62639923027911110358302233)
      ·
        refine ⟨46979942270933332768726675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62639923027911110358302233 46979942270933332768726675)
        ·
          refine ⟨70469913406399999153090013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46979942270933332768726675 70469913406399999153090013)
          ·
            refine ⟨26426217527399999682408755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70469913406399999153090013 26426217527399999682408755)
            ·
              refine ⟨39639326291099999523613133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26426217527399999682408755 39639326291099999523613133)
              ·
                refine ⟨14864747359162499821354925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39639326291099999523613133 14864747359162499821354925)
                ·
                  refine ⟨5574280259685937433008097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14864747359162499821354925 5574280259685937433008097)
                  ·
                    refine ⟨4180710194764453074756073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5574280259685937433008097 4180710194764453074756073)
                    ·
                      refine ⟨3135532646073339806067055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4180710194764453074756073 3135532646073339806067055)
                      ·
                        rfl

theorem cell23_6106428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 3, 3, 2, 2].length) (baseStart_6106428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6106428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6106428 prefixEnd_6106428 := by exact prefixLift 6106428
  have htrace : WordTrace (prefixWord ++ tailWord_6106428) baseStart_6106428 baseEnd_6106428 := by
    simpa [prefixWord, tailWord_6106428, baseEnd_6106428] using wordTrace_append hprefix tailTrace_6106428
  have hstable : (prefixWord ++ tailWord_6106428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6106428).length < 2 ^ (prefixWord ++ tailWord_6106428).sum := by decide
  have hdescent : baseEnd_6106428 < baseStart_6106428 := by decide
  rcases family_descends (prefixWord ++ tailWord_6106428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6106447 : List Nat := [1, 1, 2, 1, 1, 2, 1, 2, 3, 9]
def baseStart_6106447 : Nat := 118140960795 + 6106447 * 2 ^ 59
def prefixEnd_6106447 : Nat := 4983230072969 + 3 ^ 40 * 6106447 * 2
def baseEnd_6106447 : Nat := 1045180800735258410576489

theorem tailTrace_6106447 : CollatzResearch.WordTrace tailWord_6106447 prefixEnd_6106447 1045180800735258410576489 := by
  unfold tailWord_6106447
  simp only [CollatzResearch.WordTrace]
  refine ⟨222720419308392891963349595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148480279538928594642233063 222720419308392891963349595)
  ·
    refine ⟨334080628962589337945024393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222720419308392891963349595 334080628962589337945024393)
    ·
      refine ⟨250560471721942003458768295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 334080628962589337945024393 250560471721942003458768295)
      ·
        refine ⟨375840707582913005188152443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250560471721942003458768295 375840707582913005188152443)
        ·
          refine ⟨563761061374369507782228665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 375840707582913005188152443 563761061374369507782228665)
          ·
            refine ⟨422820796030777130836671499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 563761061374369507782228665 422820796030777130836671499)
            ·
              refine ⟨634231194046165696255007249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 422820796030777130836671499 634231194046165696255007249)
              ·
                refine ⟨475673395534624272191255437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 634231194046165696255007249 475673395534624272191255437)
                ·
                  refine ⟨178377523325484102071720789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 475673395534624272191255437 178377523325484102071720789)
                  ·
                    refine ⟨1045180800735258410576489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 178377523325484102071720789 1045180800735258410576489)
                    ·
                      rfl

theorem cell23_6106447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 9].length) (baseStart_6106447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6106447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6106447 prefixEnd_6106447 := by exact prefixLift 6106447
  have htrace : WordTrace (prefixWord ++ tailWord_6106447) baseStart_6106447 baseEnd_6106447 := by
    simpa [prefixWord, tailWord_6106447, baseEnd_6106447] using wordTrace_append hprefix tailTrace_6106447
  have hstable : (prefixWord ++ tailWord_6106447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6106447).length < 2 ^ (prefixWord ++ tailWord_6106447).sum := by decide
  have hdescent : baseEnd_6106447 < baseStart_6106447 := by decide
  rcases family_descends (prefixWord ++ tailWord_6106447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6106551 : List Nat := [1, 1, 3, 1, 3, 2, 3, 1, 2, 3, 3]
def baseStart_6106551 : Nat := 118140960795 + 6106551 * 2 ^ 59
def prefixEnd_6106551 : Nat := 4983230072969 + 3 ^ 40 * 6106551 * 2
def baseEnd_6106551 : Nat := 3135595804193842824828989

theorem tailTrace_6106551 : CollatzResearch.WordTrace tailWord_6106551 prefixEnd_6106551 3135595804193842824828989 := by
  unfold tailWord_6106551
  simp only [CollatzResearch.WordTrace]
  refine ⟨222724212500016117725135507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148482808333344078483423671 222724212500016117725135507)
  ·
    refine ⟨334086318750024176587703261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222724212500016117725135507 334086318750024176587703261)
    ·
      refine ⟨125282369531259066220388723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 334086318750024176587703261 125282369531259066220388723)
      ·
        refine ⟨187923554296888599330583085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125282369531259066220388723 187923554296888599330583085)
        ·
          refine ⟨70471332861333224748968657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 187923554296888599330583085 70471332861333224748968657)
          ·
            refine ⟨52853499645999918561726493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70471332861333224748968657 52853499645999918561726493)
            ·
              refine ⟨19820062367249969460647435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52853499645999918561726493 19820062367249969460647435)
              ·
                refine ⟨29730093550874954190971153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19820062367249969460647435 29730093550874954190971153)
                ·
                  refine ⟨22297570163156215643228365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29730093550874954190971153 22297570163156215643228365)
                  ·
                    refine ⟨8361588811183580866210637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22297570163156215643228365 8361588811183580866210637)
                    ·
                      refine ⟨3135595804193842824828989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8361588811183580866210637 3135595804193842824828989)
                      ·
                        rfl

theorem cell23_6106551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 1, 2, 3, 3].length) (baseStart_6106551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6106551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6106551 prefixEnd_6106551 := by exact prefixLift 6106551
  have htrace : WordTrace (prefixWord ++ tailWord_6106551) baseStart_6106551 baseEnd_6106551 := by
    simpa [prefixWord, tailWord_6106551, baseEnd_6106551] using wordTrace_append hprefix tailTrace_6106551
  have hstable : (prefixWord ++ tailWord_6106551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6106551).length < 2 ^ (prefixWord ++ tailWord_6106551).sum := by decide
  have hdescent : baseEnd_6106551 < baseStart_6106551 := by decide
  rcases family_descends (prefixWord ++ tailWord_6106551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6106571 : List Nat := [1, 1, 1, 1, 3, 3, 5, 1, 2, 5]
def baseStart_6106571 : Nat := 118140960795 + 6106571 * 2 ^ 59
def prefixEnd_6106571 : Nat := 4983230072969 + 3 ^ 40 * 6106571 * 2
def baseEnd_6106571 : Nat := 1045202024602310915526299

theorem tailTrace_6106571 : CollatzResearch.WordTrace tailWord_6106571 prefixEnd_6106571 1045202024602310915526299 := by
  unfold tailWord_6106571
  simp only [CollatzResearch.WordTrace]
  refine ⟨222724941959943661140863567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148483294639962440760575711 222724941959943661140863567)
  ·
    refine ⟨334087412939915491711295351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222724941959943661140863567 334087412939915491711295351)
    ·
      refine ⟨501131119409873237566943027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 334087412939915491711295351 501131119409873237566943027)
      ·
        refine ⟨751696679114809856350414541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 501131119409873237566943027 751696679114809856350414541)
        ·
          refine ⟨281886254668053696131405453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 751696679114809856350414541 281886254668053696131405453)
          ·
            refine ⟨105707345500520136049277045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 281886254668053696131405453 105707345500520136049277045)
            ·
              refine ⟨9910063640673762754619723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 105707345500520136049277045 9910063640673762754619723)
              ·
                refine ⟨14865095461010644131929585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9910063640673762754619723 14865095461010644131929585)
                ·
                  refine ⟨11148821595757983098947189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14865095461010644131929585 11148821595757983098947189)
                  ·
                    refine ⟨1045202024602310915526299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11148821595757983098947189 1045202024602310915526299)
                    ·
                      rfl

theorem cell23_6106571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 5, 1, 2, 5].length) (baseStart_6106571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6106571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6106571 prefixEnd_6106571 := by exact prefixLift 6106571
  have htrace : WordTrace (prefixWord ++ tailWord_6106571) baseStart_6106571 baseEnd_6106571 := by
    simpa [prefixWord, tailWord_6106571, baseEnd_6106571] using wordTrace_append hprefix tailTrace_6106571
  have hstable : (prefixWord ++ tailWord_6106571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6106571).length < 2 ^ (prefixWord ++ tailWord_6106571).sum := by decide
  have hdescent : baseEnd_6106571 < baseStart_6106571 := by decide
  rcases family_descends (prefixWord ++ tailWord_6106571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6106591 : List Nat := [1, 1, 2, 3, 3, 1, 2, 1, 4, 1, 4]
def baseStart_6106591 : Nat := 118140960795 + 6106591 * 2 ^ 59
def prefixEnd_6106591 : Nat := 4983230072969 + 3 ^ 40 * 6106591 * 2
def baseEnd_6106591 : Nat := 3135616343420022668328805

theorem tailTrace_6106591 : CollatzResearch.WordTrace tailWord_6106591 prefixEnd_6106591 3135616343420022668328805 := by
  unfold tailWord_6106591
  simp only [CollatzResearch.WordTrace]
  refine ⟨222725671419871204556591627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148483780946580803037727751 222725671419871204556591627)
  ·
    refine ⟨334088507129806806834887441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222725671419871204556591627 334088507129806806834887441)
    ·
      refine ⟨250566380347355105126165581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 334088507129806806834887441 250566380347355105126165581)
      ·
        refine ⟨93962392630258164422312093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 250566380347355105126165581 93962392630258164422312093)
        ·
          refine ⟨35235897236346811658367035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93962392630258164422312093 35235897236346811658367035)
          ·
            refine ⟨52853845854520217487550553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35235897236346811658367035 52853845854520217487550553)
            ·
              refine ⟨39640384390890163115662915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52853845854520217487550553 39640384390890163115662915)
              ·
                refine ⟨59460576586335244673494373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39640384390890163115662915 59460576586335244673494373)
                ·
                  refine ⟨11148858109937858376280195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59460576586335244673494373 11148858109937858376280195)
                  ·
                    refine ⟨16723287164906787564420293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11148858109937858376280195 16723287164906787564420293)
                    ·
                      refine ⟨3135616343420022668328805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16723287164906787564420293 3135616343420022668328805)
                      ·
                        rfl

theorem cell23_6106591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 1, 4, 1, 4].length) (baseStart_6106591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6106591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6106591 prefixEnd_6106591 := by exact prefixLift 6106591
  have htrace : WordTrace (prefixWord ++ tailWord_6106591) baseStart_6106591 baseEnd_6106591 := by
    simpa [prefixWord, tailWord_6106591, baseEnd_6106591] using wordTrace_append hprefix tailTrace_6106591
  have hstable : (prefixWord ++ tailWord_6106591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6106591).length < 2 ^ (prefixWord ++ tailWord_6106591).sum := by decide
  have hdescent : baseEnd_6106591 < baseStart_6106591 := by decide
  rcases family_descends (prefixWord ++ tailWord_6106591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6106608 : List Nat := [2, 1, 1, 1, 3, 4, 2, 1, 2, 4, 2]
def baseStart_6106608 : Nat := 118140960795 + 6106608 * 2 ^ 59
def prefixEnd_6106608 : Nat := 4983230072969 + 3 ^ 40 * 6106608 * 2
def baseEnd_6106608 : Nat := 3135625072591149101816227

theorem tailTrace_6106608 : CollatzResearch.WordTrace tailWord_6106608 prefixEnd_6106608 3135625072591149101816227 := by
  unfold tailWord_6106608
  simp only [CollatzResearch.WordTrace]
  refine ⟨111363145730404808229980239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148484194307206410973306985 111363145730404808229980239)
  ·
    refine ⟨167044718595607212344970359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111363145730404808229980239 167044718595607212344970359)
    ·
      refine ⟨250567077893410818517455539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167044718595607212344970359 250567077893410818517455539)
      ·
        refine ⟨375850616840116227776183309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250567077893410818517455539 375850616840116227776183309)
        ·
          refine ⟨140943981315043585416068741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 375850616840116227776183309 140943981315043585416068741)
          ·
            refine ⟨26426996496570672265512889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 140943981315043585416068741 26426996496570672265512889)
            ·
              refine ⟨19820247372428004199134667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26426996496570672265512889 19820247372428004199134667)
              ·
                refine ⟨29730371058642006298702001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19820247372428004199134667 29730371058642006298702001)
                ·
                  refine ⟨22297778293981504724026501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29730371058642006298702001 22297778293981504724026501)
                  ·
                    refine ⟨4180833430121532135754969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22297778293981504724026501 4180833430121532135754969)
                    ·
                      refine ⟨3135625072591149101816227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4180833430121532135754969 3135625072591149101816227)
                      ·
                        rfl

theorem cell23_6106608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 1, 2, 4, 2].length) (baseStart_6106608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6106608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6106608 prefixEnd_6106608 := by exact prefixLift 6106608
  have htrace : WordTrace (prefixWord ++ tailWord_6106608) baseStart_6106608 baseEnd_6106608 := by
    simpa [prefixWord, tailWord_6106608, baseEnd_6106608] using wordTrace_append hprefix tailTrace_6106608
  have hstable : (prefixWord ++ tailWord_6106608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6106608).length < 2 ^ (prefixWord ++ tailWord_6106608).sum := by decide
  have hdescent : baseEnd_6106608 < baseStart_6106608 := by decide
  rcases family_descends (prefixWord ++ tailWord_6106608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6106611 : List Nat := [1, 1, 1, 2, 2, 2, 2, 1, 6, 2, 3]
def baseStart_6106611 : Nat := 118140960795 + 6106611 * 2 ^ 59
def prefixEnd_6106611 : Nat := 4983230072969 + 3 ^ 40 * 6106611 * 2
def baseEnd_6106611 : Nat := 3135626613033112590078713

theorem tailTrace_6106611 : CollatzResearch.WordTrace tailWord_6106611 prefixEnd_6106611 3135626613033112590078713 := by
  unfold tailWord_6106611
  simp only [CollatzResearch.WordTrace]
  refine ⟨222726400879798747972319687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148484267253199165314879791 222726400879798747972319687)
  ·
    refine ⟨334089601319698121958479531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222726400879798747972319687 334089601319698121958479531)
    ·
      refine ⟨501134401979547182937719297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 334089601319698121958479531 501134401979547182937719297)
      ·
        refine ⟨375850801484660387203289473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 501134401979547182937719297 375850801484660387203289473)
        ·
          refine ⟨281888101113495290402467105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 375850801484660387203289473 281888101113495290402467105)
          ·
            refine ⟨211416075835121467801850329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 281888101113495290402467105 211416075835121467801850329)
            ·
              refine ⟨158562056876341100851387747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 211416075835121467801850329 158562056876341100851387747)
              ·
                refine ⟨237843085314511651277081621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 158562056876341100851387747 237843085314511651277081621)
                ·
                  refine ⟨11148894624117733653613201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 237843085314511651277081621 11148894624117733653613201)
                  ·
                    refine ⟨8361670968088300240209901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11148894624117733653613201 8361670968088300240209901)
                    ·
                      refine ⟨3135626613033112590078713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8361670968088300240209901 3135626613033112590078713)
                      ·
                        rfl

theorem cell23_6106611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 6, 2, 3].length) (baseStart_6106611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6106611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6106611 prefixEnd_6106611 := by exact prefixLift 6106611
  have htrace : WordTrace (prefixWord ++ tailWord_6106611) baseStart_6106611 baseEnd_6106611 := by
    simpa [prefixWord, tailWord_6106611, baseEnd_6106611] using wordTrace_append hprefix tailTrace_6106611
  have hstable : (prefixWord ++ tailWord_6106611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6106611).length < 2 ^ (prefixWord ++ tailWord_6106611).sum := by decide
  have hdescent : baseEnd_6106611 < baseStart_6106611 := by decide
  rcases family_descends (prefixWord ++ tailWord_6106611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6106624 : List Nat := [2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 9]
def baseStart_6106624 : Nat := 118140960795 + 6106624 * 2 ^ 59
def prefixEnd_6106624 : Nat := 4983230072969 + 3 ^ 40 * 6106624 * 2
def baseEnd_6106624 : Nat := 3135633288281621039216153

theorem tailTrace_6106624 : CollatzResearch.WordTrace tailWord_6106624 prefixEnd_6106624 3135633288281621039216153 := by
  unfold tailWord_6106624
  simp only [CollatzResearch.WordTrace]
  refine ⟨111363437514375825596271463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148484583352501100795028617 111363437514375825596271463)
  ·
    refine ⟨167045156271563738394407195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111363437514375825596271463 167045156271563738394407195)
    ·
      refine ⟨250567734407345607591610793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167045156271563738394407195 250567734407345607591610793)
      ·
        refine ⟨187925800805509205693708095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 250567734407345607591610793 187925800805509205693708095)
        ·
          refine ⟨281888701208263808540562143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187925800805509205693708095 281888701208263808540562143)
          ·
            refine ⟨422833051812395712810843215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 281888701208263808540562143 422833051812395712810843215)
            ·
              refine ⟨634249577718593569216264823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 422833051812395712810843215 634249577718593569216264823)
              ·
                refine ⟨951374366577890353824397235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 634249577718593569216264823 951374366577890353824397235)
                ·
                  refine ⟨1427061549866835530736595853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 951374366577890353824397235 1427061549866835530736595853)
                  ·
                    refine ⟨535148081200063324026223445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1427061549866835530736595853 535148081200063324026223445)
                    ·
                      refine ⟨3135633288281621039216153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 535148081200063324026223445 3135633288281621039216153)
                      ·
                        rfl

theorem cell23_6106624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 9].length) (baseStart_6106624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6106624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6106624 prefixEnd_6106624 := by exact prefixLift 6106624
  have htrace : WordTrace (prefixWord ++ tailWord_6106624) baseStart_6106624 baseEnd_6106624 := by
    simpa [prefixWord, tailWord_6106624, baseEnd_6106624] using wordTrace_append hprefix tailTrace_6106624
  have hstable : (prefixWord ++ tailWord_6106624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6106624).length < 2 ^ (prefixWord ++ tailWord_6106624).sum := by decide
  have hdescent : baseEnd_6106624 < baseStart_6106624 := by decide
  rcases family_descends (prefixWord ++ tailWord_6106624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6106631 : List Nat := [1, 1, 4, 3, 2, 1, 1, 2, 8]
def baseStart_6106631 : Nat := 118140960795 + 6106631 * 2 ^ 59
def prefixEnd_6106631 : Nat := 4983230072969 + 3 ^ 40 * 6106631 * 2
def baseEnd_6106631 : Nat := 348404098071800279092069

theorem tailTrace_6106631 : CollatzResearch.WordTrace tailWord_6106631 prefixEnd_6106631 348404098071800279092069 := by
  unfold tailWord_6106631
  simp only [CollatzResearch.WordTrace]
  refine ⟨222727130339726291388047747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148484753559817527592031831 222727130339726291388047747)
  ·
    refine ⟨334090695509589437082071621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222727130339726291388047747 334090695509589437082071621)
    ·
      refine ⟨62642005408048019452888429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 334090695509589437082071621 62642005408048019452888429)
      ·
        refine ⟨23490752028018007294833161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62642005408048019452888429 23490752028018007294833161)
        ·
          refine ⟨17618064021013505471124871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23490752028018007294833161 17618064021013505471124871)
          ·
            refine ⟨26427096031520258206687307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17618064021013505471124871 26427096031520258206687307)
            ·
              refine ⟨39640644047280387310030961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26427096031520258206687307 39640644047280387310030961)
              ·
                refine ⟨29730483035460290482523221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39640644047280387310030961 29730483035460290482523221)
                ·
                  refine ⟨348404098071800279092069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29730483035460290482523221 348404098071800279092069)
                  ·
                    rfl

theorem cell23_6106631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 2, 8].length) (baseStart_6106631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6106631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6106631 prefixEnd_6106631 := by exact prefixLift 6106631
  have htrace : WordTrace (prefixWord ++ tailWord_6106631) baseStart_6106631 baseEnd_6106631 := by
    simpa [prefixWord, tailWord_6106631, baseEnd_6106631] using wordTrace_append hprefix tailTrace_6106631
  have hstable : (prefixWord ++ tailWord_6106631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6106631).length < 2 ^ (prefixWord ++ tailWord_6106631).sum := by decide
  have hdescent : baseEnd_6106631 < baseStart_6106631 := by decide
  rcases family_descends (prefixWord ++ tailWord_6106631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6106652 : List Nat := [2, 2, 3, 1, 2, 1, 5, 2, 1, 4]
def baseStart_6106652 : Nat := 118140960795 + 6106652 * 2 ^ 59
def prefixEnd_6106652 : Nat := 4983230072969 + 3 ^ 40 * 6106652 * 2
def baseEnd_6106652 : Nat := 1045215888579982309888675

theorem tailTrace_6106652 : CollatzResearch.WordTrace tailWord_6106652 prefixEnd_6106652 1045215888579982309888675 := by
  unfold tailWord_6106652
  simp only [CollatzResearch.WordTrace]
  refine ⟨111363948136325105987281105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148485264181766807983041473 111363948136325105987281105)
  ·
    refine ⟨83522961102243829490460829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111363948136325105987281105 83522961102243829490460829)
    ·
      refine ⟨31321110413341436058922811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83522961102243829490460829 31321110413341436058922811)
      ·
        refine ⟨46981665620012154088384217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31321110413341436058922811 46981665620012154088384217)
        ·
          refine ⟨35236249215009115566288163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46981665620012154088384217 35236249215009115566288163)
          ·
            refine ⟨52854373822513673349432245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35236249215009115566288163 52854373822513673349432245)
            ·
              refine ⟨4955097545860656876509273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52854373822513673349432245 4955097545860656876509273)
              ·
                refine ⟨3716323159395492657381955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4955097545860656876509273 3716323159395492657381955)
                ·
                  refine ⟨5574484739093238986072933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3716323159395492657381955 5574484739093238986072933)
                  ·
                    refine ⟨1045215888579982309888675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5574484739093238986072933 1045215888579982309888675)
                    ·
                      rfl

theorem cell23_6106652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 5, 2, 1, 4].length) (baseStart_6106652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6106652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6106652 prefixEnd_6106652 := by exact prefixLift 6106652
  have htrace : WordTrace (prefixWord ++ tailWord_6106652) baseStart_6106652 baseEnd_6106652 := by
    simpa [prefixWord, tailWord_6106652, baseEnd_6106652] using wordTrace_append hprefix tailTrace_6106652
  have hstable : (prefixWord ++ tailWord_6106652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6106652).length < 2 ^ (prefixWord ++ tailWord_6106652).sum := by decide
  have hdescent : baseEnd_6106652 < baseStart_6106652 := by decide
  rcases family_descends (prefixWord ++ tailWord_6106652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6106661 : List Nat := [1, 3, 1, 2, 2, 1, 1, 4, 3, 5]
def baseStart_6106661 : Nat := 118140960795 + 6106661 * 2 ^ 59
def prefixEnd_6106661 : Nat := 4983230072969 + 3 ^ 40 * 6106661 * 2
def baseEnd_6106661 : Nat := 1045217429021945798151161

theorem tailTrace_6106661 : CollatzResearch.WordTrace tailWord_6106661 prefixEnd_6106661 1045217429021945798151161 := by
  unfold tailWord_6106661
  simp only [CollatzResearch.WordTrace]
  refine ⟨222728224529617606511639837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148485483019745071007759891 222728224529617606511639837)
  ·
    refine ⟨83523084198606602441864939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 222728224529617606511639837 83523084198606602441864939)
    ·
      refine ⟨125284626297909903662797409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83523084198606602441864939 125284626297909903662797409)
      ·
        refine ⟨93963469723432427747098057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125284626297909903662797409 93963469723432427747098057)
        ·
          refine ⟨70472602292574320810323543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93963469723432427747098057 70472602292574320810323543)
          ·
            refine ⟨105708903438861481215485315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70472602292574320810323543 105708903438861481215485315)
            ·
              refine ⟨158563355158292221823227973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105708903438861481215485315 158563355158292221823227973)
              ·
                refine ⟨29730629092179791591855245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 158563355158292221823227973 29730629092179791591855245)
                ·
                  refine ⟨11148985909567421846945717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29730629092179791591855245 11148985909567421846945717)
                  ·
                    refine ⟨1045217429021945798151161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11148985909567421846945717 1045217429021945798151161)
                    ·
                      rfl

theorem cell23_6106661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 4, 3, 5].length) (baseStart_6106661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6106661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6106661 prefixEnd_6106661 := by exact prefixLift 6106661
  have htrace : WordTrace (prefixWord ++ tailWord_6106661) baseStart_6106661 baseEnd_6106661 := by
    simpa [prefixWord, tailWord_6106661, baseEnd_6106661] using wordTrace_append hprefix tailTrace_6106661
  have hstable : (prefixWord ++ tailWord_6106661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6106661).length < 2 ^ (prefixWord ++ tailWord_6106661).sum := by decide
  have hdescent : baseEnd_6106661 < baseStart_6106661 := by decide
  rcases family_descends (prefixWord ++ tailWord_6106661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6106725 : List Nat := [1, 3, 1, 3, 3, 1, 2, 3, 2, 4]
def baseStart_6106725 : Nat := 118140960795 + 6106725 * 2 ^ 59
def prefixEnd_6106725 : Nat := 4983230072969 + 3 ^ 40 * 6106725 * 2
def baseEnd_6106725 : Nat := 1045228383275908381351063

theorem tailTrace_6106725 : CollatzResearch.WordTrace tailWord_6106725 prefixEnd_6106725 1045228383275908381351063 := by
  unfold tailWord_6106725
  simp only [CollatzResearch.WordTrace]
  refine ⟨222730558801385745441969629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148487039200923830294646419 222730558801385745441969629)
  ·
    refine ⟨83523959550519654540738611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 222730558801385745441969629 83523959550519654540738611)
    ·
      refine ⟨125285939325779481811107917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83523959550519654540738611 125285939325779481811107917)
      ·
        refine ⟨46982227247167305679165469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125285939325779481811107917 46982227247167305679165469)
        ·
          refine ⟨17618335217687739629687051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46982227247167305679165469 17618335217687739629687051)
          ·
            refine ⟨26427502826531609444530577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17618335217687739629687051 26427502826531609444530577)
            ·
              refine ⟨19820627119898707083397933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26427502826531609444530577 19820627119898707083397933)
              ·
                refine ⟨7432735169962015156274225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19820627119898707083397933 7432735169962015156274225)
                ·
                  refine ⟨5574551377471511367205669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7432735169962015156274225 5574551377471511367205669)
                  ·
                    refine ⟨1045228383275908381351063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5574551377471511367205669 1045228383275908381351063)
                    ·
                      rfl

theorem cell23_6106725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 3, 2, 4].length) (baseStart_6106725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6106725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6106725 prefixEnd_6106725 := by exact prefixLift 6106725
  have htrace : WordTrace (prefixWord ++ tailWord_6106725) baseStart_6106725 baseEnd_6106725 := by
    simpa [prefixWord, tailWord_6106725, baseEnd_6106725] using wordTrace_append hprefix tailTrace_6106725
  have hstable : (prefixWord ++ tailWord_6106725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6106725).length < 2 ^ (prefixWord ++ tailWord_6106725).sum := by decide
  have hdescent : baseEnd_6106725 < baseStart_6106725 := by decide
  rcases family_descends (prefixWord ++ tailWord_6106725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6106749 : List Nat := [1, 4, 1, 1, 4, 1, 1, 5, 1, 2, 2]
def baseStart_6106749 : Nat := 118140960795 + 6106749 * 2 ^ 59
def prefixEnd_6106749 : Nat := 4983230072969 + 3 ^ 40 * 6106749 * 2
def baseEnd_6106749 : Nat := 3135697473363433050153079

theorem tailTrace_6106749 : CollatzResearch.WordTrace tailWord_6106749 prefixEnd_6106749 3135697473363433050153079 := by
  unfold tailWord_6106749
  simp only [CollatzResearch.WordTrace]
  refine ⟨222731434153298797540843301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148487622768865865027228867 222731434153298797540843301)
  ·
    refine ⟨41762143903743524538908119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 222731434153298797540843301 41762143903743524538908119)
    ·
      refine ⟨62643215855615286808362179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41762143903743524538908119 62643215855615286808362179)
      ·
        refine ⟨93964823783422930212543269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62643215855615286808362179 93964823783422930212543269)
        ·
          refine ⟨17618404459391799414851863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93964823783422930212543269 17618404459391799414851863)
          ·
            refine ⟨26427606689087699122277795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17618404459391799414851863 26427606689087699122277795)
            ·
              refine ⟨39641410033631548683416693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26427606689087699122277795 39641410033631548683416693)
              ·
                refine ⟨3716382190652957689070315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39641410033631548683416693 3716382190652957689070315)
                ·
                  refine ⟨5574573285979436533605473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3716382190652957689070315 5574573285979436533605473)
                  ·
                    refine ⟨4180929964484577400204105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5574573285979436533605473 4180929964484577400204105)
                    ·
                      refine ⟨3135697473363433050153079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4180929964484577400204105 3135697473363433050153079)
                      ·
                        rfl

theorem cell23_6106749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 5, 1, 2, 2].length) (baseStart_6106749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6106749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6106749 prefixEnd_6106749 := by exact prefixLift 6106749
  have htrace : WordTrace (prefixWord ++ tailWord_6106749) baseStart_6106749 baseEnd_6106749 := by
    simpa [prefixWord, tailWord_6106749, baseEnd_6106749] using wordTrace_append hprefix tailTrace_6106749
  have hstable : (prefixWord ++ tailWord_6106749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6106749).length < 2 ^ (prefixWord ++ tailWord_6106749).sum := by decide
  have hdescent : baseEnd_6106749 < baseStart_6106749 := by decide
  rcases family_descends (prefixWord ++ tailWord_6106749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6106782 : List Nat := [4, 3, 1, 1, 1, 2, 3, 1, 1, 3, 3]
def baseStart_6106782 : Nat := 118140960795 + 6106782 * 2 ^ 59
def prefixEnd_6106782 : Nat := 4983230072969 + 3 ^ 40 * 6106782 * 2
def baseEnd_6106782 : Nat := 3135714418225031421040427

theorem tailTrace_6106782 : CollatzResearch.WordTrace tailWord_6106782 prefixEnd_6106782 3135714418225031421040427 := by
  unfold tailWord_6106782
  simp only [CollatzResearch.WordTrace]
  refine ⟨27841579720272405522099325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148488425174786162784529733 27841579720272405522099325)
  ·
    refine ⟨10440592395102152070787247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27841579720272405522099325 10440592395102152070787247)
    ·
      refine ⟨15660888592653228106180871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10440592395102152070787247 15660888592653228106180871)
      ·
        refine ⟨23491332888979842159271307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15660888592653228106180871 23491332888979842159271307)
        ·
          refine ⟨35236999333469763238906961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23491332888979842159271307 35236999333469763238906961)
          ·
            refine ⟨26427749500102322429180221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35236999333469763238906961 26427749500102322429180221)
            ·
              refine ⟨9910406062538370910942583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26427749500102322429180221 9910406062538370910942583)
              ·
                refine ⟨14865609093807556366413875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9910406062538370910942583 14865609093807556366413875)
                ·
                  refine ⟨22298413640711334549620813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14865609093807556366413875 22298413640711334549620813)
                  ·
                    refine ⟨8361905115266750456107805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22298413640711334549620813 8361905115266750456107805)
                    ·
                      refine ⟨3135714418225031421040427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8361905115266750456107805 3135714418225031421040427)
                      ·
                        rfl

theorem cell23_6106782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 3, 1, 1, 3, 3].length) (baseStart_6106782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6106782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6106782 prefixEnd_6106782 := by exact prefixLift 6106782
  have htrace : WordTrace (prefixWord ++ tailWord_6106782) baseStart_6106782 baseEnd_6106782 := by
    simpa [prefixWord, tailWord_6106782, baseEnd_6106782] using wordTrace_append hprefix tailTrace_6106782
  have hstable : (prefixWord ++ tailWord_6106782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6106782).length < 2 ^ (prefixWord ++ tailWord_6106782).sum := by decide
  have hdescent : baseEnd_6106782 < baseStart_6106782 := by decide
  rcases family_descends (prefixWord ++ tailWord_6106782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6106811 : List Nat := [1, 1, 1, 1, 1, 2, 3, 4, 9]
def baseStart_6106811 : Nat := 118140960795 + 6106811 * 2 ^ 59
def prefixEnd_6106811 : Nat := 4983230072969 + 3 ^ 40 * 6106811 * 2
def baseEnd_6106811 : Nat := 348414367684890200841977

theorem tailTrace_6106811 : CollatzResearch.WordTrace tailWord_6106811 prefixEnd_6106811 348414367684890200841977 := by
  unfold tailWord_6106811
  simp only [CollatzResearch.WordTrace]
  refine ⟨222733695479074182129600287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148489130319382788086400191 222733695479074182129600287)
  ·
    refine ⟨334100543218611273194400431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222733695479074182129600287 334100543218611273194400431)
    ·
      refine ⟨501150814827916909791600647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 334100543218611273194400431 501150814827916909791600647)
      ·
        refine ⟨751726222241875364687400971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 501150814827916909791600647 751726222241875364687400971)
        ·
          refine ⟨1127589333362813047031101457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 751726222241875364687400971 1127589333362813047031101457)
          ·
            refine ⟨845692000022109785273326093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1127589333362813047031101457 845692000022109785273326093)
            ·
              refine ⟨317134500008291169477497285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 845692000022109785273326093 317134500008291169477497285)
              ·
                refine ⟨59462718751554594277030741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 317134500008291169477497285 59462718751554594277030741)
                ·
                  refine ⟨348414367684890200841977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 59462718751554594277030741 348414367684890200841977)
                  ·
                    rfl

theorem cell23_6106811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 9].length) (baseStart_6106811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6106811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6106811 prefixEnd_6106811 := by exact prefixLift 6106811
  have htrace : WordTrace (prefixWord ++ tailWord_6106811) baseStart_6106811 baseEnd_6106811 := by
    simpa [prefixWord, tailWord_6106811, baseEnd_6106811] using wordTrace_append hprefix tailTrace_6106811
  have hstable : (prefixWord ++ tailWord_6106811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6106811).length < 2 ^ (prefixWord ++ tailWord_6106811).sum := by decide
  have hdescent : baseEnd_6106811 < baseStart_6106811 := by decide
  rcases family_descends (prefixWord ++ tailWord_6106811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6106858 : List Nat := [3, 1, 3, 1, 1, 1, 2, 3, 1, 7]
def baseStart_6106858 : Nat := 118140960795 + 6106858 * 2 ^ 59
def prefixEnd_6106858 : Nat := 4983230072969 + 3 ^ 40 * 6106858 * 2
def baseEnd_6106858 : Nat := 1045251147584924374563359

theorem tailTrace_6106858 : CollatzResearch.WordTrace tailWord_6106858 prefixEnd_6106858 1045251147584924374563359 := by
  unfold tailWord_6106858
  simp only [CollatzResearch.WordTrace]
  refine ⟨55683852427475977289140307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148490273139935939437707485 55683852427475977289140307)
  ·
    refine ⟨83525778641213965933710461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55683852427475977289140307 83525778641213965933710461)
    ·
      refine ⟨31322166990455237225141423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83525778641213965933710461 31322166990455237225141423)
      ·
        refine ⟨46983250485682855837712135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31322166990455237225141423 46983250485682855837712135)
        ·
          refine ⟨70474875728524283756568203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46983250485682855837712135 70474875728524283756568203)
          ·
            refine ⟨105712313592786425634852305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70474875728524283756568203 105712313592786425634852305)
            ·
              refine ⟨79284235194589819226139229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105712313592786425634852305 79284235194589819226139229)
              ·
                refine ⟨29731588197971182209802211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79284235194589819226139229 29731588197971182209802211)
                ·
                  refine ⟨44597382296956773314703317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29731588197971182209802211 44597382296956773314703317)
                  ·
                    refine ⟨1045251147584924374563359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44597382296956773314703317 1045251147584924374563359)
                    ·
                      rfl

theorem cell23_6106858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 3, 1, 7].length) (baseStart_6106858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6106858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6106858 prefixEnd_6106858 := by exact prefixLift 6106858
  have htrace : WordTrace (prefixWord ++ tailWord_6106858) baseStart_6106858 baseEnd_6106858 := by
    simpa [prefixWord, tailWord_6106858, baseEnd_6106858] using wordTrace_append hprefix tailTrace_6106858
  have hstable : (prefixWord ++ tailWord_6106858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6106858).length < 2 ^ (prefixWord ++ tailWord_6106858).sum := by decide
  have hdescent : baseEnd_6106858 < baseStart_6106858 := by decide
  rcases family_descends (prefixWord ++ tailWord_6106858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6106882 : List Nat := [3, 4, 1, 1, 1, 1, 1, 1, 1, 7, 2]
def baseStart_6106882 : Nat := 118140960795 + 6106882 * 2 ^ 59
def prefixEnd_6106882 : Nat := 4983230072969 + 3 ^ 40 * 6106882 * 2
def baseEnd_6106882 : Nat := 3135765766290481029789967

theorem tailTrace_6106882 : CollatzResearch.WordTrace tailWord_6106882 prefixEnd_6106882 3135765766290481029789967 := by
  unfold tailWord_6106882
  simp only [CollatzResearch.WordTrace]
  refine ⟨55684071265454240313858725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148490856707877974170289933 55684071265454240313858725)
  ·
    refine ⟨10440763362272670058848511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55684071265454240313858725 10440763362272670058848511)
    ·
      refine ⟨15661145043409005088272767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10440763362272670058848511 15661145043409005088272767)
      ·
        refine ⟨23491717565113507632409151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15661145043409005088272767 23491717565113507632409151)
        ·
          refine ⟨35237576347670261448613727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23491717565113507632409151 35237576347670261448613727)
          ·
            refine ⟨52856364521505392172920591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35237576347670261448613727 52856364521505392172920591)
            ·
              refine ⟨79284546782258088259380887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52856364521505392172920591 79284546782258088259380887)
              ·
                refine ⟨118926820173387132389071331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79284546782258088259380887 118926820173387132389071331)
                ·
                  refine ⟨178390230260080698583606997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 118926820173387132389071331 178390230260080698583606997)
                  ·
                    refine ⟨4181021021720641373053289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 178390230260080698583606997 4181021021720641373053289)
                    ·
                      refine ⟨3135765766290481029789967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4181021021720641373053289 3135765766290481029789967)
                      ·
                        rfl

theorem cell23_6106882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 1, 7, 2].length) (baseStart_6106882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6106882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6106882 prefixEnd_6106882 := by exact prefixLift 6106882
  have htrace : WordTrace (prefixWord ++ tailWord_6106882) baseStart_6106882 baseEnd_6106882 := by
    simpa [prefixWord, tailWord_6106882, baseEnd_6106882] using wordTrace_append hprefix tailTrace_6106882
  have hstable : (prefixWord ++ tailWord_6106882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6106882).length < 2 ^ (prefixWord ++ tailWord_6106882).sum := by decide
  have hdescent : baseEnd_6106882 < baseStart_6106882 := by decide
  rcases family_descends (prefixWord ++ tailWord_6106882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6106952 : List Nat := [2, 1, 3, 1, 1, 5, 3, 1, 6]
def baseStart_6106952 : Nat := 118140960795 + 6106952 * 2 ^ 59
def prefixEnd_6106952 : Nat := 4983230072969 + 3 ^ 40 * 6106952 * 2
def baseEnd_6106952 : Nat := 348422412215143972879405

theorem tailTrace_6106952 : CollatzResearch.WordTrace tailWord_6106952 prefixEnd_6106952 348422412215143972879405 := by
  unfold tailWord_6106952
  simp only [CollatzResearch.WordTrace]
  refine ⟨111369419085781681605241555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148492558781042242140322073 111369419085781681605241555)
  ·
    refine ⟨167054128628672522407862333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111369419085781681605241555 167054128628672522407862333)
    ·
      refine ⟨62645298235752195902948375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167054128628672522407862333 62645298235752195902948375)
      ·
        refine ⟨93967947353628293854422563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62645298235752195902948375 93967947353628293854422563)
        ·
          refine ⟨140951921030442440781633845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93967947353628293854422563 140951921030442440781633845)
          ·
            refine ⟨13214242596603978823278173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 140951921030442440781633845 13214242596603978823278173)
            ·
              refine ⟨4955340973726492058729315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13214242596603978823278173 4955340973726492058729315)
              ·
                refine ⟨7433011460589738088093973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4955340973726492058729315 7433011460589738088093973)
                ·
                  refine ⟨348422412215143972879405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7433011460589738088093973 348422412215143972879405)
                  ·
                    rfl

theorem cell23_6106952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 3, 1, 6].length) (baseStart_6106952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6106952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6106952 prefixEnd_6106952 := by exact prefixLift 6106952
  have htrace : WordTrace (prefixWord ++ tailWord_6106952) baseStart_6106952 baseEnd_6106952 := by
    simpa [prefixWord, tailWord_6106952, baseEnd_6106952] using wordTrace_append hprefix tailTrace_6106952
  have hstable : (prefixWord ++ tailWord_6106952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6106952).length < 2 ^ (prefixWord ++ tailWord_6106952).sum := by decide
  have hdescent : baseEnd_6106952 < baseStart_6106952 := by decide
  rcases family_descends (prefixWord ++ tailWord_6106952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6107005 : List Nat := [1, 4, 1, 1, 2, 1, 1, 1, 2, 6, 3]
def baseStart_6107005 : Nat := 118140960795 + 6107005 * 2 ^ 59
def prefixEnd_6107005 : Nat := 4983230072969 + 3 ^ 40 * 6107005 * 2
def baseEnd_6107005 : Nat := 3135828924410984048551901

theorem tailTrace_6107005 : CollatzResearch.WordTrace tailWord_6107005 prefixEnd_6107005 3135828924410984048551901 := by
  unfold tailWord_6107005
  simp only [CollatzResearch.WordTrace]
  refine ⟨222740771240371353262162469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148493847493580902174774979 222740771240371353262162469)
  ·
    refine ⟨41763894607569628736655463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 222740771240371353262162469 41763894607569628736655463)
    ·
      refine ⟨62645841911354443104983195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41763894607569628736655463 62645841911354443104983195)
      ·
        refine ⟨93968762867031664657474793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62645841911354443104983195 93968762867031664657474793)
        ·
          refine ⟨70476572150273748493106095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93968762867031664657474793 70476572150273748493106095)
          ·
            refine ⟨105714858225410622739659143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70476572150273748493106095 105714858225410622739659143)
            ·
              refine ⟨158572287338115934109488715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105714858225410622739659143 158572287338115934109488715)
              ·
                refine ⟨237858431007173901164233073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 158572287338115934109488715 237858431007173901164233073)
                ·
                  refine ⟨178393823255380425873174805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 237858431007173901164233073 178393823255380425873174805)
                  ·
                    refine ⟨8362210465095957462805069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 178393823255380425873174805 8362210465095957462805069)
                    ·
                      refine ⟨3135828924410984048551901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8362210465095957462805069 3135828924410984048551901)
                      ·
                        rfl

theorem cell23_6107005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 6, 3].length) (baseStart_6107005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6107005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6107005 prefixEnd_6107005 := by exact prefixLift 6107005
  have htrace : WordTrace (prefixWord ++ tailWord_6107005) baseStart_6107005 baseEnd_6107005 := by
    simpa [prefixWord, tailWord_6107005, baseEnd_6107005] using wordTrace_append hprefix tailTrace_6107005
  have hstable : (prefixWord ++ tailWord_6107005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6107005).length < 2 ^ (prefixWord ++ tailWord_6107005).sum := by decide
  have hdescent : baseEnd_6107005 < baseStart_6107005 := by decide
  rcases family_descends (prefixWord ++ tailWord_6107005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6107016 : List Nat := [2, 1, 3, 3, 4, 1, 1, 2, 1, 5]
def baseStart_6107016 : Nat := 118140960795 + 6107016 * 2 ^ 59
def prefixEnd_6107016 : Nat := 4983230072969 + 3 ^ 40 * 6107016 * 2
def baseEnd_6107016 : Nat := 1045278190899394501838117

theorem tailTrace_6107016 : CollatzResearch.WordTrace tailWord_6107016 prefixEnd_6107016 1045278190899394501838117 := by
  unfold tailWord_6107016
  simp only [CollatzResearch.WordTrace]
  refine ⟨111370586221665751070406451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148494114962221001427208601 111370586221665751070406451)
  ·
    refine ⟨167055879332498626605609677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111370586221665751070406451 167055879332498626605609677)
    ·
      refine ⟨62645954749686984977103629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167055879332498626605609677 62645954749686984977103629)
      ·
        refine ⟨23492233031132619366413861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62645954749686984977103629 23492233031132619366413861)
        ·
          refine ⟨4404793693337366131202599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23492233031132619366413861 4404793693337366131202599)
          ·
            refine ⟨6607190540006049196803899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4404793693337366131202599 6607190540006049196803899)
            ·
              refine ⟨9910785810009073795205849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6607190540006049196803899 9910785810009073795205849)
              ·
                refine ⟨7433089357506805346404387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9910785810009073795205849 7433089357506805346404387)
                ·
                  refine ⟨11149634036260208019606581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7433089357506805346404387 11149634036260208019606581)
                  ·
                    refine ⟨1045278190899394501838117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11149634036260208019606581 1045278190899394501838117)
                    ·
                      rfl

theorem cell23_6107016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 1, 2, 1, 5].length) (baseStart_6107016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6107016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6107016 prefixEnd_6107016 := by exact prefixLift 6107016
  have htrace : WordTrace (prefixWord ++ tailWord_6107016) baseStart_6107016 baseEnd_6107016 := by
    simpa [prefixWord, tailWord_6107016, baseEnd_6107016] using wordTrace_append hprefix tailTrace_6107016
  have hstable : (prefixWord ++ tailWord_6107016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6107016).length < 2 ^ (prefixWord ++ tailWord_6107016).sum := by decide
  have hdescent : baseEnd_6107016 < baseStart_6107016 := by decide
  rcases family_descends (prefixWord ++ tailWord_6107016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6107036 : List Nat := [2, 2, 3, 3, 1, 2, 3, 1, 1, 1, 4]
def baseStart_6107036 : Nat := 118140960795 + 6107036 * 2 ^ 59
def prefixEnd_6107036 : Nat := 4983230072969 + 3 ^ 40 * 6107036 * 2
def baseEnd_6107036 : Nat := 3135844842311273427264259

theorem tailTrace_6107036 : CollatzResearch.WordTrace tailWord_6107036 prefixEnd_6107036 3135844842311273427264259 := by
  unfold tailWord_6107036
  simp only [CollatzResearch.WordTrace]
  refine ⟨111370950951629522778270481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148494601268839363704360641 111370950951629522778270481)
  ·
    refine ⟨83528213213722142083702861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111370950951629522778270481 83528213213722142083702861)
    ·
      refine ⟨31323079955145803281388573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83528213213722142083702861 31323079955145803281388573)
      ·
        refine ⟨11746154983179676230520715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31323079955145803281388573 11746154983179676230520715)
        ·
          refine ⟨17619232474769514345781073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11746154983179676230520715 17619232474769514345781073)
          ·
            refine ⟨13214424356077135759335805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17619232474769514345781073 13214424356077135759335805)
            ·
              refine ⟨4955409133528925909750927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13214424356077135759335805 4955409133528925909750927)
              ·
                refine ⟨7433113700293388864626391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4955409133528925909750927 7433113700293388864626391)
                ·
                  refine ⟨11149670550440083296939587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7433113700293388864626391 11149670550440083296939587)
                  ·
                    refine ⟨16724505825660124945409381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11149670550440083296939587 16724505825660124945409381)
                    ·
                      refine ⟨3135844842311273427264259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16724505825660124945409381 3135844842311273427264259)
                      ·
                        rfl

theorem cell23_6107036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 3, 1, 1, 1, 4].length) (baseStart_6107036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6107036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6107036 prefixEnd_6107036 := by exact prefixLift 6107036
  have htrace : WordTrace (prefixWord ++ tailWord_6107036) baseStart_6107036 baseEnd_6107036 := by
    simpa [prefixWord, tailWord_6107036, baseEnd_6107036] using wordTrace_append hprefix tailTrace_6107036
  have hstable : (prefixWord ++ tailWord_6107036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6107036).length < 2 ^ (prefixWord ++ tailWord_6107036).sum := by decide
  have hdescent : baseEnd_6107036 < baseStart_6107036 := by decide
  rcases family_descends (prefixWord ++ tailWord_6107036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6107039 : List Nat := [1, 1, 2, 5, 3, 2, 1, 1, 1, 1, 5]
def baseStart_6107039 : Nat := 118140960795 + 6107039 * 2 ^ 59
def prefixEnd_6107039 : Nat := 4983230072969 + 3 ^ 40 * 6107039 * 2
def baseEnd_6107039 : Nat := 3135846382753236915526745

theorem tailTrace_6107039 : CollatzResearch.WordTrace tailWord_6107039 prefixEnd_6107039 3135846382753236915526745 := by
  unfold tailWord_6107039
  simp only [CollatzResearch.WordTrace]
  refine ⟨222742011322248177068900171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148494674214832118045933447 222742011322248177068900171)
  ·
    refine ⟨334113016983372265603350257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222742011322248177068900171 334113016983372265603350257)
    ·
      refine ⟨250584762737529199202512693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 334113016983372265603350257 250584762737529199202512693)
      ·
        refine ⟨23492321506643362425235565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 250584762737529199202512693 23492321506643362425235565)
        ·
          refine ⟨8809620564991260909463337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23492321506643362425235565 8809620564991260909463337)
          ·
            refine ⟨6607215423743445682097503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8809620564991260909463337 6607215423743445682097503)
            ·
              refine ⟨9910823135615168523146255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6607215423743445682097503 9910823135615168523146255)
              ·
                refine ⟨14866234703422752784719383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9910823135615168523146255 14866234703422752784719383)
                ·
                  refine ⟨22299352055134129177079075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14866234703422752784719383 22299352055134129177079075)
                  ·
                    refine ⟨33449028082701193765618613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22299352055134129177079075 33449028082701193765618613)
                    ·
                      refine ⟨3135846382753236915526745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33449028082701193765618613 3135846382753236915526745)
                      ·
                        rfl

theorem cell23_6107039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 1, 1, 1, 1, 5].length) (baseStart_6107039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6107039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6107039 prefixEnd_6107039 := by exact prefixLift 6107039
  have htrace : WordTrace (prefixWord ++ tailWord_6107039) baseStart_6107039 baseEnd_6107039 := by
    simpa [prefixWord, tailWord_6107039, baseEnd_6107039] using wordTrace_append hprefix tailTrace_6107039
  have hstable : (prefixWord ++ tailWord_6107039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6107039).length < 2 ^ (prefixWord ++ tailWord_6107039).sum := by decide
  have hdescent : baseEnd_6107039 < baseStart_6107039 := by decide
  rcases family_descends (prefixWord ++ tailWord_6107039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6107042 : List Nat := [3, 3, 1, 2, 4, 10]
def baseStart_6107042 : Nat := 118140960795 + 6107042 * 2 ^ 59
def prefixEnd_6107042 : Nat := 4983230072969 + 3 ^ 40 * 6107042 * 2
def baseEnd_6107042 : Nat := 12904723963766256805717

theorem tailTrace_6107042 : CollatzResearch.WordTrace tailWord_6107042 prefixEnd_6107042 12904723963766256805717 := by
  unfold tailWord_6107042
  simp only [CollatzResearch.WordTrace]
  refine ⟨55685530185309327145314845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148494747160824872387506253 55685530185309327145314845)
  ·
    refine ⟨20882073819490997679493067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55685530185309327145314845 20882073819490997679493067)
    ·
      refine ⟨31323110729236496519239601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20882073819490997679493067 31323110729236496519239601)
      ·
        refine ⟨23492333046927372389429701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31323110729236496519239601 23492333046927372389429701)
        ·
          refine ⟨4404812446298882323018069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23492333046927372389429701 4404812446298882323018069)
          ·
            refine ⟨12904723963766256805717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4404812446298882323018069 12904723963766256805717)
            ·
              rfl

theorem cell23_6107042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 10].length) (baseStart_6107042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6107042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6107042 prefixEnd_6107042 := by exact prefixLift 6107042
  have htrace : WordTrace (prefixWord ++ tailWord_6107042) baseStart_6107042 baseEnd_6107042 := by
    simpa [prefixWord, tailWord_6107042, baseEnd_6107042] using wordTrace_append hprefix tailTrace_6107042
  have hstable : (prefixWord ++ tailWord_6107042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6107042).length < 2 ^ (prefixWord ++ tailWord_6107042).sum := by decide
  have hdescent : baseEnd_6107042 < baseStart_6107042 := by decide
  rcases family_descends (prefixWord ++ tailWord_6107042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6107069 : List Nat := [1, 4, 1, 2, 3, 2, 2, 1, 1, 3, 3]
def baseStart_6107069 : Nat := 118140960795 + 6107069 * 2 ^ 59
def prefixEnd_6107069 : Nat := 4983230072969 + 3 ^ 40 * 6107069 * 2
def baseEnd_6107069 : Nat := 3135861787172871798151607

theorem tailTrace_6107069 : CollatzResearch.WordTrace tailWord_6107069 prefixEnd_6107069 3135861787172871798151607 := by
  unfold tailWord_6107069
  simp only [CollatzResearch.WordTrace]
  refine ⟨222743105512139492192492261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148495403674759661461661507 222743105512139492192492261)
  ·
    refine ⟨41764332283526154786092299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 222743105512139492192492261 41764332283526154786092299)
    ·
      refine ⟨62646498425289232179138449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41764332283526154786092299 62646498425289232179138449)
      ·
        refine ⟨46984873818966924134353837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62646498425289232179138449 46984873818966924134353837)
        ·
          refine ⟨17619327682112596550382689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46984873818966924134353837 17619327682112596550382689)
          ·
            refine ⟨13214495761584447412787017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17619327682112596550382689 13214495761584447412787017)
            ·
              refine ⟨9910871821188335559590263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13214495761584447412787017 9910871821188335559590263)
              ·
                refine ⟨14866307731782503339385395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9910871821188335559590263 14866307731782503339385395)
                ·
                  refine ⟨22299461597673755009078093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14866307731782503339385395 22299461597673755009078093)
                  ·
                    refine ⟨8362298099127658128404285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22299461597673755009078093 8362298099127658128404285)
                    ·
                      refine ⟨3135861787172871798151607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8362298099127658128404285 3135861787172871798151607)
                      ·
                        rfl

theorem cell23_6107069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 2, 1, 1, 3, 3].length) (baseStart_6107069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6107069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6107069 prefixEnd_6107069 := by exact prefixLift 6107069
  have htrace : WordTrace (prefixWord ++ tailWord_6107069) baseStart_6107069 baseEnd_6107069 := by
    simpa [prefixWord, tailWord_6107069, baseEnd_6107069] using wordTrace_append hprefix tailTrace_6107069
  have hstable : (prefixWord ++ tailWord_6107069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6107069).length < 2 ^ (prefixWord ++ tailWord_6107069).sum := by decide
  have hdescent : baseEnd_6107069 < baseStart_6107069 := by decide
  rcases family_descends (prefixWord ++ tailWord_6107069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6107079 : List Nat := [1, 1, 4, 1, 1, 2, 1, 6, 1, 3, 2]
def baseStart_6107079 : Nat := 118140960795 + 6107079 * 2 ^ 59
def prefixEnd_6107079 : Nat := 4983230072969 + 3 ^ 40 * 6107079 * 2
def baseEnd_6107079 : Nat := 3135866921979416759026561

theorem tailTrace_6107079 : CollatzResearch.WordTrace tailWord_6107079 prefixEnd_6107079 3135866921979416759026561 := by
  unfold tailWord_6107079
  simp only [CollatzResearch.WordTrace]
  refine ⟨222743470242103263900356291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148495646828068842600237527 222743470242103263900356291)
  ·
    refine ⟨334115205363154895850534437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222743470242103263900356291 334115205363154895850534437)
    ·
      refine ⟨62646601005591542971975207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 334115205363154895850534437 62646601005591542971975207)
      ·
        refine ⟨93969901508387314457962811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62646601005591542971975207 93969901508387314457962811)
        ·
          refine ⟨140954852262580971686944217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93969901508387314457962811 140954852262580971686944217)
          ·
            refine ⟨105716139196935728765208163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140954852262580971686944217 105716139196935728765208163)
            ·
              refine ⟨158574208795403593147812245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105716139196935728765208163 158574208795403593147812245)
              ·
                refine ⟨7433166037284543428803699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 158574208795403593147812245 7433166037284543428803699)
                ·
                  refine ⟨11149749055926815143205549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7433166037284543428803699 11149749055926815143205549)
                  ·
                    refine ⟨4181155895972555678702081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11149749055926815143205549 4181155895972555678702081)
                    ·
                      refine ⟨3135866921979416759026561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4181155895972555678702081 3135866921979416759026561)
                      ·
                        rfl

theorem cell23_6107079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 6, 1, 3, 2].length) (baseStart_6107079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6107079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6107079 prefixEnd_6107079 := by exact prefixLift 6107079
  have htrace : WordTrace (prefixWord ++ tailWord_6107079) baseStart_6107079 baseEnd_6107079 := by
    simpa [prefixWord, tailWord_6107079, baseEnd_6107079] using wordTrace_append hprefix tailTrace_6107079
  have hstable : (prefixWord ++ tailWord_6107079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6107079).length < 2 ^ (prefixWord ++ tailWord_6107079).sum := by decide
  have hdescent : baseEnd_6107079 < baseStart_6107079 := by decide
  rcases family_descends (prefixWord ++ tailWord_6107079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6107090 : List Nat := [3, 2, 2, 3, 3, 1, 2, 1, 1, 2, 3]
def baseStart_6107090 : Nat := 118140960795 + 6107090 * 2 ^ 59
def prefixEnd_6107090 : Nat := 4983230072969 + 3 ^ 40 * 6107090 * 2
def baseEnd_6107090 : Nat := 3135872570266616215989011

theorem tailTrace_6107090 : CollatzResearch.WordTrace tailWord_6107090 prefixEnd_6107090 3135872570266616215989011 := by
  unfold tailWord_6107090
  simp only [CollatzResearch.WordTrace]
  refine ⟨55685967861265853194751681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148495914296708941852671149 55685967861265853194751681)
  ·
    refine ⟨41764475895949389896063761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55685967861265853194751681 41764475895949389896063761)
    ·
      refine ⟨31323356921962042422047821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41764475895949389896063761 31323356921962042422047821)
      ·
        refine ⟨11746258845735765908267933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31323356921962042422047821 11746258845735765908267933)
        ·
          refine ⟨4404847067150912215600475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11746258845735765908267933 4404847067150912215600475)
          ·
            refine ⟨6607270600726368323400713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4404847067150912215600475 6607270600726368323400713)
            ·
              refine ⟨4955452950544776242550535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6607270600726368323400713 4955452950544776242550535)
              ·
                refine ⟨7433179425817164363825803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4955452950544776242550535 7433179425817164363825803)
                ·
                  refine ⟨11149769138725746545738705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7433179425817164363825803 11149769138725746545738705)
                  ·
                    refine ⟨8362326854044309909304029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11149769138725746545738705 8362326854044309909304029)
                    ·
                      refine ⟨3135872570266616215989011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8362326854044309909304029 3135872570266616215989011)
                      ·
                        rfl

theorem cell23_6107090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 2, 1, 1, 2, 3].length) (baseStart_6107090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6107090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6107090 prefixEnd_6107090 := by exact prefixLift 6107090
  have htrace : WordTrace (prefixWord ++ tailWord_6107090) baseStart_6107090 baseEnd_6107090 := by
    simpa [prefixWord, tailWord_6107090, baseEnd_6107090] using wordTrace_append hprefix tailTrace_6107090
  have hstable : (prefixWord ++ tailWord_6107090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6107090).length < 2 ^ (prefixWord ++ tailWord_6107090).sum := by decide
  have hdescent : baseEnd_6107090 < baseStart_6107090 := by decide
  rcases family_descends (prefixWord ++ tailWord_6107090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6107095 : List Nat := [1, 1, 3, 2, 1, 1, 4, 1, 1, 3, 5]
def baseStart_6107095 : Nat := 118140960795 + 6107095 * 2 ^ 59
def prefixEnd_6107095 : Nat := 4983230072969 + 3 ^ 40 * 6107095 * 2
def baseEnd_6107095 : Nat := 3135875137669888696426487

theorem tailTrace_6107095 : CollatzResearch.WordTrace tailWord_6107095 prefixEnd_6107095 3135875137669888696426487 := by
  unfold tailWord_6107095
  simp only [CollatzResearch.WordTrace]
  refine ⟨222744053810045298632938739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148496035873363532421959159 222744053810045298632938739)
  ·
    refine ⟨334116080715067947949408109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222744053810045298632938739 334116080715067947949408109)
    ·
      refine ⟨125293530268150480481028041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 334116080715067947949408109 125293530268150480481028041)
      ·
        refine ⟨93970147701112860360771031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125293530268150480481028041 93970147701112860360771031)
        ·
          refine ⟨140955221551669290541156547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93970147701112860360771031 140955221551669290541156547)
          ·
            refine ⟨211432832327503935811734821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140955221551669290541156547 211432832327503935811734821)
            ·
              refine ⟨39643656061406987964700279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 211432832327503935811734821 39643656061406987964700279)
              ·
                refine ⟨59465484092110481947050419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39643656061406987964700279 59465484092110481947050419)
                ·
                  refine ⟨89198226138165722920575629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59465484092110481947050419 89198226138165722920575629)
                  ·
                    refine ⟨33449334801812146095215861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 89198226138165722920575629 33449334801812146095215861)
                    ·
                      refine ⟨3135875137669888696426487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33449334801812146095215861 3135875137669888696426487)
                      ·
                        rfl

theorem cell23_6107095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 1, 1, 3, 5].length) (baseStart_6107095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6107095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6107095 prefixEnd_6107095 := by exact prefixLift 6107095
  have htrace : WordTrace (prefixWord ++ tailWord_6107095) baseStart_6107095 baseEnd_6107095 := by
    simpa [prefixWord, tailWord_6107095, baseEnd_6107095] using wordTrace_append hprefix tailTrace_6107095
  have hstable : (prefixWord ++ tailWord_6107095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6107095).length < 2 ^ (prefixWord ++ tailWord_6107095).sum := by decide
  have hdescent : baseEnd_6107095 < baseStart_6107095 := by decide
  rcases family_descends (prefixWord ++ tailWord_6107095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6107162 : List Nat := [3, 1, 1, 3, 1, 3, 1, 1, 4, 5]
def baseStart_6107162 : Nat := 118140960795 + 6107162 * 2 ^ 59
def prefixEnd_6107162 : Nat := 4983230072969 + 3 ^ 40 * 6107162 * 2
def baseEnd_6107162 : Nat := 1045303180291246644762893

theorem tailTrace_6107162 : CollatzResearch.WordTrace tailWord_6107162 prefixEnd_6107162 1045303180291246644762893 := by
  unfold tailWord_6107162
  simp only [CollatzResearch.WordTrace]
  refine ⟨55686624375200642268906935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148497665000535046050418493 55686624375200642268906935)
  ·
    refine ⟨83529936562800963403360403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55686624375200642268906935 83529936562800963403360403)
    ·
      refine ⟨125294904844201445105040605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83529936562800963403360403 125294904844201445105040605)
      ·
        refine ⟨46985589316575541914390227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125294904844201445105040605 46985589316575541914390227)
        ·
          refine ⟨70478383974863312871585341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46985589316575541914390227 70478383974863312871585341)
          ·
            refine ⟨26429393990573742326844503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70478383974863312871585341 26429393990573742326844503)
            ·
              refine ⟨39644090985860613490266755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26429393990573742326844503 39644090985860613490266755)
              ·
                refine ⟨59466136478790920235400133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39644090985860613490266755 59466136478790920235400133)
                ·
                  refine ⟨11149900589773297544137525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59466136478790920235400133 11149900589773297544137525)
                  ·
                    refine ⟨1045303180291246644762893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11149900589773297544137525 1045303180291246644762893)
                    ·
                      rfl

theorem cell23_6107162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 1, 4, 5].length) (baseStart_6107162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6107162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6107162 prefixEnd_6107162 := by exact prefixLift 6107162
  have htrace : WordTrace (prefixWord ++ tailWord_6107162) baseStart_6107162 baseEnd_6107162 := by
    simpa [prefixWord, tailWord_6107162, baseEnd_6107162] using wordTrace_append hprefix tailTrace_6107162
  have hstable : (prefixWord ++ tailWord_6107162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6107162).length < 2 ^ (prefixWord ++ tailWord_6107162).sum := by decide
  have hdescent : baseEnd_6107162 < baseStart_6107162 := by decide
  rcases family_descends (prefixWord ++ tailWord_6107162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6107226 : List Nat := [3, 1, 1, 2, 1, 1, 5, 4, 1, 4]
def baseStart_6107226 : Nat := 118140960795 + 6107226 * 2 ^ 59
def prefixEnd_6107226 : Nat := 4983230072969 + 3 ^ 40 * 6107226 * 2
def baseEnd_6107226 : Nat := 1045314134545209227962795

theorem tailTrace_6107226 : CollatzResearch.WordTrace tailWord_6107226 prefixEnd_6107226 1045314134545209227962795 := by
  unfold tailWord_6107226
  simp only [CollatzResearch.WordTrace]
  refine ⟨55687207943142677001489383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148499221181713805337305021 55687207943142677001489383)
  ·
    refine ⟨83530811914714015502234075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55687207943142677001489383 83530811914714015502234075)
    ·
      refine ⟨125296217872071023253351113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83530811914714015502234075 125296217872071023253351113)
      ·
        refine ⟨93972163404053267440013335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125296217872071023253351113 93972163404053267440013335)
        ·
          refine ⟨140958245106079901160020003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93972163404053267440013335 140958245106079901160020003)
          ·
            refine ⟨211437367659119851740030005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140958245106079901160020003 211437367659119851740030005)
            ·
              refine ⟨19822253218042486100627813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 211437367659119851740030005 19822253218042486100627813)
              ·
                refine ⟨3716672478382966143867715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19822253218042486100627813 3716672478382966143867715)
                ·
                  refine ⟨5575008717574449215801573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3716672478382966143867715 5575008717574449215801573)
                  ·
                    refine ⟨1045314134545209227962795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5575008717574449215801573 1045314134545209227962795)
                    ·
                      rfl

theorem cell23_6107226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 4, 1, 4].length) (baseStart_6107226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6107226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6107226 prefixEnd_6107226 := by exact prefixLift 6107226
  have htrace : WordTrace (prefixWord ++ tailWord_6107226) baseStart_6107226 baseEnd_6107226 := by
    simpa [prefixWord, tailWord_6107226, baseEnd_6107226] using wordTrace_append hprefix tailTrace_6107226
  have hstable : (prefixWord ++ tailWord_6107226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6107226).length < 2 ^ (prefixWord ++ tailWord_6107226).sum := by decide
  have hdescent : baseEnd_6107226 < baseStart_6107226 := by decide
  rcases family_descends (prefixWord ++ tailWord_6107226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6107303 : List Nat := [1, 1, 6, 2, 2, 1, 2, 2, 1, 5]
def baseStart_6107303 : Nat := 118140960795 + 6107303 * 2 ^ 59
def prefixEnd_6107303 : Nat := 4983230072969 + 3 ^ 40 * 6107303 * 2
def baseEnd_6107303 : Nat := 1045327313882007960875177

theorem tailTrace_6107303 : CollatzResearch.WordTrace tailWord_6107303 prefixEnd_6107303 1045327313882007960875177 := by
  unfold tailWord_6107303
  simp only [CollatzResearch.WordTrace]
  refine ⟨222751640193291750156510563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148501093462194500104340375 222751640193291750156510563)
  ·
    refine ⟨334127460289937625234765845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222751640193291750156510563 334127460289937625234765845)
    ·
      refine ⟨15662224701090826182879649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 334127460289937625234765845 15662224701090826182879649)
      ·
        refine ⟨11746668525818119637159737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15662224701090826182879649 11746668525818119637159737)
        ·
          refine ⟨8810001394363589727869803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11746668525818119637159737 8810001394363589727869803)
          ·
            refine ⟨13215002091545384591804705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8810001394363589727869803 13215002091545384591804705)
            ·
              refine ⟨9911251568659038443853529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13215002091545384591804705 9911251568659038443853529)
              ·
                refine ⟨7433438676494278832890147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9911251568659038443853529 7433438676494278832890147)
                ·
                  refine ⟨11150158014741418249335221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7433438676494278832890147 11150158014741418249335221)
                  ·
                    refine ⟨1045327313882007960875177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11150158014741418249335221 1045327313882007960875177)
                    ·
                      rfl

theorem cell23_6107303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 2, 2, 1, 5].length) (baseStart_6107303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6107303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6107303 prefixEnd_6107303 := by exact prefixLift 6107303
  have htrace : WordTrace (prefixWord ++ tailWord_6107303) baseStart_6107303 baseEnd_6107303 := by
    simpa [prefixWord, tailWord_6107303, baseEnd_6107303] using wordTrace_append hprefix tailTrace_6107303
  have hstable : (prefixWord ++ tailWord_6107303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6107303).length < 2 ^ (prefixWord ++ tailWord_6107303).sum := by decide
  have hdescent : baseEnd_6107303 < baseStart_6107303 := by decide
  rcases family_descends (prefixWord ++ tailWord_6107303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6107350 : List Nat := [5, 2, 1, 2, 1, 2, 1, 3, 2, 4]
def baseStart_6107350 : Nat := 118140960795 + 6107350 * 2 ^ 59
def prefixEnd_6107350 : Nat := 4983230072969 + 3 ^ 40 * 6107350 * 2
def baseEnd_6107350 : Nat := 1045335358412261732912605

theorem tailTrace_6107350 : CollatzResearch.WordTrace tailWord_6107350 prefixEnd_6107350 1045335358412261732912605 := by
  unfold tailWord_6107350
  simp only [CollatzResearch.WordTrace]
  refine ⟨13922084651507592323966969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 148502236282747651455647669 13922084651507592323966969)
  ·
    refine ⟨10441563488630694242975227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13922084651507592323966969 10441563488630694242975227)
    ·
      refine ⟨15662345232946041364462841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10441563488630694242975227 15662345232946041364462841)
      ·
        refine ⟨11746758924709531023347131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15662345232946041364462841 11746758924709531023347131)
        ·
          refine ⟨17620138387064296535020697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11746758924709531023347131 17620138387064296535020697)
          ·
            refine ⟨13215103790298222401265523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17620138387064296535020697 13215103790298222401265523)
            ·
              refine ⟨19822655685447333601898285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13215103790298222401265523 19822655685447333601898285)
              ·
                refine ⟨7433495882042750100711857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19822655685447333601898285 7433495882042750100711857)
                ·
                  refine ⟨5575121911532062575533893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7433495882042750100711857 5575121911532062575533893)
                  ·
                    refine ⟨1045335358412261732912605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5575121911532062575533893 1045335358412261732912605)
                    ·
                      rfl

theorem cell23_6107350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 3, 2, 4].length) (baseStart_6107350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6107350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6107350 prefixEnd_6107350 := by exact prefixLift 6107350
  have htrace : WordTrace (prefixWord ++ tailWord_6107350) baseStart_6107350 baseEnd_6107350 := by
    simpa [prefixWord, tailWord_6107350, baseEnd_6107350] using wordTrace_append hprefix tailTrace_6107350
  have hstable : (prefixWord ++ tailWord_6107350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6107350).length < 2 ^ (prefixWord ++ tailWord_6107350).sum := by decide
  have hdescent : baseEnd_6107350 < baseStart_6107350 := by decide
  rcases family_descends (prefixWord ++ tailWord_6107350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6107373 : List Nat := [1, 5, 1, 2, 3, 1, 1, 2, 1, 3, 3]
def baseStart_6107373 : Nat := 118140960795 + 6107373 * 2 ^ 59
def prefixEnd_6107373 : Nat := 4983230072969 + 3 ^ 40 * 6107373 * 2
def baseEnd_6107373 : Nat := 3136017885291838608750209

theorem tailTrace_6107373 : CollatzResearch.WordTrace tailWord_6107373 prefixEnd_6107373 3136017885291838608750209 := by
  unfold tailWord_6107373
  simp only [CollatzResearch.WordTrace]
  refine ⟨222754193303038152111558773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148502795535358768074372515 222754193303038152111558773)
  ·
    refine ⟨20883205622159826760458635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 222754193303038152111558773 20883205622159826760458635)
    ·
      refine ⟨31324808433239740140687953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20883205622159826760458635 31324808433239740140687953)
      ·
        refine ⟨23493606324929805105515965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31324808433239740140687953 23493606324929805105515965)
        ·
          refine ⟨8810102371848676914568487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23493606324929805105515965 8810102371848676914568487)
          ·
            refine ⟨13215153557773015371852731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8810102371848676914568487 13215153557773015371852731)
            ·
              refine ⟨19822730336659523057779097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13215153557773015371852731 19822730336659523057779097)
              ·
                refine ⟨14867047752494642293334323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19822730336659523057779097 14867047752494642293334323)
                ·
                  refine ⟨22300571628741963440001485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14867047752494642293334323 22300571628741963440001485)
                  ·
                    refine ⟨8362714360778236290000557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22300571628741963440001485 8362714360778236290000557)
                    ·
                      refine ⟨3136017885291838608750209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8362714360778236290000557 3136017885291838608750209)
                      ·
                        rfl

theorem cell23_6107373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 2, 1, 3, 3].length) (baseStart_6107373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6107373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6107373 prefixEnd_6107373 := by exact prefixLift 6107373
  have htrace : WordTrace (prefixWord ++ tailWord_6107373) baseStart_6107373 baseEnd_6107373 := by
    simpa [prefixWord, tailWord_6107373, baseEnd_6107373] using wordTrace_append hprefix tailTrace_6107373
  have hstable : (prefixWord ++ tailWord_6107373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6107373).length < 2 ^ (prefixWord ++ tailWord_6107373).sum := by decide
  have hdescent : baseEnd_6107373 < baseStart_6107373 := by decide
  rcases family_descends (prefixWord ++ tailWord_6107373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6107390 : List Nat := [4, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3]
def baseStart_6107390 : Nat := 118140960795 + 6107390 * 2 ^ 59
def prefixEnd_6107390 : Nat := 4983230072969 + 3 ^ 40 * 6107390 * 2
def baseEnd_6107390 : Nat := 3136026614462965042237631

theorem tailTrace_6107390 : CollatzResearch.WordTrace tailWord_6107390 prefixEnd_6107390 3136026614462965042237631 := by
  unfold tailWord_6107390
  simp only [CollatzResearch.WordTrace]
  refine ⟨27844351667997070501865953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148503208895984376009951749 27844351667997070501865953)
  ·
    refine ⟨20883263750997802876399465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27844351667997070501865953 20883263750997802876399465)
    ·
      refine ⟨15662447813248352157299599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20883263750997802876399465 15662447813248352157299599)
      ·
        refine ⟨23493671719872528235949399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15662447813248352157299599 23493671719872528235949399)
        ·
          refine ⟨35240507579808792353924099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23493671719872528235949399 35240507579808792353924099)
          ·
            refine ⟨52860761369713188530886149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35240507579808792353924099 52860761369713188530886149)
            ·
              refine ⟨9911392756821222849541153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52860761369713188530886149 9911392756821222849541153)
              ·
                refine ⟨7433544567615917137155865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9911392756821222849541153 7433544567615917137155865)
                ·
                  refine ⟨5575158425711937852866899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7433544567615917137155865 5575158425711937852866899)
                  ·
                    refine ⟨8362737638567906779300349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5575158425711937852866899 8362737638567906779300349)
                    ·
                      refine ⟨3136026614462965042237631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8362737638567906779300349 3136026614462965042237631)
                      ·
                        rfl

theorem cell23_6107390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3].length) (baseStart_6107390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6107390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6107390 prefixEnd_6107390 := by exact prefixLift 6107390
  have htrace : WordTrace (prefixWord ++ tailWord_6107390) baseStart_6107390 baseEnd_6107390 := by
    simpa [prefixWord, tailWord_6107390, baseEnd_6107390] using wordTrace_append hprefix tailTrace_6107390
  have hstable : (prefixWord ++ tailWord_6107390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6107390).length < 2 ^ (prefixWord ++ tailWord_6107390).sum := by decide
  have hdescent : baseEnd_6107390 < baseStart_6107390 := by decide
  rcases family_descends (prefixWord ++ tailWord_6107390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6107409 : List Nat := [1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 4]
def baseStart_6107409 : Nat := 118140960795 + 6107409 * 2 ^ 59
def prefixEnd_6107409 : Nat := 4983230072969 + 3 ^ 40 * 6107409 * 2
def baseEnd_6107409 : Nat := 3136036370595400467900043

theorem tailTrace_6107409 : CollatzResearch.WordTrace tailWord_6107409 prefixEnd_6107409 3136036370595400467900043 := by
  unfold tailWord_6107409
  simp only [CollatzResearch.WordTrace]
  refine ⟨222755506330907730259869281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148503670887271820173246187 222755506330907730259869281)
  ·
    refine ⟨167066629748180797694901961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222755506330907730259869281 167066629748180797694901961)
    ·
      refine ⟨125299972311135598271176471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167066629748180797694901961 125299972311135598271176471)
      ·
        refine ⟨187949958466703397406764707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125299972311135598271176471 187949958466703397406764707)
        ·
          refine ⟨281924937700055096110147061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187949958466703397406764707 281924937700055096110147061)
          ·
            refine ⟨26430462909380165260326287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 281924937700055096110147061 26430462909380165260326287)
            ·
              refine ⟨39645694364070247890489431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26430462909380165260326287 39645694364070247890489431)
              ·
                refine ⟨59468541546105371835734147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39645694364070247890489431 59468541546105371835734147)
                ·
                  refine ⟨89202812319158057753601221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59468541546105371835734147 89202812319158057753601221)
                  ·
                    refine ⟨16725527309842135828800229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 89202812319158057753601221 16725527309842135828800229)
                    ·
                      refine ⟨3136036370595400467900043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16725527309842135828800229 3136036370595400467900043)
                      ·
                        rfl

theorem cell23_6107409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 4].length) (baseStart_6107409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6107409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6107409 prefixEnd_6107409 := by exact prefixLift 6107409
  have htrace : WordTrace (prefixWord ++ tailWord_6107409) baseStart_6107409 baseEnd_6107409 := by
    simpa [prefixWord, tailWord_6107409, baseEnd_6107409] using wordTrace_append hprefix tailTrace_6107409
  have hstable : (prefixWord ++ tailWord_6107409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6107409).length < 2 ^ (prefixWord ++ tailWord_6107409).sum := by decide
  have hdescent : baseEnd_6107409 < baseStart_6107409 := by decide
  rcases family_descends (prefixWord ++ tailWord_6107409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6107434 : List Nat := [3, 1, 4, 2, 2, 2, 2, 1, 1, 3, 2]
def baseStart_6107434 : Nat := 118140960795 + 6107434 * 2 ^ 59
def prefixEnd_6107434 : Nat := 4983230072969 + 3 ^ 40 * 6107434 * 2
def baseEnd_6107434 : Nat := 3136049207611762870087429

theorem tailTrace_6107434 : CollatzResearch.WordTrace tailWord_6107434 prefixEnd_6107434 3136049207611762870087429 := by
  unfold tailWord_6107434
  simp only [CollatzResearch.WordTrace]
  refine ⟨55689104538954289882382339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148504278770544773019686237 55689104538954289882382339)
  ·
    refine ⟨83533656808431434823573509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55689104538954289882382339 83533656808431434823573509)
    ·
      refine ⟨15662560651580894029420033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83533656808431434823573509 15662560651580894029420033)
      ·
        refine ⟨11746920488685670522065025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15662560651580894029420033 11746920488685670522065025)
        ·
          refine ⟨8810190366514252891548769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11746920488685670522065025 8810190366514252891548769)
          ·
            refine ⟨6607642774885689668661577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8810190366514252891548769 6607642774885689668661577)
            ·
              refine ⟨4955732081164267251496183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6607642774885689668661577 4955732081164267251496183)
              ·
                refine ⟨7433598121746400877244275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4955732081164267251496183 7433598121746400877244275)
                ·
                  refine ⟨11150397182619601315866413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7433598121746400877244275 11150397182619601315866413)
                  ·
                    refine ⟨4181398943482350493449905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11150397182619601315866413 4181398943482350493449905)
                    ·
                      refine ⟨3136049207611762870087429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4181398943482350493449905 3136049207611762870087429)
                      ·
                        rfl

theorem cell23_6107434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 2, 1, 1, 3, 2].length) (baseStart_6107434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6107434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6107434 prefixEnd_6107434 := by exact prefixLift 6107434
  have htrace : WordTrace (prefixWord ++ tailWord_6107434) baseStart_6107434 baseEnd_6107434 := by
    simpa [prefixWord, tailWord_6107434, baseEnd_6107434] using wordTrace_append hprefix tailTrace_6107434
  have hstable : (prefixWord ++ tailWord_6107434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6107434).length < 2 ^ (prefixWord ++ tailWord_6107434).sum := by decide
  have hdescent : baseEnd_6107434 < baseStart_6107434 := by decide
  rcases family_descends (prefixWord ++ tailWord_6107434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6107436 : List Nat := [2, 2, 1, 1, 1, 3, 3, 5, 5]
def baseStart_6107436 : Nat := 118140960795 + 6107436 * 2 ^ 59
def prefixEnd_6107436 : Nat := 4983230072969 + 3 ^ 40 * 6107436 * 2
def baseEnd_6107436 : Nat := 348450026063674651362491

theorem tailTrace_6107436 : CollatzResearch.WordTrace tailWord_6107436 prefixEnd_6107436 348450026063674651362491 := by
  unfold tailWord_6107436
  simp only [CollatzResearch.WordTrace]
  refine ⟨111378245550904956935551081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148504327401206609247401441 111378245550904956935551081)
  ·
    refine ⟨83533684163178717701663311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111378245550904956935551081 83533684163178717701663311)
    ·
      refine ⟨125300526244768076552494967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83533684163178717701663311 125300526244768076552494967)
      ·
        refine ⟨187950789367152114828742451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125300526244768076552494967 187950789367152114828742451)
        ·
          refine ⟨281926184050728172243113677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187950789367152114828742451 281926184050728172243113677)
          ·
            refine ⟨105722319019023064591167629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 281926184050728172243113677 105722319019023064591167629)
            ·
              refine ⟨39645869632133649221687861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105722319019023064591167629 39645869632133649221687861)
              ·
                refine ⟨3716800278012529614533237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39645869632133649221687861 3716800278012529614533237)
                ·
                  refine ⟨348450026063674651362491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3716800278012529614533237 348450026063674651362491)
                  ·
                    rfl

theorem cell23_6107436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 5, 5].length) (baseStart_6107436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6107436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6107436 prefixEnd_6107436 := by exact prefixLift 6107436
  have htrace : WordTrace (prefixWord ++ tailWord_6107436) baseStart_6107436 baseEnd_6107436 := by
    simpa [prefixWord, tailWord_6107436, baseEnd_6107436] using wordTrace_append hprefix tailTrace_6107436
  have hstable : (prefixWord ++ tailWord_6107436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6107436).length < 2 ^ (prefixWord ++ tailWord_6107436).sum := by decide
  have hdescent : baseEnd_6107436 < baseStart_6107436 := by decide
  rcases family_descends (prefixWord ++ tailWord_6107436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6107456 : List Nat := [2, 1, 1, 2, 2, 1, 2, 3, 2, 5, 2]
def baseStart_6107456 : Nat := 118140960795 + 6107456 * 2 ^ 59
def prefixEnd_6107456 : Nat := 4983230072969 + 3 ^ 40 * 6107456 * 2
def baseEnd_6107456 : Nat := 3136060504186161784012327

theorem tailTrace_6107456 : CollatzResearch.WordTrace tailWord_6107456 prefixEnd_6107456 3136060504186161784012327 := by
  unfold tailWord_6107456
  simp only [CollatzResearch.WordTrace]
  refine ⟨111378610280868728643415111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148504813707824971524553481 111378610280868728643415111)
  ·
    refine ⟨167067915421303092965122667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111378610280868728643415111 167067915421303092965122667)
    ·
      refine ⟨250601873131954639447684001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167067915421303092965122667 250601873131954639447684001)
      ·
        refine ⟨187951404848965979585763001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 250601873131954639447684001 187951404848965979585763001)
        ·
          refine ⟨140963553636724484689322251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187951404848965979585763001 140963553636724484689322251)
          ·
            refine ⟨211445330455086727033983377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140963553636724484689322251 211445330455086727033983377)
            ·
              refine ⟨158583997841315045275487533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 211445330455086727033983377 158583997841315045275487533)
              ·
                refine ⟨59468999190493141978307825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 158583997841315045275487533 59468999190493141978307825)
                ·
                  refine ⟨44601749392869856483730869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59468999190493141978307825 44601749392869856483730869)
                  ·
                    refine ⟨4181414005581549045349769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44601749392869856483730869 4181414005581549045349769)
                    ·
                      refine ⟨3136060504186161784012327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4181414005581549045349769 3136060504186161784012327)
                      ·
                        rfl

theorem cell23_6107456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 3, 2, 5, 2].length) (baseStart_6107456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6107456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6107456 prefixEnd_6107456 := by exact prefixLift 6107456
  have htrace : WordTrace (prefixWord ++ tailWord_6107456) baseStart_6107456 baseEnd_6107456 := by
    simpa [prefixWord, tailWord_6107456, baseEnd_6107456] using wordTrace_append hprefix tailTrace_6107456
  have hstable : (prefixWord ++ tailWord_6107456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6107456).length < 2 ^ (prefixWord ++ tailWord_6107456).sum := by decide
  have hdescent : baseEnd_6107456 < baseStart_6107456 := by decide
  rcases family_descends (prefixWord ++ tailWord_6107456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6107459 : List Nat := [1, 1, 1, 3, 1, 3, 2, 3, 1, 2, 5]
def baseStart_6107459 : Nat := 118140960795 + 6107459 * 2 ^ 59
def prefixEnd_6107459 : Nat := 4983230072969 + 3 ^ 40 * 6107459 * 2
def baseEnd_6107459 : Nat := 3136062044628125272274813

theorem tailTrace_6107459 : CollatzResearch.WordTrace tailWord_6107459 prefixEnd_6107459 3136062044628125272274813 := by
  unfold tailWord_6107459
  simp only [CollatzResearch.WordTrace]
  refine ⟨222757329980726588799189431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148504886653817725866126287 222757329980726588799189431)
  ·
    refine ⟨334135994971089883198784147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222757329980726588799189431 334135994971089883198784147)
    ·
      refine ⟨501203992456634824798176221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 334135994971089883198784147 501203992456634824798176221)
      ·
        refine ⟨187951497171238059299316083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 501203992456634824798176221 187951497171238059299316083)
        ·
          refine ⟨281927245756857088948974125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187951497171238059299316083 281927245756857088948974125)
          ·
            refine ⟨105722717158821408355865297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 281927245756857088948974125 105722717158821408355865297)
            ·
              refine ⟨79292037869116056266898973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105722717158821408355865297 79292037869116056266898973)
              ·
                refine ⟨29734514200918521100087115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79292037869116056266898973 29734514200918521100087115)
                ·
                  refine ⟨44601771301377781650130673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29734514200918521100087115 44601771301377781650130673)
                  ·
                    refine ⟨33451328476033336237598005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44601771301377781650130673 33451328476033336237598005)
                    ·
                      refine ⟨3136062044628125272274813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33451328476033336237598005 3136062044628125272274813)
                      ·
                        rfl

theorem cell23_6107459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 1, 2, 5].length) (baseStart_6107459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6107459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6107459 prefixEnd_6107459 := by exact prefixLift 6107459
  have htrace : WordTrace (prefixWord ++ tailWord_6107459) baseStart_6107459 baseEnd_6107459 := by
    simpa [prefixWord, tailWord_6107459, baseEnd_6107459] using wordTrace_append hprefix tailTrace_6107459
  have hstable : (prefixWord ++ tailWord_6107459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6107459).length < 2 ^ (prefixWord ++ tailWord_6107459).sum := by decide
  have hdescent : baseEnd_6107459 < baseStart_6107459 := by decide
  rcases family_descends (prefixWord ++ tailWord_6107459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6107479 : List Nat := [1, 1, 3, 2, 3, 1, 1, 1, 2, 8]
def baseStart_6107479 : Nat := 118140960795 + 6107479 * 2 ^ 59
def prefixEnd_6107479 : Nat := 4983230072969 + 3 ^ 40 * 6107479 * 2
def baseEnd_6107479 : Nat := 1045357438080405064674907

theorem tailTrace_6107479 : CollatzResearch.WordTrace tailWord_6107479 prefixEnd_6107479 1045357438080405064674907 := by
  unfold tailWord_6107479
  simp only [CollatzResearch.WordTrace]
  refine ⟨222758059440654132214917491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148505372960436088143278327 222758059440654132214917491)
  ·
    refine ⟨334137089160981198322376237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222758059440654132214917491 334137089160981198322376237)
    ·
      refine ⟨125301408435367949370891089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 334137089160981198322376237 125301408435367949370891089)
      ·
        refine ⟨93976056326525962028168317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125301408435367949370891089 93976056326525962028168317)
        ·
          refine ⟨35241021122447235760563119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93976056326525962028168317 35241021122447235760563119)
          ·
            refine ⟨52861531683670853640844679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35241021122447235760563119 52861531683670853640844679)
            ·
              refine ⟨79292297525506280461267019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52861531683670853640844679 79292297525506280461267019)
              ·
                refine ⟨118938446288259420691900529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79292297525506280461267019 118938446288259420691900529)
                ·
                  refine ⟨89203834716194565518925397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 118938446288259420691900529 89203834716194565518925397)
                  ·
                    refine ⟨1045357438080405064674907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 89203834716194565518925397 1045357438080405064674907)
                    ·
                      rfl

theorem cell23_6107479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 2, 8].length) (baseStart_6107479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6107479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6107479 prefixEnd_6107479 := by exact prefixLift 6107479
  have htrace : WordTrace (prefixWord ++ tailWord_6107479) baseStart_6107479 baseEnd_6107479 := by
    simpa [prefixWord, tailWord_6107479, baseEnd_6107479] using wordTrace_append hprefix tailTrace_6107479
  have hstable : (prefixWord ++ tailWord_6107479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6107479).length < 2 ^ (prefixWord ++ tailWord_6107479).sum := by decide
  have hdescent : baseEnd_6107479 < baseStart_6107479 := by decide
  rcases family_descends (prefixWord ++ tailWord_6107479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6107489 : List Nat := [1, 2, 3, 1, 1, 1, 1, 1, 4, 3, 5]
def baseStart_6107489 : Nat := 118140960795 + 6107489 * 2 ^ 59
def prefixEnd_6107489 : Nat := 4983230072969 + 3 ^ 40 * 6107489 * 2
def baseEnd_6107489 : Nat := 3136077449047760154899675

theorem tailTrace_6107489 : CollatzResearch.WordTrace tailWord_6107489 prefixEnd_6107489 3136077449047760154899675 := by
  unfold tailWord_6107489
  simp only [CollatzResearch.WordTrace]
  refine ⟨222758424170617903922781521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148505616113745269281854347 222758424170617903922781521)
  ·
    refine ⟨167068818127963427942086141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222758424170617903922781521 167068818127963427942086141)
    ·
      refine ⟨62650806797986285478282303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167068818127963427942086141 62650806797986285478282303)
      ·
        refine ⟨93976210196979428217423455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62650806797986285478282303 93976210196979428217423455)
        ·
          refine ⟨140964315295469142326135183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93976210196979428217423455 140964315295469142326135183)
          ·
            refine ⟨211446472943203713489202775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140964315295469142326135183 211446472943203713489202775)
            ·
              refine ⟨317169709414805570233804163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 211446472943203713489202775 317169709414805570233804163)
              ·
                refine ⟨475754564122208355350706245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 317169709414805570233804163 475754564122208355350706245)
                ·
                  refine ⟨89203980772914066628257421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 475754564122208355350706245 89203980772914066628257421)
                  ·
                    refine ⟨33451492789842774985596533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 89203980772914066628257421 33451492789842774985596533)
                    ·
                      refine ⟨3136077449047760154899675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33451492789842774985596533 3136077449047760154899675)
                      ·
                        rfl

theorem cell23_6107489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 4, 3, 5].length) (baseStart_6107489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6107489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6107489 prefixEnd_6107489 := by exact prefixLift 6107489
  have htrace : WordTrace (prefixWord ++ tailWord_6107489) baseStart_6107489 baseEnd_6107489 := by
    simpa [prefixWord, tailWord_6107489, baseEnd_6107489] using wordTrace_append hprefix tailTrace_6107489
  have hstable : (prefixWord ++ tailWord_6107489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6107489).length < 2 ^ (prefixWord ++ tailWord_6107489).sum := by decide
  have hdescent : baseEnd_6107489 < baseStart_6107489 := by decide
  rcases family_descends (prefixWord ++ tailWord_6107489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6107499 : List Nat := [1, 1, 1, 1, 2, 2, 2, 2, 1, 6, 4]
def baseStart_6107499 : Nat := 118140960795 + 6107499 * 2 ^ 59
def prefixEnd_6107499 : Nat := 4983230072969 + 3 ^ 40 * 6107499 * 2
def baseEnd_6107499 : Nat := 3136082583854305115774629

theorem tailTrace_6107499 : CollatzResearch.WordTrace tailWord_6107499 prefixEnd_6107499 3136082583854305115774629 := by
  unfold tailWord_6107499
  simp only [CollatzResearch.WordTrace]
  refine ⟨222758788900581675630645551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148505859267054450420430367 222758788900581675630645551)
  ·
    refine ⟨334138183350872513445968327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222758788900581675630645551 334138183350872513445968327)
    ·
      refine ⟨501207275026308770168952491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 334138183350872513445968327 501207275026308770168952491)
      ·
        refine ⟨751810912539463155253428737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 501207275026308770168952491 751810912539463155253428737)
        ·
          refine ⟨563858184404597366440071553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 751810912539463155253428737 563858184404597366440071553)
          ·
            refine ⟨422893638303448024830053665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 563858184404597366440071553 422893638303448024830053665)
            ·
              refine ⟨317170228727586018622540249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 422893638303448024830053665 317170228727586018622540249)
              ·
                refine ⟨237877671545689513966905187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 317170228727586018622540249 237877671545689513966905187)
                ·
                  refine ⟨356816507318534270950357781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 237877671545689513966905187 356816507318534270950357781)
                  ·
                    refine ⟨16725773780556293950798021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 356816507318534270950357781 16725773780556293950798021)
                    ·
                      refine ⟨3136082583854305115774629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16725773780556293950798021 3136082583854305115774629)
                      ·
                        rfl

theorem cell23_6107499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 6, 4].length) (baseStart_6107499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6107499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6107499 prefixEnd_6107499 := by exact prefixLift 6107499
  have htrace : WordTrace (prefixWord ++ tailWord_6107499) baseStart_6107499 baseEnd_6107499 := by
    simpa [prefixWord, tailWord_6107499, baseEnd_6107499] using wordTrace_append hprefix tailTrace_6107499
  have hstable : (prefixWord ++ tailWord_6107499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6107499).length < 2 ^ (prefixWord ++ tailWord_6107499).sum := by decide
  have hdescent : baseEnd_6107499 < baseStart_6107499 := by decide
  rcases family_descends (prefixWord ++ tailWord_6107499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6107510 : List Nat := [5, 1, 1, 4, 1, 1, 1, 1, 1, 2, 5]
def baseStart_6107510 : Nat := 118140960795 + 6107510 * 2 ^ 59
def prefixEnd_6107510 : Nat := 4983230072969 + 3 ^ 40 * 6107510 * 2
def baseEnd_6107510 : Nat := 3136088232141504572737079

theorem tailTrace_6107510 : CollatzResearch.WordTrace tailWord_6107510 prefixEnd_6107510 3136088232141504572737079 := by
  unfold tailWord_6107510
  simp only [CollatzResearch.WordTrace]
  refine ⟨13922449381471364031830999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 148506126735694549672863989 13922449381471364031830999)
  ·
    refine ⟨20883674072207046047746499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13922449381471364031830999 20883674072207046047746499)
    ·
      refine ⟨31325511108310569071619749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20883674072207046047746499 31325511108310569071619749)
      ·
        refine ⟨5873533332808231700928703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31325511108310569071619749 5873533332808231700928703)
        ·
          refine ⟨8810299999212347551393055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5873533332808231700928703 8810299999212347551393055)
          ·
            refine ⟨13215449998818521327089583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8810299999212347551393055 13215449998818521327089583)
            ·
              refine ⟨19823174998227781990634375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13215449998818521327089583 19823174998227781990634375)
              ·
                refine ⟨29734762497341672985951563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19823174998227781990634375 29734762497341672985951563)
                ·
                  refine ⟨44602143746012509478927345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29734762497341672985951563 44602143746012509478927345)
                  ·
                    refine ⟨33451607809509382109195509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44602143746012509478927345 33451607809509382109195509)
                    ·
                      refine ⟨3136088232141504572737079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33451607809509382109195509 3136088232141504572737079)
                      ·
                        rfl

theorem cell23_6107510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_6107510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6107510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6107510 prefixEnd_6107510 := by exact prefixLift 6107510
  have htrace : WordTrace (prefixWord ++ tailWord_6107510) baseStart_6107510 baseEnd_6107510 := by
    simpa [prefixWord, tailWord_6107510, baseEnd_6107510] using wordTrace_append hprefix tailTrace_6107510
  have hstable : (prefixWord ++ tailWord_6107510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6107510).length < 2 ^ (prefixWord ++ tailWord_6107510).sum := by decide
  have hdescent : baseEnd_6107510 < baseStart_6107510 := by decide
  rcases family_descends (prefixWord ++ tailWord_6107510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6107560 : List Nat := [2, 1, 6, 1, 1, 2, 2, 2, 6]
def baseStart_6107560 : Nat := 118140960795 + 6107560 * 2 ^ 59
def prefixEnd_6107560 : Nat := 4983230072969 + 3 ^ 40 * 6107560 * 2
def baseEnd_6107560 : Nat := 348457100686025486345761

theorem tailTrace_6107560 : CollatzResearch.WordTrace tailWord_6107560 prefixEnd_6107560 348457100686025486345761 := by
  unfold tailWord_6107560
  simp only [CollatzResearch.WordTrace]
  refine ⟨111380506876680341524308067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148507342502240455365744089 111380506876680341524308067)
  ·
    refine ⟨167070760315020512286462101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111380506876680341524308067 167070760315020512286462101)
    ·
      refine ⟨7831441889766586513427911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 167070760315020512286462101 7831441889766586513427911)
      ·
        refine ⟨11747162834649879770141867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7831441889766586513427911 11747162834649879770141867)
        ·
          refine ⟨17620744251974819655212801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11747162834649879770141867 17620744251974819655212801)
          ·
            refine ⟨13215558188981114741409601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17620744251974819655212801 13215558188981114741409601)
            ·
              refine ⟨9911668641735836056057201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13215558188981114741409601 9911668641735836056057201)
              ·
                refine ⟨7433751481301877042042901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9911668641735836056057201 7433751481301877042042901)
                ·
                  refine ⟨348457100686025486345761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7433751481301877042042901 348457100686025486345761)
                  ·
                    rfl

theorem cell23_6107560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 2, 2, 6].length) (baseStart_6107560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6107560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6107560 prefixEnd_6107560 := by exact prefixLift 6107560
  have htrace : WordTrace (prefixWord ++ tailWord_6107560) baseStart_6107560 baseEnd_6107560 := by
    simpa [prefixWord, tailWord_6107560, baseEnd_6107560] using wordTrace_append hprefix tailTrace_6107560
  have hstable : (prefixWord ++ tailWord_6107560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6107560).length < 2 ^ (prefixWord ++ tailWord_6107560).sum := by decide
  have hdescent : baseEnd_6107560 < baseStart_6107560 := by decide
  rcases family_descends (prefixWord ++ tailWord_6107560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6107604 : List Nat := [2, 4, 1, 2, 2, 2, 2, 3, 1, 1, 3]
def baseStart_6107604 : Nat := 118140960795 + 6107604 * 2 ^ 59
def prefixEnd_6107604 : Nat := 4983230072969 + 3 ^ 40 * 6107604 * 2
def baseEnd_6107604 : Nat := 3136136499323027204961647

theorem tailTrace_6107604 : CollatzResearch.WordTrace tailWord_6107604 prefixEnd_6107604 3136136499323027204961647 := by
  unfold tailWord_6107604
  simp only [CollatzResearch.WordTrace]
  refine ⟨111381309282600639281608933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148508412376800852375478577 111381309282600639281608933)
  ·
    refine ⟨20883995490487619865301675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111381309282600639281608933 20883995490487619865301675)
    ·
      refine ⟨31325993235731429797952513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20883995490487619865301675 31325993235731429797952513)
      ·
        refine ⟨23494494926798572348464385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31325993235731429797952513 23494494926798572348464385)
        ·
          refine ⟨17620871195098929261348289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23494494926798572348464385 17620871195098929261348289)
          ·
            refine ⟨13215653396324196946011217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17620871195098929261348289 13215653396324196946011217)
            ·
              refine ⟨9911740047243147709508413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13215653396324196946011217 9911740047243147709508413)
              ·
                refine ⟨3716902517716180391065655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9911740047243147709508413 3716902517716180391065655)
                ·
                  refine ⟨5575353776574270586598483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3716902517716180391065655 5575353776574270586598483)
                  ·
                    refine ⟨8363030664861405879897725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5575353776574270586598483 8363030664861405879897725)
                    ·
                      refine ⟨3136136499323027204961647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8363030664861405879897725 3136136499323027204961647)
                      ·
                        rfl

theorem cell23_6107604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 2, 3, 1, 1, 3].length) (baseStart_6107604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6107604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6107604 prefixEnd_6107604 := by exact prefixLift 6107604
  have htrace : WordTrace (prefixWord ++ tailWord_6107604) baseStart_6107604 baseEnd_6107604 := by
    simpa [prefixWord, tailWord_6107604, baseEnd_6107604] using wordTrace_append hprefix tailTrace_6107604
  have hstable : (prefixWord ++ tailWord_6107604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6107604).length < 2 ^ (prefixWord ++ tailWord_6107604).sum := by decide
  have hdescent : baseEnd_6107604 < baseStart_6107604 := by decide
  rcases family_descends (prefixWord ++ tailWord_6107604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6107610 : List Nat := [3, 1, 1, 2, 3, 1, 1, 2, 5, 2, 2]
def baseStart_6107610 : Nat := 118140960795 + 6107610 * 2 ^ 59
def prefixEnd_6107610 : Nat := 4983230072969 + 3 ^ 40 * 6107610 * 2
def baseEnd_6107610 : Nat := 3136139580206954181486619

theorem tailTrace_6107610 : CollatzResearch.WordTrace tailWord_6107610 prefixEnd_6107610 3136139580206954181486619 := by
  unfold tailWord_6107610
  simp only [CollatzResearch.WordTrace]
  refine ⟨55690709350794885396984071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148508558268786361058624189 55690709350794885396984071)
  ·
    refine ⟨83536064026192328095476107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55690709350794885396984071 83536064026192328095476107)
    ·
      refine ⟨125304096039288492143214161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83536064026192328095476107 125304096039288492143214161)
      ·
        refine ⟨93978072029466369107410621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125304096039288492143214161 93978072029466369107410621)
        ·
          refine ⟨35241777011049888415278983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93978072029466369107410621 35241777011049888415278983)
          ·
            refine ⟨52862665516574832622918475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35241777011049888415278983 52862665516574832622918475)
            ·
              refine ⟨79293998274862248934377713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52862665516574832622918475 79293998274862248934377713)
              ·
                refine ⟨59470498706146686700783285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79293998274862248934377713 59470498706146686700783285)
                ·
                  refine ⟨5575359253701251878198433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59470498706146686700783285 5575359253701251878198433)
                  ·
                    refine ⟨4181519440275938908648825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5575359253701251878198433 4181519440275938908648825)
                    ·
                      refine ⟨3136139580206954181486619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4181519440275938908648825 3136139580206954181486619)
                      ·
                        rfl

theorem cell23_6107610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 2, 5, 2, 2].length) (baseStart_6107610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6107610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6107610 prefixEnd_6107610 := by exact prefixLift 6107610
  have htrace : WordTrace (prefixWord ++ tailWord_6107610) baseStart_6107610 baseEnd_6107610 := by
    simpa [prefixWord, tailWord_6107610, baseEnd_6107610] using wordTrace_append hprefix tailTrace_6107610
  have hstable : (prefixWord ++ tailWord_6107610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6107610).length < 2 ^ (prefixWord ++ tailWord_6107610).sum := by decide
  have hdescent : baseEnd_6107610 < baseStart_6107610 := by decide
  rcases family_descends (prefixWord ++ tailWord_6107610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6107613 : List Nat := [1, 4, 3, 1, 1, 1, 2, 3, 1, 1, 5]
def baseStart_6107613 : Nat := 118140960795 + 6107613 * 2 ^ 59
def prefixEnd_6107613 : Nat := 4983230072969 + 3 ^ 40 * 6107613 * 2
def baseEnd_6107613 : Nat := 3136141120648917669749105

theorem tailTrace_6107613 : CollatzResearch.WordTrace tailWord_6107613 prefixEnd_6107613 3136141120648917669749105 := by
  unfold tailWord_6107613
  simp only [CollatzResearch.WordTrace]
  refine ⟨222762946822168673100295493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148508631214779115400196995 222762946822168673100295493)
  ·
    refine ⟨41768052529156626206305405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 222762946822168673100295493 41768052529156626206305405)
    ·
      refine ⟨15663019698433734827364527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41768052529156626206305405 15663019698433734827364527)
      ·
        refine ⟨23494529547650602241046791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15663019698433734827364527 23494529547650602241046791)
        ·
          refine ⟨35241794321475903361570187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23494529547650602241046791 35241794321475903361570187)
          ·
            refine ⟨52862691482213855042355281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35241794321475903361570187 52862691482213855042355281)
            ·
              refine ⟨39647018611660391281766461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52862691482213855042355281 39647018611660391281766461)
              ·
                refine ⟨14867631979372646730662423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39647018611660391281766461 14867631979372646730662423)
                ·
                  refine ⟨22301447969058970095993635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14867631979372646730662423 22301447969058970095993635)
                  ·
                    refine ⟨33452171953588455143990453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22301447969058970095993635 33452171953588455143990453)
                    ·
                      refine ⟨3136141120648917669749105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33452171953588455143990453 3136141120648917669749105)
                      ·
                        rfl

theorem cell23_6107613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_6107613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6107613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6107613 prefixEnd_6107613 := by exact prefixLift 6107613
  have htrace : WordTrace (prefixWord ++ tailWord_6107613) baseStart_6107613 baseEnd_6107613 := by
    simpa [prefixWord, tailWord_6107613, baseEnd_6107613] using wordTrace_append hprefix tailTrace_6107613
  have hstable : (prefixWord ++ tailWord_6107613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6107613).length < 2 ^ (prefixWord ++ tailWord_6107613).sum := by decide
  have hdescent : baseEnd_6107613 < baseStart_6107613 := by decide
  rcases family_descends (prefixWord ++ tailWord_6107613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6107627 : List Nat := [1, 1, 1, 1, 2, 3, 3, 6, 1, 2, 2]
def baseStart_6107627 : Nat := 118140960795 + 6107627 * 2 ^ 59
def prefixEnd_6107627 : Nat := 4983230072969 + 3 ^ 40 * 6107627 * 2
def baseEnd_6107627 : Nat := 3136148309378080614974041

theorem tailTrace_6107627 : CollatzResearch.WordTrace tailWord_6107627 prefixEnd_6107627 3136148309378080614974041 := by
  unfold tailWord_6107627
  simp only [CollatzResearch.WordTrace]
  refine ⟨222763457444117953491305135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148508971629411968994203423 222763457444117953491305135)
  ·
    refine ⟨334145186166176930236957703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222763457444117953491305135 334145186166176930236957703)
    ·
      refine ⟨501217779249265395355436555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 334145186166176930236957703 501217779249265395355436555)
      ·
        refine ⟨751826668873898093033154833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 501217779249265395355436555 751826668873898093033154833)
        ·
          refine ⟨563870001655423569774866125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 751826668873898093033154833 563870001655423569774866125)
          ·
            refine ⟨211451250620783838665574797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 563870001655423569774866125 211451250620783838665574797)
            ·
              refine ⟨79294218982793939499590549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 211451250620783838665574797 79294218982793939499590549)
              ·
                refine ⟨3716916514818465914043307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 79294218982793939499590549 3716916514818465914043307)
                ·
                  refine ⟨5575374772227698871064961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3716916514818465914043307 5575374772227698871064961)
                  ·
                    refine ⟨4181531079170774153298721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5575374772227698871064961 4181531079170774153298721)
                    ·
                      refine ⟨3136148309378080614974041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4181531079170774153298721 3136148309378080614974041)
                      ·
                        rfl

theorem cell23_6107627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 6, 1, 2, 2].length) (baseStart_6107627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6107627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6107627 prefixEnd_6107627 := by exact prefixLift 6107627
  have htrace : WordTrace (prefixWord ++ tailWord_6107627) baseStart_6107627 baseEnd_6107627 := by
    simpa [prefixWord, tailWord_6107627, baseEnd_6107627] using wordTrace_append hprefix tailTrace_6107627
  have hstable : (prefixWord ++ tailWord_6107627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6107627).length < 2 ^ (prefixWord ++ tailWord_6107627).sum := by decide
  have hdescent : baseEnd_6107627 < baseStart_6107627 := by decide
  rcases family_descends (prefixWord ++ tailWord_6107627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6107637 : List Nat := [1, 3, 5, 1, 2, 2, 1, 1, 1, 6]
def baseStart_6107637 : Nat := 118140960795 + 6107637 * 2 ^ 59
def prefixEnd_6107637 : Nat := 4983230072969 + 3 ^ 40 * 6107637 * 2
def baseEnd_6107637 : Nat := 1045384481394875191949665

theorem tailTrace_6107637 : CollatzResearch.WordTrace tailWord_6107637 prefixEnd_6107637 1045384481394875191949665 := by
  unfold tailWord_6107637
  simp only [CollatzResearch.WordTrace]
  refine ⟨222763822174081725199169165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148509214782721150132779443 222763822174081725199169165)
  ·
    refine ⟨83536433315280646949688437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 222763822174081725199169165 83536433315280646949688437)
    ·
      refine ⟨7831540623307560651533291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 83536433315280646949688437 7831540623307560651533291)
      ·
        refine ⟨11747310934961340977299937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7831540623307560651533291 11747310934961340977299937)
        ·
          refine ⟨8810483201221005732974953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11747310934961340977299937 8810483201221005732974953)
          ·
            refine ⟨6607862400915754299731215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8810483201221005732974953 6607862400915754299731215)
            ·
              refine ⟨9911793601373631449596823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6607862400915754299731215 9911793601373631449596823)
              ·
                refine ⟨14867690402060447174395235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9911793601373631449596823 14867690402060447174395235)
                ·
                  refine ⟨22301535603090670761592853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14867690402060447174395235 22301535603090670761592853)
                  ·
                    refine ⟨1045384481394875191949665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22301535603090670761592853 1045384481394875191949665)
                    ·
                      rfl

theorem cell23_6107637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_6107637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6107637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6107637 prefixEnd_6107637 := by exact prefixLift 6107637
  have htrace : WordTrace (prefixWord ++ tailWord_6107637) baseStart_6107637 baseEnd_6107637 := by
    simpa [prefixWord, tailWord_6107637, baseEnd_6107637] using wordTrace_append hprefix tailTrace_6107637
  have hstable : (prefixWord ++ tailWord_6107637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6107637).length < 2 ^ (prefixWord ++ tailWord_6107637).sum := by decide
  have hdescent : baseEnd_6107637 < baseStart_6107637 := by decide
  rcases family_descends (prefixWord ++ tailWord_6107637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6107643 : List Nat := [1, 1, 1, 1, 1, 3, 2, 1, 8, 1, 3]
def baseStart_6107643 : Nat := 118140960795 + 6107643 * 2 ^ 59
def prefixEnd_6107643 : Nat := 4983230072969 + 3 ^ 40 * 6107643 * 2
def baseEnd_6107643 : Nat := 3136156525068552552373967

theorem tailTrace_6107643 : CollatzResearch.WordTrace tailWord_6107643 prefixEnd_6107643 3136156525068552552373967 := by
  unfold tailWord_6107643
  simp only [CollatzResearch.WordTrace]
  refine ⟨222764041012059988223887583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148509360674706658815925055 222764041012059988223887583)
  ·
    refine ⟨334146061518089982335831375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222764041012059988223887583 334146061518089982335831375)
    ·
      refine ⟨501219092277134973503747063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 334146061518089982335831375 501219092277134973503747063)
      ·
        refine ⟨751828638415702460255620595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 501219092277134973503747063 751828638415702460255620595)
        ·
          refine ⟨1127742957623553690383430893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 751828638415702460255620595 1127742957623553690383430893)
          ·
            refine ⟨422903609108832633893786585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1127742957623553690383430893 422903609108832633893786585)
            ·
              refine ⟨317177706831624475420339939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 422903609108832633893786585 317177706831624475420339939)
              ·
                refine ⟨475766560247436713130509909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 317177706831624475420339939 475766560247436713130509909)
                ·
                  refine ⟨5575389377899648981998163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 475766560247436713130509909 5575389377899648981998163)
                  ·
                    refine ⟨8363084066849473472997245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5575389377899648981998163 8363084066849473472997245)
                    ·
                      refine ⟨3136156525068552552373967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8363084066849473472997245 3136156525068552552373967)
                      ·
                        rfl

theorem cell23_6107643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 8, 1, 3].length) (baseStart_6107643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6107643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6107643 prefixEnd_6107643 := by exact prefixLift 6107643
  have htrace : WordTrace (prefixWord ++ tailWord_6107643) baseStart_6107643 baseEnd_6107643 := by
    simpa [prefixWord, tailWord_6107643, baseEnd_6107643] using wordTrace_append hprefix tailTrace_6107643
  have hstable : (prefixWord ++ tailWord_6107643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6107643).length < 2 ^ (prefixWord ++ tailWord_6107643).sum := by decide
  have hdescent : baseEnd_6107643 < baseStart_6107643 := by decide
  rcases family_descends (prefixWord ++ tailWord_6107643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6107650 : List Nat := [3, 4, 1, 2, 2, 1, 1, 9]
def baseStart_6107650 : Nat := 118140960795 + 6107650 * 2 ^ 59
def prefixEnd_6107650 : Nat := 4983230072969 + 3 ^ 40 * 6107650 * 2
def baseEnd_6107650 : Nat := 116154078497523482406905

theorem tailTrace_6107650 : CollatzResearch.WordTrace tailWord_6107650 prefixEnd_6107650 116154078497523482406905 := by
  unfold tailWord_6107650
  simp only [CollatzResearch.WordTrace]
  refine ⟨55691074080758657104848101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148509530882023085612928269 55691074080758657104848101)
  ·
    refine ⟨10442076390142248207159019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55691074080758657104848101 10442076390142248207159019)
    ·
      refine ⟨15663114585213372310738529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10442076390142248207159019 15663114585213372310738529)
      ·
        refine ⟨11747335938910029233053897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15663114585213372310738529 11747335938910029233053897)
        ·
          refine ⟨8810501954182521924790423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11747335938910029233053897 8810501954182521924790423)
          ·
            refine ⟨13215752931273782887185635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8810501954182521924790423 13215752931273782887185635)
            ·
              refine ⟨19823629396910674330778453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13215752931273782887185635 19823629396910674330778453)
              ·
                refine ⟨116154078497523482406905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19823629396910674330778453 116154078497523482406905)
                ·
                  rfl

theorem cell23_6107650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 9].length) (baseStart_6107650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6107650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6107650 prefixEnd_6107650 := by exact prefixLift 6107650
  have htrace : WordTrace (prefixWord ++ tailWord_6107650) baseStart_6107650 baseEnd_6107650 := by
    simpa [prefixWord, tailWord_6107650, baseEnd_6107650] using wordTrace_append hprefix tailTrace_6107650
  have hstable : (prefixWord ++ tailWord_6107650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6107650).length < 2 ^ (prefixWord ++ tailWord_6107650).sum := by decide
  have hdescent : baseEnd_6107650 < baseStart_6107650 := by decide
  rcases family_descends (prefixWord ++ tailWord_6107650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6107654 : List Nat := [6, 2, 1, 1, 1, 1, 1, 2, 4, 4]
def baseStart_6107654 : Nat := 118140960795 + 6107654 * 2 ^ 59
def prefixEnd_6107654 : Nat := 4983230072969 + 3 ^ 40 * 6107654 * 2
def baseEnd_6107654 : Nat := 1045387391118584003112139

theorem tailTrace_6107654 : CollatzResearch.WordTrace tailWord_6107654 prefixEnd_6107654 1045387391118584003112139 := by
  unfold tailWord_6107654
  simp only [CollatzResearch.WordTrace]
  refine ⟨6961388819219379284454313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 148509628143346758068358677 6961388819219379284454313)
  ·
    refine ⟨5221041614414534463340735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6961388819219379284454313 5221041614414534463340735)
    ·
      refine ⟨7831562421621801695011103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5221041614414534463340735 7831562421621801695011103)
      ·
        refine ⟨11747343632432702542516655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7831562421621801695011103 11747343632432702542516655)
        ·
          refine ⟨17621015448649053813774983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11747343632432702542516655 17621015448649053813774983)
          ·
            refine ⟨26431523172973580720662475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17621015448649053813774983 26431523172973580720662475)
            ·
              refine ⟨39647284759460371080993713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26431523172973580720662475 39647284759460371080993713)
              ·
                refine ⟨29735463569595278310745285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39647284759460371080993713 29735463569595278310745285)
                ·
                  refine ⟨5575399419299114683264741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29735463569595278310745285 5575399419299114683264741)
                  ·
                    refine ⟨1045387391118584003112139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5575399419299114683264741 1045387391118584003112139)
                    ·
                      rfl

theorem cell23_6107654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_6107654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6107654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6107654 prefixEnd_6107654 := by exact prefixLift 6107654
  have htrace : WordTrace (prefixWord ++ tailWord_6107654) baseStart_6107654 baseEnd_6107654 := by
    simpa [prefixWord, tailWord_6107654, baseEnd_6107654] using wordTrace_append hprefix tailTrace_6107654
  have hstable : (prefixWord ++ tailWord_6107654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6107654).length < 2 ^ (prefixWord ++ tailWord_6107654).sum := by decide
  have hdescent : baseEnd_6107654 < baseStart_6107654 := by decide
  rcases family_descends (prefixWord ++ tailWord_6107654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6107660 : List Nat := [2, 2, 1, 2, 4, 1, 1, 2, 4, 1, 3]
def baseStart_6107660 : Nat := 118140960795 + 6107660 * 2 ^ 59
def prefixEnd_6107660 : Nat := 4983230072969 + 3 ^ 40 * 6107660 * 2
def baseEnd_6107660 : Nat := 3136165254239678985861389

theorem tailTrace_6107660 : CollatzResearch.WordTrace tailWord_6107660 prefixEnd_6107660 3136165254239678985861389 := by
  unfold tailWord_6107660
  simp only [CollatzResearch.WordTrace]
  refine ⟨111382330526499200063628217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148509774035332266751504289 111382330526499200063628217)
  ·
    refine ⟨83536747894874400047721163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111382330526499200063628217 83536747894874400047721163)
    ·
      refine ⟨125305121842311600071581745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83536747894874400047721163 125305121842311600071581745)
      ·
        refine ⟨93978841381733700053686309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125305121842311600071581745 93978841381733700053686309)
        ·
          refine ⟨17621032759075068760066183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93978841381733700053686309 17621032759075068760066183)
          ·
            refine ⟨26431549138612603140099275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17621032759075068760066183 26431549138612603140099275)
            ·
              refine ⟨39647323707918904710148913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26431549138612603140099275 39647323707918904710148913)
              ·
                refine ⟨29735492780939178532611685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39647323707918904710148913 29735492780939178532611685)
                ·
                  refine ⟨5575404896426095974864691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29735492780939178532611685 5575404896426095974864691)
                  ·
                    refine ⟨8363107344639143962297037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5575404896426095974864691 8363107344639143962297037)
                    ·
                      refine ⟨3136165254239678985861389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8363107344639143962297037 3136165254239678985861389)
                      ·
                        rfl

theorem cell23_6107660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 2, 4, 1, 3].length) (baseStart_6107660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6107660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6107660 prefixEnd_6107660 := by exact prefixLift 6107660
  have htrace : WordTrace (prefixWord ++ tailWord_6107660) baseStart_6107660 baseEnd_6107660 := by
    simpa [prefixWord, tailWord_6107660, baseEnd_6107660] using wordTrace_append hprefix tailTrace_6107660
  have hstable : (prefixWord ++ tailWord_6107660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6107660).length < 2 ^ (prefixWord ++ tailWord_6107660).sum := by decide
  have hdescent : baseEnd_6107660 < baseStart_6107660 := by decide
  rcases family_descends (prefixWord ++ tailWord_6107660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6107694 : List Nat := [4, 1, 3, 1, 3, 1, 1, 3, 2, 1, 3]
def baseStart_6107694 : Nat := 118140960795 + 6107694 * 2 ^ 59
def prefixEnd_6107694 : Nat := 4983230072969 + 3 ^ 40 * 6107694 * 2
def baseEnd_6107694 : Nat := 3136182712581931852836233

theorem tailTrace_6107694 : CollatzResearch.WordTrace tailWord_6107694 prefixEnd_6107694 3136182712581931852836233 := by
  unfold tailWord_6107694
  simp only [CollatzResearch.WordTrace]
  refine ⟨27845737641859402991749267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148510600756583482622662757 27845737641859402991749267)
  ·
    refine ⟨41768606462789104487623901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27845737641859402991749267 41768606462789104487623901)
    ·
      refine ⟨15663227423545914182858963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41768606462789104487623901 15663227423545914182858963)
      ·
        refine ⟨23494841135318871274288445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15663227423545914182858963 23494841135318871274288445)
        ·
          refine ⟨8810565425744576727858167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23494841135318871274288445 8810565425744576727858167)
          ·
            refine ⟨13215848138616865091787251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8810565425744576727858167 13215848138616865091787251)
            ·
              refine ⟨19823772207925297637680877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13215848138616865091787251 19823772207925297637680877)
              ·
                refine ⟨7433914577971986614130329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19823772207925297637680877 7433914577971986614130329)
                ·
                  refine ⟨5575435933478989960597747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7433914577971986614130329 5575435933478989960597747)
                  ·
                    refine ⟨8363153900218484940896621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5575435933478989960597747 8363153900218484940896621)
                    ·
                      refine ⟨3136182712581931852836233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8363153900218484940896621 3136182712581931852836233)
                      ·
                        rfl

theorem cell23_6107694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 3, 2, 1, 3].length) (baseStart_6107694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6107694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6107694 prefixEnd_6107694 := by exact prefixLift 6107694
  have htrace : WordTrace (prefixWord ++ tailWord_6107694) baseStart_6107694 baseEnd_6107694 := by
    simpa [prefixWord, tailWord_6107694, baseEnd_6107694] using wordTrace_append hprefix tailTrace_6107694
  have hstable : (prefixWord ++ tailWord_6107694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6107694).length < 2 ^ (prefixWord ++ tailWord_6107694).sum := by decide
  have hdescent : baseEnd_6107694 < baseStart_6107694 := by decide
  rcases family_descends (prefixWord ++ tailWord_6107694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6107790 : List Nat := [4, 1, 1, 3, 1, 1, 2, 1, 4, 1, 4]
def baseStart_6107790 : Nat := 118140960795 + 6107790 * 2 ^ 59
def prefixEnd_6107790 : Nat := 4983230072969 + 3 ^ 40 * 6107790 * 2
def baseEnd_6107790 : Nat := 3136232006724763477235791

theorem tailTrace_6107790 : CollatzResearch.WordTrace tailWord_6107790 prefixEnd_6107790 3136232006724763477235791 := by
  unfold tailWord_6107790
  simp only [CollatzResearch.WordTrace]
  refine ⟨27846175317815929041186103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148512935028351621552992549 27846175317815929041186103)
  ·
    refine ⟨41769262976723893561779155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27846175317815929041186103 41769262976723893561779155)
    ·
      refine ⟨62653894465085840342668733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41769262976723893561779155 62653894465085840342668733)
      ·
        refine ⟨23495210424407190128500775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62653894465085840342668733 23495210424407190128500775)
        ·
          refine ⟨35242815636610785192751163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23495210424407190128500775 35242815636610785192751163)
          ·
            refine ⟨52864223454916177789126745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35242815636610785192751163 52864223454916177789126745)
            ·
              refine ⟨39648167591187133341845059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52864223454916177789126745 39648167591187133341845059)
              ·
                refine ⟨59472251386780700012767589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39648167591187133341845059 59472251386780700012767589)
                ·
                  refine ⟨11151047135021381252393923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59472251386780700012767589 11151047135021381252393923)
                  ·
                    refine ⟨16726570702532071878590885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11151047135021381252393923 16726570702532071878590885)
                    ·
                      refine ⟨3136232006724763477235791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16726570702532071878590885 3136232006724763477235791)
                      ·
                        rfl

theorem cell23_6107790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_6107790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6107790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6107790 prefixEnd_6107790 := by exact prefixLift 6107790
  have htrace : WordTrace (prefixWord ++ tailWord_6107790) baseStart_6107790 baseEnd_6107790 := by
    simpa [prefixWord, tailWord_6107790, baseEnd_6107790] using wordTrace_append hprefix tailTrace_6107790
  have hstable : (prefixWord ++ tailWord_6107790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6107790).length < 2 ^ (prefixWord ++ tailWord_6107790).sum := by decide
  have hdescent : baseEnd_6107790 < baseStart_6107790 := by decide
  rcases family_descends (prefixWord ++ tailWord_6107790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6107877 : List Nat := [1, 3, 1, 4, 1, 2, 3, 2, 1, 5]
def baseStart_6107877 : Nat := 118140960795 + 6107877 * 2 ^ 59
def prefixEnd_6107877 : Nat := 4983230072969 + 3 ^ 40 * 6107877 * 2
def baseEnd_6107877 : Nat := 1045425559847234878949297

theorem tailTrace_6107877 : CollatzResearch.WordTrace tailWord_6107877 prefixEnd_6107877 1045425559847234878949297 := by
  unfold tailWord_6107877
  simp only [CollatzResearch.WordTrace]
  refine ⟨222772575693212246187905885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148515050462141497458603923 222772575693212246187905885)
  ·
    refine ⟨83539715884954592320464707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 222772575693212246187905885 83539715884954592320464707)
    ·
      refine ⟨125309573827431888480697061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83539715884954592320464707 125309573827431888480697061)
      ·
        refine ⟨23495545092643479090130699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 125309573827431888480697061 23495545092643479090130699)
        ·
          refine ⟨35243317638965218635196049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23495545092643479090130699 35243317638965218635196049)
          ·
            refine ⟨26432488229223913976397037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35243317638965218635196049 26432488229223913976397037)
            ·
              refine ⟨9912183085958967741148889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26432488229223913976397037 9912183085958967741148889)
              ·
                refine ⟨7434137314469225805861667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9912183085958967741148889 7434137314469225805861667)
                ·
                  refine ⟨11151205971703838708792501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7434137314469225805861667 11151205971703838708792501)
                  ·
                    refine ⟨1045425559847234878949297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11151205971703838708792501 1045425559847234878949297)
                    ·
                      rfl

theorem cell23_6107877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 3, 2, 1, 5].length) (baseStart_6107877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6107877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6107877 prefixEnd_6107877 := by exact prefixLift 6107877
  have htrace : WordTrace (prefixWord ++ tailWord_6107877) baseStart_6107877 baseEnd_6107877 := by
    simpa [prefixWord, tailWord_6107877, baseEnd_6107877] using wordTrace_append hprefix tailTrace_6107877
  have hstable : (prefixWord ++ tailWord_6107877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6107877).length < 2 ^ (prefixWord ++ tailWord_6107877).sum := by decide
  have hdescent : baseEnd_6107877 < baseStart_6107877 := by decide
  rcases family_descends (prefixWord ++ tailWord_6107877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6107890 : List Nat := [3, 2, 1, 3, 1, 2, 1, 1, 3, 6]
def baseStart_6107890 : Nat := 118140960795 + 6107890 * 2 ^ 59
def prefixEnd_6107890 : Nat := 4983230072969 + 3 ^ 40 * 6107890 * 2
def baseEnd_6107890 : Nat := 1045427784930071028661777

theorem tailTrace_6107890 : CollatzResearch.WordTrace tailWord_6107890 prefixEnd_6107890 1045427784930071028661777 := by
  unfold tailWord_6107890
  simp only [CollatzResearch.WordTrace]
  refine ⟨55693262460541287352032281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148515366561443432938752749 55693262460541287352032281)
  ·
    refine ⟨41769946845405965514024211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55693262460541287352032281 41769946845405965514024211)
    ·
      refine ⟨62654920268108948271036317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41769946845405965514024211 62654920268108948271036317)
      ·
        refine ⟨23495595100540855601638619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62654920268108948271036317 23495595100540855601638619)
        ·
          refine ⟨35243392650811283402457929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23495595100540855601638619 35243392650811283402457929)
          ·
            refine ⟨26432544488108462551843447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35243392650811283402457929 26432544488108462551843447)
            ·
              refine ⟨39648816732162693827765171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26432544488108462551843447 39648816732162693827765171)
              ·
                refine ⟨59473225098244040741647757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39648816732162693827765171 59473225098244040741647757)
                ·
                  refine ⟨22302459411841515278117909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59473225098244040741647757 22302459411841515278117909)
                  ·
                    refine ⟨1045427784930071028661777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22302459411841515278117909 1045427784930071028661777)
                    ·
                      rfl

theorem cell23_6107890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 1, 3, 6].length) (baseStart_6107890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6107890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6107890 prefixEnd_6107890 := by exact prefixLift 6107890
  have htrace : WordTrace (prefixWord ++ tailWord_6107890) baseStart_6107890 baseEnd_6107890 := by
    simpa [prefixWord, tailWord_6107890, baseEnd_6107890] using wordTrace_append hprefix tailTrace_6107890
  have hstable : (prefixWord ++ tailWord_6107890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6107890).length < 2 ^ (prefixWord ++ tailWord_6107890).sum := by decide
  have hdescent : baseEnd_6107890 < baseStart_6107890 := by decide
  rcases family_descends (prefixWord ++ tailWord_6107890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6107894 : List Nat := [5, 1, 1, 1, 1, 2, 5, 1, 1, 5]
def baseStart_6107894 : Nat := 118140960795 + 6107894 * 2 ^ 59
def prefixEnd_6107894 : Nat := 4983230072969 + 3 ^ 40 * 6107894 * 2
def baseEnd_6107894 : Nat := 1045428469570943690111771

theorem tailTrace_6107894 : CollatzResearch.WordTrace tailWord_6107894 prefixEnd_6107894 1045428469570943690111771 := by
  unfold tailWord_6107894
  simp only [CollatzResearch.WordTrace]
  refine ⟨13923324733384416130704671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 148515463822767105394183157 13923324733384416130704671)
  ·
    refine ⟨20884987100076624196057007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13923324733384416130704671 20884987100076624196057007)
    ·
      refine ⟨31327480650114936294085511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20884987100076624196057007 31327480650114936294085511)
      ·
        refine ⟨46991220975172404441128267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31327480650114936294085511 46991220975172404441128267)
        ·
          refine ⟨70486831462758606661692401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46991220975172404441128267 70486831462758606661692401)
          ·
            refine ⟨52865123597068954996269301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70486831462758606661692401 52865123597068954996269301)
            ·
              refine ⟨4956105337225214530900247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52865123597068954996269301 4956105337225214530900247)
              ·
                refine ⟨7434158005837821796350371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4956105337225214530900247 7434158005837821796350371)
                ·
                  refine ⟨11151237008756732694525557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7434158005837821796350371 11151237008756732694525557)
                  ·
                    refine ⟨1045428469570943690111771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11151237008756732694525557 1045428469570943690111771)
                    ·
                      rfl

theorem cell23_6107894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 5, 1, 1, 5].length) (baseStart_6107894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6107894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6107894 prefixEnd_6107894 := by exact prefixLift 6107894
  have htrace : WordTrace (prefixWord ++ tailWord_6107894) baseStart_6107894 baseEnd_6107894 := by
    simpa [prefixWord, tailWord_6107894, baseEnd_6107894] using wordTrace_append hprefix tailTrace_6107894
  have hstable : (prefixWord ++ tailWord_6107894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6107894).length < 2 ^ (prefixWord ++ tailWord_6107894).sum := by decide
  have hdescent : baseEnd_6107894 < baseStart_6107894 := by decide
  rcases family_descends (prefixWord ++ tailWord_6107894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6107914 : List Nat := [3, 1, 2, 2, 1, 2, 2, 3, 3, 2, 2]
def baseStart_6107914 : Nat := 118140960795 + 6107914 * 2 ^ 59
def prefixEnd_6107914 : Nat := 4983230072969 + 3 ^ 40 * 6107914 * 2
def baseEnd_6107914 : Nat := 3136295678325920992085221

theorem tailTrace_6107914 : CollatzResearch.WordTrace tailWord_6107914 prefixEnd_6107914 3136295678325920992085221 := by
  unfold tailWord_6107914
  simp only [CollatzResearch.WordTrace]
  refine ⟨55693481298519550376750699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148515950129385467671335197 55693481298519550376750699)
  ·
    refine ⟨83540221947779325565126049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55693481298519550376750699 83540221947779325565126049)
    ·
      refine ⟨62655166460834494173844537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83540221947779325565126049 62655166460834494173844537)
      ·
        refine ⟨46991374845625870630383403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62655166460834494173844537 46991374845625870630383403)
        ·
          refine ⟨70487062268438805945575105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46991374845625870630383403 70487062268438805945575105)
          ·
            refine ⟨52865296701329104459181329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70487062268438805945575105 52865296701329104459181329)
            ·
              refine ⟨39648972525996828344385997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52865296701329104459181329 39648972525996828344385997)
              ·
                refine ⟨14868364697248810629144749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39648972525996828344385997 14868364697248810629144749)
                ·
                  refine ⟨5575636761468303985929281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14868364697248810629144749 5575636761468303985929281)
                  ·
                    refine ⟨4181727571101227989446961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5575636761468303985929281 4181727571101227989446961)
                    ·
                      refine ⟨3136295678325920992085221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4181727571101227989446961 3136295678325920992085221)
                      ·
                        rfl

theorem cell23_6107914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 3, 3, 2, 2].length) (baseStart_6107914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6107914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6107914 prefixEnd_6107914 := by exact prefixLift 6107914
  have htrace : WordTrace (prefixWord ++ tailWord_6107914) baseStart_6107914 baseEnd_6107914 := by
    simpa [prefixWord, tailWord_6107914, baseEnd_6107914] using wordTrace_append hprefix tailTrace_6107914
  have hstable : (prefixWord ++ tailWord_6107914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6107914).length < 2 ^ (prefixWord ++ tailWord_6107914).sum := by decide
  have hdescent : baseEnd_6107914 < baseStart_6107914 := by decide
  rcases family_descends (prefixWord ++ tailWord_6107914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6107958 : List Nat := [5, 1, 2, 2, 2, 2, 1, 2, 2, 4]
def baseStart_6107958 : Nat := 118140960795 + 6107958 * 2 ^ 59
def prefixEnd_6107958 : Nat := 4983230072969 + 3 ^ 40 * 6107958 * 2
def baseEnd_6107958 : Nat := 1045439423824906273311673

theorem tailTrace_6107958 : CollatzResearch.WordTrace tailWord_6107958 prefixEnd_6107958 1045439423824906273311673 := by
  unfold tailWord_6107958
  simp only [CollatzResearch.WordTrace]
  refine ⟨13923470625369924813850283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 148517020003945864681069685 13923470625369924813850283)
  ·
    refine ⟨20885205938054887220775425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13923470625369924813850283 20885205938054887220775425)
    ·
      refine ⟨15663904453541165415581569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20885205938054887220775425 15663904453541165415581569)
      ·
        refine ⟨11747928340155874061686177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15663904453541165415581569 11747928340155874061686177)
        ·
          refine ⟨8810946255116905546264633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11747928340155874061686177 8810946255116905546264633)
          ·
            refine ⟨6608209691337679159698475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8810946255116905546264633 6608209691337679159698475)
            ·
              refine ⟨9912314537006518739547713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6608209691337679159698475 9912314537006518739547713)
              ·
                refine ⟨7434235902754889054660785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9912314537006518739547713 7434235902754889054660785)
                ·
                  refine ⟨5575676927066166790995589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7434235902754889054660785 5575676927066166790995589)
                  ·
                    refine ⟨1045439423824906273311673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5575676927066166790995589 1045439423824906273311673)
                    ·
                      rfl

theorem cell23_6107958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 1, 2, 2, 4].length) (baseStart_6107958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6107958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6107958 prefixEnd_6107958 := by exact prefixLift 6107958
  have htrace : WordTrace (prefixWord ++ tailWord_6107958) baseStart_6107958 baseEnd_6107958 := by
    simpa [prefixWord, tailWord_6107958, baseEnd_6107958] using wordTrace_append hprefix tailTrace_6107958
  have hstable : (prefixWord ++ tailWord_6107958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6107958).length < 2 ^ (prefixWord ++ tailWord_6107958).sum := by decide
  have hdescent : baseEnd_6107958 < baseStart_6107958 := by decide
  rcases family_descends (prefixWord ++ tailWord_6107958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6107991 : List Nat := [1, 1, 3, 2, 4, 2, 2, 2, 1, 3, 2]
def baseStart_6107991 : Nat := 118140960795 + 6107991 * 2 ^ 59
def prefixEnd_6107991 : Nat := 4983230072969 + 3 ^ 40 * 6107991 * 2
def baseEnd_6107991 : Nat := 3136335216336317190822367

theorem tailTrace_6107991 : CollatzResearch.WordTrace tailWord_6107991 prefixEnd_6107991 3136335216336317190822367 := by
  unfold tailWord_6107991
  simp only [CollatzResearch.WordTrace]
  refine ⟨222776733614799243657555827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148517822409866162438370551 222776733614799243657555827)
  ·
    refine ⟨334165100422198865486333741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222776733614799243657555827 334165100422198865486333741)
    ·
      refine ⟨125311912658324574557375153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 334165100422198865486333741 125311912658324574557375153)
      ·
        refine ⟨93983934493743430918031365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125311912658324574557375153 93983934493743430918031365)
        ·
          refine ⟨17621987717576893297130881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93983934493743430918031365 17621987717576893297130881)
          ·
            refine ⟨13216490788182669972848161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17621987717576893297130881 13216490788182669972848161)
            ·
              refine ⟨9912368091137002479636121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13216490788182669972848161 9912368091137002479636121)
              ·
                refine ⟨7434276068352751859727091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9912368091137002479636121 7434276068352751859727091)
                ·
                  refine ⟨11151414102529127789590637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7434276068352751859727091 11151414102529127789590637)
                  ·
                    refine ⟨4181780288448422921096489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11151414102529127789590637 4181780288448422921096489)
                    ·
                      refine ⟨3136335216336317190822367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4181780288448422921096489 3136335216336317190822367)
                      ·
                        rfl

theorem cell23_6107991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 2, 2, 1, 3, 2].length) (baseStart_6107991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6107991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6107991 prefixEnd_6107991 := by exact prefixLift 6107991
  have htrace : WordTrace (prefixWord ++ tailWord_6107991) baseStart_6107991 baseEnd_6107991 := by
    simpa [prefixWord, tailWord_6107991, baseEnd_6107991] using wordTrace_append hprefix tailTrace_6107991
  have hstable : (prefixWord ++ tailWord_6107991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6107991).length < 2 ^ (prefixWord ++ tailWord_6107991).sum := by decide
  have hdescent : baseEnd_6107991 < baseStart_6107991 := by decide
  rcases family_descends (prefixWord ++ tailWord_6107991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6108007 : List Nat := [1, 1, 5, 1, 2, 3, 1, 1, 2, 1, 5]
def baseStart_6108007 : Nat := 118140960795 + 6108007 * 2 ^ 59
def prefixEnd_6108007 : Nat := 4983230072969 + 3 ^ 40 * 6108007 * 2
def baseEnd_6108007 : Nat := 3136343432026789128222293

theorem tailTrace_6108007 : CollatzResearch.WordTrace tailWord_6108007 prefixEnd_6108007 3136343432026789128222293 := by
  unfold tailWord_6108007
  simp only [CollatzResearch.WordTrace]
  refine ⟨222777317182741278390138275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148518211455160852260092183 222777317182741278390138275)
  ·
    refine ⟨334165975774111917585207413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222777317182741278390138275 334165975774111917585207413)
    ·
      refine ⟨31328060228822992273613195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 334165975774111917585207413 31328060228822992273613195)
      ·
        refine ⟨46992090343234488410419793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31328060228822992273613195 46992090343234488410419793)
        ·
          refine ⟨35244067757425866307814845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46992090343234488410419793 35244067757425866307814845)
          ·
            refine ⟨13216525409034699865430567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35244067757425866307814845 13216525409034699865430567)
            ·
              refine ⟨19824788113552049798145851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13216525409034699865430567 19824788113552049798145851)
              ·
                refine ⟨29737182170328074697218777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19824788113552049798145851 29737182170328074697218777)
                ·
                  refine ⟨22302886627746056022914083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29737182170328074697218777 22302886627746056022914083)
                  ·
                    refine ⟨33454329941619084034371125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22302886627746056022914083 33454329941619084034371125)
                    ·
                      refine ⟨3136343432026789128222293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33454329941619084034371125 3136343432026789128222293)
                      ·
                        rfl

theorem cell23_6108007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 1, 2, 1, 5].length) (baseStart_6108007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6108007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6108007 prefixEnd_6108007 := by exact prefixLift 6108007
  have htrace : WordTrace (prefixWord ++ tailWord_6108007) baseStart_6108007 baseEnd_6108007 := by
    simpa [prefixWord, tailWord_6108007, baseEnd_6108007] using wordTrace_append hprefix tailTrace_6108007
  have hstable : (prefixWord ++ tailWord_6108007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6108007).length < 2 ^ (prefixWord ++ tailWord_6108007).sum := by decide
  have hdescent : baseEnd_6108007 < baseStart_6108007 := by decide
  rcases family_descends (prefixWord ++ tailWord_6108007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6108021 : List Nat := [1, 3, 4, 1, 1, 2, 2, 1, 4, 2, 2]
def baseStart_6108021 : Nat := 118140960795 + 6108021 * 2 ^ 59
def prefixEnd_6108021 : Nat := 4983230072969 + 3 ^ 40 * 6108021 * 2
def baseEnd_6108021 : Nat := 3136350620755952073447229

theorem tailTrace_6108021 : CollatzResearch.WordTrace tailWord_6108021 prefixEnd_6108021 3136350620755952073447229 := by
  unfold tailWord_6108021
  simp only [CollatzResearch.WordTrace]
  refine ⟨222777827804690558781147917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148518551869793705854098611 222777827804690558781147917)
  ·
    refine ⟨83541685426758959542930469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 222777827804690558781147917 83541685426758959542930469)
    ·
      refine ⟨15664066017517304914299463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83541685426758959542930469 15664066017517304914299463)
      ·
        refine ⟨23496099026275957371449195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15664066017517304914299463 23496099026275957371449195)
        ·
          refine ⟨35244148539413936057173793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23496099026275957371449195 35244148539413936057173793)
          ·
            refine ⟨26433111404560452042880345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35244148539413936057173793 26433111404560452042880345)
            ·
              refine ⟨19824833553420339032160259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26433111404560452042880345 19824833553420339032160259)
              ·
                refine ⟨29737250330130508548240389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19824833553420339032160259 29737250330130508548240389)
                ·
                  refine ⟨5575734436899470352795073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29737250330130508548240389 5575734436899470352795073)
                  ·
                    refine ⟨4181800827674602764596305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5575734436899470352795073 4181800827674602764596305)
                    ·
                      refine ⟨3136350620755952073447229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4181800827674602764596305 3136350620755952073447229)
                      ·
                        rfl

theorem cell23_6108021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 1, 4, 2, 2].length) (baseStart_6108021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6108021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6108021 prefixEnd_6108021 := by exact prefixLift 6108021
  have htrace : WordTrace (prefixWord ++ tailWord_6108021) baseStart_6108021 baseEnd_6108021 := by
    simpa [prefixWord, tailWord_6108021, baseEnd_6108021] using wordTrace_append hprefix tailTrace_6108021
  have hstable : (prefixWord ++ tailWord_6108021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6108021).length < 2 ^ (prefixWord ++ tailWord_6108021).sum := by decide
  have hdescent : baseEnd_6108021 < baseStart_6108021 := by decide
  rcases family_descends (prefixWord ++ tailWord_6108021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6108027 : List Nat := [1, 1, 1, 1, 1, 5, 2, 6, 5]
def baseStart_6108027 : Nat := 118140960795 + 6108027 * 2 ^ 59
def prefixEnd_6108027 : Nat := 4983230072969 + 3 ^ 40 * 6108027 * 2
def baseEnd_6108027 : Nat := 348483744626653227774689

theorem tailTrace_6108027 : CollatzResearch.WordTrace tailWord_6108027 prefixEnd_6108027 348483744626653227774689 := by
  unfold tailWord_6108027
  simp only [CollatzResearch.WordTrace]
  refine ⟨222778046642668821805866335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148518697761779214537244223 222778046642668821805866335)
  ·
    refine ⟨334167069964003232708799503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222778046642668821805866335 334167069964003232708799503)
    ·
      refine ⟨501250604946004849063199255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 334167069964003232708799503 501250604946004849063199255)
      ·
        refine ⟨751875907419007273594798883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 501250604946004849063199255 751875907419007273594798883)
        ·
          refine ⟨1127813861128510910392198325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 751875907419007273594798883 1127813861128510910392198325)
          ·
            refine ⟨105732549480797897849268593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1127813861128510910392198325 105732549480797897849268593)
            ·
              refine ⟨79299412110598423386951445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 105732549480797897849268593 79299412110598423386951445)
              ·
                refine ⟨3717159942684301096263349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 79299412110598423386951445 3717159942684301096263349)
                ·
                  refine ⟨348483744626653227774689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3717159942684301096263349 348483744626653227774689)
                  ·
                    rfl

theorem cell23_6108027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 6, 5].length) (baseStart_6108027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6108027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6108027 prefixEnd_6108027 := by exact prefixLift 6108027
  have htrace : WordTrace (prefixWord ++ tailWord_6108027) baseStart_6108027 baseEnd_6108027 := by
    simpa [prefixWord, tailWord_6108027, baseEnd_6108027] using wordTrace_append hprefix tailTrace_6108027
  have hstable : (prefixWord ++ tailWord_6108027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6108027).length < 2 ^ (prefixWord ++ tailWord_6108027).sum := by decide
  have hdescent : baseEnd_6108027 < baseStart_6108027 := by decide
  rcases family_descends (prefixWord ++ tailWord_6108027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6108121 : List Nat := [1, 2, 1, 2, 5, 1, 1, 5, 1, 4]
def baseStart_6108121 : Nat := 118140960795 + 6108121 * 2 ^ 59
def prefixEnd_6108121 : Nat := 4983230072969 + 3 ^ 40 * 6108121 * 2
def baseEnd_6108121 : Nat := 1045467322940467227398923

theorem tailTrace_6108121 : CollatzResearch.WordTrace tailWord_6108121 prefixEnd_6108121 1045467322940467227398923 := by
  unfold tailWord_6108121
  simp only [CollatzResearch.WordTrace]
  refine ⟨222781475104328275859788217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148520983402885517239858811 222781475104328275859788217)
  ·
    refine ⟨167086106328246206894841163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222781475104328275859788217 167086106328246206894841163)
    ·
      refine ⟨250629159492369310342261745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167086106328246206894841163 250629159492369310342261745)
      ·
        refine ⟨187971869619276982756696309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 250629159492369310342261745 187971869619276982756696309)
        ·
          refine ⟨17622362776807217133440279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 187971869619276982756696309 17622362776807217133440279)
          ·
            refine ⟨26433544165210825700160419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17622362776807217133440279 26433544165210825700160419)
            ·
              refine ⟨39650316247816238550240629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26433544165210825700160419 39650316247816238550240629)
              ·
                refine ⟨3717217148232772364085059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39650316247816238550240629 3717217148232772364085059)
                ·
                  refine ⟨5575825722349158546127589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3717217148232772364085059 5575825722349158546127589)
                  ·
                    refine ⟨1045467322940467227398923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5575825722349158546127589 1045467322940467227398923)
                    ·
                      rfl

theorem cell23_6108121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 5, 1, 4].length) (baseStart_6108121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6108121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6108121 prefixEnd_6108121 := by exact prefixLift 6108121
  have htrace : WordTrace (prefixWord ++ tailWord_6108121) baseStart_6108121 baseEnd_6108121 := by
    simpa [prefixWord, tailWord_6108121, baseEnd_6108121] using wordTrace_append hprefix tailTrace_6108121
  have hstable : (prefixWord ++ tailWord_6108121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6108121).length < 2 ^ (prefixWord ++ tailWord_6108121).sum := by decide
  have hdescent : baseEnd_6108121 < baseStart_6108121 := by decide
  rcases family_descends (prefixWord ++ tailWord_6108121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6108161 : List Nat := [1, 2, 4, 1, 2, 2, 2, 2, 3, 1, 3]
def baseStart_6108161 : Nat := 118140960795 + 6108161 * 2 ^ 59
def prefixEnd_6108161 : Nat := 4983230072969 + 3 ^ 40 * 6108161 * 2
def baseEnd_6108161 : Nat := 3136422508047581525696585

theorem tailTrace_6108161 : CollatzResearch.WordTrace tailWord_6108161 prefixEnd_6108161 3136422508047581525696585 := by
  unfold tailWord_6108161
  simp only [CollatzResearch.WordTrace]
  refine ⟨222782934024183362691244337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148521956016122241794162891 222782934024183362691244337)
  ·
    refine ⟨167087200518137522018433253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222782934024183362691244337 167087200518137522018433253)
    ·
      refine ⟨31328850097150785378456235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 167087200518137522018433253 31328850097150785378456235)
      ·
        refine ⟨46993275145726178067684353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31328850097150785378456235 46993275145726178067684353)
        ·
          refine ⟨35244956359294633550763265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46993275145726178067684353 35244956359294633550763265)
          ·
            refine ⟨26433717269470975163072449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35244956359294633550763265 26433717269470975163072449)
            ·
              refine ⟨19825287952103231372304337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26433717269470975163072449 19825287952103231372304337)
              ·
                refine ⟨14868965964077423529228253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19825287952103231372304337 14868965964077423529228253)
                ·
                  refine ⟨5575862236529033823460595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14868965964077423529228253 5575862236529033823460595)
                  ·
                    refine ⟨8363793354793550735190893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5575862236529033823460595 8363793354793550735190893)
                    ·
                      refine ⟨3136422508047581525696585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8363793354793550735190893 3136422508047581525696585)
                      ·
                        rfl

theorem cell23_6108161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 2, 3, 1, 3].length) (baseStart_6108161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6108161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6108161 prefixEnd_6108161 := by exact prefixLift 6108161
  have htrace : WordTrace (prefixWord ++ tailWord_6108161) baseStart_6108161 baseEnd_6108161 := by
    simpa [prefixWord, tailWord_6108161, baseEnd_6108161] using wordTrace_append hprefix tailTrace_6108161
  have hstable : (prefixWord ++ tailWord_6108161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6108161).length < 2 ^ (prefixWord ++ tailWord_6108161).sum := by decide
  have hdescent : baseEnd_6108161 < baseStart_6108161 := by decide
  rcases family_descends (prefixWord ++ tailWord_6108161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6108177 : List Nat := [1, 2, 2, 1, 1, 2, 1, 6, 1, 6]
def baseStart_6108177 : Nat := 118140960795 + 6108177 * 2 ^ 59
def prefixEnd_6108177 : Nat := 4983230072969 + 3 ^ 40 * 6108177 * 2
def baseEnd_6108177 : Nat := 1045476907912684487698837

theorem tailTrace_6108177 : CollatzResearch.WordTrace tailWord_6108177 prefixEnd_6108177 1045476907912684487698837 := by
  unfold tailWord_6108177
  simp only [CollatzResearch.WordTrace]
  refine ⟨222783517592125397423826785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148522345061416931615884523 222783517592125397423826785)
  ·
    refine ⟨167087638194094048067870089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222783517592125397423826785 167087638194094048067870089)
    ·
      refine ⟨125315728645570536050902567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167087638194094048067870089 125315728645570536050902567)
      ·
        refine ⟨187973592968355804076353851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125315728645570536050902567 187973592968355804076353851)
        ·
          refine ⟨281960389452533706114530777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187973592968355804076353851 281960389452533706114530777)
          ·
            refine ⟨211470292089400279585898083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 281960389452533706114530777 211470292089400279585898083)
            ·
              refine ⟨317205438134100419378847125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 211470292089400279585898083 317205438134100419378847125)
              ·
                refine ⟨14869004912535957158383459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 317205438134100419378847125 14869004912535957158383459)
                ·
                  refine ⟨22303507368803935737575189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14869004912535957158383459 22303507368803935737575189)
                  ·
                    refine ⟨1045476907912684487698837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22303507368803935737575189 1045476907912684487698837)
                    ·
                      rfl

theorem cell23_6108177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 6].length) (baseStart_6108177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6108177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6108177 prefixEnd_6108177 := by exact prefixLift 6108177
  have htrace : WordTrace (prefixWord ++ tailWord_6108177) baseStart_6108177 baseEnd_6108177 := by
    simpa [prefixWord, tailWord_6108177, baseEnd_6108177] using wordTrace_append hprefix tailTrace_6108177
  have hstable : (prefixWord ++ tailWord_6108177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6108177).length < 2 ^ (prefixWord ++ tailWord_6108177).sum := by decide
  have hdescent : baseEnd_6108177 < baseStart_6108177 := by decide
  rcases family_descends (prefixWord ++ tailWord_6108177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6108187 : List Nat := [1, 1, 1, 1, 1, 1, 3, 2, 1, 8, 3]
def baseStart_6108187 : Nat := 118140960795 + 6108187 * 2 ^ 59
def prefixEnd_6108187 : Nat := 4983230072969 + 3 ^ 40 * 6108187 * 2
def baseEnd_6108187 : Nat := 3136435858544598423971465

theorem tailTrace_6108187 : CollatzResearch.WordTrace tailWord_6108187 prefixEnd_6108187 3136435858544598423971465 := by
  unfold tailWord_6108187
  simp only [CollatzResearch.WordTrace]
  refine ⟨222783882322089169131690815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148522588214726112754460543 222783882322089169131690815)
  ·
    refine ⟨334175823483133753697536223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222783882322089169131690815 334175823483133753697536223)
    ·
      refine ⟨501263735224700630546304335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 334175823483133753697536223 501263735224700630546304335)
      ·
        refine ⟨751895602837050945819456503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 501263735224700630546304335 751895602837050945819456503)
        ·
          refine ⟨1127843404255576418729184755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 751895602837050945819456503 1127843404255576418729184755)
          ·
            refine ⟨1691765106383364628093777133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1127843404255576418729184755 1691765106383364628093777133)
            ·
              refine ⟨634411914893761735535166425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1691765106383364628093777133 634411914893761735535166425)
              ·
                refine ⟨475808936170321301651374819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 634411914893761735535166425 475808936170321301651374819)
                ·
                  refine ⟨713713404255481952477062229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 475808936170321301651374819 713713404255481952477062229)
                  ·
                    refine ⟨8363828956118929130590573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 713713404255481952477062229 8363828956118929130590573)
                    ·
                      refine ⟨3136435858544598423971465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8363828956118929130590573 3136435858544598423971465)
                      ·
                        rfl

theorem cell23_6108187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 8, 3].length) (baseStart_6108187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6108187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6108187 prefixEnd_6108187 := by exact prefixLift 6108187
  have htrace : WordTrace (prefixWord ++ tailWord_6108187) baseStart_6108187 baseEnd_6108187 := by
    simpa [prefixWord, tailWord_6108187, baseEnd_6108187] using wordTrace_append hprefix tailTrace_6108187
  have hstable : (prefixWord ++ tailWord_6108187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6108187).length < 2 ^ (prefixWord ++ tailWord_6108187).sum := by decide
  have hdescent : baseEnd_6108187 < baseStart_6108187 := by decide
  rcases family_descends (prefixWord ++ tailWord_6108187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6108188 : List Nat := [2, 2, 3, 1, 4, 1, 1, 2, 2, 3, 2]
def baseStart_6108188 : Nat := 118140960795 + 6108188 * 2 ^ 59
def prefixEnd_6108188 : Nat := 4983230072969 + 3 ^ 40 * 6108188 * 2
def baseEnd_6108188 : Nat := 3136436372025252920058961

theorem tailTrace_6108188 : CollatzResearch.WordTrace tailWord_6108188 prefixEnd_6108188 3136436372025252920058961 := by
  unfold tailWord_6108188
  simp only [CollatzResearch.WordTrace]
  refine ⟨111391959397542773151238609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148522612530057030868318145 111391959397542773151238609)
  ·
    refine ⟨83543969548157079863428957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111391959397542773151238609 83543969548157079863428957)
    ·
      refine ⟨31328988580558904948785859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83543969548157079863428957 31328988580558904948785859)
      ·
        refine ⟨46993482870838357423178789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31328988580558904948785859 46993482870838357423178789)
        ·
          refine ⟨8811278038282192016846023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46993482870838357423178789 8811278038282192016846023)
          ·
            refine ⟨13216917057423288025269035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8811278038282192016846023 13216917057423288025269035)
            ·
              refine ⟨19825375586134932037903553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13216917057423288025269035 19825375586134932037903553)
              ·
                refine ⟨14869031689601199028427665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19825375586134932037903553 14869031689601199028427665)
                ·
                  refine ⟨11151773767200899271320749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14869031689601199028427665 11151773767200899271320749)
                  ·
                    refine ⟨4181915162700337226745281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11151773767200899271320749 4181915162700337226745281)
                    ·
                      refine ⟨3136436372025252920058961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4181915162700337226745281 3136436372025252920058961)
                      ·
                        rfl

theorem cell23_6108188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 2, 2, 3, 2].length) (baseStart_6108188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6108188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6108188 prefixEnd_6108188 := by exact prefixLift 6108188
  have htrace : WordTrace (prefixWord ++ tailWord_6108188) baseStart_6108188 baseEnd_6108188 := by
    simpa [prefixWord, tailWord_6108188, baseEnd_6108188] using wordTrace_append hprefix tailTrace_6108188
  have hstable : (prefixWord ++ tailWord_6108188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6108188).length < 2 ^ (prefixWord ++ tailWord_6108188).sum := by decide
  have hdescent : baseEnd_6108188 < baseStart_6108188 := by decide
  rcases family_descends (prefixWord ++ tailWord_6108188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6108195 : List Nat := [1, 1, 1, 4, 3, 3, 3, 2, 1, 1, 3]
def baseStart_6108195 : Nat := 118140960795 + 6108195 * 2 ^ 59
def prefixEnd_6108195 : Nat := 4983230072969 + 3 ^ 40 * 6108195 * 2
def baseEnd_6108195 : Nat := 3136439966389834392671429

theorem tailTrace_6108195 : CollatzResearch.WordTrace tailWord_6108195 prefixEnd_6108195 3136439966389834392671429 := by
  unfold tailWord_6108195
  simp only [CollatzResearch.WordTrace]
  refine ⟨222784174106060186497982039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148522782737373457665321359 222784174106060186497982039)
  ·
    refine ⟨334176261159090279746973059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222784174106060186497982039 334176261159090279746973059)
    ·
      refine ⟨501264391738635419620459589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 334176261159090279746973059 501264391738635419620459589)
      ·
        refine ⟨93987073450994141178836173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 501264391738635419620459589 93987073450994141178836173)
        ·
          refine ⟨35245152544122802942063565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93987073450994141178836173 35245152544122802942063565)
          ·
            refine ⟨13216932204046051103273837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35245152544122802942063565 13216932204046051103273837)
            ·
              refine ⟨4956349576517269163727689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13216932204046051103273837 4956349576517269163727689)
              ·
                refine ⟨3717262182387951872795767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4956349576517269163727689 3717262182387951872795767)
                ·
                  refine ⟨5575893273581927809193651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3717262182387951872795767 5575893273581927809193651)
                  ·
                    refine ⟨8363839910372891713790477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5575893273581927809193651 8363839910372891713790477)
                    ·
                      refine ⟨3136439966389834392671429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8363839910372891713790477 3136439966389834392671429)
                      ·
                        rfl

theorem cell23_6108195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 3, 2, 1, 1, 3].length) (baseStart_6108195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6108195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6108195 prefixEnd_6108195 := by exact prefixLift 6108195
  have htrace : WordTrace (prefixWord ++ tailWord_6108195) baseStart_6108195 baseEnd_6108195 := by
    simpa [prefixWord, tailWord_6108195, baseEnd_6108195] using wordTrace_append hprefix tailTrace_6108195
  have hstable : (prefixWord ++ tailWord_6108195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6108195).length < 2 ^ (prefixWord ++ tailWord_6108195).sum := by decide
  have hdescent : baseEnd_6108195 < baseStart_6108195 := by decide
  rcases family_descends (prefixWord ++ tailWord_6108195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6108197 : List Nat := [1, 3, 1, 2, 2, 2, 1, 1, 3, 1, 6]
def baseStart_6108197 : Nat := 118140960795 + 6108197 * 2 ^ 59
def prefixEnd_6108197 : Nat := 4983230072969 + 3 ^ 40 * 6108197 * 2
def baseEnd_6108197 : Nat := 3136440993351143384846419

theorem tailTrace_6108197 : CollatzResearch.WordTrace tailWord_6108197 prefixEnd_6108197 3136440993351143384846419 := by
  unfold tailWord_6108197
  simp only [CollatzResearch.WordTrace]
  refine ⟨222784247052052940839554845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148522831368035293893036563 222784247052052940839554845)
  ·
    refine ⟨83544092644519852814833067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 222784247052052940839554845 83544092644519852814833067)
    ·
      refine ⟨125316138966779779222249601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83544092644519852814833067 125316138966779779222249601)
      ·
        refine ⟨93987104225084834416687201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125316138966779779222249601 93987104225084834416687201)
        ·
          refine ⟨70490328168813625812515401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93987104225084834416687201 70490328168813625812515401)
          ·
            refine ⟨52867746126610219359386551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70490328168813625812515401 52867746126610219359386551)
            ·
              refine ⟨79301619189915329039079827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52867746126610219359386551 79301619189915329039079827)
              ·
                refine ⟨118952428784872993558619741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79301619189915329039079827 118952428784872993558619741)
                ·
                  refine ⟨44607160794327372584482403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 118952428784872993558619741 44607160794327372584482403)
                  ·
                    refine ⟨66910741191491058876723605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44607160794327372584482403 66910741191491058876723605)
                    ·
                      refine ⟨3136440993351143384846419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66910741191491058876723605 3136440993351143384846419)
                      ·
                        rfl

theorem cell23_6108197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 3, 1, 6].length) (baseStart_6108197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6108197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6108197 prefixEnd_6108197 := by exact prefixLift 6108197
  have htrace : WordTrace (prefixWord ++ tailWord_6108197) baseStart_6108197 baseEnd_6108197 := by
    simpa [prefixWord, tailWord_6108197, baseEnd_6108197] using wordTrace_append hprefix tailTrace_6108197
  have hstable : (prefixWord ++ tailWord_6108197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6108197).length < 2 ^ (prefixWord ++ tailWord_6108197).sum := by decide
  have hdescent : baseEnd_6108197 < baseStart_6108197 := by decide
  rcases family_descends (prefixWord ++ tailWord_6108197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6108204 : List Nat := [2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 3]
def baseStart_6108204 : Nat := 118140960795 + 6108204 * 2 ^ 59
def prefixEnd_6108204 : Nat := 4983230072969 + 3 ^ 40 * 6108204 * 2
def baseEnd_6108204 : Nat := 3136444587715724857458887

theorem tailTrace_6108204 : CollatzResearch.WordTrace tailWord_6108204 prefixEnd_6108204 3136444587715724857458887 := by
  unfold tailWord_6108204
  simp only [CollatzResearch.WordTrace]
  refine ⟨111392251181513790517529833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148523001575351720690039777 111392251181513790517529833)
  ·
    refine ⟨83544188386135342888147375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111392251181513790517529833 83544188386135342888147375)
    ·
      refine ⟨125316282579203014332221063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83544188386135342888147375 125316282579203014332221063)
      ·
        refine ⟨187974423868804521498331595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125316282579203014332221063 187974423868804521498331595)
        ·
          refine ⟨281961635803206782247497393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187974423868804521498331595 281961635803206782247497393)
          ·
            refine ⟨211471226852405086685623045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 281961635803206782247497393 211471226852405086685623045)
            ·
              refine ⟨39650855034825953753554321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 211471226852405086685623045 39650855034825953753554321)
              ·
                refine ⟨29738141276119465315165741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39650855034825953753554321 29738141276119465315165741)
                ·
                  refine ⟨11151802978544799493187153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29738141276119465315165741 11151802978544799493187153)
                  ·
                    refine ⟨8363852233908599619890365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11151802978544799493187153 8363852233908599619890365)
                    ·
                      refine ⟨3136444587715724857458887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8363852233908599619890365 3136444587715724857458887)
                      ·
                        rfl

theorem cell23_6108204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 3].length) (baseStart_6108204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6108204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6108204 prefixEnd_6108204 := by exact prefixLift 6108204
  have htrace : WordTrace (prefixWord ++ tailWord_6108204) baseStart_6108204 baseEnd_6108204 := by
    simpa [prefixWord, tailWord_6108204, baseEnd_6108204] using wordTrace_append hprefix tailTrace_6108204
  have hstable : (prefixWord ++ tailWord_6108204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6108204).length < 2 ^ (prefixWord ++ tailWord_6108204).sum := by decide
  have hdescent : baseEnd_6108204 < baseStart_6108204 := by decide
  rcases family_descends (prefixWord ++ tailWord_6108204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6108221 : List Nat := [1, 4, 1, 3, 1, 3, 1, 1, 3, 2, 3]
def baseStart_6108221 : Nat := 118140960795 + 6108221 * 2 ^ 59
def prefixEnd_6108221 : Nat := 4983230072969 + 3 ^ 40 * 6108221 * 2
def baseEnd_6108221 : Nat := 3136453316886851290946309

theorem tailTrace_6108221 : CollatzResearch.WordTrace tailWord_6108221 prefixEnd_6108221 3136453316886851290946309 := by
  unfold tailWord_6108221
  simp only [CollatzResearch.WordTrace]
  refine ⟨222785122403965992938428517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148523414935977328625619011 222785122403965992938428517)
  ·
    refine ⟨41772210450743623675955347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 222785122403965992938428517 41772210450743623675955347)
    ·
      refine ⟨62658315676115435513933021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41772210450743623675955347 62658315676115435513933021)
      ·
        refine ⟨23496868378543288317724883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62658315676115435513933021 23496868378543288317724883)
        ·
          refine ⟨35245302567814932476587325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23496868378543288317724883 35245302567814932476587325)
          ·
            refine ⟨13216988462930599678720247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35245302567814932476587325 13216988462930599678720247)
            ·
              refine ⟨19825482694395899518080371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13216988462930599678720247 19825482694395899518080371)
              ·
                refine ⟨29738224041593849277120557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19825482694395899518080371 29738224041593849277120557)
                ·
                  refine ⟨11151834015597693478920209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29738224041593849277120557 11151834015597693478920209)
                  ·
                    refine ⟨8363875511698270109190157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11151834015597693478920209 8363875511698270109190157)
                    ·
                      refine ⟨3136453316886851290946309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8363875511698270109190157 3136453316886851290946309)
                      ·
                        rfl

theorem cell23_6108221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 1, 3, 2, 3].length) (baseStart_6108221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6108221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6108221 prefixEnd_6108221 := by exact prefixLift 6108221
  have htrace : WordTrace (prefixWord ++ tailWord_6108221) baseStart_6108221 baseEnd_6108221 := by
    simpa [prefixWord, tailWord_6108221, baseEnd_6108221] using wordTrace_append hprefix tailTrace_6108221
  have hstable : (prefixWord ++ tailWord_6108221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6108221).length < 2 ^ (prefixWord ++ tailWord_6108221).sum := by decide
  have hdescent : baseEnd_6108221 < baseStart_6108221 := by decide
  rcases family_descends (prefixWord ++ tailWord_6108221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6108234 : List Nat := [3, 1, 2, 1, 1, 2, 3, 1, 3, 3, 3]
def baseStart_6108234 : Nat := 118140960795 + 6108234 * 2 ^ 59
def prefixEnd_6108234 : Nat := 4983230072969 + 3 ^ 40 * 6108234 * 2
def baseEnd_6108234 : Nat := 3136459992135359740083749

theorem tailTrace_6108234 : CollatzResearch.WordTrace tailWord_6108234 prefixEnd_6108234 3136459992135359740083749 := by
  unfold tailWord_6108234
  simp only [CollatzResearch.WordTrace]
  refine ⟨55696399138229724039662939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148523731035279264105767837 55696399138229724039662939)
  ·
    refine ⟨83544598707344586059494409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55696399138229724039662939 83544598707344586059494409)
    ·
      refine ⟨62658449030508439544620807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83544598707344586059494409 62658449030508439544620807)
      ·
        refine ⟨93987673545762659316931211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62658449030508439544620807 93987673545762659316931211)
        ·
          refine ⟨140981510318643988975396817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93987673545762659316931211 140981510318643988975396817)
          ·
            refine ⟨105736132738982991731547613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140981510318643988975396817 105736132738982991731547613)
            ·
              refine ⟨39651049777118621899330355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105736132738982991731547613 39651049777118621899330355)
              ·
                refine ⟨59476574665677932848995533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39651049777118621899330355 59476574665677932848995533)
                ·
                  refine ⟨22303715499629224818373325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59476574665677932848995533 22303715499629224818373325)
                  ·
                    refine ⟨8363893312360959306889997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22303715499629224818373325 8363893312360959306889997)
                    ·
                      refine ⟨3136459992135359740083749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8363893312360959306889997 3136459992135359740083749)
                      ·
                        rfl

theorem cell23_6108234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 1, 3, 3, 3].length) (baseStart_6108234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6108234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6108234 prefixEnd_6108234 := by exact prefixLift 6108234
  have htrace : WordTrace (prefixWord ++ tailWord_6108234) baseStart_6108234 baseEnd_6108234 := by
    simpa [prefixWord, tailWord_6108234, baseEnd_6108234] using wordTrace_append hprefix tailTrace_6108234
  have hstable : (prefixWord ++ tailWord_6108234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6108234).length < 2 ^ (prefixWord ++ tailWord_6108234).sum := by decide
  have hdescent : baseEnd_6108234 < baseStart_6108234 := by decide
  rcases family_descends (prefixWord ++ tailWord_6108234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6108238 : List Nat := [4, 1, 1, 1, 1, 3, 5, 1, 1, 2, 3]
def baseStart_6108238 : Nat := 118140960795 + 6108238 * 2 ^ 59
def prefixEnd_6108238 : Nat := 4983230072969 + 3 ^ 40 * 6108238 * 2
def baseEnd_6108238 : Nat := 3136462046057977724433731

theorem tailTrace_6108238 : CollatzResearch.WordTrace tailWord_6108238 prefixEnd_6108238 3136462046057977724433731 := by
  unfold tailWord_6108238
  simp only [CollatzResearch.WordTrace]
  refine ⟨27848217805613050605224671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148523828296602936561198245 27848217805613050605224671)
  ·
    refine ⟨41772326708419575907837007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27848217805613050605224671 41772326708419575907837007)
    ·
      refine ⟨62658490062629363861755511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41772326708419575907837007 62658490062629363861755511)
      ·
        refine ⟨93987735093944045792633267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62658490062629363861755511 93987735093944045792633267)
        ·
          refine ⟨140981602640916068688949901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93987735093944045792633267 140981602640916068688949901)
          ·
            refine ⟨52868100990343525758356213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 140981602640916068688949901 52868100990343525758356213)
            ·
              refine ⟨4956384467844705539845895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52868100990343525758356213 4956384467844705539845895)
              ·
                refine ⟨7434576701767058309768843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4956384467844705539845895 7434576701767058309768843)
                ·
                  refine ⟨11151865052650587464653265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7434576701767058309768843 11151865052650587464653265)
                  ·
                    refine ⟨8363898789487940598489949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11151865052650587464653265 8363898789487940598489949)
                    ·
                      refine ⟨3136462046057977724433731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8363898789487940598489949 3136462046057977724433731)
                      ·
                        rfl

theorem cell23_6108238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 5, 1, 1, 2, 3].length) (baseStart_6108238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6108238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6108238 prefixEnd_6108238 := by exact prefixLift 6108238
  have htrace : WordTrace (prefixWord ++ tailWord_6108238) baseStart_6108238 baseEnd_6108238 := by
    simpa [prefixWord, tailWord_6108238, baseEnd_6108238] using wordTrace_append hprefix tailTrace_6108238
  have hstable : (prefixWord ++ tailWord_6108238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6108238).length < 2 ^ (prefixWord ++ tailWord_6108238).sum := by decide
  have hdescent : baseEnd_6108238 < baseStart_6108238 := by decide
  rcases family_descends (prefixWord ++ tailWord_6108238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6108246 : List Nat := [5, 2, 2, 1, 2, 2, 2, 2, 1, 1, 3]
def baseStart_6108246 : Nat := 118140960795 + 6108246 * 2 ^ 59
def prefixEnd_6108246 : Nat := 4983230072969 + 3 ^ 40 * 6108246 * 2
def baseEnd_6108246 : Nat := 3136466153903213693133695

theorem tailTrace_6108246 : CollatzResearch.WordTrace tailWord_6108246 prefixEnd_6108246 3136466153903213693133695 := by
  unfold tailWord_6108246
  simp only [CollatzResearch.WordTrace]
  refine ⟨13924127139304713888005537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 148524022819250281472059061 13924127139304713888005537)
  ·
    refine ⟨10443095354478535416004153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13924127139304713888005537 10443095354478535416004153)
    ·
      refine ⟨7832321515858901562003115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10443095354478535416004153 7832321515858901562003115)
      ·
        refine ⟨11748482273788352343004673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7832321515858901562003115 11748482273788352343004673)
        ·
          refine ⟨8811361705341264257253505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11748482273788352343004673 8811361705341264257253505)
          ·
            refine ⟨6608521279005948192940129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8811361705341264257253505 6608521279005948192940129)
            ·
              refine ⟨4956390959254461144705097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6608521279005948192940129 4956390959254461144705097)
              ·
                refine ⟨3717293219440845858528823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4956390959254461144705097 3717293219440845858528823)
                ·
                  refine ⟨5575939829161268787793235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3717293219440845858528823 5575939829161268787793235)
                  ·
                    refine ⟨8363909743741903181689853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5575939829161268787793235 8363909743741903181689853)
                    ·
                      refine ⟨3136466153903213693133695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8363909743741903181689853 3136466153903213693133695)
                      ·
                        rfl

theorem cell23_6108246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 2, 2, 1, 1, 3].length) (baseStart_6108246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6108246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6108246 prefixEnd_6108246 := by exact prefixLift 6108246
  have htrace : WordTrace (prefixWord ++ tailWord_6108246) baseStart_6108246 baseEnd_6108246 := by
    simpa [prefixWord, tailWord_6108246, baseEnd_6108246] using wordTrace_append hprefix tailTrace_6108246
  have hstable : (prefixWord ++ tailWord_6108246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6108246).length < 2 ^ (prefixWord ++ tailWord_6108246).sum := by decide
  have hdescent : baseEnd_6108246 < baseStart_6108246 := by decide
  rcases family_descends (prefixWord ++ tailWord_6108246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6108261 : List Nat := [1, 3, 1, 3, 2, 1, 1, 1, 5, 3, 2]
def baseStart_6108261 : Nat := 118140960795 + 6108261 * 2 ^ 59
def prefixEnd_6108261 : Nat := 4983230072969 + 3 ^ 40 * 6108261 * 2
def baseEnd_6108261 : Nat := 3136473856113031134446125

theorem tailTrace_6108261 : CollatzResearch.WordTrace tailWord_6108261 prefixEnd_6108261 3136473856113031134446125 := by
  unfold tailWord_6108261
  simp only [CollatzResearch.WordTrace]
  refine ⟨222786581323821079769884637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148524387549214053179923091 222786581323821079769884637)
  ·
    refine ⟨83544967996432904913706739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 222786581323821079769884637 83544967996432904913706739)
    ·
      refine ⟨125317451994649357370560109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83544967996432904913706739 125317451994649357370560109)
      ·
        refine ⟨46994044497993509013960041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125317451994649357370560109 46994044497993509013960041)
        ·
          refine ⟨35245533373495131760470031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46994044497993509013960041 35245533373495131760470031)
          ·
            refine ⟨52868300060242697640705047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35245533373495131760470031 52868300060242697640705047)
            ·
              refine ⟨79302450090364046461057571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52868300060242697640705047 79302450090364046461057571)
              ·
                refine ⟨118953675135546069691586357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79302450090364046461057571 118953675135546069691586357)
                ·
                  refine ⟨11151907043957444033586221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 118953675135546069691586357 11151907043957444033586221)
                  ·
                    refine ⟨4181965141484041512594833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11151907043957444033586221 4181965141484041512594833)
                    ·
                      refine ⟨3136473856113031134446125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4181965141484041512594833 3136473856113031134446125)
                      ·
                        rfl

theorem cell23_6108261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 5, 3, 2].length) (baseStart_6108261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6108261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6108261 prefixEnd_6108261 := by exact prefixLift 6108261
  have htrace : WordTrace (prefixWord ++ tailWord_6108261) baseStart_6108261 baseEnd_6108261 := by
    simpa [prefixWord, tailWord_6108261, baseEnd_6108261] using wordTrace_append hprefix tailTrace_6108261
  have hstable : (prefixWord ++ tailWord_6108261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6108261).length < 2 ^ (prefixWord ++ tailWord_6108261).sum := by decide
  have hdescent : baseEnd_6108261 < baseStart_6108261 := by decide
  rcases family_descends (prefixWord ++ tailWord_6108261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6108274 : List Nat := [3, 2, 1, 2, 2, 1, 1, 2, 2, 3, 4]
def baseStart_6108274 : Nat := 118140960795 + 6108274 * 2 ^ 59
def prefixEnd_6108274 : Nat := 4983230072969 + 3 ^ 40 * 6108274 * 2
def baseEnd_6108274 : Nat := 3136480531361539583583565

theorem tailTrace_6108274 : CollatzResearch.WordTrace tailWord_6108274 prefixEnd_6108274 3136480531361539583583565 := by
  unfold tailWord_6108274
  simp only [CollatzResearch.WordTrace]
  refine ⟨55696763868193495747526969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148524703648515988660071917 55696763868193495747526969)
  ·
    refine ⟨41772572901145121810645227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55696763868193495747526969 41772572901145121810645227)
    ·
      refine ⟨62658859351717682715967841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41772572901145121810645227 62658859351717682715967841)
      ·
        refine ⟨46994144513788262036975881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62658859351717682715967841 46994144513788262036975881)
        ·
          refine ⟨35245608385341196527731911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46994144513788262036975881 35245608385341196527731911)
          ·
            refine ⟨52868412578011794791597867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35245608385341196527731911 52868412578011794791597867)
            ·
              refine ⟨79302618867017692187396801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52868412578011794791597867 79302618867017692187396801)
              ·
                refine ⟨59476964150263269140547601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79302618867017692187396801 59476964150263269140547601)
                ·
                  refine ⟨44607723112697451855410701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59476964150263269140547601 44607723112697451855410701)
                  ·
                    refine ⟨16727896167261544445779013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44607723112697451855410701 16727896167261544445779013)
                    ·
                      refine ⟨3136480531361539583583565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16727896167261544445779013 3136480531361539583583565)
                      ·
                        rfl

theorem cell23_6108274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 2, 2, 3, 4].length) (baseStart_6108274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6108274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6108274 prefixEnd_6108274 := by exact prefixLift 6108274
  have htrace : WordTrace (prefixWord ++ tailWord_6108274) baseStart_6108274 baseEnd_6108274 := by
    simpa [prefixWord, tailWord_6108274, baseEnd_6108274] using wordTrace_append hprefix tailTrace_6108274
  have hstable : (prefixWord ++ tailWord_6108274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6108274).length < 2 ^ (prefixWord ++ tailWord_6108274).sum := by decide
  have hdescent : baseEnd_6108274 < baseStart_6108274 := by decide
  rcases family_descends (prefixWord ++ tailWord_6108274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6108278 : List Nat := [5, 1, 1, 2, 1, 1, 1, 3, 3, 3, 2]
def baseStart_6108278 : Nat := 118140960795 + 6108278 * 2 ^ 59
def prefixEnd_6108278 : Nat := 4983230072969 + 3 ^ 40 * 6108278 * 2
def baseEnd_6108278 : Nat := 3136482585284157567933547

theorem tailTrace_6108278 : CollatzResearch.WordTrace tailWord_6108278 prefixEnd_6108278 3136482585284157567933547 := by
  unfold tailWord_6108278
  simp only [CollatzResearch.WordTrace]
  refine ⟨13924200085297468229578343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 148524800909839661115502325 13924200085297468229578343)
  ·
    refine ⟨20886300127946202344367515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13924200085297468229578343 20886300127946202344367515)
    ·
      refine ⟨31329450191919303516551273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20886300127946202344367515 31329450191919303516551273)
      ·
        refine ⟨23497087643939477637413455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31329450191919303516551273 23497087643939477637413455)
        ·
          refine ⟨35245631465909216456120183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23497087643939477637413455 35245631465909216456120183)
          ·
            refine ⟨52868447198863824684180275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35245631465909216456120183 52868447198863824684180275)
            ·
              refine ⟨79302670798295737026270413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52868447198863824684180275 79302670798295737026270413)
              ·
                refine ⟨29738501549360901384851405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79302670798295737026270413 29738501549360901384851405)
                ·
                  refine ⟨11151938081010338019319277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29738501549360901384851405 11151938081010338019319277)
                  ·
                    refine ⟨4181976780378876757244729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11151938081010338019319277 4181976780378876757244729)
                    ·
                      refine ⟨3136482585284157567933547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4181976780378876757244729 3136482585284157567933547)
                      ·
                        rfl

theorem cell23_6108278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 3, 3, 3, 2].length) (baseStart_6108278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6108278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6108278 prefixEnd_6108278 := by exact prefixLift 6108278
  have htrace : WordTrace (prefixWord ++ tailWord_6108278) baseStart_6108278 baseEnd_6108278 := by
    simpa [prefixWord, tailWord_6108278, baseEnd_6108278] using wordTrace_append hprefix tailTrace_6108278
  have hstable : (prefixWord ++ tailWord_6108278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6108278).length < 2 ^ (prefixWord ++ tailWord_6108278).sum := by decide
  have hdescent : baseEnd_6108278 < baseStart_6108278 := by decide
  rcases family_descends (prefixWord ++ tailWord_6108278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6108286 : List Nat := [4, 2, 4, 1, 2, 1, 2, 1, 1, 1, 4]
def baseStart_6108286 : Nat := 118140960795 + 6108286 * 2 ^ 59
def prefixEnd_6108286 : Nat := 4983230072969 + 3 ^ 40 * 6108286 * 2
def baseEnd_6108286 : Nat := 3136486693129393536633511

theorem tailTrace_6108286 : CollatzResearch.WordTrace tailWord_6108286 prefixEnd_6108286 3136486693129393536633511 := by
  unfold tailWord_6108286
  simp only [CollatzResearch.WordTrace]
  refine ⟨27848436643591313629943089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 148524995432487006026363141 27848436643591313629943089)
  ·
    refine ⟨20886327482693485222457317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27848436643591313629943089 20886327482693485222457317)
    ·
      refine ⟨3916186403005028479210747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20886327482693485222457317 3916186403005028479210747)
      ·
        refine ⟨5874279604507542718816121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3916186403005028479210747 5874279604507542718816121)
        ·
          refine ⟨4405709703380657039112091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5874279604507542718816121 4405709703380657039112091)
          ·
            refine ⟨6608564555070985558668137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4405709703380657039112091 6608564555070985558668137)
            ·
              refine ⟨4956423416303239169001103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6608564555070985558668137 4956423416303239169001103)
              ·
                refine ⟨7434635124454858753501655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4956423416303239169001103 7434635124454858753501655)
                ·
                  refine ⟨11151952686682288130252483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7434635124454858753501655 11151952686682288130252483)
                  ·
                    refine ⟨16727929030023432195378725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11151952686682288130252483 16727929030023432195378725)
                    ·
                      refine ⟨3136486693129393536633511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16727929030023432195378725 3136486693129393536633511)
                      ·
                        rfl

theorem cell23_6108286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 2, 1, 1, 1, 4].length) (baseStart_6108286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6108286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6108286 prefixEnd_6108286 := by exact prefixLift 6108286
  have htrace : WordTrace (prefixWord ++ tailWord_6108286) baseStart_6108286 baseEnd_6108286 := by
    simpa [prefixWord, tailWord_6108286, baseEnd_6108286] using wordTrace_append hprefix tailTrace_6108286
  have hstable : (prefixWord ++ tailWord_6108286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6108286).length < 2 ^ (prefixWord ++ tailWord_6108286).sum := by decide
  have hdescent : baseEnd_6108286 < baseStart_6108286 := by decide
  rcases family_descends (prefixWord ++ tailWord_6108286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6108291 : List Nat := [1, 1, 1, 3, 3, 2, 1, 4, 1, 4, 2]
def baseStart_6108291 : Nat := 118140960795 + 6108291 * 2 ^ 59
def prefixEnd_6108291 : Nat := 4983230072969 + 3 ^ 40 * 6108291 * 2
def baseEnd_6108291 : Nat := 3136489260532666017070987

theorem tailTrace_6108291 : CollatzResearch.WordTrace tailWord_6108291 prefixEnd_6108291 3136489260532666017070987 := by
  unfold tailWord_6108291
  simp only [CollatzResearch.WordTrace]
  refine ⟨222787675513712394893476727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148525117009141596595651151 222787675513712394893476727)
  ·
    refine ⟨334181513270568592340215091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222787675513712394893476727 334181513270568592340215091)
    ·
      refine ⟨501272269905852888510322637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 334181513270568592340215091 501272269905852888510322637)
      ·
        refine ⟨187977101214694833191370989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 501272269905852888510322637 187977101214694833191370989)
        ·
          refine ⟨70491412955510562446764121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 187977101214694833191370989 70491412955510562446764121)
          ·
            refine ⟨52868559716632921835073091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70491412955510562446764121 52868559716632921835073091)
            ·
              refine ⟨79302839574949382752609637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52868559716632921835073091 79302839574949382752609637)
              ·
                refine ⟨14869282420303009266114307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 79302839574949382752609637 14869282420303009266114307)
                ·
                  refine ⟨22303923630454513899171461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14869282420303009266114307 22303923630454513899171461)
                  ·
                    refine ⟨4181985680710221356094649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22303923630454513899171461 4181985680710221356094649)
                    ·
                      refine ⟨3136489260532666017070987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4181985680710221356094649 3136489260532666017070987)
                      ·
                        rfl

theorem cell23_6108291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 4, 1, 4, 2].length) (baseStart_6108291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6108291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6108291 prefixEnd_6108291 := by exact prefixLift 6108291
  have htrace : WordTrace (prefixWord ++ tailWord_6108291) baseStart_6108291 baseEnd_6108291 := by
    simpa [prefixWord, tailWord_6108291, baseEnd_6108291] using wordTrace_append hprefix tailTrace_6108291
  have hstable : (prefixWord ++ tailWord_6108291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6108291).length < 2 ^ (prefixWord ++ tailWord_6108291).sum := by decide
  have hdescent : baseEnd_6108291 < baseStart_6108291 := by decide
  rcases family_descends (prefixWord ++ tailWord_6108291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6108348 : List Nat := [2, 2, 2, 3, 2, 1, 3, 3, 5]
def baseStart_6108348 : Nat := 118140960795 + 6108348 * 2 ^ 59
def prefixEnd_6108348 : Nat := 4983230072969 + 3 ^ 40 * 6108348 * 2
def baseEnd_6108348 : Nat := 348502058769996921562025

theorem tailTrace_6108348 : CollatzResearch.WordTrace tailWord_6108348 prefixEnd_6108348 348502058769996921562025 := by
  unfold tailWord_6108348
  simp only [CollatzResearch.WordTrace]
  refine ⟨111394877237252946814150849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148526502983003929085534465 111394877237252946814150849)
  ·
    refine ⟨83546157927939710110613137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111394877237252946814150849 83546157927939710110613137)
    ·
      refine ⟨62659618445954782582959853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83546157927939710110613137 62659618445954782582959853)
      ·
        refine ⟨23497356917233043468609945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62659618445954782582959853 23497356917233043468609945)
        ·
          refine ⟨17623017687924782601457459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23497356917233043468609945 17623017687924782601457459)
          ·
            refine ⟨26434526531887173902186189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17623017687924782601457459 26434526531887173902186189)
            ·
              refine ⟨9912947449457690213319821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26434526531887173902186189 9912947449457690213319821)
              ·
                refine ⟨3717355293546633829994933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9912947449457690213319821 3717355293546633829994933)
                ·
                  refine ⟨348502058769996921562025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3717355293546633829994933 348502058769996921562025)
                  ·
                    rfl

theorem cell23_6108348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 3, 3, 5].length) (baseStart_6108348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6108348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6108348 prefixEnd_6108348 := by exact prefixLift 6108348
  have htrace : WordTrace (prefixWord ++ tailWord_6108348) baseStart_6108348 baseEnd_6108348 := by
    simpa [prefixWord, tailWord_6108348, baseEnd_6108348] using wordTrace_append hprefix tailTrace_6108348
  have hstable : (prefixWord ++ tailWord_6108348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6108348).length < 2 ^ (prefixWord ++ tailWord_6108348).sum := by decide
  have hdescent : baseEnd_6108348 < baseStart_6108348 := by decide
  rcases family_descends (prefixWord ++ tailWord_6108348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6108421 : List Nat := [1, 3, 1, 1, 2, 1, 6, 2, 6]
def baseStart_6108421 : Nat := 118140960795 + 6108421 * 2 ^ 59
def prefixEnd_6108421 : Nat := 4983230072969 + 3 ^ 40 * 6108421 * 2
def baseEnd_6108421 : Nat := 348506223668638945382821

theorem tailTrace_6108421 : CollatzResearch.WordTrace tailWord_6108421 prefixEnd_6108421 348506223668638945382821 := by
  unfold tailWord_6108421
  simp only [CollatzResearch.WordTrace]
  refine ⟨222792417003241427095709117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148528278002160951397139411 222792417003241427095709117)
  ·
    refine ⟨83547156376215535160890919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 222792417003241427095709117 83547156376215535160890919)
    ·
      refine ⟨125320734564323302741336379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83547156376215535160890919 125320734564323302741336379)
      ·
        refine ⟨187981101846484954112004569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125320734564323302741336379 187981101846484954112004569)
        ·
          refine ⟨140985826384863715584003427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187981101846484954112004569 140985826384863715584003427)
          ·
            refine ⟨211478739577295573376005141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140985826384863715584003427 211478739577295573376005141)
            ·
              refine ⟨9913065917685730002000241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 211478739577295573376005141 9913065917685730002000241)
              ·
                refine ⟨7434799438264297501500181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9913065917685730002000241 7434799438264297501500181)
                ·
                  refine ⟨348506223668638945382821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7434799438264297501500181 348506223668638945382821)
                  ·
                    rfl

theorem cell23_6108421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 6, 2, 6].length) (baseStart_6108421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6108421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6108421 prefixEnd_6108421 := by exact prefixLift 6108421
  have htrace : WordTrace (prefixWord ++ tailWord_6108421) baseStart_6108421 baseEnd_6108421 := by
    simpa [prefixWord, tailWord_6108421, baseEnd_6108421] using wordTrace_append hprefix tailTrace_6108421
  have hstable : (prefixWord ++ tailWord_6108421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6108421).length < 2 ^ (prefixWord ++ tailWord_6108421).sum := by decide
  have hdescent : baseEnd_6108421 < baseStart_6108421 := by decide
  rcases family_descends (prefixWord ++ tailWord_6108421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6108451 : List Nat := [1, 1, 1, 4, 2, 3, 2, 1, 3, 5]
def baseStart_6108451 : Nat := 118140960795 + 6108451 * 2 ^ 59
def prefixEnd_6108451 : Nat := 4983230072969 + 3 ^ 40 * 6108451 * 2
def baseEnd_6108451 : Nat := 1045523805812461797023417

theorem tailTrace_6108451 : CollatzResearch.WordTrace tailWord_6108451 prefixEnd_6108451 1045523805812461797023417 := by
  unfold tailWord_6108451
  simp only [CollatzResearch.WordTrace]
  refine ⟨222793511193132742219301207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148529007462088494812867471 222793511193132742219301207)
  ·
    refine ⟨334190266789699113328951811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222793511193132742219301207 334190266789699113328951811)
    ·
      refine ⟨501285400184548669993427717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 334190266789699113328951811 501285400184548669993427717)
      ·
        refine ⟨93991012534602875623767697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 501285400184548669993427717 93991012534602875623767697)
        ·
          refine ⟨70493259400952156717825773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93991012534602875623767697 70493259400952156717825773)
          ·
            refine ⟨26434972275357058769184665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70493259400952156717825773 26434972275357058769184665)
            ·
              refine ⟨19826229206517794076888499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26434972275357058769184665 19826229206517794076888499)
              ·
                refine ⟨29739343809776691115332749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19826229206517794076888499 29739343809776691115332749)
                ·
                  refine ⟨11152253928666259168249781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29739343809776691115332749 11152253928666259168249781)
                  ·
                    refine ⟨1045523805812461797023417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11152253928666259168249781 1045523805812461797023417)
                    ·
                      rfl

theorem cell23_6108451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 1, 3, 5].length) (baseStart_6108451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6108451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6108451 prefixEnd_6108451 := by exact prefixLift 6108451
  have htrace : WordTrace (prefixWord ++ tailWord_6108451) baseStart_6108451 baseEnd_6108451 := by
    simpa [prefixWord, tailWord_6108451, baseEnd_6108451] using wordTrace_append hprefix tailTrace_6108451
  have hstable : (prefixWord ++ tailWord_6108451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6108451).length < 2 ^ (prefixWord ++ tailWord_6108451).sum := by decide
  have hdescent : baseEnd_6108451 < baseStart_6108451 := by decide
  rcases family_descends (prefixWord ++ tailWord_6108451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6108505 : List Nat := [1, 2, 1, 2, 2, 2, 4, 2, 3, 2, 2]
def baseStart_6108505 : Nat := 118140960795 + 6108505 * 2 ^ 59
def prefixEnd_6108505 : Nat := 4983230072969 + 3 ^ 40 * 6108505 * 2
def baseEnd_6108505 : Nat := 3136599145392728179795003

theorem tailTrace_6108505 : CollatzResearch.WordTrace tailWord_6108505 prefixEnd_6108505 3136599145392728179795003 := by
  unfold tailWord_6108505
  simp only [CollatzResearch.WordTrace]
  refine ⟨222795480734937109441766969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148530320489958072961177979 222795480734937109441766969)
  ·
    refine ⟨167096610551202832081325227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222795480734937109441766969 167096610551202832081325227)
    ·
      refine ⟨250644915826804248121987841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167096610551202832081325227 250644915826804248121987841)
      ·
        refine ⟨187983686870103186091490881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 250644915826804248121987841 187983686870103186091490881)
        ·
          refine ⟨140987765152577389568618161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 187983686870103186091490881 140987765152577389568618161)
          ·
            refine ⟨105740823864433042176463621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 140987765152577389568618161 105740823864433042176463621)
            ·
              refine ⟨19826404474581195408086929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 105740823864433042176463621 19826404474581195408086929)
              ·
                refine ⟨14869803355935896556065197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19826404474581195408086929 14869803355935896556065197)
                ·
                  refine ⟨5576176258475961208524449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14869803355935896556065197 5576176258475961208524449)
                  ·
                    refine ⟨4182132193856970906393337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5576176258475961208524449 4182132193856970906393337)
                    ·
                      refine ⟨3136599145392728179795003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4182132193856970906393337 3136599145392728179795003)
                      ·
                        rfl

theorem cell23_6108505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 2, 3, 2, 2].length) (baseStart_6108505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6108505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6108505 prefixEnd_6108505 := by exact prefixLift 6108505
  have htrace : WordTrace (prefixWord ++ tailWord_6108505) baseStart_6108505 baseEnd_6108505 := by
    simpa [prefixWord, tailWord_6108505, baseEnd_6108505] using wordTrace_append hprefix tailTrace_6108505
  have hstable : (prefixWord ++ tailWord_6108505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6108505).length < 2 ^ (prefixWord ++ tailWord_6108505).sum := by decide
  have hdescent : baseEnd_6108505 < baseStart_6108505 := by decide
  rcases family_descends (prefixWord ++ tailWord_6108505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6108525 : List Nat := [1, 5, 1, 1, 1, 3, 2, 3, 1, 2, 3]
def baseStart_6108525 : Nat := 118140960795 + 6108525 * 2 ^ 59
def prefixEnd_6108525 : Nat := 4983230072969 + 3 ^ 40 * 6108525 * 2
def baseEnd_6108525 : Nat := 3136609415005818101544911

theorem tailTrace_6108525 : CollatzResearch.WordTrace tailWord_6108525 prefixEnd_6108525 3136609415005818101544911 := by
  unfold tailWord_6108525
  simp only [CollatzResearch.WordTrace]
  refine ⟨222796210194864652857495029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148530806796576435238330019 222796210194864652857495029)
  ·
    refine ⟨20887144705768561205390159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 222796210194864652857495029 20887144705768561205390159)
    ·
      refine ⟨31330717058652841808085239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20887144705768561205390159 31330717058652841808085239)
      ·
        refine ⟨46996075587979262712127859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31330717058652841808085239 46996075587979262712127859)
        ·
          refine ⟨70494113381968894068191789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46996075587979262712127859 70494113381968894068191789)
          ·
            refine ⟨26435292518238335275571921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70494113381968894068191789 26435292518238335275571921)
            ·
              refine ⟨19826469388678751456678941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26435292518238335275571921 19826469388678751456678941)
              ·
                refine ⟨7434926020754531796254603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19826469388678751456678941 7434926020754531796254603)
                ·
                  refine ⟨11152389031131797694381905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7434926020754531796254603 11152389031131797694381905)
                  ·
                    refine ⟨8364291773348848270786429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11152389031131797694381905 8364291773348848270786429)
                    ·
                      refine ⟨3136609415005818101544911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8364291773348848270786429 3136609415005818101544911)
                      ·
                        rfl

theorem cell23_6108525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 3, 1, 2, 3].length) (baseStart_6108525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6108525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6108525 prefixEnd_6108525 := by exact prefixLift 6108525
  have htrace : WordTrace (prefixWord ++ tailWord_6108525) baseStart_6108525 baseEnd_6108525 := by
    simpa [prefixWord, tailWord_6108525, baseEnd_6108525] using wordTrace_append hprefix tailTrace_6108525
  have hstable : (prefixWord ++ tailWord_6108525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6108525).length < 2 ^ (prefixWord ++ tailWord_6108525).sum := by decide
  have hdescent : baseEnd_6108525 < baseStart_6108525 := by decide
  rcases family_descends (prefixWord ++ tailWord_6108525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6108539 : List Nat := [1, 1, 1, 1, 1, 6, 5, 2, 1, 2, 2]
def baseStart_6108539 : Nat := 118140960795 + 6108539 * 2 ^ 59
def prefixEnd_6108539 : Nat := 4983230072969 + 3 ^ 40 * 6108539 * 2
def baseEnd_6108539 : Nat := 3136616603734981046769847

theorem tailTrace_6108539 : CollatzResearch.WordTrace tailWord_6108539 prefixEnd_6108539 3136616603734981046769847 := by
  unfold tailWord_6108539
  simp only [CollatzResearch.WordTrace]
  refine ⟨222796720816813933248504671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148531147211209288832336447 222796720816813933248504671)
  ·
    refine ⟨334195081225220899872757007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222796720816813933248504671 334195081225220899872757007)
    ·
      refine ⟨501292621837831349809135511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 334195081225220899872757007 501292621837831349809135511)
      ·
        refine ⟨751938932756747024713703267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 501292621837831349809135511 751938932756747024713703267)
        ·
          refine ⟨1127908399135120537070554901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 751938932756747024713703267 1127908399135120537070554901)
          ·
            refine ⟨52870706209458775175182261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1127908399135120537070554901 52870706209458775175182261)
            ·
              refine ⟨4956628707136760172673337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52870706209458775175182261 4956628707136760172673337)
              ·
                refine ⟨3717471530352570129505003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4956628707136760172673337 3717471530352570129505003)
                ·
                  refine ⟨5576207295528855194257505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3717471530352570129505003 5576207295528855194257505)
                  ·
                    refine ⟨4182155471646641395693129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5576207295528855194257505 4182155471646641395693129)
                    ·
                      refine ⟨3136616603734981046769847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4182155471646641395693129 3136616603734981046769847)
                      ·
                        rfl

theorem cell23_6108539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 5, 2, 1, 2, 2].length) (baseStart_6108539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6108539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6108539 prefixEnd_6108539 := by exact prefixLift 6108539
  have htrace : WordTrace (prefixWord ++ tailWord_6108539) baseStart_6108539 baseEnd_6108539 := by
    simpa [prefixWord, tailWord_6108539, baseEnd_6108539] using wordTrace_append hprefix tailTrace_6108539
  have hstable : (prefixWord ++ tailWord_6108539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6108539).length < 2 ^ (prefixWord ++ tailWord_6108539).sum := by decide
  have hdescent : baseEnd_6108539 < baseStart_6108539 := by decide
  rcases family_descends (prefixWord ++ tailWord_6108539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6108541 : List Nat := [1, 4, 1, 1, 2, 2, 2, 1, 2, 7]
def baseStart_6108541 : Nat := 118140960795 + 6108541 * 2 ^ 59
def prefixEnd_6108541 : Nat := 4983230072969 + 3 ^ 40 * 6108541 * 2
def baseEnd_6108541 : Nat := 1045539210232096679648279

theorem tailTrace_6108541 : CollatzResearch.WordTrace tailWord_6108541 prefixEnd_6108541 1045539210232096679648279 := by
  unfold tailWord_6108541
  simp only [CollatzResearch.WordTrace]
  refine ⟨222796793762806687590077477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148531195841871125060051651 222796793762806687590077477)
  ·
    refine ⟨41774398830526253923139527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 222796793762806687590077477 41774398830526253923139527)
    ·
      refine ⟨62661598245789380884709291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41774398830526253923139527 62661598245789380884709291)
      ·
        refine ⟨93992397368684071327063937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62661598245789380884709291 93992397368684071327063937)
        ·
          refine ⟨70494298026513053495297953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93992397368684071327063937 70494298026513053495297953)
          ·
            refine ⟨52870723519884790121473465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70494298026513053495297953 52870723519884790121473465)
            ·
              refine ⟨39653042639913592591105099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52870723519884790121473465 39653042639913592591105099)
              ·
                refine ⟨59479563959870388886657649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39653042639913592591105099 59479563959870388886657649)
                ·
                  refine ⟨44609672969902791664993237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59479563959870388886657649 44609672969902791664993237)
                  ·
                    refine ⟨1045539210232096679648279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44609672969902791664993237 1045539210232096679648279)
                    ·
                      rfl

theorem cell23_6108541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 1, 2, 7].length) (baseStart_6108541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6108541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6108541 prefixEnd_6108541 := by exact prefixLift 6108541
  have htrace : WordTrace (prefixWord ++ tailWord_6108541) baseStart_6108541 baseEnd_6108541 := by
    simpa [prefixWord, tailWord_6108541, baseEnd_6108541] using wordTrace_append hprefix tailTrace_6108541
  have hstable : (prefixWord ++ tailWord_6108541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6108541).length < 2 ^ (prefixWord ++ tailWord_6108541).sum := by decide
  have hdescent : baseEnd_6108541 < baseStart_6108541 := by decide
  rcases family_descends (prefixWord ++ tailWord_6108541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6108555 : List Nat := [1, 1, 1, 1, 4, 3, 3, 3, 2, 1, 3]
def baseStart_6108555 : Nat := 118140960795 + 6108555 * 2 ^ 59
def prefixEnd_6108555 : Nat := 4983230072969 + 3 ^ 40 * 6108555 * 2
def baseEnd_6108555 : Nat := 3136624819425452984169773

theorem tailTrace_6108555 : CollatzResearch.WordTrace tailWord_6108555 prefixEnd_6108555 3136624819425452984169773 := by
  unfold tailWord_6108555
  simp only [CollatzResearch.WordTrace]
  refine ⟨222797304384755967981087119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148531536256503978654058079 222797304384755967981087119)
  ·
    refine ⟨334195956577133951971630679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222797304384755967981087119 334195956577133951971630679)
    ·
      refine ⟨501293934865700927957446019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 334195956577133951971630679 501293934865700927957446019)
      ·
        refine ⟨751940902298551391936169029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 501293934865700927957446019 751940902298551391936169029)
        ·
          refine ⟨140988919180978385988031693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 751940902298551391936169029 140988919180978385988031693)
          ·
            refine ⟨52870844692866894745511885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 140988919180978385988031693 52870844692866894745511885)
            ·
              refine ⟨19826566759825085529566957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52870844692866894745511885 19826566759825085529566957)
              ·
                refine ⟨7434962534934407073587609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19826566759825085529566957 7434962534934407073587609)
                ·
                  refine ⟨5576221901200805305190707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7434962534934407073587609 5576221901200805305190707)
                  ·
                    refine ⟨8364332851801207957786061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5576221901200805305190707 8364332851801207957786061)
                    ·
                      refine ⟨3136624819425452984169773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8364332851801207957786061 3136624819425452984169773)
                      ·
                        rfl

theorem cell23_6108555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 3, 2, 1, 3].length) (baseStart_6108555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6108555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6108555 prefixEnd_6108555 := by exact prefixLift 6108555
  have htrace : WordTrace (prefixWord ++ tailWord_6108555) baseStart_6108555 baseEnd_6108555 := by
    simpa [prefixWord, tailWord_6108555, baseEnd_6108555] using wordTrace_append hprefix tailTrace_6108555
  have hstable : (prefixWord ++ tailWord_6108555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6108555).length < 2 ^ (prefixWord ++ tailWord_6108555).sum := by decide
  have hdescent : baseEnd_6108555 < baseStart_6108555 := by decide
  rcases family_descends (prefixWord ++ tailWord_6108555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6108561 : List Nat := [1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 4]
def baseStart_6108561 : Nat := 118140960795 + 6108561 * 2 ^ 59
def prefixEnd_6108561 : Nat := 4983230072969 + 3 ^ 40 * 6108561 * 2
def baseEnd_6108561 : Nat := 3136627900309379960694745

theorem tailTrace_6108561 : CollatzResearch.WordTrace tailWord_6108561 prefixEnd_6108561 3136627900309379960694745 := by
  unfold tailWord_6108561
  simp only [CollatzResearch.WordTrace]
  refine ⟨222797523222734231005805537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148531682148489487337203691 222797523222734231005805537)
  ·
    refine ⟨167098142417050673254354153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222797523222734231005805537 167098142417050673254354153)
    ·
      refine ⟨125323606812788004940765615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167098142417050673254354153 125323606812788004940765615)
      ·
        refine ⟨187985410219182007411148423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125323606812788004940765615 187985410219182007411148423)
        ·
          refine ⟨281978115328773011116722635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187985410219182007411148423 281978115328773011116722635)
          ·
            refine ⟨422967172993159516675083953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 281978115328773011116722635 422967172993159516675083953)
            ·
              refine ⟨317225379744869637506312965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 422967172993159516675083953 317225379744869637506312965)
              ·
                refine ⟨59479758702163057032433681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 317225379744869637506312965 59479758702163057032433681)
                ·
                  refine ⟨44609819026622292774325261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59479758702163057032433681 44609819026622292774325261)
                  ·
                    refine ⟨16728682134983359790371973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44609819026622292774325261 16728682134983359790371973)
                    ·
                      refine ⟨3136627900309379960694745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16728682134983359790371973 3136627900309379960694745)
                      ·
                        rfl

theorem cell23_6108561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 4].length) (baseStart_6108561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6108561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6108561 prefixEnd_6108561 := by exact prefixLift 6108561
  have htrace : WordTrace (prefixWord ++ tailWord_6108561) baseStart_6108561 baseEnd_6108561 := by
    simpa [prefixWord, tailWord_6108561, baseEnd_6108561] using wordTrace_append hprefix tailTrace_6108561
  have hstable : (prefixWord ++ tailWord_6108561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6108561).length < 2 ^ (prefixWord ++ tailWord_6108561).sum := by decide
  have hdescent : baseEnd_6108561 < baseStart_6108561 := by decide
  rcases family_descends (prefixWord ++ tailWord_6108561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6108572 : List Nat := [2, 2, 3, 4, 1, 1, 1, 2, 1, 3, 3]
def baseStart_6108572 : Nat := 118140960795 + 6108572 * 2 ^ 59
def prefixEnd_6108572 : Nat := 4983230072969 + 3 ^ 40 * 6108572 * 2
def baseEnd_6108572 : Nat := 3136633548596579417657195

theorem tailTrace_6108572 : CollatzResearch.WordTrace tailWord_6108572 prefixEnd_6108572 3136633548596579417657195 := by
  unfold tailWord_6108572
  simp only [CollatzResearch.WordTrace]
  refine ⟨111398962212847189942227985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148531949617129586589637313 111398962212847189942227985)
  ·
    refine ⟨83549221659635392456670989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111398962212847189942227985 83549221659635392456670989)
    ·
      refine ⟨31330958122363272171251621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83549221659635392456670989 31330958122363272171251621)
      ·
        refine ⟨5874554647943113532109679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31330958122363272171251621 5874554647943113532109679)
        ·
          refine ⟨8811831971914670298164519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5874554647943113532109679 8811831971914670298164519)
          ·
            refine ⟨13217747957872005447246779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8811831971914670298164519 13217747957872005447246779)
            ·
              refine ⟨19826621936808008170870169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13217747957872005447246779 19826621936808008170870169)
              ·
                refine ⟨14869966452606006128152627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19826621936808008170870169 14869966452606006128152627)
                ·
                  refine ⟨22304949678909009192228941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14869966452606006128152627 22304949678909009192228941)
                  ·
                    refine ⟨8364356129590878447085853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22304949678909009192228941 8364356129590878447085853)
                    ·
                      refine ⟨3136633548596579417657195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8364356129590878447085853 3136633548596579417657195)
                      ·
                        rfl

theorem cell23_6108572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_6108572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6108572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6108572 prefixEnd_6108572 := by exact prefixLift 6108572
  have htrace : WordTrace (prefixWord ++ tailWord_6108572) baseStart_6108572 baseEnd_6108572 := by
    simpa [prefixWord, tailWord_6108572, baseEnd_6108572] using wordTrace_append hprefix tailTrace_6108572
  have hstable : (prefixWord ++ tailWord_6108572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6108572).length < 2 ^ (prefixWord ++ tailWord_6108572).sum := by decide
  have hdescent : baseEnd_6108572 < baseStart_6108572 := by decide
  rcases family_descends (prefixWord ++ tailWord_6108572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6108581 : List Nat := [1, 3, 1, 2, 1, 1, 2, 3, 1, 3, 5]
def baseStart_6108581 : Nat := 118140960795 + 6108581 * 2 ^ 59
def prefixEnd_6108581 : Nat := 4983230072969 + 3 ^ 40 * 6108581 * 2
def baseEnd_6108581 : Nat := 3136638169922469882444653

theorem tailTrace_6108581 : CollatzResearch.WordTrace tailWord_6108581 prefixEnd_6108581 3136638169922469882444653 := by
  unfold tailWord_6108581
  simp only [CollatzResearch.WordTrace]
  refine ⟨222798252682661774421533597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148532168455107849614355731 222798252682661774421533597)
  ·
    refine ⟨83549344755998165408075099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 222798252682661774421533597 83549344755998165408075099)
    ·
      refine ⟨125324017133997248112112649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83549344755998165408075099 125324017133997248112112649)
      ·
        refine ⟨93993012850497936084084487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125324017133997248112112649 93993012850497936084084487)
        ·
          refine ⟨140989519275746904126126731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93993012850497936084084487 140989519275746904126126731)
          ·
            refine ⟨211484278913620356189190097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140989519275746904126126731 211484278913620356189190097)
            ·
              refine ⟨158613209185215267141892573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 211484278913620356189190097 158613209185215267141892573)
              ·
                refine ⟨59479953444455725178209715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 158613209185215267141892573 59479953444455725178209715)
                ·
                  refine ⟨89219930166683587767314573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59479953444455725178209715 89219930166683587767314573)
                  ·
                    refine ⟨33457473812506345412742965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 89219930166683587767314573 33457473812506345412742965)
                    ·
                      refine ⟨3136638169922469882444653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33457473812506345412742965 3136638169922469882444653)
                      ·
                        rfl

theorem cell23_6108581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 3, 1, 3, 5].length) (baseStart_6108581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6108581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6108581 prefixEnd_6108581 := by exact prefixLift 6108581
  have htrace : WordTrace (prefixWord ++ tailWord_6108581) baseStart_6108581 baseEnd_6108581 := by
    simpa [prefixWord, tailWord_6108581, baseEnd_6108581] using wordTrace_append hprefix tailTrace_6108581
  have hstable : (prefixWord ++ tailWord_6108581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6108581).length < 2 ^ (prefixWord ++ tailWord_6108581).sum := by decide
  have hdescent : baseEnd_6108581 < baseStart_6108581 := by decide
  rcases family_descends (prefixWord ++ tailWord_6108581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6108589 : List Nat := [1, 5, 2, 2, 1, 2, 2, 2, 2, 1, 3]
def baseStart_6108589 : Nat := 118140960795 + 6108589 * 2 ^ 59
def prefixEnd_6108589 : Nat := 4983230072969 + 3 ^ 40 * 6108589 * 2
def baseEnd_6108589 : Nat := 3136642277767705851144617

theorem tailTrace_6108589 : CollatzResearch.WordTrace tailWord_6108589 prefixEnd_6108589 3136642277767705851144617 := by
  unfold tailWord_6108589
  simp only [CollatzResearch.WordTrace]
  refine ⟨222798544466632791787824821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148532362977755194525216547 222798544466632791787824821)
  ·
    refine ⟨20887363543746824230108577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 222798544466632791787824821 20887363543746824230108577)
    ·
      refine ⟨15665522657810118172581433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20887363543746824230108577 15665522657810118172581433)
      ·
        refine ⟨11749141993357588629436075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15665522657810118172581433 11749141993357588629436075)
        ·
          refine ⟨17623712990036382944154113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11749141993357588629436075 17623712990036382944154113)
          ·
            refine ⟨13217784742527287208115585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17623712990036382944154113 13217784742527287208115585)
            ·
              refine ⟨9913338556895465406086689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13217784742527287208115585 9913338556895465406086689)
              ·
                refine ⟨7435003917671599054565017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9913338556895465406086689 7435003917671599054565017)
                ·
                  refine ⟨5576252938253699290923763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7435003917671599054565017 5576252938253699290923763)
                  ·
                    refine ⟨8364379407380548936385645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5576252938253699290923763 8364379407380548936385645)
                    ·
                      refine ⟨3136642277767705851144617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8364379407380548936385645 3136642277767705851144617)
                      ·
                        rfl

theorem cell23_6108589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_6108589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6108589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6108589 prefixEnd_6108589 := by exact prefixLift 6108589
  have htrace : WordTrace (prefixWord ++ tailWord_6108589) baseStart_6108589 baseEnd_6108589 := by
    simpa [prefixWord, tailWord_6108589, baseEnd_6108589] using wordTrace_append hprefix tailTrace_6108589
  have hstable : (prefixWord ++ tailWord_6108589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6108589).length < 2 ^ (prefixWord ++ tailWord_6108589).sum := by decide
  have hdescent : baseEnd_6108589 < baseStart_6108589 := by decide
  rcases family_descends (prefixWord ++ tailWord_6108589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6108591 : List Nat := [1, 1, 2, 1, 2, 2, 1, 2, 3, 4, 4]
def baseStart_6108591 : Nat := 118140960795 + 6108591 * 2 ^ 59
def prefixEnd_6108591 : Nat := 4983230072969 + 3 ^ 40 * 6108591 * 2
def baseEnd_6108591 : Nat := 3136643304729014843319607

theorem tailTrace_6108591 : CollatzResearch.WordTrace tailWord_6108591 prefixEnd_6108591 3136643304729014843319607 := by
  unfold tailWord_6108591
  simp only [CollatzResearch.WordTrace]
  refine ⟨222798617412625546129397627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148532411608417030752931751 222798617412625546129397627)
  ·
    refine ⟨334197926118938319194096441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222798617412625546129397627 334197926118938319194096441)
    ·
      refine ⟨250648444589203739395572331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 334197926118938319194096441 250648444589203739395572331)
      ·
        refine ⟨375972666883805609093358497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250648444589203739395572331 375972666883805609093358497)
        ·
          refine ⟨281979500162854206820018873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 375972666883805609093358497 281979500162854206820018873)
          ·
            refine ⟨211484625122140655115014155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 281979500162854206820018873 211484625122140655115014155)
            ·
              refine ⟨317226937683210982672521233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 211484625122140655115014155 317226937683210982672521233)
              ·
                refine ⟨237920203262408237004390925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 317226937683210982672521233 237920203262408237004390925)
                ·
                  refine ⟨89220076223403088876646597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 237920203262408237004390925 89220076223403088876646597)
                  ·
                    refine ⟨16728764291888079164371237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 89220076223403088876646597 16728764291888079164371237)
                    ·
                      refine ⟨3136643304729014843319607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16728764291888079164371237 3136643304729014843319607)
                      ·
                        rfl

theorem cell23_6108591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 3, 4, 4].length) (baseStart_6108591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6108591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6108591 prefixEnd_6108591 := by exact prefixLift 6108591
  have htrace : WordTrace (prefixWord ++ tailWord_6108591) baseStart_6108591 baseEnd_6108591 := by
    simpa [prefixWord, tailWord_6108591, baseEnd_6108591] using wordTrace_append hprefix tailTrace_6108591
  have hstable : (prefixWord ++ tailWord_6108591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6108591).length < 2 ^ (prefixWord ++ tailWord_6108591).sum := by decide
  have hdescent : baseEnd_6108591 < baseStart_6108591 := by decide
  rcases family_descends (prefixWord ++ tailWord_6108591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6108595 : List Nat := [1, 1, 1, 2, 3, 1, 1, 5, 4, 2, 2]
def baseStart_6108595 : Nat := 118140960795 + 6108595 * 2 ^ 59
def prefixEnd_6108595 : Nat := 4983230072969 + 3 ^ 40 * 6108595 * 2
def baseEnd_6108595 : Nat := 3136645358651632827669589

theorem tailTrace_6108595 : CollatzResearch.WordTrace tailWord_6108595 prefixEnd_6108595 3136645358651632827669589 := by
  unfold tailWord_6108595
  simp only [CollatzResearch.WordTrace]
  refine ⟨222798763304611054812543239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148532508869740703208362159 222798763304611054812543239)
  ·
    refine ⟨334198144956916582218814859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222798763304611054812543239 334198144956916582218814859)
    ·
      refine ⟨501297217435374873328222289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 334198144956916582218814859 501297217435374873328222289)
      ·
        refine ⟨375972913076531154996166717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 501297217435374873328222289 375972913076531154996166717)
        ·
          refine ⟨140989842403699183123562519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 375972913076531154996166717 140989842403699183123562519)
          ·
            refine ⟨211484763605548774685343779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140989842403699183123562519 211484763605548774685343779)
            ·
              refine ⟨317227145408323162028015669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 211484763605548774685343779 317227145408323162028015669)
              ·
                refine ⟨29740044882030296440126469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 317227145408323162028015669 29740044882030296440126469)
                ·
                  refine ⟨5576258415380680582523713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29740044882030296440126469 5576258415380680582523713)
                  ·
                    refine ⟨4182193811535510436892785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5576258415380680582523713 4182193811535510436892785)
                    ·
                      refine ⟨3136645358651632827669589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4182193811535510436892785 3136645358651632827669589)
                      ·
                        rfl

theorem cell23_6108595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 5, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 5, 4, 2, 2].length) (baseStart_6108595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6108595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6108595 prefixEnd_6108595 := by exact prefixLift 6108595
  have htrace : WordTrace (prefixWord ++ tailWord_6108595) baseStart_6108595 baseEnd_6108595 := by
    simpa [prefixWord, tailWord_6108595, baseEnd_6108595] using wordTrace_append hprefix tailTrace_6108595
  have hstable : (prefixWord ++ tailWord_6108595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6108595).length < 2 ^ (prefixWord ++ tailWord_6108595).sum := by decide
  have hdescent : baseEnd_6108595 < baseStart_6108595 := by decide
  rcases family_descends (prefixWord ++ tailWord_6108595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6108612 : List Nat := [2, 3, 3, 2, 1, 1, 1, 3, 1, 4, 2]
def baseStart_6108612 : Nat := 118140960795 + 6108612 * 2 ^ 59
def prefixEnd_6108612 : Nat := 4983230072969 + 3 ^ 40 * 6108612 * 2
def baseEnd_6108612 : Nat := 3136654087822759261157011

theorem tailTrace_6108612 : CollatzResearch.WordTrace tailWord_6108612 prefixEnd_6108612 3136654087822759261157011 := by
  unfold tailWord_6108612
  simp only [CollatzResearch.WordTrace]
  refine ⟨111399691672774733357956045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148532922230366311143941393 111399691672774733357956045)
  ·
    refine ⟨41774884377290525009233517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111399691672774733357956045 41774884377290525009233517)
    ·
      refine ⟨15665581641483946878462569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41774884377290525009233517 15665581641483946878462569)
      ·
        refine ⟨11749186231112960158846927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15665581641483946878462569 11749186231112960158846927)
        ·
          refine ⟨17623779346669440238270391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11749186231112960158846927 17623779346669440238270391)
          ·
            refine ⟨26435669020004160357405587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17623779346669440238270391 26435669020004160357405587)
            ·
              refine ⟨39653503530006240536108381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26435669020004160357405587 39653503530006240536108381)
              ·
                refine ⟨14870063823752340201040643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39653503530006240536108381 14870063823752340201040643)
                ·
                  refine ⟨22305095735628510301560965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14870063823752340201040643 22305095735628510301560965)
                  ·
                    refine ⟨4182205450430345681542681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22305095735628510301560965 4182205450430345681542681)
                    ·
                      refine ⟨3136654087822759261157011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4182205450430345681542681 3136654087822759261157011)
                      ·
                        rfl

theorem cell23_6108612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 3, 1, 4, 2].length) (baseStart_6108612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6108612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6108612 prefixEnd_6108612 := by exact prefixLift 6108612
  have htrace : WordTrace (prefixWord ++ tailWord_6108612) baseStart_6108612 baseEnd_6108612 := by
    simpa [prefixWord, tailWord_6108612, baseEnd_6108612] using wordTrace_append hprefix tailTrace_6108612
  have hstable : (prefixWord ++ tailWord_6108612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6108612).length < 2 ^ (prefixWord ++ tailWord_6108612).sum := by decide
  have hdescent : baseEnd_6108612 < baseStart_6108612 := by decide
  rcases family_descends (prefixWord ++ tailWord_6108612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6108618 : List Nat := [3, 1, 2, 1, 2, 4, 1, 2, 7]
def baseStart_6108618 : Nat := 118140960795 + 6108618 * 2 ^ 59
def prefixEnd_6108618 : Nat := 4983230072969 + 3 ^ 40 * 6108618 * 2
def baseEnd_6108618 : Nat := 348517463189631804186887

theorem tailTrace_6108618 : CollatzResearch.WordTrace tailWord_6108618 prefixEnd_6108618 348517463189631804186887 := by
  unfold tailWord_6108618
  simp only [CollatzResearch.WordTrace]
  refine ⟨55699900545881932435157627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148533068122351819827087005 55699900545881932435157627)
  ·
    refine ⟨83549850818822898652736441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55699900545881932435157627 83549850818822898652736441)
    ·
      refine ⟨62662388114117173989552331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83549850818822898652736441 62662388114117173989552331)
      ·
        refine ⟨93993582171175760984328497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62662388114117173989552331 93993582171175760984328497)
        ·
          refine ⟨70495186628381820738246373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93993582171175760984328497 70495186628381820738246373)
          ·
            refine ⟨13217847492821591388421195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70495186628381820738246373 13217847492821591388421195)
            ·
              refine ⟨19826771239232387082631793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13217847492821591388421195 19826771239232387082631793)
              ·
                refine ⟨14870078429424290311973845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19826771239232387082631793 14870078429424290311973845)
                ·
                  refine ⟨348517463189631804186887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14870078429424290311973845 348517463189631804186887)
                  ·
                    rfl

theorem cell23_6108618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 2, 7].length) (baseStart_6108618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6108618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6108618 prefixEnd_6108618 := by exact prefixLift 6108618
  have htrace : WordTrace (prefixWord ++ tailWord_6108618) baseStart_6108618 baseEnd_6108618 := by
    simpa [prefixWord, tailWord_6108618, baseEnd_6108618] using wordTrace_append hprefix tailTrace_6108618
  have hstable : (prefixWord ++ tailWord_6108618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6108618).length < 2 ^ (prefixWord ++ tailWord_6108618).sum := by decide
  have hdescent : baseEnd_6108618 < baseStart_6108618 := by decide
  rcases family_descends (prefixWord ++ tailWord_6108618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6108645 : List Nat := [1, 3, 1, 5, 1, 1, 1, 2, 2, 3, 3]
def baseStart_6108645 : Nat := 118140960795 + 6108645 * 2 ^ 59
def prefixEnd_6108645 : Nat := 4983230072969 + 3 ^ 40 * 6108645 * 2
def baseEnd_6108645 : Nat := 3136671032684357632044359

theorem tailTrace_6108645 : CollatzResearch.WordTrace tailWord_6108645 prefixEnd_6108645 3136671032684357632044359 := by
  unfold tailWord_6108645
  simp only [CollatzResearch.WordTrace]
  refine ⟨222800586954429913351863389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148533724636286608901242259 222800586954429913351863389)
  ·
    refine ⟨83550220107911217506948771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 222800586954429913351863389 83550220107911217506948771)
    ·
      refine ⟨125325330161866826260423157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83550220107911217506948771 125325330161866826260423157)
      ·
        refine ⟨11749249702675014961914671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 125325330161866826260423157 11749249702675014961914671)
        ·
          refine ⟨17623874554012522442872007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11749249702675014961914671 17623874554012522442872007)
          ·
            refine ⟨26435811831018783664308011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17623874554012522442872007 26435811831018783664308011)
            ·
              refine ⟨39653717746528175496462017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26435811831018783664308011 39653717746528175496462017)
              ·
                refine ⟨29740288309896131622346513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39653717746528175496462017 29740288309896131622346513)
                ·
                  refine ⟨22305216232422098716759885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29740288309896131622346513 22305216232422098716759885)
                  ·
                    refine ⟨8364456087158287018784957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22305216232422098716759885 8364456087158287018784957)
                    ·
                      refine ⟨3136671032684357632044359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8364456087158287018784957 3136671032684357632044359)
                      ·
                        rfl

theorem cell23_6108645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_6108645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6108645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6108645 prefixEnd_6108645 := by exact prefixLift 6108645
  have htrace : WordTrace (prefixWord ++ tailWord_6108645) baseStart_6108645 baseEnd_6108645 := by
    simpa [prefixWord, tailWord_6108645, baseEnd_6108645] using wordTrace_append hprefix tailTrace_6108645
  have hstable : (prefixWord ++ tailWord_6108645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6108645).length < 2 ^ (prefixWord ++ tailWord_6108645).sum := by decide
  have hdescent : baseEnd_6108645 < baseStart_6108645 := by decide
  rcases family_descends (prefixWord ++ tailWord_6108645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6108648 : List Nat := [2, 1, 4, 1, 1, 2, 2, 1, 4, 5]
def baseStart_6108648 : Nat := 118140960795 + 6108648 * 2 ^ 59
def prefixEnd_6108648 : Nat := 4983230072969 + 3 ^ 40 * 6108648 * 2
def baseEnd_6108648 : Nat := 1045557524375440373435615

theorem tailTrace_6108648 : CollatzResearch.WordTrace tailWord_6108648 prefixEnd_6108648 1045557524375440373435615 := by
  unfold tailWord_6108648
  simp only [CollatzResearch.WordTrace]
  refine ⟨111400348186709522432111299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148533797582279363242815065 111400348186709522432111299)
  ·
    refine ⟨167100522280064283648166949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111400348186709522432111299 167100522280064283648166949)
    ·
      refine ⟨31331347927512053184031303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 167100522280064283648166949 31331347927512053184031303)
      ·
        refine ⟨46997021891268079776046955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31331347927512053184031303 46997021891268079776046955)
        ·
          refine ⟨70495532836902119664070433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46997021891268079776046955 70495532836902119664070433)
          ·
            refine ⟨52871649627676589748052825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70495532836902119664070433 52871649627676589748052825)
            ·
              refine ⟨39653737220757442311039619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52871649627676589748052825 39653737220757442311039619)
              ·
                refine ⟨59480605831136163466559429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39653737220757442311039619 59480605831136163466559429)
                ·
                  refine ⟨11152613593338030649979893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59480605831136163466559429 11152613593338030649979893)
                  ·
                    refine ⟨1045557524375440373435615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11152613593338030649979893 1045557524375440373435615)
                    ·
                      rfl

theorem cell23_6108648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 1, 4, 5].length) (baseStart_6108648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6108648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6108648 prefixEnd_6108648 := by exact prefixLift 6108648
  have htrace : WordTrace (prefixWord ++ tailWord_6108648) baseStart_6108648 baseEnd_6108648 := by
    simpa [prefixWord, tailWord_6108648, baseEnd_6108648] using wordTrace_append hprefix tailTrace_6108648
  have hstable : (prefixWord ++ tailWord_6108648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6108648).length < 2 ^ (prefixWord ++ tailWord_6108648).sum := by decide
  have hdescent : baseEnd_6108648 < baseStart_6108648 := by decide
  rcases family_descends (prefixWord ++ tailWord_6108648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6108668 : List Nat := [2, 2, 2, 1, 2, 1, 3, 2, 1, 3, 4]
def baseStart_6108668 : Nat := 118140960795 + 6108668 * 2 ^ 59
def prefixEnd_6108668 : Nat := 4983230072969 + 3 ^ 40 * 6108668 * 2
def baseEnd_6108668 : Nat := 3136682842739411042056753

theorem tailTrace_6108668 : CollatzResearch.WordTrace tailWord_6108668 prefixEnd_6108668 3136682842739411042056753 := by
  unfold tailWord_6108668
  simp only [CollatzResearch.WordTrace]
  refine ⟨111400712916673294139975329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148534283888897725519967105 111400712916673294139975329)
  ·
    refine ⟨83550534687504970604981497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111400712916673294139975329 83550534687504970604981497)
    ·
      refine ⟨62662901015628727953736123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83550534687504970604981497 62662901015628727953736123)
      ·
        refine ⟨93994351523443091930604185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62662901015628727953736123 93994351523443091930604185)
        ·
          refine ⟨70495763642582318947953139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93994351523443091930604185 70495763642582318947953139)
          ·
            refine ⟨105743645463873478421929709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70495763642582318947953139 105743645463873478421929709)
            ·
              refine ⟨39653867048952554408223641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105743645463873478421929709 39653867048952554408223641)
              ·
                refine ⟨29740400286714415806167731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39653867048952554408223641 29740400286714415806167731)
                ·
                  refine ⟨44610600430071623709251597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29740400286714415806167731 44610600430071623709251597)
                  ·
                    refine ⟨16728975161276858890969349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44610600430071623709251597 16728975161276858890969349)
                    ·
                      refine ⟨3136682842739411042056753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16728975161276858890969349 3136682842739411042056753)
                      ·
                        rfl

theorem cell23_6108668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 2, 1, 3, 4].length) (baseStart_6108668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6108668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6108668 prefixEnd_6108668 := by exact prefixLift 6108668
  have htrace : WordTrace (prefixWord ++ tailWord_6108668) baseStart_6108668 baseEnd_6108668 := by
    simpa [prefixWord, tailWord_6108668, baseEnd_6108668] using wordTrace_append hprefix tailTrace_6108668
  have hstable : (prefixWord ++ tailWord_6108668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6108668).length < 2 ^ (prefixWord ++ tailWord_6108668).sum := by decide
  have hdescent : baseEnd_6108668 < baseStart_6108668 := by decide
  rcases family_descends (prefixWord ++ tailWord_6108668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6108705 : List Nat := [1, 2, 3, 2, 2, 2, 1, 1, 4, 2, 3]
def baseStart_6108705 : Nat := 118140960795 + 6108705 * 2 ^ 59
def prefixEnd_6108705 : Nat := 4983230072969 + 3 ^ 40 * 6108705 * 2
def baseEnd_6108705 : Nat := 3136701841523627397294083

theorem tailTrace_6108705 : CollatzResearch.WordTrace tailWord_6108705 prefixEnd_6108705 3136701841523627397294083 := by
  unfold tailWord_6108705
  simp only [CollatzResearch.WordTrace]
  refine ⟨222802775334212543599047569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148535183556141695732698379 222802775334212543599047569)
  ·
    refine ⟨167102081500659407699285677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222802775334212543599047569 167102081500659407699285677)
    ·
      refine ⟨62663280562747277887232129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167102081500659407699285677 62663280562747277887232129)
      ·
        refine ⟨46997460422060458415424097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62663280562747277887232129 46997460422060458415424097)
        ·
          refine ⟨35248095316545343811568073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46997460422060458415424097 35248095316545343811568073)
          ·
            refine ⟨26436071487409007858676055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35248095316545343811568073 26436071487409007858676055)
            ·
              refine ⟨39654107231113511788014083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26436071487409007858676055 39654107231113511788014083)
              ·
                refine ⟨59481160846670267682021125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39654107231113511788014083 59481160846670267682021125)
                ·
                  refine ⟨11152717658750675190378961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59481160846670267682021125 11152717658750675190378961)
                  ·
                    refine ⟨8364538244063006392784221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11152717658750675190378961 8364538244063006392784221)
                    ·
                      refine ⟨3136701841523627397294083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8364538244063006392784221 3136701841523627397294083)
                      ·
                        rfl

theorem cell23_6108705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 1, 4, 2, 3].length) (baseStart_6108705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6108705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6108705 prefixEnd_6108705 := by exact prefixLift 6108705
  have htrace : WordTrace (prefixWord ++ tailWord_6108705) baseStart_6108705 baseEnd_6108705 := by
    simpa [prefixWord, tailWord_6108705, baseEnd_6108705] using wordTrace_append hprefix tailTrace_6108705
  have hstable : (prefixWord ++ tailWord_6108705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6108705).length < 2 ^ (prefixWord ++ tailWord_6108705).sum := by decide
  have hdescent : baseEnd_6108705 < baseStart_6108705 := by decide
  rcases family_descends (prefixWord ++ tailWord_6108705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6108725 : List Nat := [1, 3, 3, 1, 1, 4, 1, 3, 6]
def baseStart_6108725 : Nat := 118140960795 + 6108725 * 2 ^ 59
def prefixEnd_6108725 : Nat := 4983230072969 + 3 ^ 40 * 6108725 * 2
def baseEnd_6108725 : Nat := 348523567904079702115999

theorem tailTrace_6108725 : CollatzResearch.WordTrace tailWord_6108725 prefixEnd_6108725 348523567904079702115999 := by
  unfold tailWord_6108725
  simp only [CollatzResearch.WordTrace]
  refine ⟨222803504794140087014775629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148535669862760058009850419 222803504794140087014775629)
  ·
    refine ⟨83551314297802532630540861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 222803504794140087014775629 83551314297802532630540861)
    ·
      refine ⟨31331742861675949736452823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83551314297802532630540861 31331742861675949736452823)
      ·
        refine ⟨46997614292513924604679235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31331742861675949736452823 46997614292513924604679235)
        ·
          refine ⟨70496421438770886907018853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46997614292513924604679235 70496421438770886907018853)
          ·
            refine ⟨13218079019769541295066035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70496421438770886907018853 13218079019769541295066035)
            ·
              refine ⟨19827118529654311942599053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13218079019769541295066035 19827118529654311942599053)
              ·
                refine ⟨7435169448620366978474645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19827118529654311942599053 7435169448620366978474645)
                ·
                  refine ⟨348523567904079702115999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7435169448620366978474645 348523567904079702115999)
                  ·
                    rfl

theorem cell23_6108725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 3, 6].length) (baseStart_6108725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6108725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6108725 prefixEnd_6108725 := by exact prefixLift 6108725
  have htrace : WordTrace (prefixWord ++ tailWord_6108725) baseStart_6108725 baseEnd_6108725 := by
    simpa [prefixWord, tailWord_6108725, baseEnd_6108725] using wordTrace_append hprefix tailTrace_6108725
  have hstable : (prefixWord ++ tailWord_6108725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6108725).length < 2 ^ (prefixWord ++ tailWord_6108725).sum := by decide
  have hdescent : baseEnd_6108725 < baseStart_6108725 := by decide
  rcases family_descends (prefixWord ++ tailWord_6108725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6108745 : List Nat := [1, 2, 1, 1, 2, 2, 1, 5, 1, 5, 2]
def baseStart_6108745 : Nat := 118140960795 + 6108745 * 2 ^ 59
def prefixEnd_6108745 : Nat := 4983230072969 + 3 ^ 40 * 6108745 * 2
def baseEnd_6108745 : Nat := 3136722380749807240793899

theorem tailTrace_6108745 : CollatzResearch.WordTrace tailWord_6108745 prefixEnd_6108745 3136722380749807240793899 := by
  unfold tailWord_6108745
  simp only [CollatzResearch.WordTrace]
  refine ⟨222804234254067630430503689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148536156169378420287002459 222804234254067630430503689)
  ·
    refine ⟨167103175690550722822877767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222804234254067630430503689 167103175690550722822877767)
    ·
      refine ⟨250654763535826084234316651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167103175690550722822877767 250654763535826084234316651)
      ·
        refine ⟨375982145303739126351474977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250654763535826084234316651 375982145303739126351474977)
        ·
          refine ⟨281986608977804344763606233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 375982145303739126351474977 281986608977804344763606233)
          ·
            refine ⟨211489956733353258572704675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 281986608977804344763606233 211489956733353258572704675)
            ·
              refine ⟨317234935100029887859057013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 211489956733353258572704675 317234935100029887859057013)
              ·
                refine ⟨29740775165627801986786595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 317234935100029887859057013 29740775165627801986786595)
                ·
                  refine ⟨44611162748441702980179893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29740775165627801986786595 44611162748441702980179893)
                  ·
                    refine ⟨4182296507666409654391865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44611162748441702980179893 4182296507666409654391865)
                    ·
                      refine ⟨3136722380749807240793899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4182296507666409654391865 3136722380749807240793899)
                      ·
                        rfl

theorem cell23_6108745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 5, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 5, 1, 5, 2].length) (baseStart_6108745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6108745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6108745 prefixEnd_6108745 := by exact prefixLift 6108745
  have htrace : WordTrace (prefixWord ++ tailWord_6108745) baseStart_6108745 baseEnd_6108745 := by
    simpa [prefixWord, tailWord_6108745, baseEnd_6108745] using wordTrace_append hprefix tailTrace_6108745
  have hstable : (prefixWord ++ tailWord_6108745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6108745).length < 2 ^ (prefixWord ++ tailWord_6108745).sum := by decide
  have hdescent : baseEnd_6108745 < baseStart_6108745 := by decide
  rcases family_descends (prefixWord ++ tailWord_6108745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6108768 : List Nat := [2, 1, 1, 3, 2, 1, 1, 1, 5, 6]
def baseStart_6108768 : Nat := 118140960795 + 6108768 * 2 ^ 59
def prefixEnd_6108768 : Nat := 4983230072969 + 3 ^ 40 * 6108768 * 2
def baseEnd_6108768 : Nat := 1045578063601620216935431

theorem tailTrace_6108768 : CollatzResearch.WordTrace tailWord_6108768 prefixEnd_6108768 1045578063601620216935431 := by
  unfold tailWord_6108768
  simp only [CollatzResearch.WordTrace]
  refine ⟨111402536566492152679295479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148536715421989536905727305 111402536566492152679295479)
  ·
    refine ⟨167103804849738229018943219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111402536566492152679295479 167103804849738229018943219)
    ·
      refine ⟨250655707274607343528414829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167103804849738229018943219 250655707274607343528414829)
      ·
        refine ⟨93995890227977753823155561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 250655707274607343528414829 93995890227977753823155561)
        ·
          refine ⟨70496917670983315367366671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93995890227977753823155561 70496917670983315367366671)
          ·
            refine ⟨105745376506474973051050007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70496917670983315367366671 105745376506474973051050007)
            ·
              refine ⟨158618064759712459576575011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105745376506474973051050007 158618064759712459576575011)
              ·
                refine ⟨237927097139568689364862517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 158618064759712459576575011 237927097139568689364862517)
                ·
                  refine ⟨22305665356834564627955861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 237927097139568689364862517 22305665356834564627955861)
                  ·
                    refine ⟨1045578063601620216935431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22305665356834564627955861 1045578063601620216935431)
                    ·
                      rfl

theorem cell23_6108768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 5, 6].length) (baseStart_6108768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6108768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6108768 prefixEnd_6108768 := by exact prefixLift 6108768
  have htrace : WordTrace (prefixWord ++ tailWord_6108768) baseStart_6108768 baseEnd_6108768 := by
    simpa [prefixWord, tailWord_6108768, baseEnd_6108768] using wordTrace_append hprefix tailTrace_6108768
  have hstable : (prefixWord ++ tailWord_6108768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6108768).length < 2 ^ (prefixWord ++ tailWord_6108768).sum := by decide
  have hdescent : baseEnd_6108768 < baseStart_6108768 := by decide
  rcases family_descends (prefixWord ++ tailWord_6108768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6108769 : List Nat := [1, 2, 3, 1, 1, 3, 3, 4, 1, 1, 3]
def baseStart_6108769 : Nat := 118140960795 + 6108769 * 2 ^ 59
def prefixEnd_6108769 : Nat := 4983230072969 + 3 ^ 40 * 6108769 * 2
def baseEnd_6108769 : Nat := 3136734704285515146893789

theorem tailTrace_6108769 : CollatzResearch.WordTrace tailWord_6108769 prefixEnd_6108769 3136734704285515146893789 := by
  unfold tailWord_6108769
  simp only [CollatzResearch.WordTrace]
  refine ⟨222805109605980682529377361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148536739737320455019584907 222805109605980682529377361)
  ·
    refine ⟨167103832204485511897033021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 222805109605980682529377361 167103832204485511897033021)
    ·
      refine ⟨62663937076682066961387383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167103832204485511897033021 62663937076682066961387383)
      ·
        refine ⟨93995905615023100442081075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62663937076682066961387383 93995905615023100442081075)
        ·
          refine ⟨140993858422534650663121613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93995905615023100442081075 140993858422534650663121613)
          ·
            refine ⟨52872696908450493998670605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 140993858422534650663121613 52872696908450493998670605)
            ·
              refine ⟨19827261340668935249501477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52872696908450493998670605 19827261340668935249501477)
              ·
                refine ⟨3717611501375425359281527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19827261340668935249501477 3717611501375425359281527)
                ·
                  refine ⟨5576417252063138038922291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3717611501375425359281527 5576417252063138038922291)
                  ·
                    refine ⟨8364625878094707058383437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5576417252063138038922291 8364625878094707058383437)
                    ·
                      refine ⟨3136734704285515146893789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8364625878094707058383437 3136734704285515146893789)
                      ·
                        rfl

theorem cell23_6108769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 4, 1, 1, 3].length) (baseStart_6108769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6108769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6108769 prefixEnd_6108769 := by exact prefixLift 6108769
  have htrace : WordTrace (prefixWord ++ tailWord_6108769) baseStart_6108769 baseEnd_6108769 := by
    simpa [prefixWord, tailWord_6108769, baseEnd_6108769] using wordTrace_append hprefix tailTrace_6108769
  have hstable : (prefixWord ++ tailWord_6108769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6108769).length < 2 ^ (prefixWord ++ tailWord_6108769).sum := by decide
  have hdescent : baseEnd_6108769 < baseStart_6108769 := by decide
  rcases family_descends (prefixWord ++ tailWord_6108769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6108775 : List Nat := [1, 1, 5, 1, 1, 1, 3, 2, 3, 1, 4]
def baseStart_6108775 : Nat := 118140960795 + 6108775 * 2 ^ 59
def prefixEnd_6108775 : Nat := 4983230072969 + 3 ^ 40 * 6108775 * 2
def baseEnd_6108775 : Nat := 3136737785169442123418761

theorem tailTrace_6108775 : CollatzResearch.WordTrace tailWord_6108775 prefixEnd_6108775 3136737785169442123418761 := by
  unfold tailWord_6108775
  simp only [CollatzResearch.WordTrace]
  refine ⟨222805328443958945554095779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148536885629305963702730519 222805328443958945554095779)
  ·
    refine ⟨334207992665938418331143669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222805328443958945554095779 334207992665938418331143669)
    ·
      refine ⟨31331999312431726718544719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 334207992665938418331143669 31331999312431726718544719)
      ·
        refine ⟨46997998968647590077817079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31331999312431726718544719 46997998968647590077817079)
        ·
          refine ⟨70496998452971385116725619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46997998968647590077817079 70496998452971385116725619)
          ·
            refine ⟨105745497679457077675088429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70496998452971385116725619 105745497679457077675088429)
            ·
              refine ⟨39654561629796404128158161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105745497679457077675088429 39654561629796404128158161)
              ·
                refine ⟨29740921222347303096118621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39654561629796404128158161 29740921222347303096118621)
                ·
                  refine ⟨11152845458380238661044483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29740921222347303096118621 11152845458380238661044483)
                  ·
                    refine ⟨16729268187570357991566725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11152845458380238661044483 16729268187570357991566725)
                    ·
                      refine ⟨3136737785169442123418761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16729268187570357991566725 3136737785169442123418761)
                      ·
                        rfl

theorem cell23_6108775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 2, 3, 1, 4].length) (baseStart_6108775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6108775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6108775 prefixEnd_6108775 := by exact prefixLift 6108775
  have htrace : WordTrace (prefixWord ++ tailWord_6108775) baseStart_6108775 baseEnd_6108775 := by
    simpa [prefixWord, tailWord_6108775, baseEnd_6108775] using wordTrace_append hprefix tailTrace_6108775
  have hstable : (prefixWord ++ tailWord_6108775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6108775).length < 2 ^ (prefixWord ++ tailWord_6108775).sum := by decide
  have hdescent : baseEnd_6108775 < baseStart_6108775 := by decide
  rcases family_descends (prefixWord ++ tailWord_6108775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6108795 : List Nat := [1, 1, 1, 1, 1, 4, 3, 3, 3, 2, 3]
def baseStart_6108795 : Nat := 118140960795 + 6108795 * 2 ^ 59
def prefixEnd_6108795 : Nat := 4983230072969 + 3 ^ 40 * 6108795 * 2
def baseEnd_6108795 : Nat := 3136748054782532045168669

theorem tailTrace_6108795 : CollatzResearch.WordTrace tailWord_6108795 prefixEnd_6108795 3136748054782532045168669 := by
  unfold tailWord_6108795
  simp only [CollatzResearch.WordTrace]
  refine ⟨222806057903886488969823839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148537371935924325979882559 222806057903886488969823839)
  ·
    refine ⟨334209086855829733454735759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222806057903886488969823839 334209086855829733454735759)
    ·
      refine ⟨501313630283744600182103639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 334209086855829733454735759 501313630283744600182103639)
      ·
        refine ⟨751970445425616900273155459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 501313630283744600182103639 751970445425616900273155459)
        ·
          refine ⟨1127955668138425350409733189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 751970445425616900273155459 1127955668138425350409733189)
          ·
            refine ⟨211491687775954753201824973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1127955668138425350409733189 211491687775954753201824973)
            ·
              refine ⟨79309382915983032450684365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 211491687775954753201824973 79309382915983032450684365)
              ·
                refine ⟨29741018593493637169006637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79309382915983032450684365 29741018593493637169006637)
                ·
                  refine ⟨11152881972560113938377489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29741018593493637169006637 11152881972560113938377489)
                  ·
                    refine ⟨8364661479420085453783117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11152881972560113938377489 8364661479420085453783117)
                    ·
                      refine ⟨3136748054782532045168669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8364661479420085453783117 3136748054782532045168669)
                      ·
                        rfl

theorem cell23_6108795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 3, 3, 2, 3].length) (baseStart_6108795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6108795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6108795 prefixEnd_6108795 := by exact prefixLift 6108795
  have htrace : WordTrace (prefixWord ++ tailWord_6108795) baseStart_6108795 baseEnd_6108795 := by
    simpa [prefixWord, tailWord_6108795, baseEnd_6108795] using wordTrace_append hprefix tailTrace_6108795
  have hstable : (prefixWord ++ tailWord_6108795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6108795).length < 2 ^ (prefixWord ++ tailWord_6108795).sum := by decide
  have hdescent : baseEnd_6108795 < baseStart_6108795 := by decide
  rcases family_descends (prefixWord ++ tailWord_6108795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6108805 : List Nat := [1, 3, 1, 1, 4, 1, 1, 4, 1, 2, 4]
def baseStart_6108805 : Nat := 118140960795 + 6108805 * 2 ^ 59
def prefixEnd_6108805 : Nat := 4983230072969 + 3 ^ 40 * 6108805 * 2
def baseEnd_6108805 : Nat := 3136753189589077006043623

theorem tailTrace_6108805 : CollatzResearch.WordTrace tailWord_6108805 prefixEnd_6108805 3136753189589077006043623 := by
  unfold tailWord_6108805
  simp only [CollatzResearch.WordTrace]
  refine ⟨222806422633850260677687869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148537615089233507118458579 222806422633850260677687869)
  ·
    refine ⟨83552408487693847754132951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 222806422633850260677687869 83552408487693847754132951)
    ·
      refine ⟨125328612731540771631199427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83552408487693847754132951 125328612731540771631199427)
      ·
        refine ⟨187992919097311157446799141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125328612731540771631199427 187992919097311157446799141)
        ·
          refine ⟨35248672330745842021274839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 187992919097311157446799141 35248672330745842021274839)
          ·
            refine ⟨52873008496118763031912259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35248672330745842021274839 52873008496118763031912259)
            ·
              refine ⟨79309512744178144547868389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52873008496118763031912259 79309512744178144547868389)
              ·
                refine ⟨14870533639533402102725323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 79309512744178144547868389 14870533639533402102725323)
                ·
                  refine ⟨22305800459300103154087985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14870533639533402102725323 22305800459300103154087985)
                  ·
                    refine ⟨16729350344475077365565989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22305800459300103154087985 16729350344475077365565989)
                    ·
                      refine ⟨3136753189589077006043623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16729350344475077365565989 3136753189589077006043623)
                      ·
                        rfl

theorem cell23_6108805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 4, 1, 2, 4].length) (baseStart_6108805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6108805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6108805 prefixEnd_6108805 := by exact prefixLift 6108805
  have htrace : WordTrace (prefixWord ++ tailWord_6108805) baseStart_6108805 baseEnd_6108805 := by
    simpa [prefixWord, tailWord_6108805, baseEnd_6108805] using wordTrace_append hprefix tailTrace_6108805
  have hstable : (prefixWord ++ tailWord_6108805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6108805).length < 2 ^ (prefixWord ++ tailWord_6108805).sum := by decide
  have hdescent : baseEnd_6108805 < baseStart_6108805 := by decide
  rcases family_descends (prefixWord ++ tailWord_6108805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6108812 : List Nat := [2, 2, 1, 2, 1, 1, 5, 3, 1, 2, 3]
def baseStart_6108812 : Nat := 118140960795 + 6108812 * 2 ^ 59
def prefixEnd_6108812 : Nat := 4983230072969 + 3 ^ 40 * 6108812 * 2
def baseEnd_6108812 : Nat := 3136756783953658478656091

theorem tailTrace_6108812 : CollatzResearch.WordTrace tailWord_6108812 prefixEnd_6108812 3136756783953658478656091 := by
  unfold tailWord_6108812
  simp only [CollatzResearch.WordTrace]
  refine ⟨111403338972412450436596345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148537785296549933915461793 111403338972412450436596345)
  ·
    refine ⟨83552504229309337827447259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111403338972412450436596345 83552504229309337827447259)
    ·
      refine ⟨125328756343964006741170889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83552504229309337827447259 125328756343964006741170889)
      ·
        refine ⟨93996567257973005055878167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125328756343964006741170889 93996567257973005055878167)
        ·
          refine ⟨140994850886959507583817251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93996567257973005055878167 140994850886959507583817251)
          ·
            refine ⟨211492276330439261375725877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 140994850886959507583817251 211492276330439261375725877)
            ·
              refine ⟨19827400905978680753974301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 211492276330439261375725877 19827400905978680753974301)
              ·
                refine ⟨7435275339742005282740363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19827400905978680753974301 7435275339742005282740363)
                ·
                  refine ⟨11152913009613007924110545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7435275339742005282740363 11152913009613007924110545)
                  ·
                    refine ⟨8364684757209755943082909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11152913009613007924110545 8364684757209755943082909)
                    ·
                      refine ⟨3136756783953658478656091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8364684757209755943082909 3136756783953658478656091)
                      ·
                        rfl

theorem cell23_6108812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 3, 1, 2, 3].length) (baseStart_6108812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6108812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6108812 prefixEnd_6108812 := by exact prefixLift 6108812
  have htrace : WordTrace (prefixWord ++ tailWord_6108812) baseStart_6108812 baseEnd_6108812 := by
    simpa [prefixWord, tailWord_6108812, baseEnd_6108812] using wordTrace_append hprefix tailTrace_6108812
  have hstable : (prefixWord ++ tailWord_6108812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6108812).length < 2 ^ (prefixWord ++ tailWord_6108812).sum := by decide
  have hdescent : baseEnd_6108812 < baseStart_6108812 := by decide
  rcases family_descends (prefixWord ++ tailWord_6108812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6108855 : List Nat := [1, 1, 3, 1, 5, 1, 1, 1, 2, 2, 5]
def baseStart_6108855 : Nat := 118140960795 + 6108855 * 2 ^ 59
def prefixEnd_6108855 : Nat := 4983230072969 + 3 ^ 40 * 6108855 * 2
def baseEnd_6108855 : Nat := 3136778863621801810418393

theorem tailTrace_6108855 : CollatzResearch.WordTrace tailWord_6108855 prefixEnd_6108855 3136778863621801810418393 := by
  unfold tailWord_6108855
  simp only [CollatzResearch.WordTrace]
  refine ⟨222808246283669119217008019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148538830855779412811338679 222808246283669119217008019)
  ·
    refine ⟨334212369425503678825512029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222808246283669119217008019 334212369425503678825512029)
    ·
      refine ⟨125329638534563879559567011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 334212369425503678825512029 125329638534563879559567011)
      ·
        refine ⟨187994457801845819339350517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125329638534563879559567011 187994457801845819339350517)
        ·
          refine ⟨17624480418923045563064111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 187994457801845819339350517 17624480418923045563064111)
          ·
            refine ⟨26436720628384568344596167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17624480418923045563064111 26436720628384568344596167)
            ·
              refine ⟨39655080942576852516894251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26436720628384568344596167 39655080942576852516894251)
              ·
                refine ⟨59482621413865278775341377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39655080942576852516894251 59482621413865278775341377)
                ·
                  refine ⟨44611966060398959081506033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59482621413865278775341377 44611966060398959081506033)
                  ·
                    refine ⟨33458974545299219311129525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44611966060398959081506033 33458974545299219311129525)
                    ·
                      refine ⟨3136778863621801810418393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33458974545299219311129525 3136778863621801810418393)
                      ·
                        rfl

theorem cell23_6108855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 1, 2, 2, 5].length) (baseStart_6108855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6108855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6108855 prefixEnd_6108855 := by exact prefixLift 6108855
  have htrace : WordTrace (prefixWord ++ tailWord_6108855) baseStart_6108855 baseEnd_6108855 := by
    simpa [prefixWord, tailWord_6108855, baseEnd_6108855] using wordTrace_append hprefix tailTrace_6108855
  have hstable : (prefixWord ++ tailWord_6108855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6108855).length < 2 ^ (prefixWord ++ tailWord_6108855).sum := by decide
  have hdescent : baseEnd_6108855 < baseStart_6108855 := by decide
  rcases family_descends (prefixWord ++ tailWord_6108855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6108866 : List Nat := [3, 5, 1, 2, 1, 2, 9]
def baseStart_6108866 : Nat := 118140960795 + 6108866 * 2 ^ 59
def prefixEnd_6108866 : Nat := 4983230072969 + 3 ^ 40 * 6108866 * 2
def baseEnd_6108866 : Nat := 38725734714925941572603

theorem tailTrace_6108866 : CollatzResearch.WordTrace tailWord_6108866 prefixEnd_6108866 38725734714925941572603 := by
  unfold tailWord_6108866
  simp only [CollatzResearch.WordTrace]
  refine ⟨55702161871657317023914613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148539098324419512063772301 55702161871657317023914613)
  ·
    refine ⟨5222077675467873470991995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 55702161871657317023914613 5222077675467873470991995)
    ·
      refine ⟨7833116513201810206487993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5222077675467873470991995 7833116513201810206487993)
      ·
        refine ⟨5874837384901357654865995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7833116513201810206487993 5874837384901357654865995)
        ·
          refine ⟨8812256077352036482298993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5874837384901357654865995 8812256077352036482298993)
          ·
            refine ⟨6609192058014027361724245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8812256077352036482298993 6609192058014027361724245)
            ·
              refine ⟨38725734714925941572603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6609192058014027361724245 38725734714925941572603)
              ·
                rfl

theorem cell23_6108866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 9].length) (baseStart_6108866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6108866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6108866 prefixEnd_6108866 := by exact prefixLift 6108866
  have htrace : WordTrace (prefixWord ++ tailWord_6108866) baseStart_6108866 baseEnd_6108866 := by
    simpa [prefixWord, tailWord_6108866, baseEnd_6108866] using wordTrace_append hprefix tailTrace_6108866
  have hstable : (prefixWord ++ tailWord_6108866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6108866).length < 2 ^ (prefixWord ++ tailWord_6108866).sum := by decide
  have hdescent : baseEnd_6108866 < baseStart_6108866 := by decide
  rcases family_descends (prefixWord ++ tailWord_6108866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6108877 : List Nat := [1, 6, 2, 1, 1, 2, 3, 2, 1, 2, 2]
def baseStart_6108877 : Nat := 118140960795 + 6108877 * 2 ^ 59
def prefixEnd_6108877 : Nat := 4983230072969 + 3 ^ 40 * 6108877 * 2
def baseEnd_6108877 : Nat := 3136790160196200724343293

theorem tailTrace_6108877 : CollatzResearch.WordTrace tailWord_6108877 prefixEnd_6108877 3136790160196200724343293 := by
  unfold tailWord_6108877
  simp only [CollatzResearch.WordTrace]
  refine ⟨222809048689589416974308885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148539365793059611316205923 222809048689589416974308885)
  ·
    refine ⟨10444174157324503920670729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 222809048689589416974308885 10444174157324503920670729)
    ·
      refine ⟨7833130617993377940503047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10444174157324503920670729 7833130617993377940503047)
      ·
        refine ⟨11749695926990066910754571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7833130617993377940503047 11749695926990066910754571)
        ·
          refine ⟨17624543890485100366131857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11749695926990066910754571 17624543890485100366131857)
          ·
            refine ⟨13218407917863825274598893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17624543890485100366131857 13218407917863825274598893)
            ·
              refine ⟨4956902969198934477974585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13218407917863825274598893 4956902969198934477974585)
              ·
                refine ⟨3717677226899200858480939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4956902969198934477974585 3717677226899200858480939)
                ·
                  refine ⟨5576515840348801287721409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3717677226899200858480939 5576515840348801287721409)
                  ·
                    refine ⟨4182386880261600965791057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5576515840348801287721409 4182386880261600965791057)
                    ·
                      refine ⟨3136790160196200724343293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4182386880261600965791057 3136790160196200724343293)
                      ·
                        rfl

theorem cell23_6108877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 3, 2, 1, 2, 2].length) (baseStart_6108877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6108877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6108877 prefixEnd_6108877 := by exact prefixLift 6108877
  have htrace : WordTrace (prefixWord ++ tailWord_6108877) baseStart_6108877 baseEnd_6108877 := by
    simpa [prefixWord, tailWord_6108877, baseEnd_6108877] using wordTrace_append hprefix tailTrace_6108877
  have hstable : (prefixWord ++ tailWord_6108877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6108877).length < 2 ^ (prefixWord ++ tailWord_6108877).sum := by decide
  have hdescent : baseEnd_6108877 < baseStart_6108877 := by decide
  rcases family_descends (prefixWord ++ tailWord_6108877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6108893 : List Nat := [1, 4, 3, 3, 1, 1, 1, 3, 2, 1, 3]
def baseStart_6108893 : Nat := 118140960795 + 6108893 * 2 ^ 59
def prefixEnd_6108893 : Nat := 4983230072969 + 3 ^ 40 * 6108893 * 2
def baseEnd_6108893 : Nat := 3136798375886672661743219

theorem tailTrace_6108893 : CollatzResearch.WordTrace tailWord_6108893 prefixEnd_6108893 3136798375886672661743219 := by
  unfold tailWord_6108893
  simp only [CollatzResearch.WordTrace]
  refine ⟨222809632257531451706891333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148539754838354301137927555 222809632257531451706891333)
  ·
    refine ⟨41776806048287147195042125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 222809632257531451706891333 41776806048287147195042125)
    ·
      refine ⟨15666302268107680198140797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41776806048287147195042125 15666302268107680198140797)
      ·
        refine ⟨5874863350540380074302799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15666302268107680198140797 5874863350540380074302799)
        ·
          refine ⟨8812295025810570111454199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5874863350540380074302799 8812295025810570111454199)
          ·
            refine ⟨13218442538715855167181299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8812295025810570111454199 13218442538715855167181299)
            ·
              refine ⟨19827663808073782750771949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13218442538715855167181299 19827663808073782750771949)
              ·
                refine ⟨7435373928027668531539481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19827663808073782750771949 7435373928027668531539481)
                ·
                  refine ⟨5576530446020751398654611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7435373928027668531539481 5576530446020751398654611)
                  ·
                    refine ⟨8364795669031127097981917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5576530446020751398654611 8364795669031127097981917)
                    ·
                      refine ⟨3136798375886672661743219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8364795669031127097981917 3136798375886672661743219)
                      ·
                        rfl

theorem cell23_6108893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_6108893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6108893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6108893 prefixEnd_6108893 := by exact prefixLift 6108893
  have htrace : WordTrace (prefixWord ++ tailWord_6108893) baseStart_6108893 baseEnd_6108893 := by
    simpa [prefixWord, tailWord_6108893, baseEnd_6108893] using wordTrace_append hprefix tailTrace_6108893
  have hstable : (prefixWord ++ tailWord_6108893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6108893).length < 2 ^ (prefixWord ++ tailWord_6108893).sum := by decide
  have hdescent : baseEnd_6108893 < baseStart_6108893 := by decide
  rcases family_descends (prefixWord ++ tailWord_6108893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6108895 : List Nat := [1, 1, 2, 3, 2, 2, 2, 1, 1, 4, 4]
def baseStart_6108895 : Nat := 118140960795 + 6108895 * 2 ^ 59
def prefixEnd_6108895 : Nat := 4983230072969 + 3 ^ 40 * 6108895 * 2
def baseEnd_6108895 : Nat := 3136799402847981653918209

theorem tailTrace_6108895 : CollatzResearch.WordTrace tailWord_6108895 prefixEnd_6108895 3136799402847981653918209 := by
  unfold tailWord_6108895
  simp only [CollatzResearch.WordTrace]
  refine ⟨222809705203524206048464139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148539803469016137365642759 222809705203524206048464139)
  ·
    refine ⟨334214557805286309072696209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222809705203524206048464139 334214557805286309072696209)
    ·
      refine ⟨250660918353964731804522157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 334214557805286309072696209 250660918353964731804522157)
      ·
        refine ⟨93997844382736774426695809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 250660918353964731804522157 93997844382736774426695809)
        ·
          refine ⟨70498383287052580820021857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93997844382736774426695809 70498383287052580820021857)
          ·
            refine ⟨52873787465289435615016393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70498383287052580820021857 52873787465289435615016393)
            ·
              refine ⟨39655340598967076711262295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52873787465289435615016393 39655340598967076711262295)
              ·
                refine ⟨59483010898450615066893443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39655340598967076711262295 59483010898450615066893443)
                ·
                  refine ⟨89224516347675922600340165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59483010898450615066893443 89224516347675922600340165)
                  ·
                    refine ⟨16729596815189235487563781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 89224516347675922600340165 16729596815189235487563781)
                    ·
                      refine ⟨3136799402847981653918209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16729596815189235487563781 3136799402847981653918209)
                      ·
                        rfl

theorem cell23_6108895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 1, 1, 4, 4].length) (baseStart_6108895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6108895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6108895 prefixEnd_6108895 := by exact prefixLift 6108895
  have htrace : WordTrace (prefixWord ++ tailWord_6108895) baseStart_6108895 baseEnd_6108895 := by
    simpa [prefixWord, tailWord_6108895, baseEnd_6108895] using wordTrace_append hprefix tailTrace_6108895
  have hstable : (prefixWord ++ tailWord_6108895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6108895).length < 2 ^ (prefixWord ++ tailWord_6108895).sum := by decide
  have hdescent : baseEnd_6108895 < baseStart_6108895 := by decide
  rcases family_descends (prefixWord ++ tailWord_6108895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6108922 : List Nat := [3, 1, 1, 1, 1, 3, 1, 7, 5]
def baseStart_6108922 : Nat := 118140960795 + 6108922 * 2 ^ 59
def prefixEnd_6108922 : Nat := 4983230072969 + 3 ^ 40 * 6108922 * 2
def baseEnd_6108922 : Nat := 348534807425072560920065

theorem tailTrace_6108922 : CollatzResearch.WordTrace tailWord_6108922 prefixEnd_6108922 348534807425072560920065 := by
  unfold tailWord_6108922
  simp only [CollatzResearch.WordTrace]
  refine ⟨55702672493606597414924255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148540459982950926439798013 55702672493606597414924255)
  ·
    refine ⟨83554008740409896122386383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55702672493606597414924255 83554008740409896122386383)
    ·
      refine ⟨125331013110614844183579575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83554008740409896122386383 125331013110614844183579575)
      ·
        refine ⟨187996519665922266275369363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125331013110614844183579575 187996519665922266275369363)
        ·
          refine ⟨281994779498883399413054045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187996519665922266275369363 281994779498883399413054045)
          ·
            refine ⟨105748042312081274779895267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 281994779498883399413054045 105748042312081274779895267)
            ·
              refine ⟨158622063468121912169842901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105748042312081274779895267 158622063468121912169842901)
              ·
                refine ⟨3717704612534107316480693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 158622063468121912169842901 3717704612534107316480693)
                ·
                  refine ⟨348534807425072560920065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3717704612534107316480693 348534807425072560920065)
                  ·
                    rfl

theorem cell23_6108922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 7, 5].length) (baseStart_6108922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6108922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6108922 prefixEnd_6108922 := by exact prefixLift 6108922
  have htrace : WordTrace (prefixWord ++ tailWord_6108922) baseStart_6108922 baseEnd_6108922 := by
    simpa [prefixWord, tailWord_6108922, baseEnd_6108922] using wordTrace_append hprefix tailTrace_6108922
  have hstable : (prefixWord ++ tailWord_6108922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6108922).length < 2 ^ (prefixWord ++ tailWord_6108922).sum := by decide
  have hdescent : baseEnd_6108922 < baseStart_6108922 := by decide
  rcases family_descends (prefixWord ++ tailWord_6108922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6108939 : List Nat := [1, 1, 1, 1, 5, 1, 6, 2, 5]
def baseStart_6108939 : Nat := 118140960795 + 6108939 * 2 ^ 59
def prefixEnd_6108939 : Nat := 4983230072969 + 3 ^ 40 * 6108939 * 2
def baseEnd_6108939 : Nat := 348535777332975497974223

theorem tailTrace_6108939 : CollatzResearch.WordTrace tailWord_6108939 prefixEnd_6108939 348535777332975497974223 := by
  unfold tailWord_6108939
  simp only [CollatzResearch.WordTrace]
  refine ⟨222811310015364801563065871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148540873343576534375377247 222811310015364801563065871)
  ·
    refine ⟨334216965023047202344598807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222811310015364801563065871 334216965023047202344598807)
    ·
      refine ⟨501325447534570803516898211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 334216965023047202344598807 501325447534570803516898211)
      ·
        refine ⟨751988171301856205275347317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 501325447534570803516898211 751988171301856205275347317)
        ·
          refine ⟨70498891059549019244563811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 751988171301856205275347317 70498891059549019244563811)
          ·
            refine ⟨105748336589323528866845717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70498891059549019244563811 105748336589323528866845717)
            ·
              refine ⟨4956953277624540415633393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 105748336589323528866845717 4956953277624540415633393)
              ·
                refine ⟨3717714958218405311725045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4956953277624540415633393 3717714958218405311725045)
                ·
                  refine ⟨348535777332975497974223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3717714958218405311725045 348535777332975497974223)
                  ·
                    rfl

theorem cell23_6108939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 6, 2, 5].length) (baseStart_6108939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6108939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6108939 prefixEnd_6108939 := by exact prefixLift 6108939
  have htrace : WordTrace (prefixWord ++ tailWord_6108939) baseStart_6108939 baseEnd_6108939 := by
    simpa [prefixWord, tailWord_6108939, baseEnd_6108939] using wordTrace_append hprefix tailTrace_6108939
  have hstable : (prefixWord ++ tailWord_6108939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6108939).length < 2 ^ (prefixWord ++ tailWord_6108939).sum := by decide
  have hdescent : baseEnd_6108939 < baseStart_6108939 := by decide
  rcases family_descends (prefixWord ++ tailWord_6108939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6108955 : List Nat := [1, 1, 1, 1, 1, 1, 4, 3, 3, 3, 4]
def baseStart_6108955 : Nat := 118140960795 + 6108955 * 2 ^ 59
def prefixEnd_6108955 : Nat := 4983230072969 + 3 ^ 40 * 6108955 * 2
def baseEnd_6108955 : Nat := 3136830211687251419167933

theorem tailTrace_6108955 : CollatzResearch.WordTrace tailWord_6108955 prefixEnd_6108955 3136830211687251419167933 := by
  unfold tailWord_6108955
  simp only [CollatzResearch.WordTrace]
  refine ⟨222811893583306836295648319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148541262388871224197098879 222811893583306836295648319)
  ·
    refine ⟨334217840374960254443472479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222811893583306836295648319 334217840374960254443472479)
    ·
      refine ⟨501326760562440381665208719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 334217840374960254443472479 501326760562440381665208719)
      ·
        refine ⟨751990140843660572497813079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 501326760562440381665208719 751990140843660572497813079)
        ·
          refine ⟨1127985211265490858746719619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 751990140843660572497813079 1127985211265490858746719619)
          ·
            refine ⟨1691977816898236288120079429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1127985211265490858746719619 1691977816898236288120079429)
            ·
              refine ⟨317245840668419304022514893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1691977816898236288120079429 317245840668419304022514893)
              ·
                refine ⟨118967190250657239008443085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 317245840668419304022514893 118967190250657239008443085)
                ·
                  refine ⟨44612696343996464628166157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 118967190250657239008443085 44612696343996464628166157)
                  ·
                    refine ⟨16729761128998674235562309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44612696343996464628166157 16729761128998674235562309)
                    ·
                      refine ⟨3136830211687251419167933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16729761128998674235562309 3136830211687251419167933)
                      ·
                        rfl

theorem cell23_6108955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 3, 3, 4].length) (baseStart_6108955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6108955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6108955 prefixEnd_6108955 := by exact prefixLift 6108955
  have htrace : WordTrace (prefixWord ++ tailWord_6108955) baseStart_6108955 baseEnd_6108955 := by
    simpa [prefixWord, tailWord_6108955, baseEnd_6108955] using wordTrace_append hprefix tailTrace_6108955
  have hstable : (prefixWord ++ tailWord_6108955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6108955).length < 2 ^ (prefixWord ++ tailWord_6108955).sum := by decide
  have hdescent : baseEnd_6108955 < baseStart_6108955 := by decide
  rcases family_descends (prefixWord ++ tailWord_6108955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6108972 : List Nat := [2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 4]
def baseStart_6108972 : Nat := 118140960795 + 6108972 * 2 ^ 59
def prefixEnd_6108972 : Nat := 4983230072969 + 3 ^ 40 * 6108972 * 2
def baseEnd_6108972 : Nat := 3136838940858377852655355

theorem tailTrace_6108972 : CollatzResearch.WordTrace tailWord_6108972 prefixEnd_6108972 3136838940858377852655355 := by
  unfold tailWord_6108972
  simp only [CollatzResearch.WordTrace]
  refine ⟨111406256812122624099508585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148541675749496832132678113 111406256812122624099508585)
  ·
    refine ⟨83554692609091968074631439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111406256812122624099508585 83554692609091968074631439)
    ·
      refine ⟨125332038913637952111947159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83554692609091968074631439 125332038913637952111947159)
      ·
        refine ⟨187998058370456928167920739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125332038913637952111947159 187998058370456928167920739)
        ·
          refine ⟨281997087555685392251881109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 187998058370456928167920739 281997087555685392251881109)
          ·
            refine ⟨13218613479172752761806927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 281997087555685392251881109 13218613479172752761806927)
            ·
              refine ⟨19827920218759129142710391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13218613479172752761806927 19827920218759129142710391)
              ·
                refine ⟨29741880328138693714065587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19827920218759129142710391 29741880328138693714065587)
                ·
                  refine ⟨44612820492208040571098381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29741880328138693714065587 44612820492208040571098381)
                  ·
                    refine ⟨16729807684578015214161893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44612820492208040571098381 16729807684578015214161893)
                    ·
                      refine ⟨3136838940858377852655355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16729807684578015214161893 3136838940858377852655355)
                      ·
                        rfl

theorem cell23_6108972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 4].length) (baseStart_6108972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6108972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6108972 prefixEnd_6108972 := by exact prefixLift 6108972
  have htrace : WordTrace (prefixWord ++ tailWord_6108972) baseStart_6108972 baseEnd_6108972 := by
    simpa [prefixWord, tailWord_6108972, baseEnd_6108972] using wordTrace_append hprefix tailTrace_6108972
  have hstable : (prefixWord ++ tailWord_6108972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6108972).length < 2 ^ (prefixWord ++ tailWord_6108972).sum := by decide
  have hdescent : baseEnd_6108972 < baseStart_6108972 := by decide
  rcases family_descends (prefixWord ++ tailWord_6108972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6109042 : List Nat := [3, 2, 1, 2, 1, 1, 1, 2, 5, 5]
def baseStart_6109042 : Nat := 118140960795 + 6109042 * 2 ^ 59
def prefixEnd_6109042 : Nat := 4983230072969 + 3 ^ 40 * 6109042 * 2
def baseEnd_6109042 : Nat := 1045624961501397526260011

theorem tailTrace_6109042 : CollatzResearch.WordTrace tailWord_6109042 prefixEnd_6109042 1045624961501397526260011 := by
  unfold tailWord_6109042
  simp only [CollatzResearch.WordTrace]
  refine ⟨55703766683497912538516345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148543377822661100102710253 55703766683497912538516345)
  ·
    refine ⟨41777825012623434403887259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55703766683497912538516345 41777825012623434403887259)
    ·
      refine ⟨62666737518935151605830889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41777825012623434403887259 62666737518935151605830889)
      ·
        refine ⟨47000053139201363704373167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62666737518935151605830889 47000053139201363704373167)
        ·
          refine ⟨70500079708802045556559751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47000053139201363704373167 70500079708802045556559751)
          ·
            refine ⟨105750119563203068334839627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70500079708802045556559751 105750119563203068334839627)
            ·
              refine ⟨158625179344804602502259441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 105750119563203068334839627 158625179344804602502259441)
              ·
                refine ⟨118968884508603451876694581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 158625179344804602502259441 118968884508603451876694581)
                ·
                  refine ⟨11153332922681573613440117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 118968884508603451876694581 11153332922681573613440117)
                  ·
                    refine ⟨1045624961501397526260011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11153332922681573613440117 1045624961501397526260011)
                    ·
                      rfl

theorem cell23_6109042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 5, 5].length) (baseStart_6109042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6109042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6109042 prefixEnd_6109042 := by exact prefixLift 6109042
  have htrace : WordTrace (prefixWord ++ tailWord_6109042) baseStart_6109042 baseEnd_6109042 := by
    simpa [prefixWord, tailWord_6109042, baseEnd_6109042] using wordTrace_append hprefix tailTrace_6109042
  have hstable : (prefixWord ++ tailWord_6109042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6109042).length < 2 ^ (prefixWord ++ tailWord_6109042).sum := by decide
  have hdescent : baseEnd_6109042 < baseStart_6109042 := by decide
  rcases family_descends (prefixWord ++ tailWord_6109042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6109063 : List Nat := [1, 1, 4, 2, 5, 1, 2, 1, 6]
def baseStart_6109063 : Nat := 118140960795 + 6109063 * 2 ^ 59
def prefixEnd_6109063 : Nat := 4983230072969 + 3 ^ 40 * 6109063 * 2
def baseEnd_6109063 : Nat := 348542851955326332957493

theorem tailTrace_6109063 : CollatzResearch.WordTrace tailWord_6109063 prefixEnd_6109063 348542851955326332957493 := by
  unfold tailWord_6109063
  simp only [CollatzResearch.WordTrace]
  refine ⟨222815832666915570740579843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148543888444610380493719895 222815832666915570740579843)
  ·
    refine ⟨334223749000373356110869765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222815832666915570740579843 334223749000373356110869765)
    ·
      refine ⟨62666952937570004270788081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 334223749000373356110869765 62666952937570004270788081)
      ·
        refine ⟨47000214703177503203091061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62666952937570004270788081 47000214703177503203091061)
        ·
          refine ⟨4406270128422890925289787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47000214703177503203091061 4406270128422890925289787)
          ·
            refine ⟨6609405192634336387934681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4406270128422890925289787 6609405192634336387934681)
            ·
              refine ⟨4957053894475752290951011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6609405192634336387934681 4957053894475752290951011)
              ·
                refine ⟨7435580841713628436426517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4957053894475752290951011 7435580841713628436426517)
                ·
                  refine ⟨348542851955326332957493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7435580841713628436426517 348542851955326332957493)
                  ·
                    rfl

theorem cell23_6109063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 2, 1, 6].length) (baseStart_6109063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6109063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6109063 prefixEnd_6109063 := by exact prefixLift 6109063
  have htrace : WordTrace (prefixWord ++ tailWord_6109063) baseStart_6109063 baseEnd_6109063 := by
    simpa [prefixWord, tailWord_6109063, baseEnd_6109063] using wordTrace_append hprefix tailTrace_6109063
  have hstable : (prefixWord ++ tailWord_6109063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6109063).length < 2 ^ (prefixWord ++ tailWord_6109063).sum := by decide
  have hdescent : baseEnd_6109063 < baseStart_6109063 := by decide
  rcases family_descends (prefixWord ++ tailWord_6109063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6109076 : List Nat := [2, 4, 2, 1, 1, 2, 3, 2, 1, 5]
def baseStart_6109076 : Nat := 118140960795 + 6109076 * 2 ^ 59
def prefixEnd_6109076 : Nat := 4983230072969 + 3 ^ 40 * 6109076 * 2
def baseEnd_6109076 : Nat := 1045630780948815148584959

theorem tailTrace_6109076 : CollatzResearch.WordTrace tailWord_6109076 prefixEnd_6109076 1045630780948815148584959 := by
  unfold tailWord_6109076
  simp only [CollatzResearch.WordTrace]
  refine ⟨111408153407934236980401541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 148544204543912315973868721 111408153407934236980401541)
  ·
    refine ⟨20889028763987669433825289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111408153407934236980401541 20889028763987669433825289)
    ·
      refine ⟨15666771572990752075368967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20889028763987669433825289 15666771572990752075368967)
      ·
        refine ⟨23500157359486128113053451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15666771572990752075368967 23500157359486128113053451)
        ·
          refine ⟨35250236039229192169580177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23500157359486128113053451 35250236039229192169580177)
          ·
            refine ⟨26437677029421894127185133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35250236039229192169580177 26437677029421894127185133)
            ·
              refine ⟨9914128886033210297694425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26437677029421894127185133 9914128886033210297694425)
              ·
                refine ⟨7435596664524907723270819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9914128886033210297694425 7435596664524907723270819)
                ·
                  refine ⟨11153394996787361584906229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7435596664524907723270819 11153394996787361584906229)
                  ·
                    refine ⟨1045630780948815148584959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11153394996787361584906229 1045630780948815148584959)
                    ·
                      rfl

theorem cell23_6109076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 3, 2, 1, 5].length) (baseStart_6109076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6109076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6109076 prefixEnd_6109076 := by exact prefixLift 6109076
  have htrace : WordTrace (prefixWord ++ tailWord_6109076) baseStart_6109076 baseEnd_6109076 := by
    simpa [prefixWord, tailWord_6109076, baseEnd_6109076] using wordTrace_append hprefix tailTrace_6109076
  have hstable : (prefixWord ++ tailWord_6109076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6109076).length < 2 ^ (prefixWord ++ tailWord_6109076).sum := by decide
  have hdescent : baseEnd_6109076 < baseStart_6109076 := by decide
  rcases family_descends (prefixWord ++ tailWord_6109076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6109079 : List Nat := [1, 1, 3, 3, 1, 4, 1, 1, 3, 1, 4]
def baseStart_6109079 : Nat := 118140960795 + 6109079 * 2 ^ 59
def prefixEnd_6109079 : Nat := 4983230072969 + 3 ^ 40 * 6109079 * 2
def baseEnd_6109079 : Nat := 3136893883288408934017363

theorem tailTrace_6109079 : CollatzResearch.WordTrace tailWord_6109079 prefixEnd_6109079 3136893883288408934017363 := by
  unfold tailWord_6109079
  simp only [CollatzResearch.WordTrace]
  refine ⟨222816416234857605473162291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148544277489905070315441527 222816416234857605473162291)
  ·
    refine ⟨334224624352286408209743437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222816416234857605473162291 334224624352286408209743437)
    ·
      refine ⟨125334234132107403078653789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 334224624352286408209743437 125334234132107403078653789)
      ·
        refine ⟨47000337799540276154495171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125334234132107403078653789 47000337799540276154495171)
        ·
          refine ⟨70500506699310414231742757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47000337799540276154495171 70500506699310414231742757)
          ·
            refine ⟨13218845006120702668451767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70500506699310414231742757 13218845006120702668451767)
            ·
              refine ⟨19828267509181054002677651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13218845006120702668451767 19828267509181054002677651)
              ·
                refine ⟨29742401263771581004016477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19828267509181054002677651 29742401263771581004016477)
                ·
                  refine ⟨11153400473914342876506179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29742401263771581004016477 11153400473914342876506179)
                  ·
                    refine ⟨16730100710871514314759269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11153400473914342876506179 16730100710871514314759269)
                    ·
                      refine ⟨3136893883288408934017363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16730100710871514314759269 3136893883288408934017363)
                      ·
                        rfl

theorem cell23_6109079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 1, 3, 1, 4].length) (baseStart_6109079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6109079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6109079 prefixEnd_6109079 := by exact prefixLift 6109079
  have htrace : WordTrace (prefixWord ++ tailWord_6109079) baseStart_6109079 baseEnd_6109079 := by
    simpa [prefixWord, tailWord_6109079, baseEnd_6109079] using wordTrace_append hprefix tailTrace_6109079
  have hstable : (prefixWord ++ tailWord_6109079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6109079).length < 2 ^ (prefixWord ++ tailWord_6109079).sum := by decide
  have hdescent : baseEnd_6109079 < baseStart_6109079 := by decide
  rcases family_descends (prefixWord ++ tailWord_6109079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6109226 : List Nat := [3, 1, 4, 1, 2, 1, 3, 1, 7]
def baseStart_6109226 : Nat := 118140960795 + 6109226 * 2 ^ 59
def prefixEnd_6109226 : Nat := 4983230072969 + 3 ^ 40 * 6109226 * 2
def baseEnd_6109226 : Nat := 348552151660513317653243

theorem tailTrace_6109226 : CollatzResearch.WordTrace tailWord_6109226 prefixEnd_6109226 348552151660513317653243 := by
  unfold tailWord_6109226
  simp only [CollatzResearch.WordTrace]
  refine ⟨55705444441331262394690883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 148547851843550033052509021 55705444441331262394690883)
  ·
    refine ⟨83558166661996893592036325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55705444441331262394690883 83558166661996893592036325)
    ·
      refine ⟨15667156249124417548506811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83558166661996893592036325 15667156249124417548506811)
      ·
        refine ⟨23500734373686626322760217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15667156249124417548506811 23500734373686626322760217)
        ·
          refine ⟨17625550780264969742070163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23500734373686626322760217 17625550780264969742070163)
          ·
            refine ⟨26438326170397454613105245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17625550780264969742070163 26438326170397454613105245)
            ·
              refine ⟨9914372313899045479914467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26438326170397454613105245 9914372313899045479914467)
              ·
                refine ⟨14871558470848568219871701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9914372313899045479914467 14871558470848568219871701)
                ·
                  refine ⟨348552151660513317653243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14871558470848568219871701 348552151660513317653243)
                  ·
                    rfl

theorem cell23_6109226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 3, 1, 7].length) (baseStart_6109226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6109226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6109226 prefixEnd_6109226 := by exact prefixLift 6109226
  have htrace : WordTrace (prefixWord ++ tailWord_6109226) baseStart_6109226 baseEnd_6109226 := by
    simpa [prefixWord, tailWord_6109226, baseEnd_6109226] using wordTrace_append hprefix tailTrace_6109226
  have hstable : (prefixWord ++ tailWord_6109226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6109226).length < 2 ^ (prefixWord ++ tailWord_6109226).sum := by decide
  have hdescent : baseEnd_6109226 < baseStart_6109226 := by decide
  rcases family_descends (prefixWord ++ tailWord_6109226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6109259 : List Nat := [1, 1, 1, 1, 3, 1, 2, 2, 6, 1, 4]
def baseStart_6109259 : Nat := 118140960795 + 6109259 * 2 ^ 59
def prefixEnd_6109259 : Nat := 4983230072969 + 3 ^ 40 * 6109259 * 2
def baseEnd_6109259 : Nat := 3136986309806218229766535

theorem tailTrace_6109259 : CollatzResearch.WordTrace tailWord_6109259 prefixEnd_6109259 3136986309806218229766535 := by
  unfold tailWord_6109259
  simp only [CollatzResearch.WordTrace]
  refine ⟨222822981374205496214714831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148548654249470330809809887 222822981374205496214714831)
  ·
    refine ⟨334234472061308244322072247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 222822981374205496214714831 334234472061308244322072247)
    ·
      refine ⟨501351708091962366483108371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 334234472061308244322072247 501351708091962366483108371)
      ·
        refine ⟨752027562137943549724662557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 501351708091962366483108371 752027562137943549724662557)
        ·
          refine ⟨282010335801728831146748459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 752027562137943549724662557 282010335801728831146748459)
          ·
            refine ⟨423015503702593246720122689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 282010335801728831146748459 423015503702593246720122689)
            ·
              refine ⟨317261627776944935040092017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 423015503702593246720122689 317261627776944935040092017)
              ·
                refine ⟨237946220832708701280069013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 317261627776944935040092017 237946220832708701280069013)
                ·
                  refine ⟨11153729101533220372503235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 237946220832708701280069013 11153729101533220372503235)
                  ·
                    refine ⟨16730593652299830558754853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11153729101533220372503235 16730593652299830558754853)
                    ·
                      refine ⟨3136986309806218229766535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16730593652299830558754853 3136986309806218229766535)
                      ·
                        rfl

theorem cell23_6109259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 6, 1, 4].length) (baseStart_6109259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6109259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6109259 prefixEnd_6109259 := by exact prefixLift 6109259
  have htrace : WordTrace (prefixWord ++ tailWord_6109259) baseStart_6109259 baseEnd_6109259 := by
    simpa [prefixWord, tailWord_6109259, baseEnd_6109259] using wordTrace_append hprefix tailTrace_6109259
  have hstable : (prefixWord ++ tailWord_6109259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6109259).length < 2 ^ (prefixWord ++ tailWord_6109259).sum := by decide
  have hdescent : baseEnd_6109259 < baseStart_6109259 := by decide
  rcases family_descends (prefixWord ++ tailWord_6109259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6109277 : List Nat := [1, 4, 4, 1, 1, 3, 2, 2, 5]
def baseStart_6109277 : Nat := 118140960795 + 6109277 * 2 ^ 59
def prefixEnd_6109277 : Nat := 4983230072969 + 3 ^ 40 * 6109277 * 2
def baseEnd_6109277 : Nat := 348555061384222128815717

theorem tailTrace_6109277 : CollatzResearch.WordTrace tailWord_6109277 prefixEnd_6109277 348555061384222128815717 := by
  unfold tailWord_6109277
  simp only [CollatzResearch.WordTrace]
  refine ⟨222823637888140285288870085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148549091925426856859246723 222823637888140285288870085)
  ·
    refine ⟨41779432104026303491663141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 222823637888140285288870085 41779432104026303491663141)
    ·
      refine ⟨7833643519504931904686839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41779432104026303491663141 7833643519504931904686839)
      ·
        refine ⟨11750465279257397857030259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7833643519504931904686839 11750465279257397857030259)
        ·
          refine ⟨17625697918886096785545389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11750465279257397857030259 17625697918886096785545389)
          ·
            refine ⟨6609636719582286294579521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17625697918886096785545389 6609636719582286294579521)
            ·
              refine ⟨4957227539686714720934641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6609636719582286294579521 4957227539686714720934641)
              ·
                refine ⟨3717920654765036040700981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4957227539686714720934641 3717920654765036040700981)
                ·
                  refine ⟨348555061384222128815717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3717920654765036040700981 348555061384222128815717)
                  ·
                    rfl

theorem cell23_6109277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 2, 2, 5].length) (baseStart_6109277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6109277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6109277 prefixEnd_6109277 := by exact prefixLift 6109277
  have htrace : WordTrace (prefixWord ++ tailWord_6109277) baseStart_6109277 baseEnd_6109277 := by
    simpa [prefixWord, tailWord_6109277, baseEnd_6109277] using wordTrace_append hprefix tailTrace_6109277
  have hstable : (prefixWord ++ tailWord_6109277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6109277).length < 2 ^ (prefixWord ++ tailWord_6109277).sum := by decide
  have hdescent : baseEnd_6109277 < baseStart_6109277 := by decide
  rcases family_descends (prefixWord ++ tailWord_6109277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6109293 : List Nat := [1, 5, 1, 1, 2, 1, 3, 1, 2, 4, 2]
def baseStart_6109293 : Nat := 118140960795 + 6109293 * 2 ^ 59
def prefixEnd_6109293 : Nat := 4983230072969 + 3 ^ 40 * 6109293 * 2
def baseEnd_6109293 : Nat := 3137003768148471096741379

theorem tailTrace_6109293 : CollatzResearch.WordTrace tailWord_6109293 prefixEnd_6109293 3137003768148471096741379 := by
  unfold tailWord_6109293
  simp only [CollatzResearch.WordTrace]
  refine ⟨222824221456082320021452533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 148549480970721546680968355 222824221456082320021452533)
  ·
    refine ⟨20889770761507717502011175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 222824221456082320021452533 20889770761507717502011175)
    ·
      refine ⟨31334656142261576253016763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20889770761507717502011175 31334656142261576253016763)
      ·
        refine ⟨47001984213392364379525145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31334656142261576253016763 47001984213392364379525145)
        ·
          refine ⟨35251488160044273284643859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47001984213392364379525145 35251488160044273284643859)
          ·
            refine ⟨52877232240066409926965789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35251488160044273284643859 52877232240066409926965789)
            ·
              refine ⟨19828962090024903722612171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52877232240066409926965789 19828962090024903722612171)
              ·
                refine ⟨29743443135037355583918257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19828962090024903722612171 29743443135037355583918257)
                ·
                  refine ⟨22307582351278016687938693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29743443135037355583918257 22307582351278016687938693)
                  ·
                    refine ⟨4182671690864628128988505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22307582351278016687938693 4182671690864628128988505)
                    ·
                      refine ⟨3137003768148471096741379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4182671690864628128988505 3137003768148471096741379)
                      ·
                        rfl

theorem cell23_6109293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 1, 2, 4, 2].length) (baseStart_6109293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6109293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6109293 prefixEnd_6109293 := by exact prefixLift 6109293
  have htrace : WordTrace (prefixWord ++ tailWord_6109293) baseStart_6109293 baseEnd_6109293 := by
    simpa [prefixWord, tailWord_6109293, baseEnd_6109293] using wordTrace_append hprefix tailTrace_6109293
  have hstable : (prefixWord ++ tailWord_6109293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6109293).length < 2 ^ (prefixWord ++ tailWord_6109293).sum := by decide
  have hdescent : baseEnd_6109293 < baseStart_6109293 := by decide
  rcases family_descends (prefixWord ++ tailWord_6109293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
