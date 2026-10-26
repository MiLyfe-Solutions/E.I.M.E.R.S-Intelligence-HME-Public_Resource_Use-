import V185TrunkScan21Chunk096

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_1177746 : List Nat := [3, 2, 3, 1, 1, 1, 4, 2, 4]
def baseStart_1177746 : Nat := 118140960795 + 1177746 * 2 ^ 59
def prefixEnd_1177746 : Nat := 4983230072969 + 3 ^ 40 * 1177746 * 2
def baseEnd_1177746 : Nat := 268777683071224132026067

theorem tailTrace_1177746 : CollatzResearch.WordTrace tailWord_1177746 prefixEnd_1177746 268777683071224132026067 := by
  unfold tailWord_1177746
  simp only [CollatzResearch.WordTrace]
  refine ⟨10738981397808714962024273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28637283727489906565398061 10738981397808714962024273)
  ·
    refine ⟨8054236048356536221518205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10738981397808714962024273 8054236048356536221518205)
    ·
      refine ⟨3020338518133701083069327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8054236048356536221518205 3020338518133701083069327)
      ·
        refine ⟨4530507777200551624603991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3020338518133701083069327 4530507777200551624603991)
        ·
          refine ⟨6795761665800827436905987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4530507777200551624603991 6795761665800827436905987)
          ·
            refine ⟨10193642498701241155358981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6795761665800827436905987 10193642498701241155358981)
            ·
              refine ⟨1911307968506482716629809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10193642498701241155358981 1911307968506482716629809)
              ·
                refine ⟨1433480976379862037472357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1911307968506482716629809 1433480976379862037472357)
                ·
                  refine ⟨268777683071224132026067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1433480976379862037472357 268777683071224132026067)
                  ·
                    rfl

theorem cell21_1177746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 4, 2, 4].length) (baseStart_1177746 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1177746 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1177746 prefixEnd_1177746 := by exact prefixLift 1177746
  have htrace : WordTrace (prefixWord ++ tailWord_1177746) baseStart_1177746 baseEnd_1177746 := by
    simpa [prefixWord, tailWord_1177746, baseEnd_1177746] using wordTrace_append hprefix tailTrace_1177746
  have hstable : (prefixWord ++ tailWord_1177746).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1177746).length < 2 ^ (prefixWord ++ tailWord_1177746).sum := by decide
  have hdescent : baseEnd_1177746 < baseStart_1177746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1177746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1177760 : List Nat := [2, 1, 1, 4, 2, 4, 1, 6]
def baseStart_1177760 : Nat := 118140960795 + 1177760 * 2 ^ 59
def prefixEnd_1177760 : Nat := 4983230072969 + 3 ^ 40 * 1177760 * 2
def baseEnd_1177760 : Nat := 89593626020654406264235

theorem tailTrace_1177760 : CollatzResearch.WordTrace tailWord_1177760 prefixEnd_1177760 89593626020654406264235 := by
  unfold tailWord_1177760
  simp only [CollatzResearch.WordTrace]
  refine ⟨21478218106592070119553367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28637624142122760159404489 21478218106592070119553367)
  ·
    refine ⟨32217327159888105179330051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21478218106592070119553367 32217327159888105179330051)
    ·
      refine ⟨48325990739832157768995077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32217327159888105179330051 48325990739832157768995077)
      ·
        refine ⟨9061123263718529581686577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48325990739832157768995077 9061123263718529581686577)
        ·
          refine ⟨6795842447788897186264933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9061123263718529581686577 6795842447788897186264933)
          ·
            refine ⟨1274220458960418222424675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6795842447788897186264933 1274220458960418222424675)
            ·
              refine ⟨1911330688440627333637013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1274220458960418222424675 1911330688440627333637013)
              ·
                refine ⟨89593626020654406264235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1911330688440627333637013 89593626020654406264235)
                ·
                  rfl

theorem cell21_1177760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 1, 6].length) (baseStart_1177760 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1177760 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1177760 prefixEnd_1177760 := by exact prefixLift 1177760
  have htrace : WordTrace (prefixWord ++ tailWord_1177760) baseStart_1177760 baseEnd_1177760 := by
    simpa [prefixWord, tailWord_1177760, baseEnd_1177760] using wordTrace_append hprefix tailTrace_1177760
  have hstable : (prefixWord ++ tailWord_1177760).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1177760).length < 2 ^ (prefixWord ++ tailWord_1177760).sum := by decide
  have hdescent : baseEnd_1177760 < baseStart_1177760 := by decide
  rcases family_descends (prefixWord ++ tailWord_1177760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1177777 : List Nat := [1, 2, 2, 5, 2, 1, 3, 5]
def baseStart_1177777 : Nat := 118140960795 + 1177777 * 2 ^ 59
def prefixEnd_1177777 : Nat := 4983230072969 + 3 ^ 40 * 1177777 * 2
def baseEnd_1177777 : Nat := 89594919231191655669779

theorem tailTrace_1177777 : CollatzResearch.WordTrace tailWord_1177777 prefixEnd_1177777 89594919231191655669779 := by
  unfold tailWord_1177777
  simp only [CollatzResearch.WordTrace]
  refine ⟨42957056254122552142475585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28638037502748368094983723 42957056254122552142475585)
  ·
    refine ⟨32217792190591914106856689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42957056254122552142475585 32217792190591914106856689)
    ·
      refine ⟨24163344142943935580142517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32217792190591914106856689 24163344142943935580142517)
      ·
        refine ⟨2265313513400993960638361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24163344142943935580142517 2265313513400993960638361)
        ·
          refine ⟨1698985135050745470478771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2265313513400993960638361 1698985135050745470478771)
          ·
            refine ⟨2548477702576118205718157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1698985135050745470478771 2548477702576118205718157)
            ·
              refine ⟨955679138466044327144309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2548477702576118205718157 955679138466044327144309)
              ·
                refine ⟨89594919231191655669779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 955679138466044327144309 89594919231191655669779)
                ·
                  rfl

theorem cell21_1177777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 3, 5].length) (baseStart_1177777 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1177777 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1177777 prefixEnd_1177777 := by exact prefixLift 1177777
  have htrace : WordTrace (prefixWord ++ tailWord_1177777) baseStart_1177777 baseEnd_1177777 := by
    simpa [prefixWord, tailWord_1177777, baseEnd_1177777] using wordTrace_append hprefix tailTrace_1177777
  have hstable : (prefixWord ++ tailWord_1177777).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1177777).length < 2 ^ (prefixWord ++ tailWord_1177777).sum := by decide
  have hdescent : baseEnd_1177777 < baseStart_1177777 := by decide
  rcases family_descends (prefixWord ++ tailWord_1177777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1177960 : List Nat := [2, 1, 4, 2, 2, 2, 2, 3, 3]
def baseStart_1177960 : Nat := 118140960795 + 1177960 * 2 ^ 59
def prefixEnd_1177960 : Nat := 4983230072969 + 3 ^ 40 * 1177960 * 2
def baseEnd_1177960 : Nat := 268826520786807315458963

theorem tailTrace_1177960 : CollatzResearch.WordTrace tailWord_1177960 prefixEnd_1177960 268826520786807315458963 := by
  unfold tailWord_1177960
  simp only [CollatzResearch.WordTrace]
  refine ⟨21481865406229787198193667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28642487208306382930924889 21481865406229787198193667)
  ·
    refine ⟨32222798109344680797290501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21481865406229787198193667 32222798109344680797290501)
    ·
      refine ⟨6041774645502127649491969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32222798109344680797290501 6041774645502127649491969)
      ·
        refine ⟨4531330984126595737118977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6041774645502127649491969 4531330984126595737118977)
        ·
          refine ⟨3398498238094946802839233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4531330984126595737118977 3398498238094946802839233)
          ·
            refine ⟨2548873678571210102129425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3398498238094946802839233 2548873678571210102129425)
            ·
              refine ⟨1911655258928407576597069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2548873678571210102129425 1911655258928407576597069)
              ·
                refine ⟨716870722098152841223901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1911655258928407576597069 716870722098152841223901)
                ·
                  refine ⟨268826520786807315458963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 716870722098152841223901 268826520786807315458963)
                  ·
                    rfl

theorem cell21_1177960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 2, 3, 3].length) (baseStart_1177960 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1177960 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1177960 prefixEnd_1177960 := by exact prefixLift 1177960
  have htrace : WordTrace (prefixWord ++ tailWord_1177960) baseStart_1177960 baseEnd_1177960 := by
    simpa [prefixWord, tailWord_1177960, baseEnd_1177960] using wordTrace_append hprefix tailTrace_1177960
  have hstable : (prefixWord ++ tailWord_1177960).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1177960).length < 2 ^ (prefixWord ++ tailWord_1177960).sum := by decide
  have hdescent : baseEnd_1177960 < baseStart_1177960 := by decide
  rcases family_descends (prefixWord ++ tailWord_1177960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1178016 : List Nat := [2, 1, 1, 4, 1, 3, 1, 2, 6]
def baseStart_1178016 : Nat := 118140960795 + 1178016 * 2 ^ 59
def prefixEnd_1178016 : Nat := 4983230072969 + 3 ^ 40 * 1178016 * 2
def baseEnd_1178016 : Nat := 268839300749763662525515

theorem tailTrace_1178016 : CollatzResearch.WordTrace tailWord_1178016 prefixEnd_1178016 268839300749763662525515 := by
  unfold tailWord_1178016
  simp only [CollatzResearch.WordTrace]
  refine ⟨21482886650128347980212951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28643848866837797306950601 21482886650128347980212951)
  ·
    refine ⟨32224329975192521970319427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21482886650128347980212951 32224329975192521970319427)
    ·
      refine ⟨48336494962788782955479141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32224329975192521970319427 48336494962788782955479141)
      ·
        refine ⟨9063092805522896804152339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48336494962788782955479141 9063092805522896804152339)
        ·
          refine ⟨13594639208284345206228509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9063092805522896804152339 13594639208284345206228509)
          ·
            refine ⟨5097989703106629452335691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13594639208284345206228509 5097989703106629452335691)
            ·
              refine ⟨7646984554659944178503537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5097989703106629452335691 7646984554659944178503537)
              ·
                refine ⟨5735238415994958133877653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7646984554659944178503537 5735238415994958133877653)
                ·
                  refine ⟨268839300749763662525515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5735238415994958133877653 268839300749763662525515)
                  ·
                    rfl

theorem cell21_1178016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 2, 6].length) (baseStart_1178016 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1178016 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1178016 prefixEnd_1178016 := by exact prefixLift 1178016
  have htrace : WordTrace (prefixWord ++ tailWord_1178016) baseStart_1178016 baseEnd_1178016 := by
    simpa [prefixWord, tailWord_1178016, baseEnd_1178016] using wordTrace_append hprefix tailTrace_1178016
  have hstable : (prefixWord ++ tailWord_1178016).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1178016).length < 2 ^ (prefixWord ++ tailWord_1178016).sum := by decide
  have hdescent : baseEnd_1178016 < baseStart_1178016 := by decide
  rcases family_descends (prefixWord ++ tailWord_1178016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1178019 : List Nat := [1, 1, 1, 4, 1, 4, 3, 3, 3]
def baseStart_1178019 : Nat := 118140960795 + 1178019 * 2 ^ 59
def prefixEnd_1178019 : Nat := 4983230072969 + 3 ^ 40 * 1178019 * 2
def baseEnd_1178019 : Nat := 268839985390636323975509

theorem tailTrace_1178019 : CollatzResearch.WordTrace tailWord_1178019 prefixEnd_1178019 268839985390636323975509 := by
  unfold tailWord_1178019
  simp only [CollatzResearch.WordTrace]
  refine ⟨42965882719245827472785111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28643921812830551648523407 42965882719245827472785111)
  ·
    refine ⟨64448824078868741209177667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42965882719245827472785111 64448824078868741209177667)
    ·
      refine ⟨96673236118303111813766501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64448824078868741209177667 96673236118303111813766501)
      ·
        refine ⟨18126231772181833465081219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 96673236118303111813766501 18126231772181833465081219)
        ·
          refine ⟨27189347658272750197621829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18126231772181833465081219 27189347658272750197621829)
          ·
            refine ⟨5098002685926140662054093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27189347658272750197621829 5098002685926140662054093)
            ·
              refine ⟨1911751007222302748270285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5098002685926140662054093 1911751007222302748270285)
              ·
                refine ⟨716906627708363530601357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1911751007222302748270285 716906627708363530601357)
                ·
                  refine ⟨268839985390636323975509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 716906627708363530601357 268839985390636323975509)
                  ·
                    rfl

theorem cell21_1178019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 3, 3, 3].length) (baseStart_1178019 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1178019 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1178019 prefixEnd_1178019 := by exact prefixLift 1178019
  have htrace : WordTrace (prefixWord ++ tailWord_1178019) baseStart_1178019 baseEnd_1178019 := by
    simpa [prefixWord, tailWord_1178019, baseEnd_1178019] using wordTrace_append hprefix tailTrace_1178019
  have hstable : (prefixWord ++ tailWord_1178019).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1178019).length < 2 ^ (prefixWord ++ tailWord_1178019).sum := by decide
  have hdescent : baseEnd_1178019 < baseStart_1178019 := by decide
  rcases family_descends (prefixWord ++ tailWord_1178019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1178106 : List Nat := [3, 1, 1, 1, 1, 2, 2, 10]
def baseStart_1178106 : Nat := 118140960795 + 1178106 * 2 ^ 59
def prefixEnd_1178106 : Nat := 4983230072969 + 3 ^ 40 * 1178106 * 2
def baseEnd_1178106 : Nat := 89619946658647835341777

theorem tailTrace_1178106 : CollatzResearch.WordTrace tailWord_1178106 prefixEnd_1178106 89619946658647835341777 := by
  unfold tailWord_1178106
  simp only [CollatzResearch.WordTrace]
  refine ⟨10742263967482660332800543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28646037246620427554134781 10742263967482660332800543)
  ·
    refine ⟨16113395951223990499200815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10742263967482660332800543 16113395951223990499200815)
    ·
      refine ⟨24170093926835985748801223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16113395951223990499200815 24170093926835985748801223)
      ·
        refine ⟨36255140890253978623201835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24170093926835985748801223 36255140890253978623201835)
        ·
          refine ⟨54382711335380967934802753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36255140890253978623201835 54382711335380967934802753)
          ·
            refine ⟨40787033501535725951102065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54382711335380967934802753 40787033501535725951102065)
            ·
              refine ⟨30590275126151794463326549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40787033501535725951102065 30590275126151794463326549)
              ·
                refine ⟨89619946658647835341777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 30590275126151794463326549 89619946658647835341777)
                ·
                  rfl

theorem cell21_1178106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 10].length) (baseStart_1178106 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1178106 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1178106 prefixEnd_1178106 := by exact prefixLift 1178106
  have htrace : WordTrace (prefixWord ++ tailWord_1178106) baseStart_1178106 baseEnd_1178106 := by
    simpa [prefixWord, tailWord_1178106, baseEnd_1178106] using wordTrace_append hprefix tailTrace_1178106
  have hstable : (prefixWord ++ tailWord_1178106).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1178106).length < 2 ^ (prefixWord ++ tailWord_1178106).sum := by decide
  have hdescent : baseEnd_1178106 < baseStart_1178106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1178106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1178154 : List Nat := [3, 1, 4, 1, 1, 2, 1, 3, 5]
def baseStart_1178154 : Nat := 118140960795 + 1178154 * 2 ^ 59
def prefixEnd_1178154 : Nat := 4983230072969 + 3 ^ 40 * 1178154 * 2
def baseEnd_1178154 : Nat := 268870794229906089225233

theorem tailTrace_1178154 : CollatzResearch.WordTrace tailWord_1178154 prefixEnd_1178154 268870794229906089225233 := by
  unfold tailWord_1178154
  simp only [CollatzResearch.WordTrace]
  refine ⟨10742701643439186382237379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28647204382504497019299677 10742701643439186382237379)
  ·
    refine ⟨16114052465158779573356069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10742701643439186382237379 16114052465158779573356069)
    ·
      refine ⟨3021384837217271170004263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16114052465158779573356069 3021384837217271170004263)
      ·
        refine ⟨4532077255825906755006395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3021384837217271170004263 4532077255825906755006395)
        ·
          refine ⟨6798115883738860132509593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4532077255825906755006395 6798115883738860132509593)
          ·
            refine ⟨5098586912804145099382195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6798115883738860132509593 5098586912804145099382195)
            ·
              refine ⟨7647880369206217649073293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5098586912804145099382195 7647880369206217649073293)
              ·
                refine ⟨2867955138452331618402485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7647880369206217649073293 2867955138452331618402485)
                ·
                  refine ⟨268870794229906089225233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2867955138452331618402485 268870794229906089225233)
                  ·
                    rfl

theorem cell21_1178154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 3, 5].length) (baseStart_1178154 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1178154 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1178154 prefixEnd_1178154 := by exact prefixLift 1178154
  have htrace : WordTrace (prefixWord ++ tailWord_1178154) baseStart_1178154 baseEnd_1178154 := by
    simpa [prefixWord, tailWord_1178154, baseEnd_1178154] using wordTrace_append hprefix tailTrace_1178154
  have hstable : (prefixWord ++ tailWord_1178154).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1178154).length < 2 ^ (prefixWord ++ tailWord_1178154).sum := by decide
  have hdescent : baseEnd_1178154 < baseStart_1178154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1178154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1178174 : List Nat := [4, 2, 1, 4, 1, 2, 2, 5]
def baseStart_1178174 : Nat := 118140960795 + 1178174 * 2 ^ 59
def prefixEnd_1178174 : Nat := 4983230072969 + 3 ^ 40 * 1178174 * 2
def baseEnd_1178174 : Nat := 89625119500796832963953

theorem tailTrace_1178174 : CollatzResearch.WordTrace tailWord_1178174 prefixEnd_1178174 89625119500796832963953 := by
  unfold tailWord_1178174
  simp only [CollatzResearch.WordTrace]
  refine ⟨5371442004210536118084697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28647690689122859296451717 5371442004210536118084697)
  ·
    refine ⟨4028581503157902088563523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5371442004210536118084697 4028581503157902088563523)
    ·
      refine ⟨6042872254736853132845285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4028581503157902088563523 6042872254736853132845285)
      ·
        refine ⟨1133038547763159962408491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6042872254736853132845285 1133038547763159962408491)
        ·
          refine ⟨1699557821644739943612737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1133038547763159962408491 1699557821644739943612737)
          ·
            refine ⟨1274668366233554957709553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1699557821644739943612737 1274668366233554957709553)
            ·
              refine ⟨956001274675166218282165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1274668366233554957709553 956001274675166218282165)
              ·
                refine ⟨89625119500796832963953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 956001274675166218282165 89625119500796832963953)
                ·
                  rfl

theorem cell21_1178174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 2, 5].length) (baseStart_1178174 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1178174 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1178174 prefixEnd_1178174 := by exact prefixLift 1178174
  have htrace : WordTrace (prefixWord ++ tailWord_1178174) baseStart_1178174 baseEnd_1178174 := by
    simpa [prefixWord, tailWord_1178174, baseEnd_1178174] using wordTrace_append hprefix tailTrace_1178174
  have hstable : (prefixWord ++ tailWord_1178174).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1178174).length < 2 ^ (prefixWord ++ tailWord_1178174).sum := by decide
  have hdescent : baseEnd_1178174 < baseStart_1178174 := by decide
  rcases family_descends (prefixWord ++ tailWord_1178174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1178216 : List Nat := [2, 1, 4, 3, 2, 1, 2, 6]
def baseStart_1178216 : Nat := 118140960795 + 1178216 * 2 ^ 59
def prefixEnd_1178216 : Nat := 4983230072969 + 3 ^ 40 * 1178216 * 2
def baseEnd_1178216 : Nat := 89628314491535919730591

theorem tailTrace_1178216 : CollatzResearch.WordTrace tailWord_1178216 prefixEnd_1178216 89628314491535919730591 := by
  unfold tailWord_1178216
  simp only [CollatzResearch.WordTrace]
  refine ⟨21486533949766065058853251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28648711933021420078471001 21486533949766065058853251)
  ·
    refine ⟨32229800924649097588279877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21486533949766065058853251 32229800924649097588279877)
    ·
      refine ⟨6043087673371705797802477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32229800924649097588279877 6043087673371705797802477)
      ·
        refine ⟨2266157877514389674175929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6043087673371705797802477 2266157877514389674175929)
        ·
          refine ⟨1699618408135792255631947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2266157877514389674175929 1699618408135792255631947)
          ·
            refine ⟨2549427612203688383447921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1699618408135792255631947 2549427612203688383447921)
            ·
              refine ⟨1912070709152766287585941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2549427612203688383447921 1912070709152766287585941)
              ·
                refine ⟨89628314491535919730591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1912070709152766287585941 89628314491535919730591)
                ·
                  rfl

theorem cell21_1178216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 2, 6].length) (baseStart_1178216 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1178216 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1178216 prefixEnd_1178216 := by exact prefixLift 1178216
  have htrace : WordTrace (prefixWord ++ tailWord_1178216) baseStart_1178216 baseEnd_1178216 := by
    simpa [prefixWord, tailWord_1178216, baseEnd_1178216] using wordTrace_append hprefix tailTrace_1178216
  have hstable : (prefixWord ++ tailWord_1178216).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1178216).length < 2 ^ (prefixWord ++ tailWord_1178216).sum := by decide
  have hdescent : baseEnd_1178216 < baseStart_1178216 := by decide
  rcases family_descends (prefixWord ++ tailWord_1178216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1178227 : List Nat := [1, 1, 1, 2, 2, 1, 1, 4, 8]
def baseStart_1178227 : Nat := 118140960795 + 1178227 * 2 ^ 59
def prefixEnd_1178227 : Nat := 4983230072969 + 3 ^ 40 * 1178227 * 2
def baseEnd_1178227 : Nat := 268887453824474184508417

theorem tailTrace_1178227 : CollatzResearch.WordTrace tailWord_1178227 prefixEnd_1178227 268887453824474184508417 := by
  unfold tailWord_1178227
  simp only [CollatzResearch.WordTrace]
  refine ⟨42973469102492278996356935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28648979401661519330904623 42973469102492278996356935)
  ·
    refine ⟨64460203653738418494535403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42973469102492278996356935 64460203653738418494535403)
    ·
      refine ⟨96690305480607627741803105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64460203653738418494535403 96690305480607627741803105)
      ·
        refine ⟨72517729110455720806352329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96690305480607627741803105 72517729110455720806352329)
        ·
          refine ⟨54388296832841790604764247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72517729110455720806352329 54388296832841790604764247)
          ·
            refine ⟨81582445249262685907146371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54388296832841790604764247 81582445249262685907146371)
            ·
              refine ⟨122373667873894028860719557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 81582445249262685907146371 122373667873894028860719557)
              ·
                refine ⟨22945062726355130411384917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 122373667873894028860719557 22945062726355130411384917)
                ·
                  refine ⟨268887453824474184508417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22945062726355130411384917 268887453824474184508417)
                  ·
                    rfl

theorem cell21_1178227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 8].length) (baseStart_1178227 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1178227 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1178227 prefixEnd_1178227 := by exact prefixLift 1178227
  have htrace : WordTrace (prefixWord ++ tailWord_1178227) baseStart_1178227 baseEnd_1178227 := by
    simpa [prefixWord, tailWord_1178227, baseEnd_1178227] using wordTrace_append hprefix tailTrace_1178227
  have hstable : (prefixWord ++ tailWord_1178227).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1178227).length < 2 ^ (prefixWord ++ tailWord_1178227).sum := by decide
  have hdescent : baseEnd_1178227 < baseStart_1178227 := by decide
  rcases family_descends (prefixWord ++ tailWord_1178227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1178351 : List Nat := [1, 1, 2, 1, 5, 2, 4, 5]
def baseStart_1178351 : Nat := 118140960795 + 1178351 * 2 ^ 59
def prefixEnd_1178351 : Nat := 4983230072969 + 3 ^ 40 * 1178351 * 2
def baseEnd_1178351 : Nat := 89638584104625841480499

theorem tailTrace_1178351 : CollatzResearch.WordTrace tailWord_1178351 prefixEnd_1178351 89638584104625841480499 := by
  unfold tailWord_1178351
  simp only [CollatzResearch.WordTrace]
  refine ⟨42977991754043048173870907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28651994502695365449247271 42977991754043048173870907)
  ·
    refine ⟨64466987631064572260806361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42977991754043048173870907 64466987631064572260806361)
    ·
      refine ⟨48350240723298429195604771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64466987631064572260806361 48350240723298429195604771)
      ·
        refine ⟨72525361084947643793407157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48350240723298429195604771 72525361084947643793407157)
        ·
          refine ⟨6799252601713841605631921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 72525361084947643793407157 6799252601713841605631921)
          ·
            refine ⟨5099439451285381204223941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6799252601713841605631921 5099439451285381204223941)
            ·
              refine ⟨956144897116008975791989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5099439451285381204223941 956144897116008975791989)
              ·
                refine ⟨89638584104625841480499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 956144897116008975791989 89638584104625841480499)
                ·
                  rfl

theorem cell21_1178351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 4, 5].length) (baseStart_1178351 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1178351 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1178351 prefixEnd_1178351 := by exact prefixLift 1178351
  have htrace : WordTrace (prefixWord ++ tailWord_1178351) baseStart_1178351 baseEnd_1178351 := by
    simpa [prefixWord, tailWord_1178351, baseEnd_1178351] using wordTrace_append hprefix tailTrace_1178351
  have hstable : (prefixWord ++ tailWord_1178351).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1178351).length < 2 ^ (prefixWord ++ tailWord_1178351).sum := by decide
  have hdescent : baseEnd_1178351 < baseStart_1178351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1178351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1178430 : List Nat := [4, 2, 1, 2, 3, 1, 2, 2, 4]
def baseStart_1178430 : Nat := 118140960795 + 1178430 * 2 ^ 59
def prefixEnd_1178430 : Nat := 4983230072969 + 3 ^ 40 * 1178430 * 2
def baseEnd_1178430 : Nat := 268933781190190942624669

theorem tailTrace_1178430 : CollatzResearch.WordTrace tailWord_1178430 prefixEnd_1178430 268933781190190942624669 := by
  unfold tailWord_1178430
  simp only [CollatzResearch.WordTrace]
  refine ⟨5372609140094605583249593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28653915413837896443997829 5372609140094605583249593)
  ·
    refine ⟨4029456855070954187437195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5372609140094605583249593 4029456855070954187437195)
    ·
      refine ⟨6044185282606431281155793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4029456855070954187437195 6044185282606431281155793)
      ·
        refine ⟨4533138961954823460866845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6044185282606431281155793 4533138961954823460866845)
        ·
          refine ⟨1699927110733058797825067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4533138961954823460866845 1699927110733058797825067)
          ·
            refine ⟨2549890666099588196737601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1699927110733058797825067 2549890666099588196737601)
            ·
              refine ⟨1912417999574691147553201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2549890666099588196737601 1912417999574691147553201)
              ·
                refine ⟨1434313499681018360664901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1912417999574691147553201 1434313499681018360664901)
                ·
                  refine ⟨268933781190190942624669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1434313499681018360664901 268933781190190942624669)
                  ·
                    rfl

theorem cell21_1178430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 2, 2, 4].length) (baseStart_1178430 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1178430 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1178430 prefixEnd_1178430 := by exact prefixLift 1178430
  have htrace : WordTrace (prefixWord ++ tailWord_1178430) baseStart_1178430 baseEnd_1178430 := by
    simpa [prefixWord, tailWord_1178430, baseEnd_1178430] using wordTrace_append hprefix tailTrace_1178430
  have hstable : (prefixWord ++ tailWord_1178430).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1178430).length < 2 ^ (prefixWord ++ tailWord_1178430).sum := by decide
  have hdescent : baseEnd_1178430 < baseStart_1178430 := by decide
  rcases family_descends (prefixWord ++ tailWord_1178430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1178489 : List Nat := [1, 2, 1, 3, 2, 5, 1, 2, 4]
def baseStart_1178489 : Nat := 118140960795 + 1178489 * 2 ^ 59
def prefixEnd_1178489 : Nat := 4983230072969 + 3 ^ 40 * 1178489 * 2
def baseEnd_1178489 : Nat := 268947245794019951141215

theorem tailTrace_1178489 : CollatzResearch.WordTrace tailWord_1178489 prefixEnd_1178489 268947245794019951141215 := by
  unfold tailWord_1178489
  simp only [CollatzResearch.WordTrace]
  refine ⟨42983025027543097742394521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28655350018362065161596347 42983025027543097742394521)
  ·
    refine ⟨32237268770657323306795891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42983025027543097742394521 32237268770657323306795891)
    ·
      refine ⟨48355903155985984960193837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32237268770657323306795891 48355903155985984960193837)
      ·
        refine ⟨18133463683494744360072689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48355903155985984960193837 18133463683494744360072689)
        ·
          refine ⟨13600097762621058270054517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18133463683494744360072689 13600097762621058270054517)
          ·
            refine ⟨1275009165245724212817611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13600097762621058270054517 1275009165245724212817611)
            ·
              refine ⟨1912513747868586319226417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1275009165245724212817611 1912513747868586319226417)
              ·
                refine ⟨1434385310901439739419813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1912513747868586319226417 1434385310901439739419813)
                ·
                  refine ⟨268947245794019951141215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1434385310901439739419813 268947245794019951141215)
                  ·
                    rfl

theorem cell21_1178489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 1, 2, 4].length) (baseStart_1178489 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1178489 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1178489 prefixEnd_1178489 := by exact prefixLift 1178489
  have htrace : WordTrace (prefixWord ++ tailWord_1178489) baseStart_1178489 baseEnd_1178489 := by
    simpa [prefixWord, tailWord_1178489, baseEnd_1178489] using wordTrace_append hprefix tailTrace_1178489
  have hstable : (prefixWord ++ tailWord_1178489).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1178489).length < 2 ^ (prefixWord ++ tailWord_1178489).sum := by decide
  have hdescent : baseEnd_1178489 < baseStart_1178489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1178489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1178506 : List Nat := [3, 1, 2, 4, 1, 2, 3, 1, 4]
def baseStart_1178506 : Nat := 118140960795 + 1178506 * 2 ^ 59
def prefixEnd_1178506 : Nat := 4983230072969 + 3 ^ 40 * 1178506 * 2
def baseEnd_1178506 : Nat := 268951125425631699357847

theorem tailTrace_1178506 : CollatzResearch.WordTrace tailWord_1178506 prefixEnd_1178506 268951125425631699357847 := by
  unfold tailWord_1178506
  simp only [CollatzResearch.WordTrace]
  refine ⟨10745911267120377411440843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28655763378987673097175581 10745911267120377411440843)
  ·
    refine ⟨16118866900680566117161265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10745911267120377411440843 16118866900680566117161265)
    ·
      refine ⟨12089150175510424587870949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16118866900680566117161265 12089150175510424587870949)
      ·
        refine ⟨2266715657908204610225803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12089150175510424587870949 2266715657908204610225803)
        ·
          refine ⟨3400073486862306915338705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2266715657908204610225803 3400073486862306915338705)
          ·
            refine ⟨2550055115146730186504029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3400073486862306915338705 2550055115146730186504029)
            ·
              refine ⟨956270668180023819939011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2550055115146730186504029 956270668180023819939011)
              ·
                refine ⟨1434406002270035729908517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 956270668180023819939011 1434406002270035729908517)
                ·
                  refine ⟨268951125425631699357847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1434406002270035729908517 268951125425631699357847)
                  ·
                    rfl

theorem cell21_1178506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 3, 1, 4].length) (baseStart_1178506 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1178506 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1178506 prefixEnd_1178506 := by exact prefixLift 1178506
  have htrace : WordTrace (prefixWord ++ tailWord_1178506) baseStart_1178506 baseEnd_1178506 := by
    simpa [prefixWord, tailWord_1178506, baseEnd_1178506] using wordTrace_append hprefix tailTrace_1178506
  have hstable : (prefixWord ++ tailWord_1178506).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1178506).length < 2 ^ (prefixWord ++ tailWord_1178506).sum := by decide
  have hdescent : baseEnd_1178506 < baseStart_1178506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1178506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1178517 : List Nat := [1, 3, 2, 1, 1, 4, 2, 2, 5]
def baseStart_1178517 : Nat := 118140960795 + 1178517 * 2 ^ 59
def prefixEnd_1178517 : Nat := 4983230072969 + 3 ^ 40 * 1178517 * 2
def baseEnd_1178517 : Nat := 268953635775498124674491

theorem tailTrace_1178517 : CollatzResearch.WordTrace tailWord_1178517 prefixEnd_1178517 268953635775498124674491 := by
  unfold tailWord_1178517
  simp only [CollatzResearch.WordTrace]
  refine ⟨42984046271441658524413805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28656030847627772349609203 42984046271441658524413805)
  ·
    refine ⟨16119017351790621946655177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42984046271441658524413805 16119017351790621946655177)
    ·
      refine ⟨12089263013842966459991383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16119017351790621946655177 12089263013842966459991383)
      ·
        refine ⟨18133894520764449689987075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12089263013842966459991383 18133894520764449689987075)
        ·
          refine ⟨27200841781146674534980613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18133894520764449689987075 27200841781146674534980613)
          ·
            refine ⟨5100157833965001475308865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27200841781146674534980613 5100157833965001475308865)
            ·
              refine ⟨3825118375473751106481649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5100157833965001475308865 3825118375473751106481649)
              ·
                refine ⟨2868838781605313329861237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3825118375473751106481649 2868838781605313329861237)
                ·
                  refine ⟨268953635775498124674491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2868838781605313329861237 268953635775498124674491)
                  ·
                    rfl

theorem cell21_1178517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 2, 5].length) (baseStart_1178517 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1178517 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1178517 prefixEnd_1178517 := by exact prefixLift 1178517
  have htrace : WordTrace (prefixWord ++ tailWord_1178517) baseStart_1178517 baseEnd_1178517 := by
    simpa [prefixWord, tailWord_1178517, baseEnd_1178517] using wordTrace_append hprefix tailTrace_1178517
  have hstable : (prefixWord ++ tailWord_1178517).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1178517).length < 2 ^ (prefixWord ++ tailWord_1178517).sum := by decide
  have hdescent : baseEnd_1178517 < baseStart_1178517 := by decide
  rcases family_descends (prefixWord ++ tailWord_1178517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1178531 : List Nat := [1, 1, 1, 4, 1, 2, 3, 2, 6]
def baseStart_1178531 : Nat := 118140960795 + 1178531 * 2 ^ 59
def prefixEnd_1178531 : Nat := 4983230072969 + 3 ^ 40 * 1178531 * 2
def baseEnd_1178531 : Nat := 268956830766237211441129

theorem tailTrace_1178531 : CollatzResearch.WordTrace tailWord_1178531 prefixEnd_1178531 268956830766237211441129 := by
  unfold tailWord_1178531
  simp only [CollatzResearch.WordTrace]
  refine ⟨42984556893390938915423447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28656371262260625943615631 42984556893390938915423447)
  ·
    refine ⟨64476835340086408373135171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42984556893390938915423447 64476835340086408373135171)
    ·
      refine ⟨96715253010129612559702757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64476835340086408373135171 96715253010129612559702757)
      ·
        refine ⟨18134109939399302354944267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 96715253010129612559702757 18134109939399302354944267)
        ·
          refine ⟨27201164909098953532416401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18134109939399302354944267 27201164909098953532416401)
          ·
            refine ⟨20400873681824215149312301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27201164909098953532416401 20400873681824215149312301)
            ·
              refine ⟨7650327630684080680992113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20400873681824215149312301 7650327630684080680992113)
              ·
                refine ⟨5737745723013060510744085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7650327630684080680992113 5737745723013060510744085)
                ·
                  refine ⟨268956830766237211441129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5737745723013060510744085 268956830766237211441129)
                  ·
                    rfl

theorem cell21_1178531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 2, 6].length) (baseStart_1178531 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1178531 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1178531 prefixEnd_1178531 := by exact prefixLift 1178531
  have htrace : WordTrace (prefixWord ++ tailWord_1178531) baseStart_1178531 baseEnd_1178531 := by
    simpa [prefixWord, tailWord_1178531, baseEnd_1178531] using wordTrace_append hprefix tailTrace_1178531
  have hstable : (prefixWord ++ tailWord_1178531).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1178531).length < 2 ^ (prefixWord ++ tailWord_1178531).sum := by decide
  have hdescent : baseEnd_1178531 < baseStart_1178531 := by decide
  rcases family_descends (prefixWord ++ tailWord_1178531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1178576 : List Nat := [2, 1, 1, 1, 1, 2, 3, 3, 7]
def baseStart_1178576 : Nat := 118140960795 + 1178576 * 2 ^ 59
def prefixEnd_1178576 : Nat := 4983230072969 + 3 ^ 40 * 1178576 * 2
def baseEnd_1178576 : Nat := 268967100379327133191037

theorem tailTrace_1178576 : CollatzResearch.WordTrace tailWord_1178576 prefixEnd_1178576 268967100379327133191037 := by
  unfold tailWord_1178576
  simp only [CollatzResearch.WordTrace]
  refine ⟨21493099089113955800405791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28657465452151941067207721 21493099089113955800405791)
  ·
    refine ⟨32239648633670933700608687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21493099089113955800405791 32239648633670933700608687)
    ·
      refine ⟨48359472950506400550913031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32239648633670933700608687 48359472950506400550913031)
      ·
        refine ⟨72539209425759600826369547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48359472950506400550913031 72539209425759600826369547)
        ·
          refine ⟨108808814138639401239554321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72539209425759600826369547 108808814138639401239554321)
          ·
            refine ⟨81606610603979550929665741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 108808814138639401239554321 81606610603979550929665741)
            ·
              refine ⟨30602478976492331598624653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81606610603979550929665741 30602478976492331598624653)
              ·
                refine ⟨11475929616184624349484245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30602478976492331598624653 11475929616184624349484245)
                ·
                  refine ⟨268967100379327133191037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11475929616184624349484245 268967100379327133191037)
                  ·
                    rfl

theorem cell21_1178576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 3, 7].length) (baseStart_1178576 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1178576 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1178576 prefixEnd_1178576 := by exact prefixLift 1178576
  have htrace : WordTrace (prefixWord ++ tailWord_1178576) baseStart_1178576 baseEnd_1178576 := by
    simpa [prefixWord, tailWord_1178576, baseEnd_1178576] using wordTrace_append hprefix tailTrace_1178576
  have hstable : (prefixWord ++ tailWord_1178576).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1178576).length < 2 ^ (prefixWord ++ tailWord_1178576).sum := by decide
  have hdescent : baseEnd_1178576 < baseStart_1178576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1178576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1178613 : List Nat := [1, 3, 5, 2, 1, 2, 1, 6]
def baseStart_1178613 : Nat := 118140960795 + 1178613 * 2 ^ 59
def prefixEnd_1178613 : Nat := 4983230072969 + 3 ^ 40 * 1178613 * 2
def baseEnd_1178613 : Nat := 89658514761141097024765

theorem tailTrace_1178613 : CollatzResearch.WordTrace tailWord_1178613 prefixEnd_1178613 89658514761141097024765 := by
  unfold tailWord_1178613
  simp only [CollatzResearch.WordTrace]
  refine ⟨42987547679093866919908493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28658365119395911279938995 42987547679093866919908493)
  ·
    refine ⟨16120330379660200094965685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42987547679093866919908493 16120330379660200094965685)
    ·
      refine ⟨1511280973093143758903033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16120330379660200094965685 1511280973093143758903033)
      ·
        refine ⟨1133460729819857819177275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1511280973093143758903033 1133460729819857819177275)
        ·
          refine ⟨1700191094729786728765913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1133460729819857819177275 1700191094729786728765913)
          ·
            refine ⟨1275143321047340046574435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1700191094729786728765913 1275143321047340046574435)
            ·
              refine ⟨1912714981571010069861653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1275143321047340046574435 1912714981571010069861653)
              ·
                refine ⟨89658514761141097024765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1912714981571010069861653 89658514761141097024765)
                ·
                  rfl

theorem cell21_1178613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 1, 6].length) (baseStart_1178613 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1178613 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1178613 prefixEnd_1178613 := by exact prefixLift 1178613
  have htrace : WordTrace (prefixWord ++ tailWord_1178613) baseStart_1178613 baseEnd_1178613 := by
    simpa [prefixWord, tailWord_1178613, baseEnd_1178613] using wordTrace_append hprefix tailTrace_1178613
  have hstable : (prefixWord ++ tailWord_1178613).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1178613).length < 2 ^ (prefixWord ++ tailWord_1178613).sum := by decide
  have hdescent : baseEnd_1178613 < baseStart_1178613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1178613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1178686 : List Nat := [4, 2, 1, 3, 1, 1, 2, 2, 5]
def baseStart_1178686 : Nat := 118140960795 + 1178686 * 2 ^ 59
def prefixEnd_1178686 : Nat := 4983230072969 + 3 ^ 40 * 1178686 * 2
def baseEnd_1178686 : Nat := 268992203877991386357479

theorem tailTrace_1178686 : CollatzResearch.WordTrace tailWord_1178686 prefixEnd_1178686 268992203877991386357479 := by
  unfold tailWord_1178686
  simp only [CollatzResearch.WordTrace]
  refine ⟨5373776275978675048414489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28660140138552933591543941 5373776275978675048414489)
  ·
    refine ⟨4030332206984006286310867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5373776275978675048414489 4030332206984006286310867)
    ·
      refine ⟨6045498310476009429466301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4030332206984006286310867 6045498310476009429466301)
      ·
        refine ⟨2267061866428503536049863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6045498310476009429466301 2267061866428503536049863)
        ·
          refine ⟨3400592799642755304074795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2267061866428503536049863 3400592799642755304074795)
          ·
            refine ⟨5100889199464132956112193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3400592799642755304074795 5100889199464132956112193)
            ·
              refine ⟨3825666899598099717084145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5100889199464132956112193 3825666899598099717084145)
              ·
                refine ⟨2869250174698574787813109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3825666899598099717084145 2869250174698574787813109)
                ·
                  refine ⟨268992203877991386357479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2869250174698574787813109 268992203877991386357479)
                  ·
                    rfl

theorem cell21_1178686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 2, 5].length) (baseStart_1178686 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1178686 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1178686 prefixEnd_1178686 := by exact prefixLift 1178686
  have htrace : WordTrace (prefixWord ++ tailWord_1178686) baseStart_1178686 baseEnd_1178686 := by
    simpa [prefixWord, tailWord_1178686, baseEnd_1178686] using wordTrace_append hprefix tailTrace_1178686
  have hstable : (prefixWord ++ tailWord_1178686).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1178686).length < 2 ^ (prefixWord ++ tailWord_1178686).sum := by decide
  have hdescent : baseEnd_1178686 < baseStart_1178686 := by decide
  rcases family_descends (prefixWord ++ tailWord_1178686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1178689 : List Nat := [1, 2, 5, 1, 4, 1, 2, 5]
def baseStart_1178689 : Nat := 118140960795 + 1178689 * 2 ^ 59
def prefixEnd_1178689 : Nat := 4983230072969 + 3 ^ 40 * 1178689 * 2
def baseEnd_1178689 : Nat := 89664296172954682602491

theorem tailTrace_1178689 : CollatzResearch.WordTrace tailWord_1178689 prefixEnd_1178689 89664296172954682602491 := by
  unfold tailWord_1178689
  simp only [CollatzResearch.WordTrace]
  refine ⟨42990319626818531899675121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28660213084545687933116747 42990319626818531899675121)
  ·
    refine ⟨32242739720113898924756341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42990319626818531899675121 32242739720113898924756341)
    ·
      refine ⟨3022756848760678024195907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 32242739720113898924756341 3022756848760678024195907)
      ·
        refine ⟨4534135273141017036293861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3022756848760678024195907 4534135273141017036293861)
        ·
          refine ⟨850150363713940694305099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4534135273141017036293861 850150363713940694305099)
          ·
            refine ⟨1275225545570911041457649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 850150363713940694305099 1275225545570911041457649)
            ·
              refine ⟨956419159178183281093237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1275225545570911041457649 956419159178183281093237)
              ·
                refine ⟨89664296172954682602491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 956419159178183281093237 89664296172954682602491)
                ·
                  rfl

theorem cell21_1178689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 2, 5].length) (baseStart_1178689 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1178689 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1178689 prefixEnd_1178689 := by exact prefixLift 1178689
  have htrace : WordTrace (prefixWord ++ tailWord_1178689) baseStart_1178689 baseEnd_1178689 := by
    simpa [prefixWord, tailWord_1178689, baseEnd_1178689] using wordTrace_append hprefix tailTrace_1178689
  have hstable : (prefixWord ++ tailWord_1178689).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1178689).length < 2 ^ (prefixWord ++ tailWord_1178689).sum := by decide
  have hdescent : baseEnd_1178689 < baseStart_1178689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1178689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1178734 : List Nat := [4, 1, 2, 2, 1, 4, 2, 1, 4]
def baseStart_1178734 : Nat := 118140960795 + 1178734 * 2 ^ 59
def prefixEnd_1178734 : Nat := 4983230072969 + 3 ^ 40 * 1178734 * 2
def baseEnd_1178734 : Nat := 269003158131953969557381

theorem tailTrace_1178734 : CollatzResearch.WordTrace tailWord_1178734 prefixEnd_1178734 269003158131953969557381 := by
  unfold tailWord_1178734
  simp only [CollatzResearch.WordTrace]
  refine ⟨5373995113956938073132907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28661307274437003056708837 5373995113956938073132907)
  ·
    refine ⟨8060992670935407109699361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5373995113956938073132907 8060992670935407109699361)
    ·
      refine ⟨6045744503201555332274521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8060992670935407109699361 6045744503201555332274521)
      ·
        refine ⟨4534308377401166499205891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6045744503201555332274521 4534308377401166499205891)
        ·
          refine ⟨6801462566101749748808837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4534308377401166499205891 6801462566101749748808837)
          ·
            refine ⟨1275274231144078077901657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6801462566101749748808837 1275274231144078077901657)
            ·
              refine ⟨956455673358058558426243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1275274231144078077901657 956455673358058558426243)
              ·
                refine ⟨1434683510037087837639365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 956455673358058558426243 1434683510037087837639365)
                ·
                  refine ⟨269003158131953969557381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1434683510037087837639365 269003158131953969557381)
                  ·
                    rfl

theorem cell21_1178734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 2, 1, 4].length) (baseStart_1178734 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1178734 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1178734 prefixEnd_1178734 := by exact prefixLift 1178734
  have htrace : WordTrace (prefixWord ++ tailWord_1178734) baseStart_1178734 baseEnd_1178734 := by
    simpa [prefixWord, tailWord_1178734, baseEnd_1178734] using wordTrace_append hprefix tailTrace_1178734
  have hstable : (prefixWord ++ tailWord_1178734).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1178734).length < 2 ^ (prefixWord ++ tailWord_1178734).sum := by decide
  have hdescent : baseEnd_1178734 < baseStart_1178734 := by decide
  rcases family_descends (prefixWord ++ tailWord_1178734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1178762 : List Nat := [3, 1, 2, 3, 1, 1, 2, 5, 3]
def baseStart_1178762 : Nat := 118140960795 + 1178762 * 2 ^ 59
def prefixEnd_1178762 : Nat := 4983230072969 + 3 ^ 40 * 1178762 * 2
def baseEnd_1178762 : Nat := 269009548113432143090657

theorem tailTrace_1178762 : CollatzResearch.WordTrace tailWord_1178762 prefixEnd_1178762 269009548113432143090657 := by
  unfold tailWord_1178762
  simp only [CollatzResearch.WordTrace]
  refine ⟨10748245538888516341770635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28661988103702710244721693 10748245538888516341770635)
  ·
    refine ⟨16122368308332774512655953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10748245538888516341770635 16122368308332774512655953)
    ·
      refine ⟨12091776231249580884491965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16122368308332774512655953 12091776231249580884491965)
      ·
        refine ⟨4534416086718592831684487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12091776231249580884491965 4534416086718592831684487)
        ·
          refine ⟨6801624130077889247526731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4534416086718592831684487 6801624130077889247526731)
          ·
            refine ⟨10202436195116833871290097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6801624130077889247526731 10202436195116833871290097)
            ·
              refine ⟨7651827146337625403467573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10202436195116833871290097 7651827146337625403467573)
              ·
                refine ⟨717358794969152381575085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7651827146337625403467573 717358794969152381575085)
                ·
                  refine ⟨269009548113432143090657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 717358794969152381575085 269009548113432143090657)
                  ·
                    rfl

theorem cell21_1178762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 5, 3].length) (baseStart_1178762 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1178762 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1178762 prefixEnd_1178762 := by exact prefixLift 1178762
  have htrace : WordTrace (prefixWord ++ tailWord_1178762) baseStart_1178762 baseEnd_1178762 := by
    simpa [prefixWord, tailWord_1178762, baseEnd_1178762] using wordTrace_append hprefix tailTrace_1178762
  have hstable : (prefixWord ++ tailWord_1178762).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1178762).length < 2 ^ (prefixWord ++ tailWord_1178762).sum := by decide
  have hdescent : baseEnd_1178762 < baseStart_1178762 := by decide
  rcases family_descends (prefixWord ++ tailWord_1178762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1178776 : List Nat := [2, 1, 2, 4, 2, 1, 1, 4, 4]
def baseStart_1178776 : Nat := 118140960795 + 1178776 * 2 ^ 59
def prefixEnd_1178776 : Nat := 4983230072969 + 3 ^ 40 * 1178776 * 2
def baseEnd_1178776 : Nat := 269012743104171229857295

theorem tailTrace_1178776 : CollatzResearch.WordTrace tailWord_1178776 prefixEnd_1178776 269012743104171229857295 := by
  unfold tailWord_1178776
  simp only [CollatzResearch.WordTrace]
  refine ⟨21496746388751672879046091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28662328518335563838728121 21496746388751672879046091)
  ·
    refine ⟨32245119583127509318569137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21496746388751672879046091 32245119583127509318569137)
    ·
      refine ⟨24183839687345631988926853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32245119583127509318569137 24183839687345631988926853)
      ·
        refine ⟨4534469941377305997923785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24183839687345631988926853 4534469941377305997923785)
        ·
          refine ⟨3400852456032979498442839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4534469941377305997923785 3400852456032979498442839)
          ·
            refine ⟨5101278684049469247664259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3400852456032979498442839 5101278684049469247664259)
            ·
              refine ⟨7651918026074203871496389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5101278684049469247664259 7651918026074203871496389)
              ·
                refine ⟨1434734629888913225905573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7651918026074203871496389 1434734629888913225905573)
                ·
                  refine ⟨269012743104171229857295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1434734629888913225905573 269012743104171229857295)
                  ·
                    rfl

theorem cell21_1178776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 4, 4].length) (baseStart_1178776 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1178776 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1178776 prefixEnd_1178776 := by exact prefixLift 1178776
  have htrace : WordTrace (prefixWord ++ tailWord_1178776) baseStart_1178776 baseEnd_1178776 := by
    simpa [prefixWord, tailWord_1178776, baseEnd_1178776] using wordTrace_append hprefix tailTrace_1178776
  have hstable : (prefixWord ++ tailWord_1178776).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1178776).length < 2 ^ (prefixWord ++ tailWord_1178776).sum := by decide
  have hdescent : baseEnd_1178776 < baseStart_1178776 := by decide
  rcases family_descends (prefixWord ++ tailWord_1178776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1178945 : List Nat := [1, 2, 5, 2, 1, 2, 2, 2, 4]
def baseStart_1178945 : Nat := 118140960795 + 1178945 * 2 ^ 59
def prefixEnd_1178945 : Nat := 4983230072969 + 3 ^ 40 * 1178945 * 2
def baseEnd_1178945 : Nat := 269051311206664491540283

theorem tailTrace_1178945 : CollatzResearch.WordTrace tailWord_1178945 prefixEnd_1178945 269051311206664491540283 := by
  unfold tailWord_1178945
  simp only [CollatzResearch.WordTrace]
  refine ⟨42999656713891087620994289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28666437809260725080662859 42999656713891087620994289)
  ·
    refine ⟨32249742535418315715745717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42999656713891087620994289 32249742535418315715745717)
    ·
      refine ⟨3023413362695467098351161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 32249742535418315715745717 3023413362695467098351161)
      ·
        refine ⟨2267560022021600323763371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3023413362695467098351161 2267560022021600323763371)
        ·
          refine ⟨3401340033032400485645057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2267560022021600323763371 3401340033032400485645057)
          ·
            refine ⟨2551005024774300364233793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3401340033032400485645057 2551005024774300364233793)
            ·
              refine ⟨1913253768580725273175345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2551005024774300364233793 1913253768580725273175345)
              ·
                refine ⟨1434940326435543954881509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1913253768580725273175345 1434940326435543954881509)
                ·
                  refine ⟨269051311206664491540283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1434940326435543954881509 269051311206664491540283)
                  ·
                    rfl

theorem cell21_1178945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 2, 2, 4].length) (baseStart_1178945 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1178945 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1178945 prefixEnd_1178945 := by exact prefixLift 1178945
  have htrace : WordTrace (prefixWord ++ tailWord_1178945) baseStart_1178945 baseEnd_1178945 := by
    simpa [prefixWord, tailWord_1178945, baseEnd_1178945] using wordTrace_append hprefix tailTrace_1178945
  have hstable : (prefixWord ++ tailWord_1178945).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1178945).length < 2 ^ (prefixWord ++ tailWord_1178945).sum := by decide
  have hdescent : baseEnd_1178945 < baseStart_1178945 := by decide
  rcases family_descends (prefixWord ++ tailWord_1178945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1178948 : List Nat := [2, 3, 4, 1, 1, 1, 4, 2, 3]
def baseStart_1178948 : Nat := 118140960795 + 1178948 * 2 ^ 59
def prefixEnd_1178948 : Nat := 4983230072969 + 3 ^ 40 * 1178948 * 2
def baseEnd_1178948 : Nat := 269051995847537152990277

theorem tailTrace_1178948 : CollatzResearch.WordTrace tailWord_1178948 prefixEnd_1178948 269051995847537152990277 := by
  unfold tailWord_1178948
  simp only [CollatzResearch.WordTrace]
  refine ⟨21499883066440109566676749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28666510755253479422235665 21499883066440109566676749)
  ·
    refine ⟨8062456149915041087503781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21499883066440109566676749 8062456149915041087503781)
    ·
      refine ⟨1511710528109070203906959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8062456149915041087503781 1511710528109070203906959)
      ·
        refine ⟨2267565792163605305860439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1511710528109070203906959 2267565792163605305860439)
        ·
          refine ⟨3401348688245407958790659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2267565792163605305860439 3401348688245407958790659)
          ·
            refine ⟨5102023032368111938185989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3401348688245407958790659 5102023032368111938185989)
            ·
              refine ⟨956629318569020988409873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5102023032368111938185989 956629318569020988409873)
              ·
                refine ⟨717471988926765741307405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 956629318569020988409873 717471988926765741307405)
                ·
                  refine ⟨269051995847537152990277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 717471988926765741307405 269051995847537152990277)
                  ·
                    rfl

theorem cell21_1178948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 4, 2, 3].length) (baseStart_1178948 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1178948 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1178948 prefixEnd_1178948 := by exact prefixLift 1178948
  have htrace : WordTrace (prefixWord ++ tailWord_1178948) baseStart_1178948 baseEnd_1178948 := by
    simpa [prefixWord, tailWord_1178948, baseEnd_1178948] using wordTrace_append hprefix tailTrace_1178948
  have hstable : (prefixWord ++ tailWord_1178948).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1178948).length < 2 ^ (prefixWord ++ tailWord_1178948).sum := by decide
  have hdescent : baseEnd_1178948 < baseStart_1178948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1178948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1179063 : List Nat := [1, 1, 3, 1, 3, 2, 2, 4, 4]
def baseStart_1179063 : Nat := 118140960795 + 1179063 * 2 ^ 59
def prefixEnd_1179063 : Nat := 4983230072969 + 3 ^ 40 * 1179063 * 2
def baseEnd_1179063 : Nat := 269078240414322508573375

theorem tailTrace_1179063 : CollatzResearch.WordTrace tailWord_1179063 prefixEnd_1179063 269078240414322508573375 := by
  unfold tailWord_1179063
  simp only [CollatzResearch.WordTrace]
  refine ⟨43003960527463593773789843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28669307018309062515859895 43003960527463593773789843)
  ·
    refine ⟨64505940791195390660684765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43003960527463593773789843 64505940791195390660684765)
    ·
      refine ⟨24189727796698271497756787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64505940791195390660684765 24189727796698271497756787)
      ·
        refine ⟨36284591695047407246635181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24189727796698271497756787 36284591695047407246635181)
        ·
          refine ⟨13606721885642777717488193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36284591695047407246635181 13606721885642777717488193)
          ·
            refine ⟨10205041414232083288116145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13606721885642777717488193 10205041414232083288116145)
            ·
              refine ⟨7653781060674062466087109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10205041414232083288116145 7653781060674062466087109)
              ·
                refine ⟨1435083948876386712391333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7653781060674062466087109 1435083948876386712391333)
                ·
                  refine ⟨269078240414322508573375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1435083948876386712391333 269078240414322508573375)
                  ·
                    rfl

theorem cell21_1179063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 4, 4].length) (baseStart_1179063 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1179063 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1179063 prefixEnd_1179063 := by exact prefixLift 1179063
  have htrace : WordTrace (prefixWord ++ tailWord_1179063) baseStart_1179063 baseEnd_1179063 := by
    simpa [prefixWord, tailWord_1179063, baseEnd_1179063] using wordTrace_append hprefix tailTrace_1179063
  have hstable : (prefixWord ++ tailWord_1179063).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1179063).length < 2 ^ (prefixWord ++ tailWord_1179063).sum := by decide
  have hdescent : baseEnd_1179063 < baseStart_1179063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1179063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1179117 : List Nat := [1, 5, 1, 3, 3, 1, 2, 2, 3]
def baseStart_1179117 : Nat := 118140960795 + 1179117 * 2 ^ 59
def prefixEnd_1179117 : Nat := 4983230072969 + 3 ^ 40 * 1179117 * 2
def baseEnd_1179117 : Nat := 269090563950030414673265

theorem tailTrace_1179117 : CollatzResearch.WordTrace tailWord_1179117 prefixEnd_1179117 269090563950030414673265 := by
  unfold tailWord_1179117
  simp only [CollatzResearch.WordTrace]
  refine ⟨43005930069267960996255605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28670620046178640664170403 43005930069267960996255605)
  ·
    refine ⟨4031805943993871343398963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 43005930069267960996255605 4031805943993871343398963)
    ·
      refine ⟨6047708915990807015098445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4031805943993871343398963 6047708915990807015098445)
      ·
        refine ⟨2267890843496552630661917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6047708915990807015098445 2267890843496552630661917)
        ·
          refine ⟨850459066311207236498219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2267890843496552630661917 850459066311207236498219)
          ·
            refine ⟨1275688599466810854747329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 850459066311207236498219 1275688599466810854747329)
            ·
              refine ⟨956766449600108141060497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1275688599466810854747329 956766449600108141060497)
              ·
                refine ⟨717574837200081105795373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 956766449600108141060497 717574837200081105795373)
                ·
                  refine ⟨269090563950030414673265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 717574837200081105795373 269090563950030414673265)
                  ·
                    rfl

theorem cell21_1179117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 2, 2, 3].length) (baseStart_1179117 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1179117 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1179117 prefixEnd_1179117 := by exact prefixLift 1179117
  have htrace : WordTrace (prefixWord ++ tailWord_1179117) baseStart_1179117 baseEnd_1179117 := by
    simpa [prefixWord, tailWord_1179117, baseEnd_1179117] using wordTrace_append hprefix tailTrace_1179117
  have hstable : (prefixWord ++ tailWord_1179117).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1179117).length < 2 ^ (prefixWord ++ tailWord_1179117).sum := by decide
  have hdescent : baseEnd_1179117 < baseStart_1179117 := by decide
  rcases family_descends (prefixWord ++ tailWord_1179117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1179190 : List Nat := [5, 1, 2, 1, 3, 1, 3, 1, 4]
def baseStart_1179190 : Nat := 118140960795 + 1179190 * 2 ^ 59
def prefixEnd_1179190 : Nat := 4983230072969 + 3 ^ 40 * 1179190 * 2
def baseEnd_1179190 : Nat := 269107223544598509956449

theorem tailTrace_1179190 : CollatzResearch.WordTrace tailWord_1179190 prefixEnd_1179190 269107223544598509956449 := by
  unfold tailWord_1179190
  simp only [CollatzResearch.WordTrace]
  refine ⟨2688037037375218403978939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28672395065335662975775349 2688037037375218403978939)
  ·
    refine ⟨4032055556062827605968409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2688037037375218403978939 4032055556062827605968409)
    ·
      refine ⟨3024041667047120704476307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4032055556062827605968409 3024041667047120704476307)
      ·
        refine ⟨4536062500570681056714461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3024041667047120704476307 4536062500570681056714461)
        ·
          refine ⟨1701023437714005396267923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4536062500570681056714461 1701023437714005396267923)
          ·
            refine ⟨2551535156571008094401885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1701023437714005396267923 2551535156571008094401885)
            ·
              refine ⟨956825683714128035400707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2551535156571008094401885 956825683714128035400707)
              ·
                refine ⟨1435238525571192053101061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 956825683714128035400707 1435238525571192053101061)
                ·
                  refine ⟨269107223544598509956449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1435238525571192053101061 269107223544598509956449)
                  ·
                    rfl

theorem cell21_1179190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 3, 1, 4].length) (baseStart_1179190 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1179190 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1179190 prefixEnd_1179190 := by exact prefixLift 1179190
  have htrace : WordTrace (prefixWord ++ tailWord_1179190) baseStart_1179190 baseEnd_1179190 := by
    simpa [prefixWord, tailWord_1179190, baseEnd_1179190] using wordTrace_append hprefix tailTrace_1179190
  have hstable : (prefixWord ++ tailWord_1179190).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1179190).length < 2 ^ (prefixWord ++ tailWord_1179190).sum := by decide
  have hdescent : baseEnd_1179190 < baseStart_1179190 := by decide
  rcases family_descends (prefixWord ++ tailWord_1179190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1179218 : List Nat := [3, 2, 2, 1, 2, 2, 3, 3, 3]
def baseStart_1179218 : Nat := 118140960795 + 1179218 * 2 ^ 59
def prefixEnd_1179218 : Nat := 4983230072969 + 3 ^ 40 * 1179218 * 2
def baseEnd_1179218 : Nat := 269113613526076683489725

theorem tailTrace_1179218 : CollatzResearch.WordTrace tailWord_1179218 prefixEnd_1179218 269113613526076683489725 := by
  unfold tailWord_1179218
  simp only [CollatzResearch.WordTrace]
  refine ⟨10752403460475513811420577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28673075894601370163788205 10752403460475513811420577)
  ·
    refine ⟨8064302595356635358565433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10752403460475513811420577 8064302595356635358565433)
    ·
      refine ⟨6048226946517476518924075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8064302595356635358565433 6048226946517476518924075)
      ·
        refine ⟨9072340419776214778386113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6048226946517476518924075 9072340419776214778386113)
        ·
          refine ⟨6804255314832161083789585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9072340419776214778386113 6804255314832161083789585)
          ·
            refine ⟨5103191486124120812842189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6804255314832161083789585 5103191486124120812842189)
            ·
              refine ⟨1913696807296545304815821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5103191486124120812842189 1913696807296545304815821)
              ·
                refine ⟨717636302736204489305933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1913696807296545304815821 717636302736204489305933)
                ·
                  refine ⟨269113613526076683489725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 717636302736204489305933 269113613526076683489725)
                  ·
                    rfl

theorem cell21_1179218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 3, 3, 3].length) (baseStart_1179218 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1179218 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1179218 prefixEnd_1179218 := by exact prefixLift 1179218
  have htrace : WordTrace (prefixWord ++ tailWord_1179218) baseStart_1179218 baseEnd_1179218 := by
    simpa [prefixWord, tailWord_1179218, baseEnd_1179218] using wordTrace_append hprefix tailTrace_1179218
  have hstable : (prefixWord ++ tailWord_1179218).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1179218).length < 2 ^ (prefixWord ++ tailWord_1179218).sum := by decide
  have hdescent : baseEnd_1179218 < baseStart_1179218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1179218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1179322 : List Nat := [3, 1, 1, 1, 2, 5, 3, 5]
def baseStart_1179322 : Nat := 118140960795 + 1179322 * 2 ^ 59
def prefixEnd_1179322 : Nat := 4983230072969 + 3 ^ 40 * 1179322 * 2
def baseEnd_1179322 : Nat := 89712449247665204585393

theorem tailTrace_1179322 : CollatzResearch.WordTrace tailWord_1179322 prefixEnd_1179322 89712449247665204585393 := by
  unfold tailWord_1179322
  simp only [CollatzResearch.WordTrace]
  refine ⟨10753351758381320251867055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28675604689016854004978813 10753351758381320251867055)
  ·
    refine ⟨16130027637571980377800583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10753351758381320251867055 16130027637571980377800583)
    ·
      refine ⟨24195041456357970566700875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16130027637571980377800583 24195041456357970566700875)
      ·
        refine ⟨36292562184536955850051313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24195041456357970566700875 36292562184536955850051313)
        ·
          refine ⟨27219421638402716887538485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36292562184536955850051313 27219421638402716887538485)
          ·
            refine ⟨2551820778600254708206733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27219421638402716887538485 2551820778600254708206733)
            ·
              refine ⟨956932791975095515577525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2551820778600254708206733 956932791975095515577525)
              ·
                refine ⟨89712449247665204585393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 956932791975095515577525 89712449247665204585393)
                ·
                  rfl

theorem cell21_1179322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 3, 5].length) (baseStart_1179322 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1179322 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1179322 prefixEnd_1179322 := by exact prefixLift 1179322
  have htrace : WordTrace (prefixWord ++ tailWord_1179322) baseStart_1179322 baseEnd_1179322 := by
    simpa [prefixWord, tailWord_1179322, baseEnd_1179322] using wordTrace_append hprefix tailTrace_1179322
  have hstable : (prefixWord ++ tailWord_1179322).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1179322).length < 2 ^ (prefixWord ++ tailWord_1179322).sum := by decide
  have hdescent : baseEnd_1179322 < baseStart_1179322 := by decide
  rcases family_descends (prefixWord ++ tailWord_1179322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1179353 : List Nat := [1, 2, 1, 2, 3, 3, 2, 4, 3]
def baseStart_1179353 : Nat := 118140960795 + 1179353 * 2 ^ 59
def prefixEnd_1179353 : Nat := 4983230072969 + 3 ^ 40 * 1179353 * 2
def baseEnd_1179353 : Nat := 269144422365346448739449

theorem tailTrace_1179353 : CollatzResearch.WordTrace tailWord_1179353 prefixEnd_1179353 269144422365346448739449 := by
  unfold tailWord_1179353
  simp only [CollatzResearch.WordTrace]
  refine ⟨43014537696412973301846713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28676358464275315534564475 43014537696412973301846713)
  ·
    refine ⟨32260903272309729976385035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43014537696412973301846713 32260903272309729976385035)
    ·
      refine ⟨48391354908464594964577553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32260903272309729976385035 48391354908464594964577553)
      ·
        refine ⟨36293516181348446223433165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48391354908464594964577553 36293516181348446223433165)
        ·
          refine ⟨13610068568005667333787437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36293516181348446223433165 13610068568005667333787437)
          ·
            refine ⟨5103775713002125250170289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13610068568005667333787437 5103775713002125250170289)
            ·
              refine ⟨3827831784751593937627717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5103775713002125250170289 3827831784751593937627717)
              ·
                refine ⟨717718459640923863305197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3827831784751593937627717 717718459640923863305197)
                ·
                  refine ⟨269144422365346448739449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 717718459640923863305197 269144422365346448739449)
                  ·
                    rfl

theorem cell21_1179353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 4, 3].length) (baseStart_1179353 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1179353 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1179353 prefixEnd_1179353 := by exact prefixLift 1179353
  have htrace : WordTrace (prefixWord ++ tailWord_1179353) baseStart_1179353 baseEnd_1179353 := by
    simpa [prefixWord, tailWord_1179353, baseEnd_1179353] using wordTrace_append hprefix tailTrace_1179353
  have hstable : (prefixWord ++ tailWord_1179353).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1179353).length < 2 ^ (prefixWord ++ tailWord_1179353).sum := by decide
  have hdescent : baseEnd_1179353 < baseStart_1179353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1179353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1179395 : List Nat := [1, 1, 1, 3, 2, 2, 2, 2, 7]
def baseStart_1179395 : Nat := 118140960795 + 1179395 * 2 ^ 59
def prefixEnd_1179395 : Nat := 4983230072969 + 3 ^ 40 * 1179395 * 2
def baseEnd_1179395 : Nat := 269154007337563709039363

theorem tailTrace_1179395 : CollatzResearch.WordTrace tailWord_1179395 prefixEnd_1179395 269154007337563709039363 := by
  unfold tailWord_1179395
  simp only [CollatzResearch.WordTrace]
  refine ⟨43016069562260814474875639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28677379708173876316583759 43016069562260814474875639)
  ·
    refine ⟨64524104343391221712313459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43016069562260814474875639 64524104343391221712313459)
    ·
      refine ⟨96786156515086832568470189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64524104343391221712313459 96786156515086832568470189)
      ·
        refine ⟨36294808693157562213176321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 96786156515086832568470189 36294808693157562213176321)
        ·
          refine ⟨27221106519868171659882241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36294808693157562213176321 27221106519868171659882241)
          ·
            refine ⟨20415829889901128744911681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27221106519868171659882241 20415829889901128744911681)
            ·
              refine ⟨15311872417425846558683761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20415829889901128744911681 15311872417425846558683761)
              ·
                refine ⟨11483904313069384919012821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15311872417425846558683761 11483904313069384919012821)
                ·
                  refine ⟨269154007337563709039363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11483904313069384919012821 269154007337563709039363)
                  ·
                    rfl

theorem cell21_1179395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 2, 7].length) (baseStart_1179395 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1179395 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1179395 prefixEnd_1179395 := by exact prefixLift 1179395
  have htrace : WordTrace (prefixWord ++ tailWord_1179395) baseStart_1179395 baseEnd_1179395 := by
    simpa [prefixWord, tailWord_1179395, baseEnd_1179395] using wordTrace_append hprefix tailTrace_1179395
  have hstable : (prefixWord ++ tailWord_1179395).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1179395).length < 2 ^ (prefixWord ++ tailWord_1179395).sum := by decide
  have hdescent : baseEnd_1179395 < baseStart_1179395 := by decide
  rcases family_descends (prefixWord ++ tailWord_1179395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1179474 : List Nat := [3, 2, 2, 1, 1, 5, 1, 6]
def baseStart_1179474 : Nat := 118140960795 + 1179474 * 2 ^ 59
def prefixEnd_1179474 : Nat := 4983230072969 + 3 ^ 40 * 1179474 * 2
def baseEnd_1179474 : Nat := 89724012071292375740845

theorem tailTrace_1179474 : CollatzResearch.WordTrace tailWord_1179474 prefixEnd_1179474 89724012071292375740845 := by
  unfold tailWord_1179474
  simp only [CollatzResearch.WordTrace]
  refine ⟨10754737732243652741750369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28679300619316407311334317 10754737732243652741750369)
  ·
    refine ⟨8066053299182739556312777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10754737732243652741750369 8066053299182739556312777)
    ·
      refine ⟨6049539974387054667234583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8066053299182739556312777 6049539974387054667234583)
      ·
        refine ⟨9074309961580582000851875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6049539974387054667234583 9074309961580582000851875)
        ·
          refine ⟨13611464942370873001277813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9074309961580582000851875 13611464942370873001277813)
          ·
            refine ⟨1276074838347269343869795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13611464942370873001277813 1276074838347269343869795)
            ·
              refine ⟨1914112257520904015804693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1276074838347269343869795 1914112257520904015804693)
              ·
                refine ⟨89724012071292375740845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1914112257520904015804693 89724012071292375740845)
                ·
                  rfl

theorem cell21_1179474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 1, 6].length) (baseStart_1179474 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1179474 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1179474 prefixEnd_1179474 := by exact prefixLift 1179474
  have htrace : WordTrace (prefixWord ++ tailWord_1179474) baseStart_1179474 baseEnd_1179474 := by
    simpa [prefixWord, tailWord_1179474, baseEnd_1179474] using wordTrace_append hprefix tailTrace_1179474
  have hstable : (prefixWord ++ tailWord_1179474).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1179474).length < 2 ^ (prefixWord ++ tailWord_1179474).sum := by decide
  have hdescent : baseEnd_1179474 < baseStart_1179474 := by decide
  rcases family_descends (prefixWord ++ tailWord_1179474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1179488 : List Nat := [2, 1, 1, 3, 3, 3, 1, 2, 5]
def baseStart_1179488 : Nat := 118140960795 + 1179488 * 2 ^ 59
def prefixEnd_1179488 : Nat := 4983230072969 + 3 ^ 40 * 1179488 * 2
def baseEnd_1179488 : Nat := 269175231204616213989173

theorem tailTrace_1179488 : CollatzResearch.WordTrace tailWord_1179488 prefixEnd_1179488 269175231204616213989173 := by
  unfold tailWord_1179488
  simp only [CollatzResearch.WordTrace]
  refine ⟨21509730775461945679005559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28679641033949260905340745 21509730775461945679005559)
  ·
    refine ⟨32264596163192918518508339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21509730775461945679005559 32264596163192918518508339)
    ·
      refine ⟨48396894244789377777762509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32264596163192918518508339 48396894244789377777762509)
      ·
        refine ⟨18148835341796016666660941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48396894244789377777762509 18148835341796016666660941)
        ·
          refine ⟨6805813253173506249997853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18148835341796016666660941 6805813253173506249997853)
          ·
            refine ⟨2552179969940064843749195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6805813253173506249997853 2552179969940064843749195)
            ·
              refine ⟨3828269954910097265623793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2552179969940064843749195 3828269954910097265623793)
              ·
                refine ⟨2871202466182572949217845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3828269954910097265623793 2871202466182572949217845)
                ·
                  refine ⟨269175231204616213989173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2871202466182572949217845 269175231204616213989173)
                  ·
                    rfl

theorem cell21_1179488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 2, 5].length) (baseStart_1179488 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1179488 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1179488 prefixEnd_1179488 := by exact prefixLift 1179488
  have htrace : WordTrace (prefixWord ++ tailWord_1179488) baseStart_1179488 baseEnd_1179488 := by
    simpa [prefixWord, tailWord_1179488, baseEnd_1179488] using wordTrace_append hprefix tailTrace_1179488
  have hstable : (prefixWord ++ tailWord_1179488).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1179488).length < 2 ^ (prefixWord ++ tailWord_1179488).sum := by decide
  have hdescent : baseEnd_1179488 < baseStart_1179488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1179488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1179505 : List Nat := [1, 2, 2, 2, 1, 3, 4, 3, 3]
def baseStart_1179505 : Nat := 118140960795 + 1179505 * 2 ^ 59
def prefixEnd_1179505 : Nat := 4983230072969 + 3 ^ 40 * 1179505 * 2
def baseEnd_1179505 : Nat := 269179110836227962205805

theorem tailTrace_1179505 : CollatzResearch.WordTrace tailWord_1179505 prefixEnd_1179505 269179110836227962205805 := by
  unfold tailWord_1179505
  simp only [CollatzResearch.WordTrace]
  refine ⟨43020081591862303261379969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28680054394574868840919979 43020081591862303261379969)
  ·
    refine ⟨32265061193896727446034977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43020081591862303261379969 32265061193896727446034977)
    ·
      refine ⟨24198795895422545584526233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32265061193896727446034977 24198795895422545584526233)
      ·
        refine ⟨18149096921566909188394675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24198795895422545584526233 18149096921566909188394675)
        ·
          refine ⟨27223645382350363782592013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18149096921566909188394675 27223645382350363782592013)
          ·
            refine ⟨10208867018381386418472005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27223645382350363782592013 10208867018381386418472005)
            ·
              refine ⟨1914162565946509953463501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10208867018381386418472005 1914162565946509953463501)
              ·
                refine ⟨717810962229941232548813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1914162565946509953463501 717810962229941232548813)
                ·
                  refine ⟨269179110836227962205805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 717810962229941232548813 269179110836227962205805)
                  ·
                    rfl

theorem cell21_1179505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 4, 3, 3].length) (baseStart_1179505 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1179505 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1179505 prefixEnd_1179505 := by exact prefixLift 1179505
  have htrace : WordTrace (prefixWord ++ tailWord_1179505) baseStart_1179505 baseEnd_1179505 := by
    simpa [prefixWord, tailWord_1179505, baseEnd_1179505] using wordTrace_append hprefix tailTrace_1179505
  have hstable : (prefixWord ++ tailWord_1179505).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1179505).length < 2 ^ (prefixWord ++ tailWord_1179505).sum := by decide
  have hdescent : baseEnd_1179505 < baseStart_1179505 := by decide
  rcases family_descends (prefixWord ++ tailWord_1179505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1179542 : List Nat := [5, 3, 1, 1, 3, 1, 2, 5]
def baseStart_1179542 : Nat := 118140960795 + 1179542 * 2 ^ 59
def prefixEnd_1179542 : Nat := 4983230072969 + 3 ^ 40 * 1179542 * 2
def baseEnd_1179542 : Nat := 89729184913441373363021

theorem tailTrace_1179542 : CollatzResearch.WordTrace tailWord_1179542 prefixEnd_1179542 89729184913441373363021 := by
  unfold tailWord_1179542
  simp only [CollatzResearch.WordTrace]
  refine ⟨2688839443295516161279805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28680954061818839053651253 2688839443295516161279805)
  ·
    refine ⟨1008314791235818560479927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2688839443295516161279805 1008314791235818560479927)
    ·
      refine ⟨1512472186853727840719891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1008314791235818560479927 1512472186853727840719891)
      ·
        refine ⟨2268708280280591761079837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1512472186853727840719891 2268708280280591761079837)
        ·
          refine ⟨850765605105221910404939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2268708280280591761079837 850765605105221910404939)
          ·
            refine ⟨1276148407657832865607409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 850765605105221910404939 1276148407657832865607409)
            ·
              refine ⟨957111305743374649205557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1276148407657832865607409 957111305743374649205557)
              ·
                refine ⟨89729184913441373363021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 957111305743374649205557 89729184913441373363021)
                ·
                  rfl

theorem cell21_1179542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 2, 5].length) (baseStart_1179542 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1179542 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1179542 prefixEnd_1179542 := by exact prefixLift 1179542
  have htrace : WordTrace (prefixWord ++ tailWord_1179542) baseStart_1179542 baseEnd_1179542 := by
    simpa [prefixWord, tailWord_1179542, baseEnd_1179542] using wordTrace_append hprefix tailTrace_1179542
  have hstable : (prefixWord ++ tailWord_1179542).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1179542).length < 2 ^ (prefixWord ++ tailWord_1179542).sum := by decide
  have hdescent : baseEnd_1179542 < baseStart_1179542 := by decide
  rcases family_descends (prefixWord ++ tailWord_1179542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1179581 : List Nat := [1, 4, 1, 2, 3, 3, 1, 1, 5]
def baseStart_1179581 : Nat := 118140960795 + 1179581 * 2 ^ 59
def prefixEnd_1179581 : Nat := 4983230072969 + 3 ^ 40 * 1179581 * 2
def baseEnd_1179581 : Nat := 269196455071668718938983

theorem tailTrace_1179581 : CollatzResearch.WordTrace tailWord_1179581 prefixEnd_1179581 269196455071668718938983 := by
  unfold tailWord_1179581
  simp only [CollatzResearch.WordTrace]
  refine ⟨43022853539586968241146597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28681902359724645494097731 43022853539586968241146597)
  ·
    refine ⟨8066785038672556545214987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43022853539586968241146597 8066785038672556545214987)
    ·
      refine ⟨12100177558008834817822481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8066785038672556545214987 12100177558008834817822481)
      ·
        refine ⟨9075133168506626113366861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12100177558008834817822481 9075133168506626113366861)
        ·
          refine ⟨3403174938189984792512573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9075133168506626113366861 3403174938189984792512573)
          ·
            refine ⟨1276190601821244297192215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3403174938189984792512573 1276190601821244297192215)
            ·
              refine ⟨1914285902731866445788323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1276190601821244297192215 1914285902731866445788323)
              ·
                refine ⟨2871428854097799668682485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1914285902731866445788323 2871428854097799668682485)
                ·
                  refine ⟨269196455071668718938983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2871428854097799668682485 269196455071668718938983)
                  ·
                    rfl

theorem cell21_1179581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 1, 1, 5].length) (baseStart_1179581 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1179581 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1179581 prefixEnd_1179581 := by exact prefixLift 1179581
  have htrace : WordTrace (prefixWord ++ tailWord_1179581) baseStart_1179581 baseEnd_1179581 := by
    simpa [prefixWord, tailWord_1179581, baseEnd_1179581] using wordTrace_append hprefix tailTrace_1179581
  have hstable : (prefixWord ++ tailWord_1179581).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1179581).length < 2 ^ (prefixWord ++ tailWord_1179581).sum := by decide
  have hdescent : baseEnd_1179581 < baseStart_1179581 := by decide
  rcases family_descends (prefixWord ++ tailWord_1179581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1179629 : List Nat := [1, 5, 1, 4, 1, 1, 2, 2, 4]
def baseStart_1179629 : Nat := 118140960795 + 1179629 * 2 ^ 59
def prefixEnd_1179629 : Nat := 4983230072969 + 3 ^ 40 * 1179629 * 2
def baseEnd_1179629 : Nat := 269207409325631302138885

theorem tailTrace_1179629 : CollatzResearch.WordTrace tailWord_1179629 prefixEnd_1179629 269207409325631302138885 := by
  unfold tailWord_1179629
  simp only [CollatzResearch.WordTrace]
  refine ⟨43024604243413072438893941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28683069495608714959262627 43024604243413072438893941)
  ·
    refine ⟨4033556647819975541146307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 43024604243413072438893941 4033556647819975541146307)
    ·
      refine ⟨6050334971729963311719461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4033556647819975541146307 6050334971729963311719461)
      ·
        refine ⟨1134437807199368120947399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6050334971729963311719461 1134437807199368120947399)
        ·
          refine ⟨1701656710799052181421099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1134437807199368120947399 1701656710799052181421099)
          ·
            refine ⟨2552485066198578272131649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1701656710799052181421099 2552485066198578272131649)
            ·
              refine ⟨1914363799648933704098737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2552485066198578272131649 1914363799648933704098737)
              ·
                refine ⟨1435772849736700278074053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1914363799648933704098737 1435772849736700278074053)
                ·
                  refine ⟨269207409325631302138885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1435772849736700278074053 269207409325631302138885)
                  ·
                    rfl

theorem cell21_1179629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 2, 2, 4].length) (baseStart_1179629 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1179629 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1179629 prefixEnd_1179629 := by exact prefixLift 1179629
  have htrace : WordTrace (prefixWord ++ tailWord_1179629) baseStart_1179629 baseEnd_1179629 := by
    simpa [prefixWord, tailWord_1179629, baseEnd_1179629] using wordTrace_append hprefix tailTrace_1179629
  have hstable : (prefixWord ++ tailWord_1179629).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1179629).length < 2 ^ (prefixWord ++ tailWord_1179629).sum := by decide
  have hdescent : baseEnd_1179629 < baseStart_1179629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1179629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1179688 : List Nat := [2, 1, 5, 3, 1, 1, 1, 1, 6]
def baseStart_1179688 : Nat := 118140960795 + 1179688 * 2 ^ 59
def prefixEnd_1179688 : Nat := 4983230072969 + 3 ^ 40 * 1179688 * 2
def baseEnd_1179688 : Nat := 269220873929460310655431

theorem tailTrace_1179688 : CollatzResearch.WordTrace tailWord_1179688 prefixEnd_1179688 269220873929460310655431 := by
  unfold tailWord_1179688
  simp only [CollatzResearch.WordTrace]
  refine ⟨21513378075099662757645859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28684504100132883676861145 21513378075099662757645859)
  ·
    refine ⟨32270067112649494136468789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21513378075099662757645859 32270067112649494136468789)
    ·
      refine ⟨3025318791810890075293949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 32270067112649494136468789 3025318791810890075293949)
      ·
        refine ⟨1134494546929083778235231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3025318791810890075293949 1134494546929083778235231)
        ·
          refine ⟨1701741820393625667352847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1134494546929083778235231 1701741820393625667352847)
          ·
            refine ⟨2552612730590438501029271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1701741820393625667352847 2552612730590438501029271)
            ·
              refine ⟨3828919095885657751543907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2552612730590438501029271 3828919095885657751543907)
              ·
                refine ⟨5743378643828486627315861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3828919095885657751543907 5743378643828486627315861)
                ·
                  refine ⟨269220873929460310655431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5743378643828486627315861 269220873929460310655431)
                  ·
                    rfl

theorem cell21_1179688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 1, 6].length) (baseStart_1179688 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1179688 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1179688 prefixEnd_1179688 := by exact prefixLift 1179688
  have htrace : WordTrace (prefixWord ++ tailWord_1179688) baseStart_1179688 baseEnd_1179688 := by
    simpa [prefixWord, tailWord_1179688, baseEnd_1179688] using wordTrace_append hprefix tailTrace_1179688
  have hstable : (prefixWord ++ tailWord_1179688).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1179688).length < 2 ^ (prefixWord ++ tailWord_1179688).sum := by decide
  have hdescent : baseEnd_1179688 < baseStart_1179688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1179688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1179699 : List Nat := [1, 1, 1, 2, 4, 1, 3, 3, 5]
def baseStart_1179699 : Nat := 118140960795 + 1179699 * 2 ^ 59
def prefixEnd_1179699 : Nat := 4983230072969 + 3 ^ 40 * 1179699 * 2
def baseEnd_1179699 : Nat := 269223384279326735972075

theorem tailTrace_1179699 : CollatzResearch.WordTrace tailWord_1179699 prefixEnd_1179699 269223384279326735972075 := by
  unfold tailWord_1179699
  simp only [CollatzResearch.WordTrace]
  refine ⟨43027157353159474393942151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28684771568772982929294767 43027157353159474393942151)
  ·
    refine ⟨64540736029739211590913227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43027157353159474393942151 64540736029739211590913227)
    ·
      refine ⟨96811104044608817386369841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64540736029739211590913227 96811104044608817386369841)
      ·
        refine ⟨72608328033456613039777381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 96811104044608817386369841 72608328033456613039777381)
        ·
          refine ⟨13614061506273114944958259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 72608328033456613039777381 13614061506273114944958259)
          ·
            refine ⟨20421092259409672417437389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13614061506273114944958259 20421092259409672417437389)
            ·
              refine ⟨7657909597278627156539021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20421092259409672417437389 7657909597278627156539021)
              ·
                refine ⟨2871716098979485183702133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7657909597278627156539021 2871716098979485183702133)
                ·
                  refine ⟨269223384279326735972075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2871716098979485183702133 269223384279326735972075)
                  ·
                    rfl

theorem cell21_1179699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 3, 5].length) (baseStart_1179699 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1179699 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1179699 prefixEnd_1179699 := by exact prefixLift 1179699
  have htrace : WordTrace (prefixWord ++ tailWord_1179699) baseStart_1179699 baseEnd_1179699 := by
    simpa [prefixWord, tailWord_1179699, baseEnd_1179699] using wordTrace_append hprefix tailTrace_1179699
  have hstable : (prefixWord ++ tailWord_1179699).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1179699).length < 2 ^ (prefixWord ++ tailWord_1179699).sum := by decide
  have hdescent : baseEnd_1179699 < baseStart_1179699 := by decide
  rcases family_descends (prefixWord ++ tailWord_1179699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1179733 : List Nat := [1, 3, 2, 2, 1, 3, 3, 3, 3]
def baseStart_1179733 : Nat := 118140960795 + 1179733 * 2 ^ 59
def prefixEnd_1179733 : Nat := 4983230072969 + 3 ^ 40 * 1179733 * 2
def baseEnd_1179733 : Nat := 269231143542550232405339

theorem tailTrace_1179733 : CollatzResearch.WordTrace tailWord_1179733 prefixEnd_1179733 269231143542550232405339 := by
  unfold tailWord_1179733
  simp only [CollatzResearch.WordTrace]
  refine ⟨43028397435036298200679853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28685598290024198800453235 43028397435036298200679853)
  ·
    refine ⟨16135649038138611825254945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43028397435036298200679853 16135649038138611825254945)
    ·
      refine ⟨12101736778603958868941209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16135649038138611825254945 12101736778603958868941209)
      ·
        refine ⟨9076302583952969151705907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12101736778603958868941209 9076302583952969151705907)
        ·
          refine ⟨13614453875929453727558861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9076302583952969151705907 13614453875929453727558861)
          ·
            refine ⟨5105420203473545147834573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13614453875929453727558861 5105420203473545147834573)
            ·
              refine ⟨1914532576302579430437965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5105420203473545147834573 1914532576302579430437965)
              ·
                refine ⟨717949716113467286414237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1914532576302579430437965 717949716113467286414237)
                ·
                  refine ⟨269231143542550232405339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 717949716113467286414237 269231143542550232405339)
                  ·
                    rfl

theorem cell21_1179733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 3, 3, 3].length) (baseStart_1179733 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1179733 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1179733 prefixEnd_1179733 := by exact prefixLift 1179733
  have htrace : WordTrace (prefixWord ++ tailWord_1179733) baseStart_1179733 baseEnd_1179733 := by
    simpa [prefixWord, tailWord_1179733, baseEnd_1179733] using wordTrace_append hprefix tailTrace_1179733
  have hstable : (prefixWord ++ tailWord_1179733).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1179733).length < 2 ^ (prefixWord ++ tailWord_1179733).sum := by decide
  have hdescent : baseEnd_1179733 < baseStart_1179733 := by decide
  rcases family_descends (prefixWord ++ tailWord_1179733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1179744 : List Nat := [2, 1, 1, 3, 2, 3, 9]
def baseStart_1179744 : Nat := 118140960795 + 1179744 * 2 ^ 59
def prefixEnd_1179744 : Nat := 4983230072969 + 3 ^ 40 * 1179744 * 2
def baseEnd_1179744 : Nat := 29914850432490739746887

theorem tailTrace_1179744 : CollatzResearch.WordTrace tailWord_1179744 prefixEnd_1179744 29914850432490739746887 := by
  unfold tailWord_1179744
  simp only [CollatzResearch.WordTrace]
  refine ⟨21514399318998223539665143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28685865758664298052886857 21514399318998223539665143)
  ·
    refine ⟨32271598978497335309497715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21514399318998223539665143 32271598978497335309497715)
    ·
      refine ⟨48407398467746002964246573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32271598978497335309497715 48407398467746002964246573)
      ·
        refine ⟨18152774425404751111592465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48407398467746002964246573 18152774425404751111592465)
        ·
          refine ⟨13614580819053563333694349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18152774425404751111592465 13614580819053563333694349)
          ·
            refine ⟨5105467807145086250135381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13614580819053563333694349 5105467807145086250135381)
            ·
              refine ⟨29914850432490739746887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5105467807145086250135381 29914850432490739746887)
              ·
                rfl

theorem cell21_1179744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 9].length) (baseStart_1179744 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1179744 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1179744 prefixEnd_1179744 := by exact prefixLift 1179744
  have htrace : WordTrace (prefixWord ++ tailWord_1179744) baseStart_1179744 baseEnd_1179744 := by
    simpa [prefixWord, tailWord_1179744, baseEnd_1179744] using wordTrace_append hprefix tailTrace_1179744
  have hstable : (prefixWord ++ tailWord_1179744).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1179744).length < 2 ^ (prefixWord ++ tailWord_1179744).sum := by decide
  have hdescent : baseEnd_1179744 < baseStart_1179744 := by decide
  rcases family_descends (prefixWord ++ tailWord_1179744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1179792 : List Nat := [2, 1, 1, 1, 1, 1, 6, 5, 3]
def baseStart_1179792 : Nat := 118140960795 + 1179792 * 2 ^ 59
def prefixEnd_1179792 : Nat := 4983230072969 + 3 ^ 40 * 1179792 * 2
def baseEnd_1179792 : Nat := 269244608146379240921885

theorem tailTrace_1179792 : CollatzResearch.WordTrace tailWord_1179792 prefixEnd_1179792 269244608146379240921885 := by
  unfold tailWord_1179792
  simp only [CollatzResearch.WordTrace]
  refine ⟨21515274670911275638538815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28687032894548367518051753 21515274670911275638538815)
  ·
    refine ⟨32272912006366913457808223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21515274670911275638538815 32272912006366913457808223)
    ·
      refine ⟨48409368009550370186712335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32272912006366913457808223 48409368009550370186712335)
      ·
        refine ⟨72614052014325555280068503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48409368009550370186712335 72614052014325555280068503)
        ·
          refine ⟨108921078021488332920102755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72614052014325555280068503 108921078021488332920102755)
          ·
            refine ⟨163381617032232499380154133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108921078021488332920102755 163381617032232499380154133)
            ·
              refine ⟨7658513298385898408444725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 163381617032232499380154133 7658513298385898408444725)
              ·
                refine ⟨717985621723677975791693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7658513298385898408444725 717985621723677975791693)
                ·
                  refine ⟨269244608146379240921885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 717985621723677975791693 269244608146379240921885)
                  ·
                    rfl

theorem cell21_1179792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 5, 3].length) (baseStart_1179792 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1179792 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1179792 prefixEnd_1179792 := by exact prefixLift 1179792
  have htrace : WordTrace (prefixWord ++ tailWord_1179792) baseStart_1179792 baseEnd_1179792 := by
    simpa [prefixWord, tailWord_1179792, baseEnd_1179792] using wordTrace_append hprefix tailTrace_1179792
  have hstable : (prefixWord ++ tailWord_1179792).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1179792).length < 2 ^ (prefixWord ++ tailWord_1179792).sum := by decide
  have hdescent : baseEnd_1179792 < baseStart_1179792 := by decide
  rcases family_descends (prefixWord ++ tailWord_1179792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1179809 : List Nat := [1, 2, 3, 3, 1, 3, 1, 4, 3]
def baseStart_1179809 : Nat := 118140960795 + 1179809 * 2 ^ 59
def prefixEnd_1179809 : Nat := 4983230072969 + 3 ^ 40 * 1179809 * 2
def baseEnd_1179809 : Nat := 269248487777990989138517

theorem tailTrace_1179809 : CollatzResearch.WordTrace tailWord_1179809 prefixEnd_1179809 269248487777990989138517 := by
  unfold tailWord_1179809
  simp only [CollatzResearch.WordTrace]
  refine ⟨43031169382760963180446481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28687446255173975453630987 43031169382760963180446481)
  ·
    refine ⟨32273377037070722385334861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43031169382760963180446481 32273377037070722385334861)
    ·
      refine ⟨12102516388901520894500573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32273377037070722385334861 12102516388901520894500573)
      ·
        refine ⟨4538443645838070335437715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12102516388901520894500573 4538443645838070335437715)
        ·
          refine ⟨6807665468757105503156573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4538443645838070335437715 6807665468757105503156573)
          ·
            refine ⟨2552874550783914563683715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6807665468757105503156573 2552874550783914563683715)
            ·
              refine ⟨3829311826175871845525573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2552874550783914563683715 3829311826175871845525573)
              ·
                refine ⟨717995967407975971036045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3829311826175871845525573 717995967407975971036045)
                ·
                  refine ⟨269248487777990989138517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 717995967407975971036045 269248487777990989138517)
                  ·
                    rfl

theorem cell21_1179809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 4, 3].length) (baseStart_1179809 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1179809 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1179809 prefixEnd_1179809 := by exact prefixLift 1179809
  have htrace : WordTrace (prefixWord ++ tailWord_1179809) baseStart_1179809 baseEnd_1179809 := by
    simpa [prefixWord, tailWord_1179809, baseEnd_1179809] using wordTrace_append hprefix tailTrace_1179809
  have hstable : (prefixWord ++ tailWord_1179809).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1179809).length < 2 ^ (prefixWord ++ tailWord_1179809).sum := by decide
  have hdescent : baseEnd_1179809 < baseStart_1179809 := by decide
  rcases family_descends (prefixWord ++ tailWord_1179809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1179933 : List Nat := [1, 4, 2, 3, 2, 2, 2, 1, 4]
def baseStart_1179933 : Nat := 118140960795 + 1179933 * 2 ^ 59
def prefixEnd_1179933 : Nat := 4983230072969 + 3 ^ 40 * 1179933 * 2
def baseEnd_1179933 : Nat := 269276786267394329071597

theorem tailTrace_1179933 : CollatzResearch.WordTrace tailWord_1179933 prefixEnd_1179933 269276786267394329071597 := by
  unfold tailWord_1179933
  simp only [CollatzResearch.WordTrace]
  refine ⟨43035692034311732357960453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28690461356207821571973635 43035692034311732357960453)
  ·
    refine ⟨8069192256433449817117585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43035692034311732357960453 8069192256433449817117585)
    ·
      refine ⟨6051894192325087362838189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8069192256433449817117585 6051894192325087362838189)
      ·
        refine ⟨2269460322121907761064321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6051894192325087362838189 2269460322121907761064321)
        ·
          refine ⟨1702095241591430820798241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2269460322121907761064321 1702095241591430820798241)
          ·
            refine ⟨1276571431193573115598681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1702095241591430820798241 1276571431193573115598681)
            ·
              refine ⟨957428573395179836699011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1276571431193573115598681 957428573395179836699011)
              ·
                refine ⟨1436142860092769755048517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 957428573395179836699011 1436142860092769755048517)
                ·
                  refine ⟨269276786267394329071597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1436142860092769755048517 269276786267394329071597)
                  ·
                    rfl

theorem cell21_1179933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 2, 1, 4].length) (baseStart_1179933 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1179933 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1179933 prefixEnd_1179933 := by exact prefixLift 1179933
  have htrace : WordTrace (prefixWord ++ tailWord_1179933) baseStart_1179933 baseEnd_1179933 := by
    simpa [prefixWord, tailWord_1179933, baseEnd_1179933] using wordTrace_append hprefix tailTrace_1179933
  have hstable : (prefixWord ++ tailWord_1179933).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1179933).length < 2 ^ (prefixWord ++ tailWord_1179933).sum := by decide
  have hdescent : baseEnd_1179933 < baseStart_1179933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1179933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180003 : List Nat := [1, 1, 1, 5, 2, 1, 3, 2, 5]
def baseStart_1180003 : Nat := 118140960795 + 1180003 * 2 ^ 59
def prefixEnd_1180003 : Nat := 4983230072969 + 3 ^ 40 * 1180003 * 2
def baseEnd_1180003 : Nat := 269292761221089762904787

theorem tailTrace_1180003 : CollatzResearch.WordTrace tailWord_1180003 prefixEnd_1180003 269292761221089762904787 := by
  unfold tailWord_1180003
  simp only [CollatzResearch.WordTrace]
  refine ⟨43038245144058134313008663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28692163429372089542005775 43038245144058134313008663)
  ·
    refine ⟨64557367716087201469512995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43038245144058134313008663 64557367716087201469512995)
    ·
      refine ⟨96836051574130802204269493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64557367716087201469512995 96836051574130802204269493)
      ·
        refine ⟨9078379835074762706650265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 96836051574130802204269493 9078379835074762706650265)
        ·
          refine ⟨6808784876306072029987699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9078379835074762706650265 6808784876306072029987699)
          ·
            refine ⟨10213177314459108044981549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6808784876306072029987699 10213177314459108044981549)
            ·
              refine ⟨3829941492922165516868081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10213177314459108044981549 3829941492922165516868081)
              ·
                refine ⟨2872456119691624137651061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3829941492922165516868081 2872456119691624137651061)
                ·
                  refine ⟨269292761221089762904787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2872456119691624137651061 269292761221089762904787)
                  ·
                    rfl

theorem cell21_1180003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 2, 5].length) (baseStart_1180003 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1180003 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1180003 prefixEnd_1180003 := by exact prefixLift 1180003
  have htrace : WordTrace (prefixWord ++ tailWord_1180003) baseStart_1180003 baseEnd_1180003 := by
    simpa [prefixWord, tailWord_1180003, baseEnd_1180003] using wordTrace_append hprefix tailTrace_1180003
  have hstable : (prefixWord ++ tailWord_1180003).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180003).length < 2 ^ (prefixWord ++ tailWord_1180003).sum := by decide
  have hdescent : baseEnd_1180003 < baseStart_1180003 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180017 : List Nat := [1, 2, 2, 2, 1, 2, 1, 4, 6]
def baseStart_1180017 : Nat := 118140960795 + 1180017 * 2 ^ 59
def prefixEnd_1180017 : Nat := 4983230072969 + 3 ^ 40 * 1180017 * 2
def baseEnd_1180017 : Nat := 269295956211828849671425

theorem tailTrace_1180017 : CollatzResearch.WordTrace tailWord_1180017 prefixEnd_1180017 269295956211828849671425 := by
  unfold tailWord_1180017
  simp only [CollatzResearch.WordTrace]
  refine ⟨43038755766007414704018305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28692503844004943136012203 43038755766007414704018305)
  ·
    refine ⟨32279066824505561028013729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43038755766007414704018305 32279066824505561028013729)
    ·
      refine ⟨24209300118379170771010297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32279066824505561028013729 24209300118379170771010297)
      ·
        refine ⟨18156975088784378078257723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24209300118379170771010297 18156975088784378078257723)
        ·
          refine ⟨27235462633176567117386585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18156975088784378078257723 27235462633176567117386585)
          ·
            refine ⟨20426596974882425338039939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27235462633176567117386585 20426596974882425338039939)
            ·
              refine ⟨30639895462323638007059909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20426596974882425338039939 30639895462323638007059909)
              ·
                refine ⟨5744980399185682126323733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30639895462323638007059909 5744980399185682126323733)
                ·
                  refine ⟨269295956211828849671425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5744980399185682126323733 269295956211828849671425)
                  ·
                    rfl

theorem cell21_1180017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 4, 6].length) (baseStart_1180017 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1180017 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1180017 prefixEnd_1180017 := by exact prefixLift 1180017
  have htrace : WordTrace (prefixWord ++ tailWord_1180017) baseStart_1180017 baseEnd_1180017 := by
    simpa [prefixWord, tailWord_1180017, baseEnd_1180017] using wordTrace_append hprefix tailTrace_1180017
  have hstable : (prefixWord ++ tailWord_1180017).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180017).length < 2 ^ (prefixWord ++ tailWord_1180017).sum := by decide
  have hdescent : baseEnd_1180017 < baseStart_1180017 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180189 : List Nat := [1, 4, 2, 2, 1, 3, 2, 3, 3]
def baseStart_1180189 : Nat := 118140960795 + 1180189 * 2 ^ 59
def prefixEnd_1180189 : Nat := 4983230072969 + 3 ^ 40 * 1180189 * 2
def baseEnd_1180189 : Nat := 269335208955194772804407

theorem tailTrace_1180189 : CollatzResearch.WordTrace tailWord_1180189 prefixEnd_1180189 269335208955194772804407 := by
  unfold tailWord_1180189
  simp only [CollatzResearch.WordTrace]
  refine ⟨43045029121384288079279621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28696686080922858719519747 43045029121384288079279621)
  ·
    refine ⟨8070942960259554014864929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43045029121384288079279621 8070942960259554014864929)
    ·
      refine ⟨6053207220194665511148697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8070942960259554014864929 6053207220194665511148697)
      ·
        refine ⟨4539905415145999133361523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6053207220194665511148697 4539905415145999133361523)
        ·
          refine ⟨6809858122718998700042285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4539905415145999133361523 6809858122718998700042285)
          ·
            refine ⟨2553696796019624512515857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6809858122718998700042285 2553696796019624512515857)
            ·
              refine ⟨1915272597014718384386893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2553696796019624512515857 1915272597014718384386893)
              ·
                refine ⟨718227223880519394145085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1915272597014718384386893 718227223880519394145085)
                ·
                  refine ⟨269335208955194772804407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 718227223880519394145085 269335208955194772804407)
                  ·
                    rfl

theorem cell21_1180189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 2, 3, 3].length) (baseStart_1180189 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1180189 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1180189 prefixEnd_1180189 := by exact prefixLift 1180189
  have htrace : WordTrace (prefixWord ++ tailWord_1180189) baseStart_1180189 baseEnd_1180189 := by
    simpa [prefixWord, tailWord_1180189, baseEnd_1180189] using wordTrace_append hprefix tailTrace_1180189
  have hstable : (prefixWord ++ tailWord_1180189).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180189).length < 2 ^ (prefixWord ++ tailWord_1180189).sum := by decide
  have hdescent : baseEnd_1180189 < baseStart_1180189 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180231 : List Nat := [1, 1, 4, 1, 4, 1, 2, 2, 5]
def baseStart_1180231 : Nat := 118140960795 + 1180231 * 2 ^ 59
def prefixEnd_1180231 : Nat := 4983230072969 + 3 ^ 40 * 1180231 * 2
def baseEnd_1180231 : Nat := 269344793927412033104321

theorem tailTrace_1180231 : CollatzResearch.WordTrace tailWord_1180231 prefixEnd_1180231 269344793927412033104321 := by
  unfold tailWord_1180231
  simp only [CollatzResearch.WordTrace]
  refine ⟨43046560987232129252308547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28697707324821419501539031 43046560987232129252308547)
  ·
    refine ⟨64569841480848193878462821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43046560987232129252308547 64569841480848193878462821)
    ·
      refine ⟨12106845277659036352211779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64569841480848193878462821 12106845277659036352211779)
      ·
        refine ⟨18160267916488554528317669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12106845277659036352211779 18160267916488554528317669)
        ·
          refine ⟨3405050234341603974059563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18160267916488554528317669 3405050234341603974059563)
          ·
            refine ⟨5107575351512405961089345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3405050234341603974059563 5107575351512405961089345)
            ·
              refine ⟨3830681513634304470817009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5107575351512405961089345 3830681513634304470817009)
              ·
                refine ⟨2873011135225728353112757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3830681513634304470817009 2873011135225728353112757)
                ·
                  refine ⟨269344793927412033104321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2873011135225728353112757 269344793927412033104321)
                  ·
                    rfl

theorem cell21_1180231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 2, 5].length) (baseStart_1180231 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1180231 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1180231 prefixEnd_1180231 := by exact prefixLift 1180231
  have htrace : WordTrace (prefixWord ++ tailWord_1180231) baseStart_1180231 baseEnd_1180231 := by
    simpa [prefixWord, tailWord_1180231, baseEnd_1180231] using wordTrace_append hprefix tailTrace_1180231
  have hstable : (prefixWord ++ tailWord_1180231).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180231).length < 2 ^ (prefixWord ++ tailWord_1180231).sum := by decide
  have hdescent : baseEnd_1180231 < baseStart_1180231 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180245 : List Nat := [1, 3, 2, 2, 1, 1, 3, 2, 6]
def baseStart_1180245 : Nat := 118140960795 + 1180245 * 2 ^ 59
def prefixEnd_1180245 : Nat := 4983230072969 + 3 ^ 40 * 1180245 * 2
def baseEnd_1180245 : Nat := 269347988918151119870959

theorem tailTrace_1180245 : CollatzResearch.WordTrace tailWord_1180245 prefixEnd_1180245 269347988918151119870959 := by
  unfold tailWord_1180245
  simp only [CollatzResearch.WordTrace]
  refine ⟨43047071609181409643318189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28698047739454273095545459 43047071609181409643318189)
  ·
    refine ⟨16142651853443028616244321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43047071609181409643318189 16142651853443028616244321)
    ·
      refine ⟨12106988890082271462183241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16142651853443028616244321 12106988890082271462183241)
      ·
        refine ⟨9080241667561703596637431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12106988890082271462183241 9080241667561703596637431)
        ·
          refine ⟨13620362501342555394956147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9080241667561703596637431 13620362501342555394956147)
          ·
            refine ⟨20430543752013833092434221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13620362501342555394956147 20430543752013833092434221)
            ·
              refine ⟨7661453907005187409662833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20430543752013833092434221 7661453907005187409662833)
              ·
                refine ⟨5746090430253890557247125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7661453907005187409662833 5746090430253890557247125)
                ·
                  refine ⟨269347988918151119870959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5746090430253890557247125 269347988918151119870959)
                  ·
                    rfl

theorem cell21_1180245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 2, 6].length) (baseStart_1180245 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1180245 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1180245 prefixEnd_1180245 := by exact prefixLift 1180245
  have htrace : WordTrace (prefixWord ++ tailWord_1180245) baseStart_1180245 baseEnd_1180245 := by
    simpa [prefixWord, tailWord_1180245, baseEnd_1180245] using wordTrace_append hprefix tailTrace_1180245
  have hstable : (prefixWord ++ tailWord_1180245).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180245).length < 2 ^ (prefixWord ++ tailWord_1180245).sum := by decide
  have hdescent : baseEnd_1180245 < baseStart_1180245 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180248 : List Nat := [2, 1, 2, 2, 1, 2, 5, 3, 3]
def baseStart_1180248 : Nat := 118140960795 + 1180248 * 2 ^ 59
def prefixEnd_1180248 : Nat := 4983230072969 + 3 ^ 40 * 1180248 * 2
def baseEnd_1180248 : Nat := 269348673559023781320953

theorem tailTrace_1180248 : CollatzResearch.WordTrace tailWord_1180248 prefixEnd_1180248 269348673559023781320953 := by
  unfold tailWord_1180248
  simp only [CollatzResearch.WordTrace]
  refine ⟨21523590514085270577838699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28698120685447027437118265 21523590514085270577838699)
  ·
    refine ⟨32285385771127905866758049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21523590514085270577838699 32285385771127905866758049)
    ·
      refine ⟨24214039328345929400068537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32285385771127905866758049 24214039328345929400068537)
      ·
        refine ⟨18160529496259447050051403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24214039328345929400068537 18160529496259447050051403)
        ·
          refine ⟨27240794244389170575077105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18160529496259447050051403 27240794244389170575077105)
          ·
            refine ⟨20430595683291877931307829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27240794244389170575077105 20430595683291877931307829)
            ·
              refine ⟨1915368345308613556060109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20430595683291877931307829 1915368345308613556060109)
              ·
                refine ⟨718263129490730083522541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1915368345308613556060109 718263129490730083522541)
                ·
                  refine ⟨269348673559023781320953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 718263129490730083522541 269348673559023781320953)
                  ·
                    rfl

theorem cell21_1180248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 5, 3, 3].length) (baseStart_1180248 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1180248 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1180248 prefixEnd_1180248 := by exact prefixLift 1180248
  have htrace : WordTrace (prefixWord ++ tailWord_1180248) baseStart_1180248 baseEnd_1180248 := by
    simpa [prefixWord, tailWord_1180248, baseEnd_1180248] using wordTrace_append hprefix tailTrace_1180248
  have hstable : (prefixWord ++ tailWord_1180248).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180248).length < 2 ^ (prefixWord ++ tailWord_1180248).sum := by decide
  have hdescent : baseEnd_1180248 < baseStart_1180248 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180324 : List Nat := [2, 3, 1, 2, 2, 1, 3, 4, 3]
def baseStart_1180324 : Nat := 118140960795 + 1180324 * 2 ^ 59
def prefixEnd_1180324 : Nat := 4983230072969 + 3 ^ 40 * 1180324 * 2
def baseEnd_1180324 : Nat := 269366017794464538054131

theorem tailTrace_1180324 : CollatzResearch.WordTrace tailWord_1180324 prefixEnd_1180324 269366017794464538054131 := by
  unfold tailWord_1180324
  simp only [CollatzResearch.WordTrace]
  refine ⟨21524976487947603067722013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28699968650596804090296017 21524976487947603067722013)
  ·
    refine ⟨8071866182980351150395755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21524976487947603067722013 8071866182980351150395755)
    ·
      refine ⟨12107799274470526725593633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8071866182980351150395755 12107799274470526725593633)
      ·
        refine ⟨9080849455852895044195225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12107799274470526725593633 9080849455852895044195225)
        ·
          refine ⟨6810637091889671283146419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9080849455852895044195225 6810637091889671283146419)
          ·
            refine ⟨10215955637834506924719629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6810637091889671283146419 10215955637834506924719629)
            ·
              refine ⟨3830983364187940096769861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10215955637834506924719629 3830983364187940096769861)
              ·
                refine ⟨718309380785238768144349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3830983364187940096769861 718309380785238768144349)
                ·
                  refine ⟨269366017794464538054131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 718309380785238768144349 269366017794464538054131)
                  ·
                    rfl

theorem cell21_1180324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 4, 3].length) (baseStart_1180324 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1180324 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1180324 prefixEnd_1180324 := by exact prefixLift 1180324
  have htrace : WordTrace (prefixWord ++ tailWord_1180324) baseStart_1180324 baseEnd_1180324 := by
    simpa [prefixWord, tailWord_1180324, baseEnd_1180324] using wordTrace_append hprefix tailTrace_1180324
  have hstable : (prefixWord ++ tailWord_1180324).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180324).length < 2 ^ (prefixWord ++ tailWord_1180324).sum := by decide
  have hdescent : baseEnd_1180324 < baseStart_1180324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180327 : List Nat := [1, 1, 6, 3, 2, 1, 1, 6]
def baseStart_1180327 : Nat := 118140960795 + 1180327 * 2 ^ 59
def prefixEnd_1180327 : Nat := 4983230072969 + 3 ^ 40 * 1180327 * 2
def baseEnd_1180327 : Nat := 89788900811779066501375

theorem tailTrace_1180327 : CollatzResearch.WordTrace tailWord_1180327 prefixEnd_1180327 89788900811779066501375 := by
  unfold tailWord_1180327
  simp only [CollatzResearch.WordTrace]
  refine ⟨43050062394884337647803235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28700041596589558431868823 43050062394884337647803235)
  ·
    refine ⟨64575093592326506471704853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43050062394884337647803235 64575093592326506471704853)
    ·
      refine ⟨3026957512140304990861165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 64575093592326506471704853 3026957512140304990861165)
      ·
        refine ⟨1135109067052614371572937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3026957512140304990861165 1135109067052614371572937)
        ·
          refine ⟨851331800289460778679703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1135109067052614371572937 851331800289460778679703)
          ·
            refine ⟨1276997700434191168019555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 851331800289460778679703 1276997700434191168019555)
            ·
              refine ⟨1915496550651286752029333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1276997700434191168019555 1915496550651286752029333)
              ·
                refine ⟨89788900811779066501375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1915496550651286752029333 89788900811779066501375)
                ·
                  rfl

theorem cell21_1180327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 1, 6].length) (baseStart_1180327 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1180327 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1180327 prefixEnd_1180327 := by exact prefixLift 1180327
  have htrace : WordTrace (prefixWord ++ tailWord_1180327) baseStart_1180327 baseEnd_1180327 := by
    simpa [prefixWord, tailWord_1180327, baseEnd_1180327] using wordTrace_append hprefix tailTrace_1180327
  have hstable : (prefixWord ++ tailWord_1180327).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180327).length < 2 ^ (prefixWord ++ tailWord_1180327).sum := by decide
  have hdescent : baseEnd_1180327 < baseStart_1180327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180372 : List Nat := [2, 4, 1, 3, 2, 2, 1, 2, 4]
def baseStart_1180372 : Nat := 118140960795 + 1180372 * 2 ^ 59
def prefixEnd_1180372 : Nat := 4983230072969 + 3 ^ 40 * 1180372 * 2
def baseEnd_1180372 : Nat := 269376972048427121254033

theorem tailTrace_1180372 : CollatzResearch.WordTrace tailWord_1180372 prefixEnd_1180372 269376972048427121254033 := by
  unfold tailWord_1180372
  simp only [CollatzResearch.WordTrace]
  refine ⟨21525851839860655166595685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28701135786480873555460913 21525851839860655166595685)
  ·
    refine ⟨4036097219973872843736691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21525851839860655166595685 4036097219973872843736691)
    ·
      refine ⟨6054145829960809265605037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4036097219973872843736691 6054145829960809265605037)
      ·
        refine ⟨2270304686235303474601889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6054145829960809265605037 2270304686235303474601889)
        ·
          refine ⟨1702728514676477605951417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2270304686235303474601889 1702728514676477605951417)
          ·
            refine ⟨1277046386007358204463563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1702728514676477605951417 1277046386007358204463563)
            ·
              refine ⟨1915569579011037306695345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1277046386007358204463563 1915569579011037306695345)
              ·
                refine ⟨1436677184258277980021509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1915569579011037306695345 1436677184258277980021509)
                ·
                  refine ⟨269376972048427121254033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1436677184258277980021509 269376972048427121254033)
                  ·
                    rfl

theorem cell21_1180372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 1, 2, 4].length) (baseStart_1180372 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1180372 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1180372 prefixEnd_1180372 := by exact prefixLift 1180372
  have htrace : WordTrace (prefixWord ++ tailWord_1180372) baseStart_1180372 baseEnd_1180372 := by
    simpa [prefixWord, tailWord_1180372, baseEnd_1180372] using wordTrace_append hprefix tailTrace_1180372
  have hstable : (prefixWord ++ tailWord_1180372).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180372).length < 2 ^ (prefixWord ++ tailWord_1180372).sum := by decide
  have hdescent : baseEnd_1180372 < baseStart_1180372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180383 : List Nat := [1, 1, 2, 3, 2, 4, 2, 1, 5]
def baseStart_1180383 : Nat := 118140960795 + 1180383 * 2 ^ 59
def prefixEnd_1180383 : Nat := 4983230072969 + 3 ^ 40 * 1180383 * 2
def baseEnd_1180383 : Nat := 269379482398293546570677

theorem tailTrace_1180383 : CollatzResearch.WordTrace tailWord_1180383 prefixEnd_1180383 269379482398293546570677 := by
  unfold tailWord_1180383
  simp only [CollatzResearch.WordTrace]
  refine ⟨43052104882681459211841803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28701403255120972807894535 43052104882681459211841803)
  ·
    refine ⟨64578157324022188817762705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43052104882681459211841803 64578157324022188817762705)
    ·
      refine ⟨48433617993016641613322029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64578157324022188817762705 48433617993016641613322029)
      ·
        refine ⟨18162606747381240604995761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48433617993016641613322029 18162606747381240604995761)
        ·
          refine ⟨13621955060535930453746821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18162606747381240604995761 13621955060535930453746821)
          ·
            refine ⟨2554116573850486960077529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13621955060535930453746821 2554116573850486960077529)
            ·
              refine ⟨1915587430387865220058147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2554116573850486960077529 1915587430387865220058147)
              ·
                refine ⟨2873381145581797830087221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1915587430387865220058147 2873381145581797830087221)
                ·
                  refine ⟨269379482398293546570677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2873381145581797830087221 269379482398293546570677)
                  ·
                    rfl

theorem cell21_1180383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 2, 1, 5].length) (baseStart_1180383 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1180383 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1180383 prefixEnd_1180383 := by exact prefixLift 1180383
  have htrace : WordTrace (prefixWord ++ tailWord_1180383) baseStart_1180383 baseEnd_1180383 := by
    simpa [prefixWord, tailWord_1180383, baseEnd_1180383] using wordTrace_append hprefix tailTrace_1180383
  have hstable : (prefixWord ++ tailWord_1180383).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180383).length < 2 ^ (prefixWord ++ tailWord_1180383).sum := by decide
  have hdescent : baseEnd_1180383 < baseStart_1180383 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180414 : List Nat := [4, 2, 2, 1, 2, 1, 1, 2, 6]
def baseStart_1180414 : Nat := 118140960795 + 1180414 * 2 ^ 59
def prefixEnd_1180414 : Nat := 4983230072969 + 3 ^ 40 * 1180414 * 2
def baseEnd_1180414 : Nat := 269386557020644381553947

theorem tailTrace_1180414 : CollatzResearch.WordTrace tailWord_1180414 prefixEnd_1180414 269386557020644381553947 := by
  unfold tailWord_1180414
  simp only [CollatzResearch.WordTrace]
  refine ⟨5381654443196143938277537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28702157030379434337480197 5381654443196143938277537)
  ·
    refine ⟨4036240832397107953708153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5381654443196143938277537 4036240832397107953708153)
    ·
      refine ⟨3027180624297830965281115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4036240832397107953708153 3027180624297830965281115)
      ·
        refine ⟨4540770936446746447921673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3027180624297830965281115 4540770936446746447921673)
        ·
          refine ⟨3405578202335059835941255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4540770936446746447921673 3405578202335059835941255)
          ·
            refine ⟨5108367303502589753911883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3405578202335059835941255 5108367303502589753911883)
            ·
              refine ⟨7662550955253884630867825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5108367303502589753911883 7662550955253884630867825)
              ·
                refine ⟨5746913216440413473150869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7662550955253884630867825 5746913216440413473150869)
                ·
                  refine ⟨269386557020644381553947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5746913216440413473150869 269386557020644381553947)
                  ·
                    rfl

theorem cell21_1180414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 2, 6].length) (baseStart_1180414 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1180414 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1180414 prefixEnd_1180414 := by exact prefixLift 1180414
  have htrace : WordTrace (prefixWord ++ tailWord_1180414) baseStart_1180414 baseEnd_1180414 := by
    simpa [prefixWord, tailWord_1180414, baseEnd_1180414] using wordTrace_append hprefix tailTrace_1180414
  have hstable : (prefixWord ++ tailWord_1180414).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180414).length < 2 ^ (prefixWord ++ tailWord_1180414).sum := by decide
  have hdescent : baseEnd_1180414 < baseStart_1180414 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180434 : List Nat := [3, 2, 4, 1, 3, 1, 1, 1, 5]
def baseStart_1180434 : Nat := 118140960795 + 1180434 * 2 ^ 59
def prefixEnd_1180434 : Nat := 4983230072969 + 3 ^ 40 * 1180434 * 2
def baseEnd_1180434 : Nat := 269391121293128791220573

theorem tailTrace_1180434 : CollatzResearch.WordTrace tailWord_1180434 prefixEnd_1180434 269391121293128791220573 := by
  unfold tailWord_1180434
  simp only [CollatzResearch.WordTrace]
  refine ⟨10763491251374173730487089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28702643336997796614632237 10763491251374173730487089)
  ·
    refine ⟨8072618438530630297865317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10763491251374173730487089 8072618438530630297865317)
    ·
      refine ⟨1513615957224493180849747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8072618438530630297865317 1513615957224493180849747)
      ·
        refine ⟨2270423935836739771274621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1513615957224493180849747 2270423935836739771274621)
        ·
          refine ⟨851408975938777414227983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2270423935836739771274621 851408975938777414227983)
          ·
            refine ⟨1277113463908166121341975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 851408975938777414227983 1277113463908166121341975)
            ·
              refine ⟨1915670195862249182012963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1277113463908166121341975 1915670195862249182012963)
              ·
                refine ⟨2873505293793373773019445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1915670195862249182012963 2873505293793373773019445)
                ·
                  refine ⟨269391121293128791220573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2873505293793373773019445 269391121293128791220573)
                  ·
                    rfl

theorem cell21_1180434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 1, 1, 5].length) (baseStart_1180434 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1180434 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1180434 prefixEnd_1180434 := by exact prefixLift 1180434
  have htrace : WordTrace (prefixWord ++ tailWord_1180434) baseStart_1180434 baseEnd_1180434 := by
    simpa [prefixWord, tailWord_1180434, baseEnd_1180434] using wordTrace_append hprefix tailTrace_1180434
  have hstable : (prefixWord ++ tailWord_1180434).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180434).length < 2 ^ (prefixWord ++ tailWord_1180434).sum := by decide
  have hdescent : baseEnd_1180434 < baseStart_1180434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180549 : List Nat := [1, 3, 1, 1, 3, 4, 1, 1, 6]
def baseStart_1180549 : Nat := 118140960795 + 1180549 * 2 ^ 59
def prefixEnd_1180549 : Nat := 4983230072969 + 3 ^ 40 * 1180549 * 2
def baseEnd_1180549 : Nat := 269417365859914146803671

theorem tailTrace_1180549 : CollatzResearch.WordTrace tailWord_1180549 prefixEnd_1180549 269417365859914146803671 := by
  unfold tailWord_1180549
  simp only [CollatzResearch.WordTrace]
  refine ⟨43058159400080069562384701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28705439600053379708256467 43058159400080069562384701)
  ·
    refine ⟨16146809775030026085894263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43058159400080069562384701 16146809775030026085894263)
    ·
      refine ⟨24220214662545039128841395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16146809775030026085894263 24220214662545039128841395)
      ·
        refine ⟨36330321993817558693262093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24220214662545039128841395 36330321993817558693262093)
        ·
          refine ⟨13623870747681584509973285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36330321993817558693262093 13623870747681584509973285)
          ·
            refine ⟨2554475765190297095619991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13623870747681584509973285 2554475765190297095619991)
            ·
              refine ⟨3831713647785445643429987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2554475765190297095619991 3831713647785445643429987)
              ·
                refine ⟨5747570471678168465144981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3831713647785445643429987 5747570471678168465144981)
                ·
                  refine ⟨269417365859914146803671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5747570471678168465144981 269417365859914146803671)
                  ·
                    rfl

theorem cell21_1180549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 1, 6].length) (baseStart_1180549 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1180549 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1180549 prefixEnd_1180549 := by exact prefixLift 1180549
  have htrace : WordTrace (prefixWord ++ tailWord_1180549) baseStart_1180549 baseEnd_1180549 := by
    simpa [prefixWord, tailWord_1180549, baseEnd_1180549] using wordTrace_append hprefix tailTrace_1180549
  have hstable : (prefixWord ++ tailWord_1180549).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180549).length < 2 ^ (prefixWord ++ tailWord_1180549).sum := by decide
  have hdescent : baseEnd_1180549 < baseStart_1180549 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180552 : List Nat := [2, 1, 3, 3, 2, 1, 2, 4, 3]
def baseStart_1180552 : Nat := 118140960795 + 1180552 * 2 ^ 59
def prefixEnd_1180552 : Nat := 4983230072969 + 3 ^ 40 * 1180552 * 2
def baseEnd_1180552 : Nat := 269418050500786808253665

theorem tailTrace_1180552 : CollatzResearch.WordTrace tailWord_1180552 prefixEnd_1180552 269418050500786808253665 := by
  unfold tailWord_1180552
  simp only [CollatzResearch.WordTrace]
  refine ⟨21529134409534600537371955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28705512546046134049829273 21529134409534600537371955)
  ·
    refine ⟨32293701614301900806057933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21529134409534600537371955 32293701614301900806057933)
    ·
      refine ⟨12110138105363212802271725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32293701614301900806057933 12110138105363212802271725)
      ·
        refine ⟨4541301789511204800851897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12110138105363212802271725 4541301789511204800851897)
        ·
          refine ⟨3405976342133403600638923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4541301789511204800851897 3405976342133403600638923)
          ·
            refine ⟨5108964513200105400958385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3405976342133403600638923 5108964513200105400958385)
            ·
              refine ⟨3831723384900079050718789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5108964513200105400958385 3831723384900079050718789)
              ·
                refine ⟨718448134668764822009773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3831723384900079050718789 718448134668764822009773)
                ·
                  refine ⟨269418050500786808253665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 718448134668764822009773 269418050500786808253665)
                  ·
                    rfl

theorem cell21_1180552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 4, 3].length) (baseStart_1180552 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1180552 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1180552 prefixEnd_1180552 := by exact prefixLift 1180552
  have htrace : WordTrace (prefixWord ++ tailWord_1180552) baseStart_1180552 baseEnd_1180552 := by
    simpa [prefixWord, tailWord_1180552, baseEnd_1180552] using wordTrace_append hprefix tailTrace_1180552
  have hstable : (prefixWord ++ tailWord_1180552).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180552).length < 2 ^ (prefixWord ++ tailWord_1180552).sum := by decide
  have hdescent : baseEnd_1180552 < baseStart_1180552 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180625 : List Nat := [1, 2, 2, 1, 2, 1, 5, 3, 4]
def baseStart_1180625 : Nat := 118140960795 + 1180625 * 2 ^ 59
def prefixEnd_1180625 : Nat := 4983230072969 + 3 ^ 40 * 1180625 * 2
def baseEnd_1180625 : Nat := 269434710095354903536849

theorem tailTrace_1180625 : CollatzResearch.WordTrace tailWord_1180625 prefixEnd_1180625 269434710095354903536849 := by
  unfold tailWord_1180625
  simp only [CollatzResearch.WordTrace]
  refine ⟨43060931347804734542151329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28707287565203156361434219 43060931347804734542151329)
  ·
    refine ⟨32295698510853550906613497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43060931347804734542151329 32295698510853550906613497)
    ·
      refine ⟨24221773883140163179960123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32295698510853550906613497 24221773883140163179960123)
      ·
        refine ⟨36332660824710244769940185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24221773883140163179960123 36332660824710244769940185)
        ·
          refine ⟨27249495618532683577455139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36332660824710244769940185 27249495618532683577455139)
          ·
            refine ⟨40874243427799025366182709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27249495618532683577455139 40874243427799025366182709)
            ·
              refine ⟨3831960321356158628079629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40874243427799025366182709 3831960321356158628079629)
              ·
                refine ⟨1436985120508559485529861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3831960321356158628079629 1436985120508559485529861)
                ·
                  refine ⟨269434710095354903536849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1436985120508559485529861 269434710095354903536849)
                  ·
                    rfl

theorem cell21_1180625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 3, 4].length) (baseStart_1180625 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1180625 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1180625 prefixEnd_1180625 := by exact prefixLift 1180625
  have htrace : WordTrace (prefixWord ++ tailWord_1180625) baseStart_1180625 baseEnd_1180625 := by
    simpa [prefixWord, tailWord_1180625, baseEnd_1180625] using wordTrace_append hprefix tailTrace_1180625
  have hstable : (prefixWord ++ tailWord_1180625).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180625).length < 2 ^ (prefixWord ++ tailWord_1180625).sum := by decide
  have hdescent : baseEnd_1180625 < baseStart_1180625 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180662 : List Nat := [5, 1, 1, 1, 3, 3, 2, 2, 3]
def baseStart_1180662 : Nat := 118140960795 + 1180662 * 2 ^ 59
def prefixEnd_1180662 : Nat := 4983230072969 + 3 ^ 40 * 1180662 * 2
def baseEnd_1180662 : Nat := 269443153999451061420107

theorem tailTrace_1180662 : CollatzResearch.WordTrace tailWord_1180662 prefixEnd_1180662 269443153999451061420107 := by
  unfold tailWord_1180662
  simp only [CollatzResearch.WordTrace]
  refine ⟨2691392553041918116328015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28708187232447126574165493 2691392553041918116328015)
  ·
    refine ⟨4037088829562877174492023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2691392553041918116328015 4037088829562877174492023)
    ·
      refine ⟨6055633244344315761738035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4037088829562877174492023 6055633244344315761738035)
      ·
        refine ⟨9083449866516473642607053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6055633244344315761738035 9083449866516473642607053)
        ·
          refine ⟨3406293699943677615977645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9083449866516473642607053 3406293699943677615977645)
          ·
            refine ⟨1277360137478879105991617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3406293699943677615977645 1277360137478879105991617)
            ·
              refine ⟨958020103109159329493713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1277360137478879105991617 958020103109159329493713)
              ·
                refine ⟨718515077331869497120285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 958020103109159329493713 718515077331869497120285)
                ·
                  refine ⟨269443153999451061420107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 718515077331869497120285 269443153999451061420107)
                  ·
                    rfl

theorem cell21_1180662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 2, 2, 3].length) (baseStart_1180662 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1180662 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1180662 prefixEnd_1180662 := by exact prefixLift 1180662
  have htrace : WordTrace (prefixWord ++ tailWord_1180662) baseStart_1180662 baseEnd_1180662 := by
    simpa [prefixWord, tailWord_1180662, baseEnd_1180662] using wordTrace_append hprefix tailTrace_1180662
  have hstable : (prefixWord ++ tailWord_1180662).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180662).length < 2 ^ (prefixWord ++ tailWord_1180662).sum := by decide
  have hdescent : baseEnd_1180662 < baseStart_1180662 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180746 : List Nat := [3, 1, 2, 1, 1, 2, 4, 2, 5]
def baseStart_1180746 : Nat := 118140960795 + 1180746 * 2 ^ 59
def prefixEnd_1180746 : Nat := 4983230072969 + 3 ^ 40 * 1180746 * 2
def baseEnd_1180746 : Nat := 269462323943885582019935

theorem tailTrace_1180746 : CollatzResearch.WordTrace tailWord_1180746 prefixEnd_1180746 269462323943885582019935 := by
  unfold tailWord_1180746
  simp only [CollatzResearch.WordTrace]
  refine ⟨10766336145091593051826523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28710229720244248138204061 10766336145091593051826523)
  ·
    refine ⟨16149504217637389577739785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10766336145091593051826523 16149504217637389577739785)
    ·
      refine ⟨12112128163228042183304839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16149504217637389577739785 12112128163228042183304839)
      ·
        refine ⟨18168192244842063274957259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12112128163228042183304839 18168192244842063274957259)
        ·
          refine ⟨27252288367263094912435889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18168192244842063274957259 27252288367263094912435889)
          ·
            refine ⟨20439216275447321184326917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27252288367263094912435889 20439216275447321184326917)
            ·
              refine ⟨3832353051646372722061297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20439216275447321184326917 3832353051646372722061297)
              ·
                refine ⟨2874264788734779541545973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3832353051646372722061297 2874264788734779541545973)
                ·
                  refine ⟨269462323943885582019935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2874264788734779541545973 269462323943885582019935)
                  ·
                    rfl

theorem cell21_1180746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 2, 5].length) (baseStart_1180746 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1180746 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1180746 prefixEnd_1180746 := by exact prefixLift 1180746
  have htrace : WordTrace (prefixWord ++ tailWord_1180746) baseStart_1180746 baseEnd_1180746 := by
    simpa [prefixWord, tailWord_1180746, baseEnd_1180746] using wordTrace_append hprefix tailTrace_1180746
  have hstable : (prefixWord ++ tailWord_1180746).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180746).length < 2 ^ (prefixWord ++ tailWord_1180746).sum := by decide
  have hdescent : baseEnd_1180746 < baseStart_1180746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180749 : List Nat := [1, 6, 1, 1, 1, 2, 4, 5]
def baseStart_1180749 : Nat := 118140960795 + 1180749 * 2 ^ 59
def prefixEnd_1180749 : Nat := 4983230072969 + 3 ^ 40 * 1180749 * 2
def baseEnd_1180749 : Nat := 89821002861586081156643

theorem tailTrace_1180749 : CollatzResearch.WordTrace tailWord_1180749 prefixEnd_1180749 89821002861586081156643 := by
  unfold tailWord_1180749
  simp only [CollatzResearch.WordTrace]
  refine ⟨43065453999355503719665301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28710302666237002479776867 43065453999355503719665301)
  ·
    refine ⟨2018693156219789236859311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 43065453999355503719665301 2018693156219789236859311)
    ·
      refine ⟨3028039734329683855288967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2018693156219789236859311 3028039734329683855288967)
      ·
        refine ⟨4542059601494525782933451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3028039734329683855288967 4542059601494525782933451)
        ·
          refine ⟨6813089402241788674400177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4542059601494525782933451 6813089402241788674400177)
          ·
            refine ⟨5109817051681341505800133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6813089402241788674400177 5109817051681341505800133)
            ·
              refine ⟨958090697190251532337525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5109817051681341505800133 958090697190251532337525)
              ·
                refine ⟨89821002861586081156643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 958090697190251532337525 89821002861586081156643)
                ·
                  rfl

theorem cell21_1180749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 4, 5].length) (baseStart_1180749 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1180749 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1180749 prefixEnd_1180749 := by exact prefixLift 1180749
  have htrace : WordTrace (prefixWord ++ tailWord_1180749) baseStart_1180749 baseEnd_1180749 := by
    simpa [prefixWord, tailWord_1180749, baseEnd_1180749] using wordTrace_append hprefix tailTrace_1180749
  have hstable : (prefixWord ++ tailWord_1180749).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180749).length < 2 ^ (prefixWord ++ tailWord_1180749).sum := by decide
  have hdescent : baseEnd_1180749 < baseStart_1180749 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180760 : List Nat := [2, 1, 2, 2, 1, 3, 1, 1, 8]
def baseStart_1180760 : Nat := 118140960795 + 1180760 * 2 ^ 59
def prefixEnd_1180760 : Nat := 4983230072969 + 3 ^ 40 * 1180760 * 2
def baseEnd_1180760 : Nat := 269465518934624668786573

theorem tailTrace_1180760 : CollatzResearch.WordTrace tailWord_1180760 prefixEnd_1180760 269465518934624668786573 := by
  unfold tailWord_1180760
  simp only [CollatzResearch.WordTrace]
  refine ⟨21532927601157826299157867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28710570134877101732210489 21532927601157826299157867)
  ·
    refine ⟨32299391401736739448736801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21532927601157826299157867 32299391401736739448736801)
    ·
      refine ⟨24224543551302554586552601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32299391401736739448736801 24224543551302554586552601)
      ·
        refine ⟨18168407663476915939914451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24224543551302554586552601 18168407663476915939914451)
        ·
          refine ⟨27252611495215373909871677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18168407663476915939914451 27252611495215373909871677)
          ·
            refine ⟨10219729310705765216201879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27252611495215373909871677 10219729310705765216201879)
            ·
              refine ⟨15329593966058647824302819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10219729310705765216201879 15329593966058647824302819)
              ·
                refine ⟨22994390949087971736454229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15329593966058647824302819 22994390949087971736454229)
                ·
                  refine ⟨269465518934624668786573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22994390949087971736454229 269465518934624668786573)
                  ·
                    rfl

theorem cell21_1180760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 8].length) (baseStart_1180760 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1180760 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1180760 prefixEnd_1180760 := by exact prefixLift 1180760
  have htrace : WordTrace (prefixWord ++ tailWord_1180760) baseStart_1180760 baseEnd_1180760 := by
    simpa [prefixWord, tailWord_1180760, baseEnd_1180760] using wordTrace_append hprefix tailTrace_1180760
  have hstable : (prefixWord ++ tailWord_1180760).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180760).length < 2 ^ (prefixWord ++ tailWord_1180760).sum := by decide
  have hdescent : baseEnd_1180760 < baseStart_1180760 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180766 : List Nat := [4, 4, 1, 1, 1, 3, 7]
def baseStart_1180766 : Nat := 118140960795 + 1180766 * 2 ^ 59
def prefixEnd_1180766 : Nat := 4983230072969 + 3 ^ 40 * 1180766 * 2
def baseEnd_1180766 : Nat := 29940765357374443520729

theorem tailTrace_1180766 : CollatzResearch.WordTrace tailWord_1180766 prefixEnd_1180766 29940765357374443520729 := by
  unfold tailWord_1180766
  simp only [CollatzResearch.WordTrace]
  refine ⟨5383259255036739452879269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28710716026862610415356101 5383259255036739452879269)
  ·
    refine ⟨1009361110319388647414863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5383259255036739452879269 1009361110319388647414863)
    ·
      refine ⟨1514041665479082971122295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1009361110319388647414863 1514041665479082971122295)
      ·
        refine ⟨2271062498218624456683443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1514041665479082971122295 2271062498218624456683443)
        ·
          refine ⟨3406593747327936685025165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2271062498218624456683443 3406593747327936685025165)
          ·
            refine ⟨1277472655247976256884437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3406593747327936685025165 1277472655247976256884437)
            ·
              refine ⟨29940765357374443520729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1277472655247976256884437 29940765357374443520729)
              ·
                rfl

theorem cell21_1180766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 7].length) (baseStart_1180766 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1180766 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1180766 prefixEnd_1180766 := by exact prefixLift 1180766
  have htrace : WordTrace (prefixWord ++ tailWord_1180766) baseStart_1180766 baseEnd_1180766 := by
    simpa [prefixWord, tailWord_1180766, baseEnd_1180766] using wordTrace_append hprefix tailTrace_1180766
  have hstable : (prefixWord ++ tailWord_1180766).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180766).length < 2 ^ (prefixWord ++ tailWord_1180766).sum := by decide
  have hdescent : baseEnd_1180766 < baseStart_1180766 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180780 : List Nat := [2, 2, 1, 1, 3, 2, 5, 2, 3]
def baseStart_1180780 : Nat := 118140960795 + 1180780 * 2 ^ 59
def prefixEnd_1180780 : Nat := 4983230072969 + 3 ^ 40 * 1180780 * 2
def baseEnd_1180780 : Nat := 269470083207109078453199

theorem tailTrace_1180780 : CollatzResearch.WordTrace tailWord_1180780 prefixEnd_1180780 269470083207109078453199 := by
  unfold tailWord_1180780
  simp only [CollatzResearch.WordTrace]
  refine ⟨21533292331121598007021897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28711056441495464009362529 21533292331121598007021897)
  ·
    refine ⟨16149969248341198505266423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21533292331121598007021897 16149969248341198505266423)
    ·
      refine ⟨24224953872511797757899635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16149969248341198505266423 24224953872511797757899635)
      ·
        refine ⟨36337430808767696636849453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24224953872511797757899635 36337430808767696636849453)
        ·
          refine ⟨13626536553287886238818545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36337430808767696636849453 13626536553287886238818545)
          ·
            refine ⟨10219902414965914679113909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13626536553287886238818545 10219902414965914679113909)
            ·
              refine ⟨958115851403054501166929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10219902414965914679113909 958115851403054501166929)
              ·
                refine ⟨718586888552290875875197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 958115851403054501166929 718586888552290875875197)
                ·
                  refine ⟨269470083207109078453199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 718586888552290875875197 269470083207109078453199)
                  ·
                    rfl

theorem cell21_1180780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 5, 2, 3].length) (baseStart_1180780 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1180780 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1180780 prefixEnd_1180780 := by exact prefixLift 1180780
  have htrace : WordTrace (prefixWord ++ tailWord_1180780) baseStart_1180780 baseEnd_1180780 := by
    simpa [prefixWord, tailWord_1180780, baseEnd_1180780] using wordTrace_append hprefix tailTrace_1180780
  have hstable : (prefixWord ++ tailWord_1180780).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180780).length < 2 ^ (prefixWord ++ tailWord_1180780).sum := by decide
  have hdescent : baseEnd_1180780 < baseStart_1180780 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180791 : List Nat := [1, 1, 3, 1, 1, 4, 4, 6]
def baseStart_1180791 : Nat := 118140960795 + 1180791 * 2 ^ 59
def prefixEnd_1180791 : Nat := 4983230072969 + 3 ^ 40 * 1180791 * 2
def baseEnd_1180791 : Nat := 89824197852325167923281

theorem tailTrace_1180791 : CollatzResearch.WordTrace tailWord_1180791 prefixEnd_1180791 89824197852325167923281 := by
  unfold tailWord_1180791
  simp only [CollatzResearch.WordTrace]
  refine ⟨43066985865203344892694227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28711323910135563261796151 43066985865203344892694227)
  ·
    refine ⟨64600478797805017339041341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43066985865203344892694227 64600478797805017339041341)
    ·
      refine ⟨24225179549176881502140503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64600478797805017339041341 24225179549176881502140503)
      ·
        refine ⟨36337769323765322253210755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24225179549176881502140503 36337769323765322253210755)
        ·
          refine ⟨54506653985647983379816133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36337769323765322253210755 54506653985647983379816133)
          ·
            refine ⟨10219997622308996883715525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54506653985647983379816133 10219997622308996883715525)
            ·
              refine ⟨1916249554182936915696661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10219997622308996883715525 1916249554182936915696661)
              ·
                refine ⟨89824197852325167923281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1916249554182936915696661 89824197852325167923281)
                ·
                  rfl

theorem cell21_1180791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 4, 6].length) (baseStart_1180791 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1180791 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1180791 prefixEnd_1180791 := by exact prefixLift 1180791
  have htrace : WordTrace (prefixWord ++ tailWord_1180791) baseStart_1180791 baseEnd_1180791 := by
    simpa [prefixWord, tailWord_1180791, baseEnd_1180791] using wordTrace_append hprefix tailTrace_1180791
  have hstable : (prefixWord ++ tailWord_1180791).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180791).length < 2 ^ (prefixWord ++ tailWord_1180791).sum := by decide
  have hdescent : baseEnd_1180791 < baseStart_1180791 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180881 : List Nat := [1, 2, 2, 1, 2, 2, 1, 1, 9]
def baseStart_1180881 : Nat := 118140960795 + 1180881 * 2 ^ 59
def prefixEnd_1180881 : Nat := 4983230072969 + 3 ^ 40 * 1180881 * 2
def baseEnd_1180881 : Nat := 269493132783155347269659

theorem tailTrace_1180881 : CollatzResearch.WordTrace tailWord_1180881 prefixEnd_1180881 269493132783155347269659 := by
  unfold tailWord_1180881
  simp only [CollatzResearch.WordTrace]
  refine ⟨43070268434877290263470497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28713512289918193508980331 43070268434877290263470497)
  ·
    refine ⟨32302701326157967697602873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43070268434877290263470497 32302701326157967697602873)
    ·
      refine ⟨24227025994618475773202155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32302701326157967697602873 24227025994618475773202155)
      ·
        refine ⟨36340538991927713659803233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24227025994618475773202155 36340538991927713659803233)
        ·
          refine ⟨27255404243945785244852425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36340538991927713659803233 27255404243945785244852425)
          ·
            refine ⟨20441553182959338933639319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27255404243945785244852425 20441553182959338933639319)
            ·
              refine ⟨30662329774439008400458979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20441553182959338933639319 30662329774439008400458979)
              ·
                refine ⟨45993494661658512600688469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30662329774439008400458979 45993494661658512600688469)
                ·
                  refine ⟨269493132783155347269659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 45993494661658512600688469 269493132783155347269659)
                  ·
                    rfl

theorem cell21_1180881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 9].length) (baseStart_1180881 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1180881 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1180881 prefixEnd_1180881 := by exact prefixLift 1180881
  have htrace : WordTrace (prefixWord ++ tailWord_1180881) baseStart_1180881 baseEnd_1180881 := by
    simpa [prefixWord, tailWord_1180881, baseEnd_1180881] using wordTrace_append hprefix tailTrace_1180881
  have hstable : (prefixWord ++ tailWord_1180881).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180881).length < 2 ^ (prefixWord ++ tailWord_1180881).sum := by decide
  have hdescent : baseEnd_1180881 < baseStart_1180881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180932 : List Nat := [2, 3, 2, 2, 2, 1, 3, 3, 3]
def baseStart_1180932 : Nat := 118140960795 + 1180932 * 2 ^ 59
def prefixEnd_1180932 : Nat := 4983230072969 + 3 ^ 40 * 1180932 * 2
def baseEnd_1180932 : Nat := 269504771677990591919555

theorem tailTrace_1180932 : CollatzResearch.WordTrace tailWord_1180932 prefixEnd_1180932 269504771677990591919555 := by
  unfold tailWord_1180932
  simp only [CollatzResearch.WordTrace]
  refine ⟨21536064278846262986788525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28714752371795017315718033 21536064278846262986788525)
  ·
    refine ⟨8076024104567348620045697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21536064278846262986788525 8076024104567348620045697)
    ·
      refine ⟨6057018078425511465034273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8076024104567348620045697 6057018078425511465034273)
      ·
        refine ⟨4542763558819133598775705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6057018078425511465034273 4542763558819133598775705)
        ·
          refine ⟨3407072669114350199081779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4542763558819133598775705 3407072669114350199081779)
          ·
            refine ⟨5110609003671525298622669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3407072669114350199081779 5110609003671525298622669)
            ·
              refine ⟨1916478376376821986983501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5110609003671525298622669 1916478376376821986983501)
              ·
                refine ⟨718679391141308245118813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1916478376376821986983501 718679391141308245118813)
                ·
                  refine ⟨269504771677990591919555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 718679391141308245118813 269504771677990591919555)
                  ·
                    rfl

theorem cell21_1180932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 3, 3, 3].length) (baseStart_1180932 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1180932 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1180932 prefixEnd_1180932 := by exact prefixLift 1180932
  have htrace : WordTrace (prefixWord ++ tailWord_1180932) baseStart_1180932 baseEnd_1180932 := by
    simpa [prefixWord, tailWord_1180932, baseEnd_1180932] using wordTrace_append hprefix tailTrace_1180932
  have hstable : (prefixWord ++ tailWord_1180932).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180932).length < 2 ^ (prefixWord ++ tailWord_1180932).sum := by decide
  have hdescent : baseEnd_1180932 < baseStart_1180932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1180960 : List Nat := [2, 1, 1, 5, 3, 1, 2, 6]
def baseStart_1180960 : Nat := 118140960795 + 1180960 * 2 ^ 59
def prefixEnd_1180960 : Nat := 4983230072969 + 3 ^ 40 * 1180960 * 2
def baseEnd_1180960 : Nat := 89837053886489588484277

theorem tailTrace_1180960 : CollatzResearch.WordTrace tailWord_1180960 prefixEnd_1180960 89837053886489588484277 := by
  unfold tailWord_1180960
  simp only [CollatzResearch.WordTrace]
  refine ⟨21536574900795543377798167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28715433201060724503730889 21536574900795543377798167)
  ·
    refine ⟨32304862351193315066697251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21536574900795543377798167 32304862351193315066697251)
    ·
      refine ⟨48457293526789972600045877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32304862351193315066697251 48457293526789972600045877)
      ·
        refine ⟨4542871268136559931254301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 48457293526789972600045877 4542871268136559931254301)
        ·
          refine ⟨1703576725551209974220363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4542871268136559931254301 1703576725551209974220363)
          ·
            refine ⟨2555365088326814961330545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1703576725551209974220363 2555365088326814961330545)
            ·
              refine ⟨1916523816245111220997909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2555365088326814961330545 1916523816245111220997909)
              ·
                refine ⟨89837053886489588484277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1916523816245111220997909 89837053886489588484277)
                ·
                  rfl

theorem cell21_1180960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 2, 6].length) (baseStart_1180960 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1180960 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1180960 prefixEnd_1180960 := by exact prefixLift 1180960
  have htrace : WordTrace (prefixWord ++ tailWord_1180960) baseStart_1180960 baseEnd_1180960 := by
    simpa [prefixWord, tailWord_1180960, baseEnd_1180960] using wordTrace_append hprefix tailTrace_1180960
  have hstable : (prefixWord ++ tailWord_1180960).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1180960).length < 2 ^ (prefixWord ++ tailWord_1180960).sum := by decide
  have hdescent : baseEnd_1180960 < baseStart_1180960 := by decide
  rcases family_descends (prefixWord ++ tailWord_1180960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1181036 : List Nat := [2, 2, 1, 1, 5, 2, 3, 5]
def baseStart_1181036 : Nat := 118140960795 + 1181036 * 2 ^ 59
def prefixEnd_1181036 : Nat := 4983230072969 + 3 ^ 40 * 1181036 * 2
def baseEnd_1181036 : Nat := 89842835298303174062003

theorem tailTrace_1181036 : CollatzResearch.WordTrace tailWord_1181036 prefixEnd_1181036 89842835298303174062003 := by
  unfold tailWord_1181036
  simp only [CollatzResearch.WordTrace]
  refine ⟨21537960874657875867681481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28717281166210501156908641 21537960874657875867681481)
  ·
    refine ⟨16153470655993406900761111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21537960874657875867681481 16153470655993406900761111)
    ·
      refine ⟨24230205983990110351141667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16153470655993406900761111 24230205983990110351141667)
      ·
        refine ⟨36345308975985165526712501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24230205983990110351141667 36345308975985165526712501)
        ·
          refine ⟨3407372716498609268129297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36345308975985165526712501 3407372716498609268129297)
          ·
            refine ⟨2555529537373956951096973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3407372716498609268129297 2555529537373956951096973)
            ·
              refine ⟨958323576515233856661365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2555529537373956951096973 958323576515233856661365)
              ·
                refine ⟨89842835298303174062003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 958323576515233856661365 89842835298303174062003)
                ·
                  rfl

theorem cell21_1181036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 3, 5].length) (baseStart_1181036 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1181036 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1181036 prefixEnd_1181036 := by exact prefixLift 1181036
  have htrace : WordTrace (prefixWord ++ tailWord_1181036) baseStart_1181036 baseEnd_1181036 := by
    simpa [prefixWord, tailWord_1181036, baseEnd_1181036] using wordTrace_append hprefix tailTrace_1181036
  have hstable : (prefixWord ++ tailWord_1181036).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1181036).length < 2 ^ (prefixWord ++ tailWord_1181036).sum := by decide
  have hdescent : baseEnd_1181036 < baseStart_1181036 := by decide
  rcases family_descends (prefixWord ++ tailWord_1181036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1181095 : List Nat := [1, 1, 6, 1, 1, 1, 3, 7]
def baseStart_1181095 : Nat := 118140960795 + 1181095 * 2 ^ 59
def prefixEnd_1181095 : Nat := 4983230072969 + 3 ^ 40 * 1181095 * 2
def baseEnd_1181095 : Nat := 89847323499579510234185

theorem tailTrace_1181095 : CollatzResearch.WordTrace tailWord_1181095 prefixEnd_1181095 89847323499579510234185 := by
  unfold tailWord_1181095
  simp only [CollatzResearch.WordTrace]
  refine ⟨43078073656102004811760739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28718715770734669874507159 43078073656102004811760739)
  ·
    refine ⟨64617110484153007217641109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43078073656102004811760739 64617110484153007217641109)
    ·
      refine ⟨3028927053944672213326927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 64617110484153007217641109 3028927053944672213326927)
      ·
        refine ⟨4543390580917008319990391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3028927053944672213326927 4543390580917008319990391)
        ·
          refine ⟨6815085871375512479985587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4543390580917008319990391 6815085871375512479985587)
          ·
            refine ⟨10222628807063268719978381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6815085871375512479985587 10222628807063268719978381)
            ·
              refine ⟨3833485802648725769991893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10222628807063268719978381 3833485802648725769991893)
              ·
                refine ⟨89847323499579510234185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3833485802648725769991893 89847323499579510234185)
                ·
                  rfl

theorem cell21_1181095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 7].length) (baseStart_1181095 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1181095 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1181095 prefixEnd_1181095 := by exact prefixLift 1181095
  have htrace : WordTrace (prefixWord ++ tailWord_1181095) baseStart_1181095 baseEnd_1181095 := by
    simpa [prefixWord, tailWord_1181095, baseEnd_1181095] using wordTrace_append hprefix tailTrace_1181095
  have hstable : (prefixWord ++ tailWord_1181095).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1181095).length < 2 ^ (prefixWord ++ tailWord_1181095).sum := by decide
  have hdescent : baseEnd_1181095 < baseStart_1181095 := by decide
  rcases family_descends (prefixWord ++ tailWord_1181095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1181101 : List Nat := [1, 5, 2, 2, 1, 3, 1, 3, 3]
def baseStart_1181101 : Nat := 118140960795 + 1181101 * 2 ^ 59
def prefixEnd_1181101 : Nat := 4983230072969 + 3 ^ 40 * 1181101 * 2
def baseEnd_1181101 : Nat := 269543339780483853602543

theorem tailTrace_1181101 : CollatzResearch.WordTrace tailWord_1181101 prefixEnd_1181101 269543339780483853602543 := by
  unfold tailWord_1181101
  simp only [CollatzResearch.WordTrace]
  refine ⟨43078292494080267836479157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28718861662720178557652771 43078292494080267836479157)
  ·
    refine ⟨4038589921320025109669921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 43078292494080267836479157 4038589921320025109669921)
    ·
      refine ⟨3028942440990018832252441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4038589921320025109669921 3028942440990018832252441)
      ·
        refine ⟨2271706830742514124189331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3028942440990018832252441 2271706830742514124189331)
        ·
          refine ⟨3407560246113771186283997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2271706830742514124189331 3407560246113771186283997)
          ·
            refine ⟨1277835092292664194856499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3407560246113771186283997 1277835092292664194856499)
            ·
              refine ⟨1916752638438996292284749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1277835092292664194856499 1916752638438996292284749)
              ·
                refine ⟨718782239414623609606781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1916752638438996292284749 718782239414623609606781)
                ·
                  refine ⟨269543339780483853602543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 718782239414623609606781 269543339780483853602543)
                  ·
                    rfl

theorem cell21_1181101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 1, 3, 3].length) (baseStart_1181101 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1181101 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1181101 prefixEnd_1181101 := by exact prefixLift 1181101
  have htrace : WordTrace (prefixWord ++ tailWord_1181101) baseStart_1181101 baseEnd_1181101 := by
    simpa [prefixWord, tailWord_1181101, baseEnd_1181101] using wordTrace_append hprefix tailTrace_1181101
  have hstable : (prefixWord ++ tailWord_1181101).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1181101).length < 2 ^ (prefixWord ++ tailWord_1181101).sum := by decide
  have hdescent : baseEnd_1181101 < baseStart_1181101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1181101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1181174 : List Nat := [5, 1, 1, 1, 2, 3, 2, 2, 4]
def baseStart_1181174 : Nat := 118140960795 + 1181174 * 2 ^ 59
def prefixEnd_1181174 : Nat := 4983230072969 + 3 ^ 40 * 1181174 * 2
def baseEnd_1181174 : Nat := 269559999375051948885727

theorem tailTrace_1181174 : CollatzResearch.WordTrace tailWord_1181174 prefixEnd_1181174 269559999375051948885727 := by
  unfold tailWord_1181174
  simp only [CollatzResearch.WordTrace]
  refine ⟨2692559688925987581492911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28720636681877200869257717 2692559688925987581492911)
  ·
    refine ⟨4038839533388981372239367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2692559688925987581492911 4038839533388981372239367)
    ·
      refine ⟨6058259300083472058359051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4038839533388981372239367 6058259300083472058359051)
      ·
        refine ⟨9087388950125208087538577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6058259300083472058359051 9087388950125208087538577)
        ·
          refine ⟨6815541712593906065653933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9087388950125208087538577 6815541712593906065653933)
          ·
            refine ⟨2555828142222714774620225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6815541712593906065653933 2555828142222714774620225)
            ·
              refine ⟨1916871106667036080965169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2555828142222714774620225 1916871106667036080965169)
              ·
                refine ⟨1437653330000277060723877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1916871106667036080965169 1437653330000277060723877)
                ·
                  refine ⟨269559999375051948885727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1437653330000277060723877 269559999375051948885727)
                  ·
                    rfl

theorem cell21_1181174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 2, 2, 4].length) (baseStart_1181174 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1181174 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1181174 prefixEnd_1181174 := by exact prefixLift 1181174
  have htrace : WordTrace (prefixWord ++ tailWord_1181174) baseStart_1181174 baseEnd_1181174 := by
    simpa [prefixWord, tailWord_1181174, baseEnd_1181174] using wordTrace_append hprefix tailTrace_1181174
  have hstable : (prefixWord ++ tailWord_1181174).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1181174).length < 2 ^ (prefixWord ++ tailWord_1181174).sum := by decide
  have hdescent : baseEnd_1181174 < baseStart_1181174 := by decide
  rcases family_descends (prefixWord ++ tailWord_1181174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1181292 : List Nat := [2, 2, 1, 1, 3, 1, 1, 6, 4]
def baseStart_1181292 : Nat := 118140960795 + 1181292 * 2 ^ 59
def prefixEnd_1181292 : Nat := 4983230072969 + 3 ^ 40 * 1181292 * 2
def baseEnd_1181292 : Nat := 269586928582709965918819

theorem tailTrace_1181292 : CollatzResearch.WordTrace tailWord_1181292 prefixEnd_1181292 269586928582709965918819 := by
  unfold tailWord_1181292
  simp only [CollatzResearch.WordTrace]
  refine ⟨21542629418194153728341065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28723505890925538304454753 21542629418194153728341065)
  ·
    refine ⟨16156972063645615296255799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21542629418194153728341065 16156972063645615296255799)
    ·
      refine ⟨24235458095468422944383699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16156972063645615296255799 24235458095468422944383699)
      ·
        refine ⟨36353187143202634416575549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24235458095468422944383699 36353187143202634416575549)
        ·
          refine ⟨13632445178700987906215831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36353187143202634416575549 13632445178700987906215831)
          ·
            refine ⟨20448667768051481859323747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13632445178700987906215831 20448667768051481859323747)
            ·
              refine ⟨30673001652077222788985621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20448667768051481859323747 30673001652077222788985621)
              ·
                refine ⟨1437796952441119818233701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 30673001652077222788985621 1437796952441119818233701)
                ·
                  refine ⟨269586928582709965918819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1437796952441119818233701 269586928582709965918819)
                  ·
                    rfl

theorem cell21_1181292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 4].length) (baseStart_1181292 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1181292 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1181292 prefixEnd_1181292 := by exact prefixLift 1181292
  have htrace : WordTrace (prefixWord ++ tailWord_1181292) baseStart_1181292 baseEnd_1181292 := by
    simpa [prefixWord, tailWord_1181292, baseEnd_1181292] using wordTrace_append hprefix tailTrace_1181292
  have hstable : (prefixWord ++ tailWord_1181292).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1181292).length < 2 ^ (prefixWord ++ tailWord_1181292).sum := by decide
  have hdescent : baseEnd_1181292 < baseStart_1181292 := by decide
  rcases family_descends (prefixWord ++ tailWord_1181292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1181309 : List Nat := [1, 4, 1, 1, 4, 2, 1, 3, 4]
def baseStart_1181309 : Nat := 118140960795 + 1181309 * 2 ^ 59
def prefixEnd_1181309 : Nat := 4983230072969 + 3 ^ 40 * 1181309 * 2
def baseEnd_1181309 : Nat := 269590808214321714135451

theorem tailTrace_1181309 : CollatzResearch.WordTrace tailWord_1181309 prefixEnd_1181309 269590808214321714135451 := by
  unfold tailWord_1181309
  simp only [CollatzResearch.WordTrace]
  refine ⟨43085878877326719360050981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28723919251551146240033987 43085878877326719360050981)
  ·
    refine ⟨8078602289498759880009559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43085878877326719360050981 8078602289498759880009559)
    ·
      refine ⟨12117903434248139820014339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8078602289498759880009559 12117903434248139820014339)
      ·
        refine ⟨18176855151372209730021509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12117903434248139820014339 18176855151372209730021509)
        ·
          refine ⟨3408160340882289324379033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18176855151372209730021509 3408160340882289324379033)
          ·
            refine ⟨2556120255661716993284275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3408160340882289324379033 2556120255661716993284275)
            ·
              refine ⟨3834180383492575489926413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2556120255661716993284275 3834180383492575489926413)
              ·
                refine ⟨1437817643809715808722405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3834180383492575489926413 1437817643809715808722405)
                ·
                  refine ⟨269590808214321714135451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1437817643809715808722405 269590808214321714135451)
                  ·
                    rfl

theorem cell21_1181309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 3, 4].length) (baseStart_1181309 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1181309 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1181309 prefixEnd_1181309 := by exact prefixLift 1181309
  have htrace : WordTrace (prefixWord ++ tailWord_1181309) baseStart_1181309 baseEnd_1181309 := by
    simpa [prefixWord, tailWord_1181309, baseEnd_1181309] using wordTrace_append hprefix tailTrace_1181309
  have hstable : (prefixWord ++ tailWord_1181309).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1181309).length < 2 ^ (prefixWord ++ tailWord_1181309).sum := by decide
  have hdescent : baseEnd_1181309 < baseStart_1181309 := by decide
  rcases family_descends (prefixWord ++ tailWord_1181309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1181346 : List Nat := [3, 3, 1, 4, 1, 2, 2, 2, 3]
def baseStart_1181346 : Nat := 118140960795 + 1181346 * 2 ^ 59
def prefixEnd_1181346 : Nat := 4983230072969 + 3 ^ 40 * 1181346 * 2
def baseEnd_1181346 : Nat := 269599252118417872018709

theorem tailTrace_1181346 : CollatzResearch.WordTrace tailWord_1181346 prefixEnd_1181346 269599252118417872018709 := by
  unfold tailWord_1181346
  simp only [CollatzResearch.WordTrace]
  refine ⟨10771807094548168669786973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28724818918795116452765261 10771807094548168669786973)
  ·
    refine ⟨4039427660455563251170115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10771807094548168669786973 4039427660455563251170115)
    ·
      refine ⟨6059141490683344876755173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4039427660455563251170115 6059141490683344876755173)
      ·
        refine ⟨1136089029503127164391595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6059141490683344876755173 1136089029503127164391595)
        ·
          refine ⟨1704133544254690746587393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1136089029503127164391595 1704133544254690746587393)
          ·
            refine ⟨1278100158191018059940545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1704133544254690746587393 1278100158191018059940545)
            ·
              refine ⟨958575118643263544955409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1278100158191018059940545 958575118643263544955409)
              ·
                refine ⟨718931338982447658716557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 958575118643263544955409 718931338982447658716557)
                ·
                  refine ⟨269599252118417872018709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 718931338982447658716557 269599252118417872018709)
                  ·
                    rfl

theorem cell21_1181346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 2, 2, 3].length) (baseStart_1181346 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1181346 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1181346 prefixEnd_1181346 := by exact prefixLift 1181346
  have htrace : WordTrace (prefixWord ++ tailWord_1181346) baseStart_1181346 baseEnd_1181346 := by
    simpa [prefixWord, tailWord_1181346, baseEnd_1181346] using wordTrace_append hprefix tailTrace_1181346
  have hstable : (prefixWord ++ tailWord_1181346).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1181346).length < 2 ^ (prefixWord ++ tailWord_1181346).sum := by decide
  have hdescent : baseEnd_1181346 < baseStart_1181346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1181346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1181388 : List Nat := [2, 2, 1, 5, 2, 1, 2, 3, 3]
def baseStart_1181388 : Nat := 118140960795 + 1181388 * 2 ^ 59
def prefixEnd_1181388 : Nat := 4983230072969 + 3 ^ 40 * 1181388 * 2
def baseEnd_1181388 : Nat := 269608837090635132318623

theorem tailTrace_1181388 : CollatzResearch.WordTrace tailWord_1181388 prefixEnd_1181388 269608837090635132318623 := by
  unfold tailWord_1181388
  simp only [CollatzResearch.WordTrace]
  refine ⟨21544380122020257926088409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28725840162693677234784545 21544380122020257926088409)
  ·
    refine ⟨16158285091515193444566307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21544380122020257926088409 16158285091515193444566307)
    ·
      refine ⟨24237427637272790166849461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16158285091515193444566307 24237427637272790166849461)
      ·
        refine ⟨2272258840994324078142137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24237427637272790166849461 2272258840994324078142137)
        ·
          refine ⟨1704194130745743058606603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2272258840994324078142137 1704194130745743058606603)
          ·
            refine ⟨2556291196118614587909905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1704194130745743058606603 2556291196118614587909905)
            ·
              refine ⟨1917218397088960940932429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2556291196118614587909905 1917218397088960940932429)
              ·
                refine ⟨718956898908360352849661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1917218397088960940932429 718956898908360352849661)
                ·
                  refine ⟨269608837090635132318623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 718956898908360352849661 269608837090635132318623)
                  ·
                    rfl

theorem cell21_1181388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 2, 3, 3].length) (baseStart_1181388 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1181388 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1181388 prefixEnd_1181388 := by exact prefixLift 1181388
  have htrace : WordTrace (prefixWord ++ tailWord_1181388) baseStart_1181388 baseEnd_1181388 := by
    simpa [prefixWord, tailWord_1181388, baseEnd_1181388] using wordTrace_append hprefix tailTrace_1181388
  have hstable : (prefixWord ++ tailWord_1181388).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1181388).length < 2 ^ (prefixWord ++ tailWord_1181388).sum := by decide
  have hdescent : baseEnd_1181388 < baseStart_1181388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1181388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1181430 : List Nat := [5, 1, 1, 1, 1, 3, 2, 2, 5]
def baseStart_1181430 : Nat := 118140960795 + 1181430 * 2 ^ 59
def prefixEnd_1181430 : Nat := 4983230072969 + 3 ^ 40 * 1181430 * 2
def baseEnd_1181430 : Nat := 269618422062852392618537

theorem tailTrace_1181430 : CollatzResearch.WordTrace tailWord_1181430 prefixEnd_1181430 269618422062852392618537 := by
  unfold tailWord_1181430
  simp only [CollatzResearch.WordTrace]
  refine ⟨2693143256868022314075359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28726861406592238016803829 2693143256868022314075359)
  ·
    refine ⟨4039714885302033471113039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2693143256868022314075359 4039714885302033471113039)
    ·
      refine ⟨6059572327953050206669559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4039714885302033471113039 6059572327953050206669559)
      ·
        refine ⟨9089358491929575310004339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6059572327953050206669559 9089358491929575310004339)
        ·
          refine ⟨13634037737894362965006509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9089358491929575310004339 13634037737894362965006509)
          ·
            refine ⟨5112764151710386111877441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13634037737894362965006509 5112764151710386111877441)
            ·
              refine ⟨3834573113782789583908081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5112764151710386111877441 3834573113782789583908081)
              ·
                refine ⟨2875929835337092187931061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3834573113782789583908081 2875929835337092187931061)
                ·
                  refine ⟨269618422062852392618537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2875929835337092187931061 269618422062852392618537)
                  ·
                    rfl

theorem cell21_1181430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 2, 5].length) (baseStart_1181430 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1181430 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1181430 prefixEnd_1181430 := by exact prefixLift 1181430
  have htrace : WordTrace (prefixWord ++ tailWord_1181430) baseStart_1181430 baseEnd_1181430 := by
    simpa [prefixWord, tailWord_1181430, baseEnd_1181430] using wordTrace_append hprefix tailTrace_1181430
  have hstable : (prefixWord ++ tailWord_1181430).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1181430).length < 2 ^ (prefixWord ++ tailWord_1181430).sum := by decide
  have hdescent : baseEnd_1181430 < baseStart_1181430 := by decide
  rcases family_descends (prefixWord ++ tailWord_1181430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1181444 : List Nat := [2, 3, 2, 2, 1, 2, 1, 2, 6]
def baseStart_1181444 : Nat := 118140960795 + 1181444 * 2 ^ 59
def prefixEnd_1181444 : Nat := 4983230072969 + 3 ^ 40 * 1181444 * 2
def baseEnd_1181444 : Nat := 269621617053591479385175

theorem tailTrace_1181444 : CollatzResearch.WordTrace tailWord_1181444 prefixEnd_1181444 269621617053591479385175 := by
  unfold tailWord_1181444
  simp only [CollatzResearch.WordTrace]
  refine ⟨21545401365918818708107693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28727201821225091610810257 21545401365918818708107693)
  ·
    refine ⟨8079525512219557015540385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21545401365918818708107693 8079525512219557015540385)
    ·
      refine ⟨6059644134164667761655289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8079525512219557015540385 6059644134164667761655289)
      ·
        refine ⟨4544733100623500821241467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6059644134164667761655289 4544733100623500821241467)
        ·
          refine ⟨6817099650935251231862201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4544733100623500821241467 6817099650935251231862201)
          ·
            refine ⟨5112824738201438423896651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6817099650935251231862201 5112824738201438423896651)
            ·
              refine ⟨7669237107302157635844977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5112824738201438423896651 7669237107302157635844977)
              ·
                refine ⟨5751927830476618226883733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7669237107302157635844977 5751927830476618226883733)
                ·
                  refine ⟨269621617053591479385175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5751927830476618226883733 269621617053591479385175)
                  ·
                    rfl

theorem cell21_1181444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 2, 6].length) (baseStart_1181444 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1181444 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1181444 prefixEnd_1181444 := by exact prefixLift 1181444
  have htrace : WordTrace (prefixWord ++ tailWord_1181444) baseStart_1181444 baseEnd_1181444 := by
    simpa [prefixWord, tailWord_1181444, baseEnd_1181444] using wordTrace_append hprefix tailTrace_1181444
  have hstable : (prefixWord ++ tailWord_1181444).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1181444).length < 2 ^ (prefixWord ++ tailWord_1181444).sum := by decide
  have hdescent : baseEnd_1181444 < baseStart_1181444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1181444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1181686 : List Nat := [5, 1, 1, 1, 13]
def baseStart_1181686 : Nat := 118140960795 + 1181686 * 2 ^ 59
def prefixEnd_1181686 : Nat := 4983230072969 + 3 ^ 40 * 1181686 * 2
def baseEnd_1181686 : Nat := 3329343762353738720387

theorem tailTrace_1181686 : CollatzResearch.WordTrace tailWord_1181686 prefixEnd_1181686 3329343762353738720387 := by
  unfold tailWord_1181686
  simp only [CollatzResearch.WordTrace]
  refine ⟨2693726824810057046657807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28733086131307275164349941 2693726824810057046657807)
  ·
    refine ⟨4040590237215085569986711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2693726824810057046657807 4040590237215085569986711)
    ·
      refine ⟨6060885355822628354980067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4040590237215085569986711 6060885355822628354980067)
      ·
        refine ⟨9091328033733942532470101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6060885355822628354980067 9091328033733942532470101)
        ·
          refine ⟨3329343762353738720387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 9091328033733942532470101 3329343762353738720387)
          ·
            rfl

theorem cell21_1181686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 13].length) (baseStart_1181686 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1181686 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1181686 prefixEnd_1181686 := by exact prefixLift 1181686
  have htrace : WordTrace (prefixWord ++ tailWord_1181686) baseStart_1181686 baseEnd_1181686 := by
    simpa [prefixWord, tailWord_1181686, baseEnd_1181686] using wordTrace_append hprefix tailTrace_1181686
  have hstable : (prefixWord ++ tailWord_1181686).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1181686).length < 2 ^ (prefixWord ++ tailWord_1181686).sum := by decide
  have hdescent : baseEnd_1181686 < baseStart_1181686 := by decide
  rcases family_descends (prefixWord ++ tailWord_1181686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1181703 : List Nat := [1, 1, 4, 3, 1, 4, 1, 6]
def baseStart_1181703 : Nat := 118140960795 + 1181703 * 2 ^ 59
def prefixEnd_1181703 : Nat := 4983230072969 + 3 ^ 40 * 1181703 * 2
def baseEnd_1181703 : Nat := 89893574794088194855993

theorem tailTrace_1181703 : CollatzResearch.WordTrace tailWord_1181703 prefixEnd_1181703 89893574794088194855993 := by
  unfold tailWord_1181703
  simp only [CollatzResearch.WordTrace]
  refine ⟨43100249237899324649893763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28733499491932883099929175 43100249237899324649893763)
  ·
    refine ⟨64650373856848986974840645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43100249237899324649893763 64650373856848986974840645)
    ·
      refine ⟨12121945098159185057782621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64650373856848986974840645 12121945098159185057782621)
      ·
        refine ⟨4545729411809694396668483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12121945098159185057782621 4545729411809694396668483)
        ·
          refine ⟨6818594117714541595002725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4545729411809694396668483 6818594117714541595002725)
          ·
            refine ⟨1278486397071476549063011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6818594117714541595002725 1278486397071476549063011)
            ·
              refine ⟨1917729595607214823594517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1278486397071476549063011 1917729595607214823594517)
              ·
                refine ⟨89893574794088194855993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1917729595607214823594517 89893574794088194855993)
                ·
                  rfl

theorem cell21_1181703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 1, 6].length) (baseStart_1181703 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1181703 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1181703 prefixEnd_1181703 := by exact prefixLift 1181703
  have htrace : WordTrace (prefixWord ++ tailWord_1181703) baseStart_1181703 baseEnd_1181703 := by
    simpa [prefixWord, tailWord_1181703, baseEnd_1181703] using wordTrace_append hprefix tailTrace_1181703
  have hstable : (prefixWord ++ tailWord_1181703).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1181703).length < 2 ^ (prefixWord ++ tailWord_1181703).sum := by decide
  have hdescent : baseEnd_1181703 < baseStart_1181703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1181703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1181731 : List Nat := [1, 1, 1, 4, 3, 1, 2, 2, 6]
def baseStart_1181731 : Nat := 118140960795 + 1181731 * 2 ^ 59
def prefixEnd_1181731 : Nat := 4983230072969 + 3 ^ 40 * 1181731 * 2
def baseEnd_1181731 : Nat := 269687114363742758101255

theorem tailTrace_1181731 : CollatzResearch.WordTrace tailWord_1181731 prefixEnd_1181731 269687114363742758101255 := by
  unfold tailWord_1181731
  simp only [CollatzResearch.WordTrace]
  refine ⟨43101270481797885431913047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28734180321198590287942031 43101270481797885431913047)
  ·
    refine ⟨64651905722696828147869571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43101270481797885431913047 64651905722696828147869571)
    ·
      refine ⟨96977858584045242221804357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64651905722696828147869571 96977858584045242221804357)
      ·
        refine ⟨18183348484508482916588317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 96977858584045242221804357 18183348484508482916588317)
        ·
          refine ⟨6818755681690681093720619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18183348484508482916588317 6818755681690681093720619)
          ·
            refine ⟨10228133522536021640580929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6818755681690681093720619 10228133522536021640580929)
            ·
              refine ⟨7671100141902016230435697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10228133522536021640580929 7671100141902016230435697)
              ·
                refine ⟨5753325106426512172826773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7671100141902016230435697 5753325106426512172826773)
                ·
                  refine ⟨269687114363742758101255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5753325106426512172826773 269687114363742758101255)
                  ·
                    rfl

theorem cell21_1181731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 2, 6].length) (baseStart_1181731 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1181731 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1181731 prefixEnd_1181731 := by exact prefixLift 1181731
  have htrace : WordTrace (prefixWord ++ tailWord_1181731) baseStart_1181731 baseEnd_1181731 := by
    simpa [prefixWord, tailWord_1181731, baseEnd_1181731] using wordTrace_append hprefix tailTrace_1181731
  have hstable : (prefixWord ++ tailWord_1181731).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1181731).length < 2 ^ (prefixWord ++ tailWord_1181731).sum := by decide
  have hdescent : baseEnd_1181731 < baseStart_1181731 := by decide
  rcases family_descends (prefixWord ++ tailWord_1181731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1181807 : List Nat := [1, 1, 2, 1, 3, 4, 2, 1, 6]
def baseStart_1181807 : Nat := 118140960795 + 1181807 * 2 ^ 59
def prefixEnd_1181807 : Nat := 4983230072969 + 3 ^ 40 * 1181807 * 2
def baseEnd_1181807 : Nat := 269704458599183514834433

theorem tailTrace_1181807 : CollatzResearch.WordTrace tailWord_1181807 prefixEnd_1181807 269704458599183514834433 := by
  unfold tailWord_1181807
  simp only [CollatzResearch.WordTrace]
  refine ⟨43104042429522550411679675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28736028286348366941119783 43104042429522550411679675)
  ·
    refine ⟨64656063644283825617519513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43104042429522550411679675 64656063644283825617519513)
    ·
      refine ⟨48492047733212869213139635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64656063644283825617519513 48492047733212869213139635)
      ·
        refine ⟨72738071599819303819709453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48492047733212869213139635 72738071599819303819709453)
        ·
          refine ⟨27276776849932238932391045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 72738071599819303819709453 27276776849932238932391045)
          ·
            refine ⟨5114395659362294799823321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27276776849932238932391045 5114395659362294799823321)
            ·
              refine ⟨3835796744521721099867491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5114395659362294799823321 3835796744521721099867491)
              ·
                refine ⟨5753695116782581649801237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3835796744521721099867491 5753695116782581649801237)
                ·
                  refine ⟨269704458599183514834433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5753695116782581649801237 269704458599183514834433)
                  ·
                    rfl

theorem cell21_1181807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 1, 6].length) (baseStart_1181807 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1181807 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1181807 prefixEnd_1181807 := by exact prefixLift 1181807
  have htrace : WordTrace (prefixWord ++ tailWord_1181807) baseStart_1181807 baseEnd_1181807 := by
    simpa [prefixWord, tailWord_1181807, baseEnd_1181807] using wordTrace_append hprefix tailTrace_1181807
  have hstable : (prefixWord ++ tailWord_1181807).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1181807).length < 2 ^ (prefixWord ++ tailWord_1181807).sum := by decide
  have hdescent : baseEnd_1181807 < baseStart_1181807 := by decide
  rcases family_descends (prefixWord ++ tailWord_1181807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1181810 : List Nat := [3, 2, 1, 2, 2, 4, 1, 1, 5]
def baseStart_1181810 : Nat := 118140960795 + 1181810 * 2 ^ 59
def prefixEnd_1181810 : Nat := 4983230072969 + 3 ^ 40 * 1181810 * 2
def baseEnd_1181810 : Nat := 269705143240056176284427

theorem tailTrace_1181810 : CollatzResearch.WordTrace tailWord_1181810 prefixEnd_1181810 269705143240056176284427 := by
  unfold tailWord_1181810
  simp only [CollatzResearch.WordTrace]
  refine ⟨10776037962127920481009721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28736101232341121282692589 10776037962127920481009721)
  ·
    refine ⟨8082028471595940360757291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10776037962127920481009721 8082028471595940360757291)
    ·
      refine ⟨12123042707393910541135937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8082028471595940360757291 12123042707393910541135937)
      ·
        refine ⟨9092282030545432905851953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12123042707393910541135937 9092282030545432905851953)
        ·
          refine ⟨6819211522909074679388965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9092282030545432905851953 6819211522909074679388965)
          ·
            refine ⟨1278602160545451502385431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6819211522909074679388965 1278602160545451502385431)
            ·
              refine ⟨1917903240818177253578147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1278602160545451502385431 1917903240818177253578147)
              ·
                refine ⟨2876854861227265880367221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1917903240818177253578147 2876854861227265880367221)
                ·
                  refine ⟨269705143240056176284427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2876854861227265880367221 269705143240056176284427)
                  ·
                    rfl

theorem cell21_1181810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 1, 1, 5].length) (baseStart_1181810 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1181810 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1181810 prefixEnd_1181810 := by exact prefixLift 1181810
  have htrace : WordTrace (prefixWord ++ tailWord_1181810) baseStart_1181810 baseEnd_1181810 := by
    simpa [prefixWord, tailWord_1181810, baseEnd_1181810] using wordTrace_append hprefix tailTrace_1181810
  have hstable : (prefixWord ++ tailWord_1181810).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1181810).length < 2 ^ (prefixWord ++ tailWord_1181810).sum := by decide
  have hdescent : baseEnd_1181810 < baseStart_1181810 := by decide
  rcases family_descends (prefixWord ++ tailWord_1181810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1181883 : List Nat := [1, 1, 1, 1, 1, 2, 5, 5, 4]
def baseStart_1181883 : Nat := 118140960795 + 1181883 * 2 ^ 59
def prefixEnd_1181883 : Nat := 4983230072969 + 3 ^ 40 * 1181883 * 2
def baseEnd_1181883 : Nat := 269721802834624271567611

theorem tailTrace_1181883 : CollatzResearch.WordTrace tailWord_1181883 prefixEnd_1181883 269721802834624271567611 := by
  unfold tailWord_1181883
  simp only [CollatzResearch.WordTrace]
  refine ⟨43106814377247215391446303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28737876251498143594297535 43106814377247215391446303)
  ·
    refine ⟨64660221565870823087169455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43106814377247215391446303 64660221565870823087169455)
    ·
      refine ⟨96990332348806234630754183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64660221565870823087169455 96990332348806234630754183)
      ·
        refine ⟨145485498523209351946131275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96990332348806234630754183 145485498523209351946131275)
        ·
          refine ⟨218228247784814027919196913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 145485498523209351946131275 218228247784814027919196913)
          ·
            refine ⟨163671185838610520939397685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 218228247784814027919196913 163671185838610520939397685)
            ·
              refine ⟨15344173672369736338068533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 163671185838610520939397685 15344173672369736338068533)
              ·
                refine ⟨1438516281784662781693925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15344173672369736338068533 1438516281784662781693925)
                ·
                  refine ⟨269721802834624271567611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1438516281784662781693925 269721802834624271567611)
                  ·
                    rfl

theorem cell21_1181883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 5, 4].length) (baseStart_1181883 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1181883 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1181883 prefixEnd_1181883 := by exact prefixLift 1181883
  have htrace : WordTrace (prefixWord ++ tailWord_1181883) baseStart_1181883 baseEnd_1181883 := by
    simpa [prefixWord, tailWord_1181883, baseEnd_1181883] using wordTrace_append hprefix tailTrace_1181883
  have hstable : (prefixWord ++ tailWord_1181883).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1181883).length < 2 ^ (prefixWord ++ tailWord_1181883).sum := by decide
  have hdescent : baseEnd_1181883 < baseStart_1181883 := by decide
  rcases family_descends (prefixWord ++ tailWord_1181883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1181886 : List Nat := [4, 2, 1, 1, 4, 1, 1, 2, 5]
def baseStart_1181886 : Nat := 118140960795 + 1181886 * 2 ^ 59
def prefixEnd_1181886 : Nat := 4983230072969 + 3 ^ 40 * 1181886 * 2
def baseEnd_1181886 : Nat := 269722487475496933017605

theorem tailTrace_1181886 : CollatzResearch.WordTrace tailWord_1181886 prefixEnd_1181886 269722487475496933017605 := by
  unfold tailWord_1181886
  simp only [CollatzResearch.WordTrace]
  refine ⟨5388365474529543362975689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28737949197490897935870341 5388365474529543362975689)
  ·
    refine ⟨4041274105897157522231767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5388365474529543362975689 4041274105897157522231767)
    ·
      refine ⟨6061911158845736283347651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4041274105897157522231767 6061911158845736283347651)
      ·
        refine ⟨9092866738268604425021477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6061911158845736283347651 9092866738268604425021477)
        ·
          refine ⟨1704912513425363329691527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9092866738268604425021477 1704912513425363329691527)
          ·
            refine ⟨2557368770138044994537291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1704912513425363329691527 2557368770138044994537291)
            ·
              refine ⟨3836053155207067491805937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2557368770138044994537291 3836053155207067491805937)
              ·
                refine ⟨2877039866405300618854453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3836053155207067491805937 2877039866405300618854453)
                ·
                  refine ⟨269722487475496933017605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2877039866405300618854453 269722487475496933017605)
                  ·
                    rfl

theorem cell21_1181886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 2, 5].length) (baseStart_1181886 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1181886 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1181886 prefixEnd_1181886 := by exact prefixLift 1181886
  have htrace : WordTrace (prefixWord ++ tailWord_1181886) baseStart_1181886 baseEnd_1181886 := by
    simpa [prefixWord, tailWord_1181886, baseEnd_1181886] using wordTrace_append hprefix tailTrace_1181886
  have hstable : (prefixWord ++ tailWord_1181886).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1181886).length < 2 ^ (prefixWord ++ tailWord_1181886).sum := by decide
  have hdescent : baseEnd_1181886 < baseStart_1181886 := by decide
  rcases family_descends (prefixWord ++ tailWord_1181886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1181917 : List Nat := [1, 4, 3, 2, 1, 1, 3, 2, 4]
def baseStart_1181917 : Nat := 118140960795 + 1181917 * 2 ^ 59
def prefixEnd_1181917 : Nat := 4983230072969 + 3 ^ 40 * 1181917 * 2
def baseEnd_1181917 : Nat := 269729562097847768000875

theorem tailTrace_1181917 : CollatzResearch.WordTrace tailWord_1181917 prefixEnd_1181917 269729562097847768000875 := by
  unfold tailWord_1181917
  simp only [CollatzResearch.WordTrace]
  refine ⟨43108054459124039198184005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28738702972749359465456003 43108054459124039198184005)
  ·
    refine ⟨8082760211085757349659501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43108054459124039198184005 8082760211085757349659501)
    ·
      refine ⟨3031035079157159006122313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8082760211085757349659501 3031035079157159006122313)
      ·
        refine ⟨2273276309367869254591735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3031035079157159006122313 2273276309367869254591735)
        ·
          refine ⟨3409914464051803881887603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2273276309367869254591735 3409914464051803881887603)
          ·
            refine ⟨5114871696077705822831405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3409914464051803881887603 5114871696077705822831405)
            ·
              refine ⟨1918076886029139683561777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5114871696077705822831405 1918076886029139683561777)
              ·
                refine ⟨1438557664521854762671333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1918076886029139683561777 1438557664521854762671333)
                ·
                  refine ⟨269729562097847768000875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1438557664521854762671333 269729562097847768000875)
                  ·
                    rfl

theorem cell21_1181917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 3, 2, 4].length) (baseStart_1181917 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1181917 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1181917 prefixEnd_1181917 := by exact prefixLift 1181917
  have htrace : WordTrace (prefixWord ++ tailWord_1181917) baseStart_1181917 baseEnd_1181917 := by
    simpa [prefixWord, tailWord_1181917, baseEnd_1181917] using wordTrace_append hprefix tailTrace_1181917
  have hstable : (prefixWord ++ tailWord_1181917).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1181917).length < 2 ^ (prefixWord ++ tailWord_1181917).sum := by decide
  have hdescent : baseEnd_1181917 < baseStart_1181917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1181917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1181962 : List Nat := [3, 1, 2, 2, 1, 1, 5, 3, 3]
def baseStart_1181962 : Nat := 118140960795 + 1181962 * 2 ^ 59
def prefixEnd_1181962 : Nat := 4983230072969 + 3 ^ 40 * 1181962 * 2
def baseEnd_1181962 : Nat := 269739831710937689750783

theorem tailTrace_1181962 : CollatzResearch.WordTrace tailWord_1181962 prefixEnd_1181962 269739831710937689750783 := by
  unfold tailWord_1181962
  simp only [CollatzResearch.WordTrace]
  refine ⟨10777423935990252970893035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28739797162640674589048093 10777423935990252970893035)
  ·
    refine ⟨16166135903985379456339553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10777423935990252970893035 16166135903985379456339553)
    ·
      refine ⟨12124601927989034592254665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16166135903985379456339553 12124601927989034592254665)
      ·
        refine ⟨9093451445991775944190999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12124601927989034592254665 9093451445991775944190999)
        ·
          refine ⟨13640177168987663916286499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9093451445991775944190999 13640177168987663916286499)
          ·
            refine ⟨20460265753481495874429749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13640177168987663916286499 20460265753481495874429749)
            ·
              refine ⟨1918149914388890238227789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20460265753481495874429749 1918149914388890238227789)
              ·
                refine ⟨719306217895833839335421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1918149914388890238227789 719306217895833839335421)
                ·
                  refine ⟨269739831710937689750783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 719306217895833839335421 269739831710937689750783)
                  ·
                    rfl

theorem cell21_1181962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 5, 3, 3].length) (baseStart_1181962 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1181962 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1181962 prefixEnd_1181962 := by exact prefixLift 1181962
  have htrace : WordTrace (prefixWord ++ tailWord_1181962) baseStart_1181962 baseEnd_1181962 := by
    simpa [prefixWord, tailWord_1181962, baseEnd_1181962] using wordTrace_append hprefix tailTrace_1181962
  have hstable : (prefixWord ++ tailWord_1181962).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1181962).length < 2 ^ (prefixWord ++ tailWord_1181962).sum := by decide
  have hdescent : baseEnd_1181962 < baseStart_1181962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1181962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1181973 : List Nat := [1, 3, 2, 1, 2, 1, 11]
def baseStart_1181973 : Nat := 118140960795 + 1181973 * 2 ^ 59
def prefixEnd_1181973 : Nat := 4983230072969 + 3 ^ 40 * 1181973 * 2
def baseEnd_1181973 : Nat := 29971371340089346118603

theorem tailTrace_1181973 : CollatzResearch.WordTrace tailWord_1181973 prefixEnd_1181973 29971371340089346118603 := by
  unfold tailWord_1181973
  simp only [CollatzResearch.WordTrace]
  refine ⟨43110096946921160762222573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28740064631280773841481715 43110096946921160762222573)
  ·
    refine ⟨16166286355095435285833465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43110096946921160762222573 16166286355095435285833465)
    ·
      refine ⟨12124714766321576464375099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16166286355095435285833465 12124714766321576464375099)
      ·
        refine ⟨18187072149482364696562649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12124714766321576464375099 18187072149482364696562649)
        ·
          refine ⟨13640304112111773522421987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18187072149482364696562649 13640304112111773522421987)
          ·
            refine ⟨20460456168167660283632981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13640304112111773522421987 20460456168167660283632981)
            ·
              refine ⟨29971371340089346118603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 20460456168167660283632981 29971371340089346118603)
              ·
                rfl

theorem cell21_1181973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 11].length) (baseStart_1181973 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1181973 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1181973 prefixEnd_1181973 := by exact prefixLift 1181973
  have htrace : WordTrace (prefixWord ++ tailWord_1181973) baseStart_1181973 baseEnd_1181973 := by
    simpa [prefixWord, tailWord_1181973, baseEnd_1181973] using wordTrace_append hprefix tailTrace_1181973
  have hstable : (prefixWord ++ tailWord_1181973).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1181973).length < 2 ^ (prefixWord ++ tailWord_1181973).sum := by decide
  have hdescent : baseEnd_1181973 < baseStart_1181973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1181973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1182148 : List Nat := [2, 3, 3, 2, 2, 1, 3, 2, 3]
def baseStart_1182148 : Nat := 118140960795 + 1182148 * 2 ^ 59
def prefixEnd_1182148 : Nat := 4983230072969 + 3 ^ 40 * 1182148 * 2
def baseEnd_1182148 : Nat := 269782279445042699650403

theorem tailTrace_1182148 : CollatzResearch.WordTrace tailWord_1182148 prefixEnd_1182148 269782279445042699650403 := by
  unfold tailWord_1182148
  simp only [CollatzResearch.WordTrace]
  refine ⟨21558239860643582824921549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28744319814191443766562065 21558239860643582824921549)
  ·
    refine ⟨8084339947741343559345581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21558239860643582824921549 8084339947741343559345581)
    ·
      refine ⟨3031627480403003834754593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8084339947741343559345581 3031627480403003834754593)
      ·
        refine ⟨2273720610302252876065945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3031627480403003834754593 2273720610302252876065945)
        ·
          refine ⟨1705290457726689657049459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2273720610302252876065945 1705290457726689657049459)
          ·
            refine ⟨2557935686590034485574189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1705290457726689657049459 2557935686590034485574189)
            ·
              refine ⟨959225882471262932090321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2557935686590034485574189 959225882471262932090321)
              ·
                refine ⟨719419411853447199067741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 959225882471262932090321 719419411853447199067741)
                ·
                  refine ⟨269782279445042699650403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 719419411853447199067741 269782279445042699650403)
                  ·
                    rfl

theorem cell21_1182148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 3, 2, 3].length) (baseStart_1182148 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1182148 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1182148 prefixEnd_1182148 := by exact prefixLift 1182148
  have htrace : WordTrace (prefixWord ++ tailWord_1182148) baseStart_1182148 baseEnd_1182148 := by
    simpa [prefixWord, tailWord_1182148, baseEnd_1182148] using wordTrace_append hprefix tailTrace_1182148
  have hstable : (prefixWord ++ tailWord_1182148).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1182148).length < 2 ^ (prefixWord ++ tailWord_1182148).sum := by decide
  have hdescent : baseEnd_1182148 < baseStart_1182148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1182148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1182232 : List Nat := [2, 1, 2, 3, 3, 1, 1, 1, 7]
def baseStart_1182232 : Nat := 118140960795 + 1182232 * 2 ^ 59
def prefixEnd_1182232 : Nat := 4983230072969 + 3 ^ 40 * 1182232 * 2
def baseEnd_1182232 : Nat := 269801449389477220250231

theorem tailTrace_1182232 : CollatzResearch.WordTrace tailWord_1182232 prefixEnd_1182232 269801449389477220250231 := by
  unfold tailWord_1182232
  simp only [CollatzResearch.WordTrace]
  refine ⟨21559771726491423997950475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28746362301988565330600633 21559771726491423997950475)
  ·
    refine ⟨32339657589737135996925713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21559771726491423997950475 32339657589737135996925713)
    ·
      refine ⟨24254743192302851997694285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32339657589737135996925713 24254743192302851997694285)
      ·
        refine ⟨9095528697113569499135357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24254743192302851997694285 9095528697113569499135357)
        ·
          refine ⟨3410823261417588562175759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9095528697113569499135357 3410823261417588562175759)
          ·
            refine ⟨5116234892126382843263639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3410823261417588562175759 5116234892126382843263639)
            ·
              refine ⟨7674352338189574264895459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5116234892126382843263639 7674352338189574264895459)
              ·
                refine ⟨11511528507284361397343189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7674352338189574264895459 11511528507284361397343189)
                ·
                  refine ⟨269801449389477220250231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11511528507284361397343189 269801449389477220250231)
                  ·
                    rfl

theorem cell21_1182232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 1, 7].length) (baseStart_1182232 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1182232 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1182232 prefixEnd_1182232 := by exact prefixLift 1182232
  have htrace : WordTrace (prefixWord ++ tailWord_1182232) baseStart_1182232 baseEnd_1182232 := by
    simpa [prefixWord, tailWord_1182232, baseEnd_1182232] using wordTrace_append hprefix tailTrace_1182232
  have hstable : (prefixWord ++ tailWord_1182232).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1182232).length < 2 ^ (prefixWord ++ tailWord_1182232).sum := by decide
  have hdescent : baseEnd_1182232 < baseStart_1182232 := by decide
  rcases family_descends (prefixWord ++ tailWord_1182232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1182300 : List Nat := [2, 2, 4, 1, 4, 1, 1, 3, 3]
def baseStart_1182300 : Nat := 118140960795 + 1182300 * 2 ^ 59
def prefixEnd_1182300 : Nat := 4983230072969 + 3 ^ 40 * 1182300 * 2
def baseEnd_1182300 : Nat := 269816967915924213116759

theorem tailTrace_1182300 : CollatzResearch.WordTrace tailWord_1182300 prefixEnd_1182300 269816967915924213116759 := by
  unfold tailWord_1182300
  simp only [CollatzResearch.WordTrace]
  refine ⟨21561011808368247804688177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28748015744490997072917569 21561011808368247804688177)
  ·
    refine ⟨16170758856276185853516133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21561011808368247804688177 16170758856276185853516133)
    ·
      refine ⟨3032017285551784847534275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16170758856276185853516133 3032017285551784847534275)
      ·
        refine ⟨4548025928327677271301413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3032017285551784847534275 4548025928327677271301413)
        ·
          refine ⟨852754861561439488369015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4548025928327677271301413 852754861561439488369015)
          ·
            refine ⟨1279132292342159232553523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 852754861561439488369015 1279132292342159232553523)
            ·
              refine ⟨1918698438513238848830285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1279132292342159232553523 1918698438513238848830285)
              ·
                refine ⟨719511914442464568311357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1918698438513238848830285 719511914442464568311357)
                ·
                  refine ⟨269816967915924213116759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 719511914442464568311357 269816967915924213116759)
                  ·
                    rfl

theorem cell21_1182300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 1, 3, 3].length) (baseStart_1182300 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1182300 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1182300 prefixEnd_1182300 := by exact prefixLift 1182300
  have htrace : WordTrace (prefixWord ++ tailWord_1182300) baseStart_1182300 baseEnd_1182300 := by
    simpa [prefixWord, tailWord_1182300, baseEnd_1182300] using wordTrace_append hprefix tailTrace_1182300
  have hstable : (prefixWord ++ tailWord_1182300).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1182300).length < 2 ^ (prefixWord ++ tailWord_1182300).sum := by decide
  have hdescent : baseEnd_1182300 < baseStart_1182300 := by decide
  rcases family_descends (prefixWord ++ tailWord_1182300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1182460 : List Nat := [2, 2, 2, 1, 3, 2, 2, 2, 5]
def baseStart_1182460 : Nat := 118140960795 + 1182460 * 2 ^ 59
def prefixEnd_1182460 : Nat := 4983230072969 + 3 ^ 40 * 1182460 * 2
def baseEnd_1182460 : Nat := 269853482095799490449765

theorem tailTrace_1182460 : CollatzResearch.WordTrace tailWord_1182460 prefixEnd_1182460 269853482095799490449765 := by
  unfold tailWord_1182460
  simp only [CollatzResearch.WordTrace]
  refine ⟨21563929648078421467600417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28751906197437895290133889 21563929648078421467600417)
  ·
    refine ⟨16172947236058816100700313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21563929648078421467600417 16172947236058816100700313)
    ·
      refine ⟨12129710427044112075525235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16172947236058816100700313 12129710427044112075525235)
      ·
        refine ⟨18194565640566168113287853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12129710427044112075525235 18194565640566168113287853)
        ·
          refine ⟨6822962115212313042482945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18194565640566168113287853 6822962115212313042482945)
          ·
            refine ⟨5117221586409234781862209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6822962115212313042482945 5117221586409234781862209)
            ·
              refine ⟨3837916189806926086396657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5117221586409234781862209 3837916189806926086396657)
              ·
                refine ⟨2878437142355194564797493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3837916189806926086396657 2878437142355194564797493)
                ·
                  refine ⟨269853482095799490449765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2878437142355194564797493 269853482095799490449765)
                  ·
                    rfl

theorem cell21_1182460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 2, 5].length) (baseStart_1182460 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1182460 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1182460 prefixEnd_1182460 := by exact prefixLift 1182460
  have htrace : WordTrace (prefixWord ++ tailWord_1182460) baseStart_1182460 baseEnd_1182460 := by
    simpa [prefixWord, tailWord_1182460, baseEnd_1182460] using wordTrace_append hprefix tailTrace_1182460
  have hstable : (prefixWord ++ tailWord_1182460).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1182460).length < 2 ^ (prefixWord ++ tailWord_1182460).sum := by decide
  have hdescent : baseEnd_1182460 < baseStart_1182460 := by decide
  rcases family_descends (prefixWord ++ tailWord_1182460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1182474 : List Nat := [3, 1, 2, 2, 1, 2, 1, 1, 8]
def baseStart_1182474 : Nat := 118140960795 + 1182474 * 2 ^ 59
def prefixEnd_1182474 : Nat := 4983230072969 + 3 ^ 40 * 1182474 * 2
def baseEnd_1182474 : Nat := 269856677086538577216403

theorem tailTrace_1182474 : CollatzResearch.WordTrace tailWord_1182474 prefixEnd_1182474 269856677086538577216403 := by
  unfold tailWord_1182474
  simp only [CollatzResearch.WordTrace]
  refine ⟨10782092479526530831552619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28752246612070748884140317 10782092479526530831552619)
  ·
    refine ⟨16173138719289796247328929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10782092479526530831552619 16173138719289796247328929)
    ·
      refine ⟨12129854039467347185496697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16173138719289796247328929 12129854039467347185496697)
      ·
        refine ⟨9097390529600510389122523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12129854039467347185496697 9097390529600510389122523)
        ·
          refine ⟨13646085794400765583683785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9097390529600510389122523 13646085794400765583683785)
          ·
            refine ⟨10234564345800574187762839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13646085794400765583683785 10234564345800574187762839)
            ·
              refine ⟨15351846518700861281644259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10234564345800574187762839 15351846518700861281644259)
              ·
                refine ⟨23027769778051291922466389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15351846518700861281644259 23027769778051291922466389)
                ·
                  refine ⟨269856677086538577216403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23027769778051291922466389 269856677086538577216403)
                  ·
                    rfl

theorem cell21_1182474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 8].length) (baseStart_1182474 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1182474 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1182474 prefixEnd_1182474 := by exact prefixLift 1182474
  have htrace : WordTrace (prefixWord ++ tailWord_1182474) baseStart_1182474 baseEnd_1182474 := by
    simpa [prefixWord, tailWord_1182474, baseEnd_1182474] using wordTrace_append hprefix tailTrace_1182474
  have hstable : (prefixWord ++ tailWord_1182474).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1182474).length < 2 ^ (prefixWord ++ tailWord_1182474).sum := by decide
  have hdescent : baseEnd_1182474 < baseStart_1182474 := by decide
  rcases family_descends (prefixWord ++ tailWord_1182474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1182519 : List Nat := [1, 1, 3, 1, 2, 1, 4, 1, 7]
def baseStart_1182519 : Nat := 118140960795 + 1182519 * 2 ^ 59
def prefixEnd_1182519 : Nat := 4983230072969 + 3 ^ 40 * 1182519 * 2
def baseEnd_1182519 : Nat := 269866946699628498966311

theorem tailTrace_1182519 : CollatzResearch.WordTrace tailWord_1182519 prefixEnd_1182519 269866946699628498966311 := by
  unfold tailWord_1182519
  simp only [CollatzResearch.WordTrace]
  refine ⟨43130011202943096011598611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28753340801962064007732407 43130011202943096011598611)
  ·
    refine ⟨64695016804414644017397917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43130011202943096011598611 64695016804414644017397917)
    ·
      refine ⟨24260631301655491506524219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64695016804414644017397917 24260631301655491506524219)
      ·
        refine ⟨36390946952483237259786329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24260631301655491506524219 36390946952483237259786329)
        ·
          refine ⟨27293210214362427944839747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36390946952483237259786329 27293210214362427944839747)
          ·
            refine ⟨40939815321543641917259621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27293210214362427944839747 40939815321543641917259621)
            ·
              refine ⟨7676215372789432859486179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40939815321543641917259621 7676215372789432859486179)
              ·
                refine ⟨11514323059184149289229269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7676215372789432859486179 11514323059184149289229269)
                ·
                  refine ⟨269866946699628498966311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11514323059184149289229269 269866946699628498966311)
                  ·
                    rfl

theorem cell21_1182519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 1, 7].length) (baseStart_1182519 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1182519 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1182519 prefixEnd_1182519 := by exact prefixLift 1182519
  have htrace : WordTrace (prefixWord ++ tailWord_1182519) baseStart_1182519 baseEnd_1182519 := by
    simpa [prefixWord, tailWord_1182519, baseEnd_1182519] using wordTrace_append hprefix tailTrace_1182519
  have hstable : (prefixWord ++ tailWord_1182519).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1182519).length < 2 ^ (prefixWord ++ tailWord_1182519).sum := by decide
  have hdescent : baseEnd_1182519 < baseStart_1182519 := by decide
  rcases family_descends (prefixWord ++ tailWord_1182519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1182553 : List Nat := [1, 2, 1, 2, 2, 5, 1, 4, 3]
def baseStart_1182553 : Nat := 118140960795 + 1182553 * 2 ^ 59
def prefixEnd_1182553 : Nat := 4983230072969 + 3 ^ 40 * 1182553 * 2
def baseEnd_1182553 : Nat := 269874705962851995399575

theorem tailTrace_1182553 : CollatzResearch.WordTrace tailWord_1182553 prefixEnd_1182553 269874705962851995399575 := by
  unfold tailWord_1182553
  simp only [CollatzResearch.WordTrace]
  refine ⟨43131251284819919818336313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28754167523213279878890875 43131251284819919818336313)
  ·
    refine ⟨32348438463614939863752235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43131251284819919818336313 32348438463614939863752235)
    ·
      refine ⟨48522657695422409795628353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32348438463614939863752235 48522657695422409795628353)
      ·
        refine ⟨36391993271566807346721265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48522657695422409795628353 36391993271566807346721265)
        ·
          refine ⟨27293994953675105510040949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36391993271566807346721265 27293994953675105510040949)
          ·
            refine ⟨2558812026907041141566339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27293994953675105510040949 2558812026907041141566339)
            ·
              refine ⟨3838218040360561712349509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2558812026907041141566339 3838218040360561712349509)
              ·
                refine ⟨719665882567605321065533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3838218040360561712349509 719665882567605321065533)
                ·
                  refine ⟨269874705962851995399575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 719665882567605321065533 269874705962851995399575)
                  ·
                    rfl

theorem cell21_1182553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 4, 3].length) (baseStart_1182553 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1182553 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1182553 prefixEnd_1182553 := by exact prefixLift 1182553
  have htrace : WordTrace (prefixWord ++ tailWord_1182553) baseStart_1182553 baseEnd_1182553 := by
    simpa [prefixWord, tailWord_1182553, baseEnd_1182553] using wordTrace_append hprefix tailTrace_1182553
  have hstable : (prefixWord ++ tailWord_1182553).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1182553).length < 2 ^ (prefixWord ++ tailWord_1182553).sum := by decide
  have hdescent : baseEnd_1182553 < baseStart_1182553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1182553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1182567 : List Nat := [1, 1, 5, 1, 2, 2, 2, 3, 4]
def baseStart_1182567 : Nat := 118140960795 + 1182567 * 2 ^ 59
def prefixEnd_1182567 : Nat := 4983230072969 + 3 ^ 40 * 1182567 * 2
def baseEnd_1182567 : Nat := 269877900953591082166213

theorem tailTrace_1182567 : CollatzResearch.WordTrace tailWord_1182567 prefixEnd_1182567 269877900953591082166213 := by
  unfold tailWord_1182567
  simp only [CollatzResearch.WordTrace]
  refine ⟨43131761906769200209345955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28754507937846133472897303 43131761906769200209345955)
  ·
    refine ⟨64697642860153800314018933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43131761906769200209345955 64697642860153800314018933)
    ·
      refine ⟨6065404018139418779439275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 64697642860153800314018933 6065404018139418779439275)
      ·
        refine ⟨9098106027209128169158913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6065404018139418779439275 9098106027209128169158913)
        ·
          refine ⟨6823579520406846126869185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9098106027209128169158913 6823579520406846126869185)
          ·
            refine ⟨5117684640305134595151889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6823579520406846126869185 5117684640305134595151889)
            ·
              refine ⟨3838263480228850946363917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5117684640305134595151889 3838263480228850946363917)
              ·
                refine ⟨1439348805085819104886469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3838263480228850946363917 1439348805085819104886469)
                ·
                  refine ⟨269877900953591082166213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1439348805085819104886469 269877900953591082166213)
                  ·
                    rfl

theorem cell21_1182567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 3, 4].length) (baseStart_1182567 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1182567 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1182567 prefixEnd_1182567 := by exact prefixLift 1182567
  have htrace : WordTrace (prefixWord ++ tailWord_1182567) baseStart_1182567 baseEnd_1182567 := by
    simpa [prefixWord, tailWord_1182567, baseEnd_1182567] using wordTrace_append hprefix tailTrace_1182567
  have hstable : (prefixWord ++ tailWord_1182567).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1182567).length < 2 ^ (prefixWord ++ tailWord_1182567).sum := by decide
  have hdescent : baseEnd_1182567 < baseStart_1182567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1182567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1182595 : List Nat := [1, 1, 1, 3, 4, 1, 1, 2, 7]
def baseStart_1182595 : Nat := 118140960795 + 1182595 * 2 ^ 59
def prefixEnd_1182595 : Nat := 4983230072969 + 3 ^ 40 * 1182595 * 2
def baseEnd_1182595 : Nat := 269884290935069255699489

theorem tailTrace_1182595 : CollatzResearch.WordTrace tailWord_1182595 prefixEnd_1182595 269884290935069255699489 := by
  unfold tailWord_1182595
  simp only [CollatzResearch.WordTrace]
  refine ⟨43132783150667760991365239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28755188767111840660910159 43132783150667760991365239)
  ·
    refine ⟨64699174726001641487047859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43132783150667760991365239 64699174726001641487047859)
    ·
      refine ⟨97048762089002462230571789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64699174726001641487047859 97048762089002462230571789)
      ·
        refine ⟨36393285783375923336464421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97048762089002462230571789 36393285783375923336464421)
        ·
          refine ⟨6823741084382985625587079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36393285783375923336464421 6823741084382985625587079)
          ·
            refine ⟨10235611626574478438380619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6823741084382985625587079 10235611626574478438380619)
            ·
              refine ⟨15353417439861717657570929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10235611626574478438380619 15353417439861717657570929)
              ·
                refine ⟨11515063079896288243178197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15353417439861717657570929 11515063079896288243178197)
                ·
                  refine ⟨269884290935069255699489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11515063079896288243178197 269884290935069255699489)
                  ·
                    rfl

theorem cell21_1182595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 2, 7].length) (baseStart_1182595 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1182595 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1182595 prefixEnd_1182595 := by exact prefixLift 1182595
  have htrace : WordTrace (prefixWord ++ tailWord_1182595) baseStart_1182595 baseEnd_1182595 := by
    simpa [prefixWord, tailWord_1182595, baseEnd_1182595] using wordTrace_append hprefix tailTrace_1182595
  have hstable : (prefixWord ++ tailWord_1182595).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1182595).length < 2 ^ (prefixWord ++ tailWord_1182595).sum := by decide
  have hdescent : baseEnd_1182595 < baseStart_1182595 := by decide
  rcases family_descends (prefixWord ++ tailWord_1182595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1182674 : List Nat := [3, 2, 2, 3, 1, 2, 2, 6]
def baseStart_1182674 : Nat := 118140960795 + 1182674 * 2 ^ 59
def prefixEnd_1182674 : Nat := 4983230072969 + 3 ^ 40 * 1182674 * 2
def baseEnd_1182674 : Nat := 89967439937127557960887

theorem tailTrace_1182674 : CollatzResearch.WordTrace tailWord_1182674 prefixEnd_1182674 89967439937127557960887 := by
  unfold tailWord_1182674
  simp only [CollatzResearch.WordTrace]
  refine ⟨10783916129345389370872769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28757109678254371655660717 10783916129345389370872769)
  ·
    refine ⟨8087937097009042028154577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10783916129345389370872769 8087937097009042028154577)
    ·
      refine ⟨6065952822756781521115933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8087937097009042028154577 6065952822756781521115933)
      ·
        refine ⟨2274732308533793070418475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6065952822756781521115933 2274732308533793070418475)
        ·
          refine ⟨3412098462800689605627713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2274732308533793070418475 3412098462800689605627713)
          ·
            refine ⟨2559073847100517204220785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3412098462800689605627713 2559073847100517204220785)
            ·
              refine ⟨1919305385325387903165589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2559073847100517204220785 1919305385325387903165589)
              ·
                refine ⟨89967439937127557960887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1919305385325387903165589 89967439937127557960887)
                ·
                  rfl

theorem cell21_1182674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 2, 6].length) (baseStart_1182674 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1182674 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1182674 prefixEnd_1182674 := by exact prefixLift 1182674
  have htrace : WordTrace (prefixWord ++ tailWord_1182674) baseStart_1182674 baseEnd_1182674 := by
    simpa [prefixWord, tailWord_1182674, baseEnd_1182674] using wordTrace_append hprefix tailTrace_1182674
  have hstable : (prefixWord ++ tailWord_1182674).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1182674).length < 2 ^ (prefixWord ++ tailWord_1182674).sum := by decide
  have hdescent : baseEnd_1182674 < baseStart_1182674 := by decide
  rcases family_descends (prefixWord ++ tailWord_1182674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1182677 : List Nat := [1, 3, 2, 3, 3, 2, 2, 1, 4]
def baseStart_1182677 : Nat := 118140960795 + 1182677 * 2 ^ 59
def prefixEnd_1182677 : Nat := 4983230072969 + 3 ^ 40 * 1182677 * 2
def baseEnd_1182677 : Nat := 269903004452255335332655

theorem tailTrace_1182677 : CollatzResearch.WordTrace tailWord_1182677 prefixEnd_1182677 269903004452255335332655 := by
  unfold tailWord_1182677
  simp only [CollatzResearch.WordTrace]
  refine ⟨43135773936370688995850285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28757182624247125997233523 43135773936370688995850285)
  ·
    refine ⟨16175915226139008373443857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43135773936370688995850285 16175915226139008373443857)
    ·
      refine ⟨12131936419604256280082893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16175915226139008373443857 12131936419604256280082893)
      ·
        refine ⟨4549476157351596105031085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12131936419604256280082893 4549476157351596105031085)
        ·
          refine ⟨1706053559006848539386657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4549476157351596105031085 1706053559006848539386657)
          ·
            refine ⟨1279540169255136404539993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1706053559006848539386657 1279540169255136404539993)
            ·
              refine ⟨959655126941352303404995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1279540169255136404539993 959655126941352303404995)
              ·
                refine ⟨1439482690412028455107493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 959655126941352303404995 1439482690412028455107493)
                ·
                  refine ⟨269903004452255335332655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1439482690412028455107493 269903004452255335332655)
                  ·
                    rfl

theorem cell21_1182677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 2, 1, 4].length) (baseStart_1182677 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1182677 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1182677 prefixEnd_1182677 := by exact prefixLift 1182677
  have htrace : WordTrace (prefixWord ++ tailWord_1182677) baseStart_1182677 baseEnd_1182677 := by
    simpa [prefixWord, tailWord_1182677, baseEnd_1182677] using wordTrace_append hprefix tailTrace_1182677
  have hstable : (prefixWord ++ tailWord_1182677).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1182677).length < 2 ^ (prefixWord ++ tailWord_1182677).sum := by decide
  have hdescent : baseEnd_1182677 < baseStart_1182677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1182677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1182708 : List Nat := [2, 6, 2, 1, 1, 9]
def baseStart_1182708 : Nat := 118140960795 + 1182708 * 2 ^ 59
def prefixEnd_1182708 : Nat := 4983230072969 + 3 ^ 40 * 1182708 * 2
def baseEnd_1182708 : Nat := 9996669595355784085775

theorem tailTrace_1182708 : CollatzResearch.WordTrace tailWord_1182708 prefixEnd_1182708 9996669595355784085775 := by
  unfold tailWord_1182708
  simp only [CollatzResearch.WordTrace]
  refine ⟨21568452299629190645114389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28757936399505587526819185 21568452299629190645114389)
  ·
    refine ⟨1011021201545118311489737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 21568452299629190645114389 1011021201545118311489737)
    ·
      refine ⟨758265901158838733617303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1011021201545118311489737 758265901158838733617303)
      ·
        refine ⟨1137398851738258100425955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 758265901158838733617303 1137398851738258100425955)
        ·
          refine ⟨1706098277607387150638933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1137398851738258100425955 1706098277607387150638933)
          ·
            refine ⟨9996669595355784085775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1706098277607387150638933 9996669595355784085775)
            ·
              rfl

theorem cell21_1182708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 9].length) (baseStart_1182708 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1182708 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1182708 prefixEnd_1182708 := by exact prefixLift 1182708
  have htrace : WordTrace (prefixWord ++ tailWord_1182708) baseStart_1182708 baseEnd_1182708 := by
    simpa [prefixWord, tailWord_1182708, baseEnd_1182708] using wordTrace_append hprefix tailTrace_1182708
  have hstable : (prefixWord ++ tailWord_1182708).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1182708).length < 2 ^ (prefixWord ++ tailWord_1182708).sum := by decide
  have hdescent : baseEnd_1182708 < baseStart_1182708 := by decide
  rcases family_descends (prefixWord ++ tailWord_1182708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1182716 : List Nat := [2, 2, 2, 1, 2, 12]
def baseStart_1182716 : Nat := 118140960795 + 1182716 * 2 ^ 59
def prefixEnd_1182716 : Nat := 4983230072969 + 3 ^ 40 * 1182716 * 2
def baseEnd_1182716 : Nat := 9996737214207404969725

theorem tailTrace_1182716 : CollatzResearch.WordTrace tailWord_1182716 prefixEnd_1182716 9996737214207404969725 := by
  unfold tailWord_1182716
  simp only [CollatzResearch.WordTrace]
  refine ⟨21568598191614699328260001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28758130922152932437680001 21568598191614699328260001)
  ·
    refine ⟨16176448643711024496195001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21568598191614699328260001 16176448643711024496195001)
    ·
      refine ⟨12132336482783268372146251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16176448643711024496195001 12132336482783268372146251)
      ·
        refine ⟨18198504724174902558219377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12132336482783268372146251 18198504724174902558219377)
        ·
          refine ⟨13648878543131176918664533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18198504724174902558219377 13648878543131176918664533)
          ·
            refine ⟨9996737214207404969725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 13648878543131176918664533 9996737214207404969725)
            ·
              rfl

theorem cell21_1182716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 12].length) (baseStart_1182716 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1182716 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1182716 prefixEnd_1182716 := by exact prefixLift 1182716
  have htrace : WordTrace (prefixWord ++ tailWord_1182716) baseStart_1182716 baseEnd_1182716 := by
    simpa [prefixWord, tailWord_1182716, baseEnd_1182716] using wordTrace_append hprefix tailTrace_1182716
  have hstable : (prefixWord ++ tailWord_1182716).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1182716).length < 2 ^ (prefixWord ++ tailWord_1182716).sum := by decide
  have hdescent : baseEnd_1182716 < baseStart_1182716 := by decide
  rcases family_descends (prefixWord ++ tailWord_1182716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1182781 : List Nat := [1, 4, 1, 3, 1, 2, 2, 4, 3]
def baseStart_1182781 : Nat := 118140960795 + 1182781 * 2 ^ 59
def prefixEnd_1182781 : Nat := 4983230072969 + 3 ^ 40 * 1182781 * 2
def baseEnd_1182781 : Nat := 269926738669174265599109

theorem tailTrace_1182781 : CollatzResearch.WordTrace tailWord_1182781 prefixEnd_1182781 269926738669174265599109 := by
  unfold tailWord_1182781
  simp only [CollatzResearch.WordTrace]
  refine ⟨43139567127993914757636197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28759711418662609838424131 43139567127993914757636197)
  ·
    refine ⟨8088668836498859017056787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43139567127993914757636197 8088668836498859017056787)
    ·
      refine ⟨12133003254748288525585181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8088668836498859017056787 12133003254748288525585181)
      ·
        refine ⟨4549876220530608197094443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12133003254748288525585181 4549876220530608197094443)
        ·
          refine ⟨6824814330795912295641665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4549876220530608197094443 6824814330795912295641665)
          ·
            refine ⟨5118610748096934221731249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6824814330795912295641665 5118610748096934221731249)
            ·
              refine ⟨3838958061072700666298437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5118610748096934221731249 3838958061072700666298437)
              ·
                refine ⟨719804636451131374930957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3838958061072700666298437 719804636451131374930957)
                ·
                  refine ⟨269926738669174265599109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 719804636451131374930957 269926738669174265599109)
                  ·
                    rfl

theorem cell21_1182781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 4, 3].length) (baseStart_1182781 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1182781 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1182781 prefixEnd_1182781 := by exact prefixLift 1182781
  have htrace : WordTrace (prefixWord ++ tailWord_1182781) baseStart_1182781 baseEnd_1182781 := by
    simpa [prefixWord, tailWord_1182781, baseEnd_1182781] using wordTrace_append hprefix tailTrace_1182781
  have hstable : (prefixWord ++ tailWord_1182781).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1182781).length < 2 ^ (prefixWord ++ tailWord_1182781).sum := by decide
  have hdescent : baseEnd_1182781 < baseStart_1182781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1182781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1182792 : List Nat := [2, 1, 3, 1, 1, 1, 4, 8]
def baseStart_1182792 : Nat := 118140960795 + 1182792 * 2 ^ 59
def prefixEnd_1182792 : Nat := 4983230072969 + 3 ^ 40 * 1182792 * 2
def baseEnd_1182792 : Nat := 89976416339680230305251

theorem tailTrace_1182792 : CollatzResearch.WordTrace tailWord_1182792 prefixEnd_1182792 89976416339680230305251 := by
  unfold tailWord_1182792
  simp only [CollatzResearch.WordTrace]
  refine ⟨21569984165477031818143315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28759978887302709090857753 21569984165477031818143315)
  ·
    refine ⟨32354976248215547727214973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21569984165477031818143315 32354976248215547727214973)
    ·
      refine ⟨12133116093080830397705615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32354976248215547727214973 12133116093080830397705615)
      ·
        refine ⟨18199674139621245596558423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12133116093080830397705615 18199674139621245596558423)
        ·
          refine ⟨27299511209431868394837635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18199674139621245596558423 27299511209431868394837635)
          ·
            refine ⟨40949266814147802592256453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27299511209431868394837635 40949266814147802592256453)
            ·
              refine ⟨7677987527652712986048085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40949266814147802592256453 7677987527652712986048085)
              ·
                refine ⟨89976416339680230305251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7677987527652712986048085 89976416339680230305251)
                ·
                  rfl

theorem cell21_1182792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 8].length) (baseStart_1182792 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1182792 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1182792 prefixEnd_1182792 := by exact prefixLift 1182792
  have htrace : WordTrace (prefixWord ++ tailWord_1182792) baseStart_1182792 baseEnd_1182792 := by
    simpa [prefixWord, tailWord_1182792, baseEnd_1182792] using wordTrace_append hprefix tailTrace_1182792
  have hstable : (prefixWord ++ tailWord_1182792).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1182792).length < 2 ^ (prefixWord ++ tailWord_1182792).sum := by decide
  have hdescent : baseEnd_1182792 < baseStart_1182792 := by decide
  rcases family_descends (prefixWord ++ tailWord_1182792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1182840 : List Nat := [2, 1, 2, 1, 1, 1, 4, 6, 3]
def baseStart_1182840 : Nat := 118140960795 + 1182840 * 2 ^ 59
def prefixEnd_1182840 : Nat := 4983230072969 + 3 ^ 40 * 1182840 * 2
def baseEnd_1182840 : Nat := 269940203273003274115655

theorem tailTrace_1182840 : CollatzResearch.WordTrace tailWord_1182840 prefixEnd_1182840 269940203273003274115655 := by
  unfold tailWord_1182840
  simp only [CollatzResearch.WordTrace]
  refine ⟨21570859517390083917016987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28761146023186778556022649 21570859517390083917016987)
  ·
    refine ⟨32356289276085125875525481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21570859517390083917016987 32356289276085125875525481)
    ·
      refine ⟨24267216957063844406644111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32356289276085125875525481 24267216957063844406644111)
      ·
        refine ⟨36400825435595766609966167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24267216957063844406644111 36400825435595766609966167)
        ·
          refine ⟨54601238153393649914949251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36400825435595766609966167 54601238153393649914949251)
          ·
            refine ⟨81901857230090474872423877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54601238153393649914949251 81901857230090474872423877)
            ·
              refine ⟨15356598230641964038579477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 81901857230090474872423877 15356598230641964038579477)
              ·
                refine ⟨719840542061342064308413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 15356598230641964038579477 719840542061342064308413)
                ·
                  refine ⟨269940203273003274115655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 719840542061342064308413 269940203273003274115655)
                  ·
                    rfl

theorem cell21_1182840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 6, 3].length) (baseStart_1182840 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1182840 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1182840 prefixEnd_1182840 := by exact prefixLift 1182840
  have htrace : WordTrace (prefixWord ++ tailWord_1182840) baseStart_1182840 baseEnd_1182840 := by
    simpa [prefixWord, tailWord_1182840, baseEnd_1182840] using wordTrace_append hprefix tailTrace_1182840
  have hstable : (prefixWord ++ tailWord_1182840).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1182840).length < 2 ^ (prefixWord ++ tailWord_1182840).sum := by decide
  have hdescent : baseEnd_1182840 < baseStart_1182840 := by decide
  rcases family_descends (prefixWord ++ tailWord_1182840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1182846 : List Nat := [4, 2, 4, 1, 1, 1, 1, 3, 4]
def baseStart_1182846 : Nat := 118140960795 + 1182846 * 2 ^ 59
def prefixEnd_1182846 : Nat := 4983230072969 + 3 ^ 40 * 1182846 * 2
def baseEnd_1182846 : Nat := 269941572554748597015643

theorem tailTrace_1182846 : CollatzResearch.WordTrace tailWord_1182846 prefixEnd_1182846 269941572554748597015643 := by
  unfold tailWord_1182846
  simp only [CollatzResearch.WordTrace]
  refine ⟨5392742234094803857344049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28761291915172287239168261 5392742234094803857344049)
  ·
    refine ⟨4044556675571102893008037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5392742234094803857344049 4044556675571102893008037)
    ·
      refine ⟨758354376669581792439007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4044556675571102893008037 758354376669581792439007)
      ·
        refine ⟨1137531565004372688658511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 758354376669581792439007 1137531565004372688658511)
        ·
          refine ⟨1706297347506559032987767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1137531565004372688658511 1706297347506559032987767)
          ·
            refine ⟨2559446021259838549481651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1706297347506559032987767 2559446021259838549481651)
            ·
              refine ⟨3839169031889757824222477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2559446021259838549481651 3839169031889757824222477)
              ·
                refine ⟨1439688386958659184083429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3839169031889757824222477 1439688386958659184083429)
                ·
                  refine ⟨269941572554748597015643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1439688386958659184083429 269941572554748597015643)
                  ·
                    rfl

theorem cell21_1182846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 3, 4].length) (baseStart_1182846 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1182846 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1182846 prefixEnd_1182846 := by exact prefixLift 1182846
  have htrace : WordTrace (prefixWord ++ tailWord_1182846) baseStart_1182846 baseEnd_1182846 := by
    simpa [prefixWord, tailWord_1182846, baseEnd_1182846] using wordTrace_append hprefix tailTrace_1182846
  have hstable : (prefixWord ++ tailWord_1182846).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1182846).length < 2 ^ (prefixWord ++ tailWord_1182846).sum := by decide
  have hdescent : baseEnd_1182846 < baseStart_1182846 := by decide
  rcases family_descends (prefixWord ++ tailWord_1182846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1182930 : List Nat := [3, 2, 2, 2, 1, 1, 2, 2, 6]
def baseStart_1182930 : Nat := 118140960795 + 1182930 * 2 ^ 59
def prefixEnd_1182930 : Nat := 4983230072969 + 3 ^ 40 * 1182930 * 2
def baseEnd_1182930 : Nat := 269960742499183117615471

theorem tailTrace_1182930 : CollatzResearch.WordTrace tailWord_1182930 prefixEnd_1182930 269960742499183117615471 := by
  unfold tailWord_1182930
  simp only [CollatzResearch.WordTrace]
  refine ⟨10786250401113528301202561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28763334402969408803206829 10786250401113528301202561)
  ·
    refine ⟨8089687800835146225901921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10786250401113528301202561 8089687800835146225901921)
    ·
      refine ⟨6067265850626359669426441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8089687800835146225901921 6067265850626359669426441)
      ·
        refine ⟨4550449387969769752069831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6067265850626359669426441 4550449387969769752069831)
        ·
          refine ⟨6825674081954654628104747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4550449387969769752069831 6825674081954654628104747)
          ·
            refine ⟨10238511122931981942157121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6825674081954654628104747 10238511122931981942157121)
            ·
              refine ⟨7678883342198986456617841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10238511122931981942157121 7678883342198986456617841)
              ·
                refine ⟨5759162506649239842463381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7678883342198986456617841 5759162506649239842463381)
                ·
                  refine ⟨269960742499183117615471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5759162506649239842463381 269960742499183117615471)
                  ·
                    rfl

theorem cell21_1182930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 2, 6].length) (baseStart_1182930 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1182930 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1182930 prefixEnd_1182930 := by exact prefixLift 1182930
  have htrace : WordTrace (prefixWord ++ tailWord_1182930) baseStart_1182930 baseEnd_1182930 := by
    simpa [prefixWord, tailWord_1182930, baseEnd_1182930] using wordTrace_append hprefix tailTrace_1182930
  have hstable : (prefixWord ++ tailWord_1182930).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1182930).length < 2 ^ (prefixWord ++ tailWord_1182930).sum := by decide
  have hdescent : baseEnd_1182930 < baseStart_1182930 := by decide
  rcases family_descends (prefixWord ++ tailWord_1182930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1182933 : List Nat := [1, 3, 2, 4, 1, 1, 1, 5, 3]
def baseStart_1182933 : Nat := 118140960795 + 1182933 * 2 ^ 59
def prefixEnd_1182933 : Nat := 4983230072969 + 3 ^ 40 * 1182933 * 2
def baseEnd_1182933 : Nat := 269961427140055779065465

theorem tailTrace_1182933 : CollatzResearch.WordTrace tailWord_1182933 prefixEnd_1182933 269961427140055779065465 := by
  unfold tailWord_1182933
  simp only [CollatzResearch.WordTrace]
  refine ⟨43145111023443244717169453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28763407348962163144779635 43145111023443244717169453)
  ·
    refine ⟨16179416633791216768938545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43145111023443244717169453 16179416633791216768938545)
    ·
      refine ⟨12134562475343412576703909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16179416633791216768938545 12134562475343412576703909)
      ·
        refine ⟨2275230464126889858131983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12134562475343412576703909 2275230464126889858131983)
        ·
          refine ⟨3412845696190334787197975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2275230464126889858131983 3412845696190334787197975)
          ·
            refine ⟨5119268544285502180796963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3412845696190334787197975 5119268544285502180796963)
            ·
              refine ⟨7678902816428253271195445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5119268544285502180796963 7678902816428253271195445)
              ·
                refine ⟨719897139040148744174573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7678902816428253271195445 719897139040148744174573)
                ·
                  refine ⟨269961427140055779065465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 719897139040148744174573 269961427140055779065465)
                  ·
                    rfl

theorem cell21_1182933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 5, 3].length) (baseStart_1182933 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1182933 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1182933 prefixEnd_1182933 := by exact prefixLift 1182933
  have htrace : WordTrace (prefixWord ++ tailWord_1182933) baseStart_1182933 baseEnd_1182933 := by
    simpa [prefixWord, tailWord_1182933, baseEnd_1182933] using wordTrace_append hprefix tailTrace_1182933
  have hstable : (prefixWord ++ tailWord_1182933).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1182933).length < 2 ^ (prefixWord ++ tailWord_1182933).sum := by decide
  have hdescent : baseEnd_1182933 < baseStart_1182933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1182933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1182944 : List Nat := [2, 1, 1, 3, 1, 5, 8]
def baseStart_1182944 : Nat := 118140960795 + 1182944 * 2 ^ 59
def prefixEnd_1182944 : Nat := 4983230072969 + 3 ^ 40 * 1182944 * 2
def baseEnd_1182944 : Nat := 29995993054435800486901

theorem tailTrace_1182944 : CollatzResearch.WordTrace tailWord_1182944 prefixEnd_1182944 29995993054435800486901 := by
  unfold tailWord_1182944
  simp only [CollatzResearch.WordTrace]
  refine ⟨21572756113201696797909943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28763674817602262397213257 21572756113201696797909943)
  ·
    refine ⟨32359134169802545196864915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21572756113201696797909943 32359134169802545196864915)
    ·
      refine ⟨48538701254703817795297373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32359134169802545196864915 48538701254703817795297373)
      ·
        refine ⟨18202012970513931673236515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48538701254703817795297373 18202012970513931673236515)
        ·
          refine ⟨27303019455770897509854773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18202012970513931673236515 27303019455770897509854773)
          ·
            refine ⟨2559658073978521641548885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27303019455770897509854773 2559658073978521641548885)
            ·
              refine ⟨29995993054435800486901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2559658073978521641548885 29995993054435800486901)
              ·
                rfl

theorem cell21_1182944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 8].length) (baseStart_1182944 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1182944 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1182944 prefixEnd_1182944 := by exact prefixLift 1182944
  have htrace : WordTrace (prefixWord ++ tailWord_1182944) baseStart_1182944 baseEnd_1182944 := by
    simpa [prefixWord, tailWord_1182944, baseEnd_1182944] using wordTrace_append hprefix tailTrace_1182944
  have hstable : (prefixWord ++ tailWord_1182944).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1182944).length < 2 ^ (prefixWord ++ tailWord_1182944).sum := by decide
  have hdescent : baseEnd_1182944 < baseStart_1182944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1182944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1182975 : List Nat := [1, 1, 2, 2, 1, 5, 2, 2, 5]
def baseStart_1182975 : Nat := 118140960795 + 1182975 * 2 ^ 59
def prefixEnd_1182975 : Nat := 4983230072969 + 3 ^ 40 * 1182975 * 2
def baseEnd_1182975 : Nat := 269971012112273039365379

theorem tailTrace_1182975 : CollatzResearch.WordTrace tailWord_1182975 prefixEnd_1182975 269971012112273039365379 := by
  unfold tailWord_1182975
  simp only [CollatzResearch.WordTrace]
  refine ⟨43146642889291085890198379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28764428592860723926798919 43146642889291085890198379)
  ·
    refine ⟨64719964333936628835297569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43146642889291085890198379 64719964333936628835297569)
    ·
      refine ⟨48539973250452471626473177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64719964333936628835297569 48539973250452471626473177)
      ·
        refine ⟨36404979937839353719854883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48539973250452471626473177 36404979937839353719854883)
        ·
          refine ⟨54607469906759030579782325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36404979937839353719854883 54607469906759030579782325)
          ·
            refine ⟨5119450303758659116854593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 54607469906759030579782325 5119450303758659116854593)
            ·
              refine ⟨3839587727818994337640945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5119450303758659116854593 3839587727818994337640945)
              ·
                refine ⟨2879690795864245753230709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3839587727818994337640945 2879690795864245753230709)
                ·
                  refine ⟨269971012112273039365379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2879690795864245753230709 269971012112273039365379)
                  ·
                    rfl

theorem cell21_1182975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 2, 5].length) (baseStart_1182975 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1182975 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1182975 prefixEnd_1182975 := by exact prefixLift 1182975
  have htrace : WordTrace (prefixWord ++ tailWord_1182975) baseStart_1182975 baseEnd_1182975 := by
    simpa [prefixWord, tailWord_1182975, baseEnd_1182975] using wordTrace_append hprefix tailTrace_1182975
  have hstable : (prefixWord ++ tailWord_1182975).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1182975).length < 2 ^ (prefixWord ++ tailWord_1182975).sum := by decide
  have hdescent : baseEnd_1182975 < baseStart_1182975 := by decide
  rcases family_descends (prefixWord ++ tailWord_1182975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1182978 : List Nat := [3, 4, 1, 1, 3, 1, 1, 7]
def baseStart_1182978 : Nat := 118140960795 + 1182978 * 2 ^ 59
def prefixEnd_1182978 : Nat := 4983230072969 + 3 ^ 40 * 1182978 * 2
def baseEnd_1182978 : Nat := 89990565584381900271791

theorem tailTrace_1182978 : CollatzResearch.WordTrace tailWord_1182978 prefixEnd_1182978 89990565584381900271791 := by
  unfold tailWord_1182978
  simp only [CollatzResearch.WordTrace]
  refine ⟨10786688077070054350639397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28764501538853478268371725 10786688077070054350639397)
  ·
    refine ⟨2022504014450635190744887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10786688077070054350639397 2022504014450635190744887)
    ·
      refine ⟨3033756021675952786117331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2022504014450635190744887 3033756021675952786117331)
      ·
        refine ⟨4550634032513929179175997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3033756021675952786117331 4550634032513929179175997)
        ·
          refine ⟨1706487762192723442190999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4550634032513929179175997 1706487762192723442190999)
          ·
            refine ⟨2559731643289085163286499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1706487762192723442190999 2559731643289085163286499)
            ·
              refine ⟨3839597464933627744929749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2559731643289085163286499 3839597464933627744929749)
              ·
                refine ⟨89990565584381900271791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3839597464933627744929749 89990565584381900271791)
                ·
                  rfl

theorem cell21_1182978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 7].length) (baseStart_1182978 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1182978 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1182978 prefixEnd_1182978 := by exact prefixLift 1182978
  have htrace : WordTrace (prefixWord ++ tailWord_1182978) baseStart_1182978 baseEnd_1182978 := by
    simpa [prefixWord, tailWord_1182978, baseEnd_1182978] using wordTrace_append hprefix tailTrace_1182978
  have hstable : (prefixWord ++ tailWord_1182978).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1182978).length < 2 ^ (prefixWord ++ tailWord_1182978).sum := by decide
  have hdescent : baseEnd_1182978 < baseStart_1182978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1182978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1183065 : List Nat := [1, 2, 1, 2, 2, 2, 2, 3, 6]
def baseStart_1183065 : Nat := 118140960795 + 1183065 * 2 ^ 59
def prefixEnd_1183065 : Nat := 4983230072969 + 3 ^ 40 * 1183065 * 2
def baseEnd_1183065 : Nat := 269991551338452882865195

theorem tailTrace_1183065 : CollatzResearch.WordTrace tailWord_1183065 prefixEnd_1183065 269991551338452882865195 := by
  unfold tailWord_1183065
  simp only [CollatzResearch.WordTrace]
  refine ⟨43149925458965031260974649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28766616972643354173983099 43149925458965031260974649)
  ·
    refine ⟨32362444094223773445730987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43149925458965031260974649 32362444094223773445730987)
    ·
      refine ⟨48543666141335660168596481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32362444094223773445730987 48543666141335660168596481)
      ·
        refine ⟨36407749606001745126447361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48543666141335660168596481 36407749606001745126447361)
        ·
          refine ⟨27305812204501308844835521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36407749606001745126447361 27305812204501308844835521)
          ·
            refine ⟨20479359153375981633626641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27305812204501308844835521 20479359153375981633626641)
            ·
              refine ⟨15359519365031986225219981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20479359153375981633626641 15359519365031986225219981)
              ·
                refine ⟨5759819761886994834457493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15359519365031986225219981 5759819761886994834457493)
                ·
                  refine ⟨269991551338452882865195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5759819761886994834457493 269991551338452882865195)
                  ·
                    rfl

theorem cell21_1183065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 3, 6].length) (baseStart_1183065 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1183065 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1183065 prefixEnd_1183065 := by exact prefixLift 1183065
  have htrace : WordTrace (prefixWord ++ tailWord_1183065) baseStart_1183065 baseEnd_1183065 := by
    simpa [prefixWord, tailWord_1183065, baseEnd_1183065] using wordTrace_append hprefix tailTrace_1183065
  have hstable : (prefixWord ++ tailWord_1183065).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1183065).length < 2 ^ (prefixWord ++ tailWord_1183065).sum := by decide
  have hdescent : baseEnd_1183065 < baseStart_1183065 := by decide
  rcases family_descends (prefixWord ++ tailWord_1183065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1183265 : List Nat := [1, 2, 3, 2, 2, 3, 3, 5]
def baseStart_1183265 : Nat := 118140960795 + 1183265 * 2 ^ 59
def prefixEnd_1183265 : Nat := 4983230072969 + 3 ^ 40 * 1183265 * 2
def baseEnd_1183265 : Nat := 90012398021098993177151

theorem tailTrace_1183265 : CollatzResearch.WordTrace tailWord_1183265 prefixEnd_1183265 90012398021098993177151 := by
  unfold tailWord_1183265
  simp only [CollatzResearch.WordTrace]
  refine ⟨43157220058240465418255249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28771480038826976945503499 43157220058240465418255249)
  ·
    refine ⟨32367915043680349063691437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43157220058240465418255249 32367915043680349063691437)
    ·
      refine ⟨12137968141380130898884289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32367915043680349063691437 12137968141380130898884289)
      ·
        refine ⟨9103476106035098174163217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12137968141380130898884289 9103476106035098174163217)
        ·
          refine ⟨6827607079526323630622413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9103476106035098174163217 6827607079526323630622413)
          ·
            refine ⟨2560352654822371361483405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6827607079526323630622413 2560352654822371361483405)
            ·
              refine ⟨960132245558389260556277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2560352654822371361483405 960132245558389260556277)
              ·
                refine ⟨90012398021098993177151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 960132245558389260556277 90012398021098993177151)
                ·
                  rfl

theorem cell21_1183265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 3, 5].length) (baseStart_1183265 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1183265 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1183265 prefixEnd_1183265 := by exact prefixLift 1183265
  have htrace : WordTrace (prefixWord ++ tailWord_1183265) baseStart_1183265 baseEnd_1183265 := by
    simpa [prefixWord, tailWord_1183265, baseEnd_1183265] using wordTrace_append hprefix tailTrace_1183265
  have hstable : (prefixWord ++ tailWord_1183265).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1183265).length < 2 ^ (prefixWord ++ tailWord_1183265).sum := by decide
  have hdescent : baseEnd_1183265 < baseStart_1183265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1183265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1183307 : List Nat := [1, 1, 1, 1, 3, 1, 3, 10]
def baseStart_1183307 : Nat := 118140960795 + 1183307 * 2 ^ 59
def prefixEnd_1183307 : Nat := 4983230072969 + 3 ^ 40 * 1183307 * 2
def baseEnd_1183307 : Nat := 90015593011838079943789

theorem tailTrace_1183307 : CollatzResearch.WordTrace tailWord_1183307 prefixEnd_1183307 90015593011838079943789 := by
  unfold tailWord_1183307
  simp only [CollatzResearch.WordTrace]
  refine ⟨43158751924088306591284175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28772501282725537727522783 43158751924088306591284175)
  ·
    refine ⟨64738127886132459886926263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43158751924088306591284175 64738127886132459886926263)
    ·
      refine ⟨97107191829198689830389395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64738127886132459886926263 97107191829198689830389395)
      ·
        refine ⟨145660787743798034745584093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97107191829198689830389395 145660787743798034745584093)
        ·
          refine ⟨54622795403924263029594035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 145660787743798034745584093 54622795403924263029594035)
          ·
            refine ⟨81934193105886394544391053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54622795403924263029594035 81934193105886394544391053)
            ·
              refine ⟨30725322414707397954146645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 81934193105886394544391053 30725322414707397954146645)
              ·
                refine ⟨90015593011838079943789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 30725322414707397954146645 90015593011838079943789)
                ·
                  rfl

theorem cell21_1183307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 10].length) (baseStart_1183307 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1183307 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1183307 prefixEnd_1183307 := by exact prefixLift 1183307
  have htrace : WordTrace (prefixWord ++ tailWord_1183307) baseStart_1183307 baseEnd_1183307 := by
    simpa [prefixWord, tailWord_1183307, baseEnd_1183307] using wordTrace_append hprefix tailTrace_1183307
  have hstable : (prefixWord ++ tailWord_1183307).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1183307).length < 2 ^ (prefixWord ++ tailWord_1183307).sum := by decide
  have hdescent : baseEnd_1183307 < baseStart_1183307 := by decide
  rcases family_descends (prefixWord ++ tailWord_1183307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1183341 : List Nat := [1, 5, 1, 1, 4, 2, 7]
def baseStart_1183341 : Nat := 118140960795 + 1183341 * 2 ^ 59
def prefixEnd_1183341 : Nat := 4983230072969 + 3 ^ 40 * 1183341 * 2
def baseEnd_1183341 : Nat := 30006059810970859584959

theorem tailTrace_1183341 : CollatzResearch.WordTrace tailWord_1183341 prefixEnd_1183341 30006059810970859584959 := by
  unfold tailWord_1183341
  simp only [CollatzResearch.WordTrace]
  refine ⟨43159992005965130398021877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28773328003976753598681251 43159992005965130398021877)
  ·
    refine ⟨4046249250559230974814551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 43159992005965130398021877 4046249250559230974814551)
    ·
      refine ⟨6069373875838846462221827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4046249250559230974814551 6069373875838846462221827)
      ·
        refine ⟨9104060813758269693332741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6069373875838846462221827 9104060813758269693332741)
        ·
          refine ⟨1707011402579675567499889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9104060813758269693332741 1707011402579675567499889)
          ·
            refine ⟨1280258551934756675624917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1707011402579675567499889 1280258551934756675624917)
            ·
              refine ⟨30006059810970859584959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1280258551934756675624917 30006059810970859584959)
              ·
                rfl

theorem cell21_1183341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 7].length) (baseStart_1183341 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1183341 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1183341 prefixEnd_1183341 := by exact prefixLift 1183341
  have htrace : WordTrace (prefixWord ++ tailWord_1183341) baseStart_1183341 baseEnd_1183341 := by
    simpa [prefixWord, tailWord_1183341, baseEnd_1183341] using wordTrace_append hprefix tailTrace_1183341
  have hstable : (prefixWord ++ tailWord_1183341).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1183341).length < 2 ^ (prefixWord ++ tailWord_1183341).sum := by decide
  have hdescent : baseEnd_1183341 < baseStart_1183341 := by decide
  rcases family_descends (prefixWord ++ tailWord_1183341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1183406 : List Nat := [4, 1, 4, 1, 2, 1, 1, 4, 3]
def baseStart_1183406 : Nat := 118140960795 + 1183406 * 2 ^ 59
def prefixEnd_1183406 : Nat := 4983230072969 + 3 ^ 40 * 1183406 * 2
def baseEnd_1183406 : Nat := 270069372184312067681165

theorem tailTrace_1183406 : CollatzResearch.WordTrace tailWord_1183406 prefixEnd_1183406 270069372184312067681165 := by
  unfold tailWord_1183406
  simp only [CollatzResearch.WordTrace]
  refine ⟨5395295343841205812392259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28774908500486430999425381 5395295343841205812392259)
  ·
    refine ⟨8092943015761808718588389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5395295343841205812392259 8092943015761808718588389)
    ·
      refine ⟨1517426815455339134735323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8092943015761808718588389 1517426815455339134735323)
      ·
        refine ⟨2276140223183008702102985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1517426815455339134735323 2276140223183008702102985)
        ·
          refine ⟨1707105167387256526577239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2276140223183008702102985 1707105167387256526577239)
          ·
            refine ⟨2560657751080884789865859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1707105167387256526577239 2560657751080884789865859)
            ·
              refine ⟨3840986626621327184798789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2560657751080884789865859 3840986626621327184798789)
              ·
                refine ⟨720184992491498847149773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3840986626621327184798789 720184992491498847149773)
                ·
                  refine ⟨270069372184312067681165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 720184992491498847149773 270069372184312067681165)
                  ·
                    rfl

theorem cell21_1183406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 4, 3].length) (baseStart_1183406 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1183406 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1183406 prefixEnd_1183406 := by exact prefixLift 1183406
  have htrace : WordTrace (prefixWord ++ tailWord_1183406) baseStart_1183406 baseEnd_1183406 := by
    simpa [prefixWord, tailWord_1183406, baseEnd_1183406] using wordTrace_append hprefix tailTrace_1183406
  have hstable : (prefixWord ++ tailWord_1183406).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1183406).length < 2 ^ (prefixWord ++ tailWord_1183406).sum := by decide
  have hdescent : baseEnd_1183406 < baseStart_1183406 := by decide
  rcases family_descends (prefixWord ++ tailWord_1183406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1183448 : List Nat := [2, 1, 2, 2, 3, 1, 4, 3, 3]
def baseStart_1183448 : Nat := 118140960795 + 1183448 * 2 ^ 59
def prefixEnd_1183448 : Nat := 4983230072969 + 3 ^ 40 * 1183448 * 2
def baseEnd_1183448 : Nat := 270078957156529327981079

theorem tailTrace_1183448 : CollatzResearch.WordTrace tailWord_1183448 prefixEnd_1183448 270078957156529327981079 := by
  unfold tailWord_1183448
  simp only [CollatzResearch.WordTrace]
  refine ⟨21581947308288743836083499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28775929744384991781444665 21581947308288743836083499)
  ·
    refine ⟨32372920962433115754125249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21581947308288743836083499 32372920962433115754125249)
    ·
      refine ⟨24279690721824836815593937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32372920962433115754125249 24279690721824836815593937)
      ·
        refine ⟨18209768041368627611695453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24279690721824836815593937 18209768041368627611695453)
        ·
          refine ⟨6828663015513235354385795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18209768041368627611695453 6828663015513235354385795)
          ·
            refine ⟨10242994523269853031578693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6828663015513235354385795 10242994523269853031578693)
            ·
              refine ⟨1920561473113097443421005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10242994523269853031578693 1920561473113097443421005)
              ·
                refine ⟨720210552417411541282877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1920561473113097443421005 720210552417411541282877)
                ·
                  refine ⟨270078957156529327981079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 720210552417411541282877 270078957156529327981079)
                  ·
                    rfl

theorem cell21_1183448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 4, 3, 3].length) (baseStart_1183448 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1183448 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1183448 prefixEnd_1183448 := by exact prefixLift 1183448
  have htrace : WordTrace (prefixWord ++ tailWord_1183448) baseStart_1183448 baseEnd_1183448 := by
    simpa [prefixWord, tailWord_1183448, baseEnd_1183448] using wordTrace_append hprefix tailTrace_1183448
  have hstable : (prefixWord ++ tailWord_1183448).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1183448).length < 2 ^ (prefixWord ++ tailWord_1183448).sum := by decide
  have hdescent : baseEnd_1183448 < baseStart_1183448 := by decide
  rcases family_descends (prefixWord ++ tailWord_1183448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1183507 : List Nat := [1, 1, 1, 2, 1, 3, 2, 7, 3]
def baseStart_1183507 : Nat := 118140960795 + 1183507 * 2 ^ 59
def prefixEnd_1183507 : Nat := 4983230072969 + 3 ^ 40 * 1183507 * 2
def baseEnd_1183507 : Nat := 270092421760358336497625

theorem tailTrace_1183507 : CollatzResearch.WordTrace tailWord_1183507 prefixEnd_1183507 270092421760358336497625 := by
  unfold tailWord_1183507
  simp only [CollatzResearch.WordTrace]
  refine ⟨43166046523363740748564775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28777364348909160499043183 43166046523363740748564775)
  ·
    refine ⟨64749069785045611122847163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43166046523363740748564775 64749069785045611122847163)
    ·
      refine ⟨97123604677568416684270745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64749069785045611122847163 97123604677568416684270745)
      ·
        refine ⟨72842703508176312513203059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97123604677568416684270745 72842703508176312513203059)
        ·
          refine ⟨109264055262264468769804589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72842703508176312513203059 109264055262264468769804589)
          ·
            refine ⟨40974020723349175788676721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 109264055262264468769804589 40974020723349175788676721)
            ·
              refine ⟨30730515542511881841507541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40974020723349175788676721 30730515542511881841507541)
              ·
                refine ⟨720246458027622230660333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 30730515542511881841507541 720246458027622230660333)
                ·
                  refine ⟨270092421760358336497625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 720246458027622230660333 270092421760358336497625)
                  ·
                    rfl

theorem cell21_1183507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 7, 3].length) (baseStart_1183507 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1183507 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1183507 prefixEnd_1183507 := by exact prefixLift 1183507
  have htrace : WordTrace (prefixWord ++ tailWord_1183507) baseStart_1183507 baseEnd_1183507 := by
    simpa [prefixWord, tailWord_1183507, baseEnd_1183507] using wordTrace_append hprefix tailTrace_1183507
  have hstable : (prefixWord ++ tailWord_1183507).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1183507).length < 2 ^ (prefixWord ++ tailWord_1183507).sum := by decide
  have hdescent : baseEnd_1183507 < baseStart_1183507 := by decide
  rcases family_descends (prefixWord ++ tailWord_1183507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1183521 : List Nat := [1, 2, 3, 2, 1, 3, 2, 1, 6]
def baseStart_1183521 : Nat := 118140960795 + 1183521 * 2 ^ 59
def prefixEnd_1183521 : Nat := 4983230072969 + 3 ^ 40 * 1183521 * 2
def baseEnd_1183521 : Nat := 270095616751097423264263

theorem tailTrace_1183521 : CollatzResearch.WordTrace tailWord_1183521 prefixEnd_1183521 270095616751097423264263 := by
  unfold tailWord_1183521
  simp only [CollatzResearch.WordTrace]
  refine ⟨43166557145313021139574417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28777704763542014093049611 43166557145313021139574417)
  ·
    refine ⟨32374917858984765854680813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43166557145313021139574417 32374917858984765854680813)
    ·
      refine ⟨12140594197119287195505305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32374917858984765854680813 12140594197119287195505305)
      ·
        refine ⟨9105445647839465396628979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12140594197119287195505305 9105445647839465396628979)
        ·
          refine ⟨13658168471759198094943469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9105445647839465396628979 13658168471759198094943469)
          ·
            refine ⟨5121813176909699285603801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13658168471759198094943469 5121813176909699285603801)
            ·
              refine ⟨3841359882682274464202851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5121813176909699285603801 3841359882682274464202851)
              ·
                refine ⟨5762039824023411696304277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3841359882682274464202851 5762039824023411696304277)
                ·
                  refine ⟨270095616751097423264263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5762039824023411696304277 270095616751097423264263)
                  ·
                    rfl

theorem cell21_1183521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 1, 6].length) (baseStart_1183521 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1183521 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1183521 prefixEnd_1183521 := by exact prefixLift 1183521
  have htrace : WordTrace (prefixWord ++ tailWord_1183521) baseStart_1183521 baseEnd_1183521 := by
    simpa [prefixWord, tailWord_1183521, baseEnd_1183521] using wordTrace_append hprefix tailTrace_1183521
  have hstable : (prefixWord ++ tailWord_1183521).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1183521).length < 2 ^ (prefixWord ++ tailWord_1183521).sum := by decide
  have hdescent : baseEnd_1183521 < baseStart_1183521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1183521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1183524 : List Nat := [2, 3, 1, 3, 2, 3, 1, 1, 5]
def baseStart_1183524 : Nat := 118140960795 + 1183524 * 2 ^ 59
def prefixEnd_1183524 : Nat := 4983230072969 + 3 ^ 40 * 1183524 * 2
def baseEnd_1183524 : Nat := 270096301391970084714257

theorem tailTrace_1183524 : CollatzResearch.WordTrace tailWord_1183524 prefixEnd_1183524 270096301391970084714257 := by
  unfold tailWord_1183524
  simp only [CollatzResearch.WordTrace]
  refine ⟨21583333282151076325966813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28777777709534768434622417 21583333282151076325966813)
  ·
    refine ⟨8093749980806653622237555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21583333282151076325966813 8093749980806653622237555)
    ·
      refine ⟨12140624971209980433356333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8093749980806653622237555 12140624971209980433356333)
      ·
        refine ⟨4552734364203742662508625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12140624971209980433356333 4552734364203742662508625)
        ·
          refine ⟨3414550773152806996881469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4552734364203742662508625 3414550773152806996881469)
          ·
            refine ⟨1280456539932302623830551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3414550773152806996881469 1280456539932302623830551)
            ·
              refine ⟨1920684809898453935745827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1280456539932302623830551 1920684809898453935745827)
              ·
                refine ⟨2881027214847680903618741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1920684809898453935745827 2881027214847680903618741)
                ·
                  refine ⟨270096301391970084714257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2881027214847680903618741 270096301391970084714257)
                  ·
                    rfl

theorem cell21_1183524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 1, 1, 5].length) (baseStart_1183524 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1183524 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1183524 prefixEnd_1183524 := by exact prefixLift 1183524
  have htrace : WordTrace (prefixWord ++ tailWord_1183524) baseStart_1183524 baseEnd_1183524 := by
    simpa [prefixWord, tailWord_1183524, baseEnd_1183524] using wordTrace_append hprefix tailTrace_1183524
  have hstable : (prefixWord ++ tailWord_1183524).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1183524).length < 2 ^ (prefixWord ++ tailWord_1183524).sum := by decide
  have hdescent : baseEnd_1183524 < baseStart_1183524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1183524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1183538 : List Nat := [3, 2, 1, 1, 3, 3, 1, 3, 4]
def baseStart_1183538 : Nat := 118140960795 + 1183538 * 2 ^ 59
def prefixEnd_1183538 : Nat := 4983230072969 + 3 ^ 40 * 1183538 * 2
def baseEnd_1183538 : Nat := 270099496382709171480895

theorem tailTrace_1183538 : CollatzResearch.WordTrace tailWord_1183538 prefixEnd_1183538 270099496382709171480895 := by
  unfold tailWord_1183538
  simp only [CollatzResearch.WordTrace]
  refine ⟨10791794296562858260735817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28778118124167622028628845 10791794296562858260735817)
  ·
    refine ⟨8093845722422143695551863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10791794296562858260735817 8093845722422143695551863)
    ·
      refine ⟨12140768583633215543327795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8093845722422143695551863 12140768583633215543327795)
      ·
        refine ⟨18211152875449823314991693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12140768583633215543327795 18211152875449823314991693)
        ·
          refine ⟨6829182328293683743121885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18211152875449823314991693 6829182328293683743121885)
          ·
            refine ⟨2560943373110131403670707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6829182328293683743121885 2560943373110131403670707)
            ·
              refine ⟨3841415059665197105506061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2560943373110131403670707 3841415059665197105506061)
              ·
                refine ⟨1440530647374448914564773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3841415059665197105506061 1440530647374448914564773)
                ·
                  refine ⟨270099496382709171480895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1440530647374448914564773 270099496382709171480895)
                  ·
                    rfl

theorem cell21_1183538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 3, 4].length) (baseStart_1183538 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1183538 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1183538 prefixEnd_1183538 := by exact prefixLift 1183538
  have htrace : WordTrace (prefixWord ++ tailWord_1183538) baseStart_1183538 baseEnd_1183538 := by
    simpa [prefixWord, tailWord_1183538, baseEnd_1183538] using wordTrace_append hprefix tailTrace_1183538
  have hstable : (prefixWord ++ tailWord_1183538).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1183538).length < 2 ^ (prefixWord ++ tailWord_1183538).sum := by decide
  have hdescent : baseEnd_1183538 < baseStart_1183538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1183538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1183749 : List Nat := [1, 3, 1, 1, 2, 4, 1, 4, 4]
def baseStart_1183749 : Nat := 118140960795 + 1183749 * 2 ^ 59
def prefixEnd_1183749 : Nat := 4983230072969 + 3 ^ 40 * 1183749 * 2
def baseEnd_1183749 : Nat := 270147649457419693463797

theorem tailTrace_1183749 : CollatzResearch.WordTrace tailWord_1183749 prefixEnd_1183749 270147649457419693463797 := by
  unfold tailWord_1183749
  simp only [CollatzResearch.WordTrace]
  refine ⟨43174872988487016078874301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28783248658991344052582867 43174872988487016078874301)
  ·
    refine ⟨16190577370682631029577863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43174872988487016078874301 16190577370682631029577863)
    ·
      refine ⟨24285866056023946544366795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16190577370682631029577863 24285866056023946544366795)
      ·
        refine ⟨36428799084035919816550193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24285866056023946544366795 36428799084035919816550193)
        ·
          refine ⟨27321599313026939862412645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36428799084035919816550193 27321599313026939862412645)
          ·
            refine ⟨5122799871192551224202371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27321599313026939862412645 5122799871192551224202371)
            ·
              refine ⟨7684199806788826836303557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5122799871192551224202371 7684199806788826836303557)
              ·
                refine ⟨1440787463772905031806917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7684199806788826836303557 1440787463772905031806917)
                ·
                  refine ⟨270147649457419693463797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1440787463772905031806917 270147649457419693463797)
                  ·
                    rfl

theorem cell21_1183749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 4, 4].length) (baseStart_1183749 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1183749 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1183749 prefixEnd_1183749 := by exact prefixLift 1183749
  have htrace : WordTrace (prefixWord ++ tailWord_1183749) baseStart_1183749 baseEnd_1183749 := by
    simpa [prefixWord, tailWord_1183749, baseEnd_1183749] using wordTrace_append hprefix tailTrace_1183749
  have hstable : (prefixWord ++ tailWord_1183749).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1183749).length < 2 ^ (prefixWord ++ tailWord_1183749).sum := by decide
  have hdescent : baseEnd_1183749 < baseStart_1183749 := by decide
  rcases family_descends (prefixWord ++ tailWord_1183749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1183763 : List Nat := [1, 1, 1, 2, 1, 4, 5, 6]
def baseStart_1183763 : Nat := 118140960795 + 1183763 * 2 ^ 59
def prefixEnd_1183763 : Nat := 4983230072969 + 3 ^ 40 * 1183763 * 2
def baseEnd_1183763 : Nat := 90050281482719593410145

theorem tailTrace_1183763 : CollatzResearch.WordTrace tailWord_1183763 prefixEnd_1183763 90050281482719593410145 := by
  unfold tailWord_1183763
  simp only [CollatzResearch.WordTrace]
  refine ⟨43175383610436296469883943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28783589073624197646589295 43175383610436296469883943)
  ·
    refine ⟨64763075415654444704825915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43175383610436296469883943 64763075415654444704825915)
    ·
      refine ⟨97144613123481667057238873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64763075415654444704825915 97144613123481667057238873)
      ·
        refine ⟨72858459842611250292929155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97144613123481667057238873 72858459842611250292929155)
        ·
          refine ⟨109287689763916875439393733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 72858459842611250292929155 109287689763916875439393733)
          ·
            refine ⟨20491441830734414144886325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 109287689763916875439393733 20491441830734414144886325)
            ·
              refine ⟨1921072671631351326083093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20491441830734414144886325 1921072671631351326083093)
              ·
                refine ⟨90050281482719593410145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1921072671631351326083093 90050281482719593410145)
                ·
                  rfl

theorem cell21_1183763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 5, 6].length) (baseStart_1183763 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1183763 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1183763 prefixEnd_1183763 := by exact prefixLift 1183763
  have htrace : WordTrace (prefixWord ++ tailWord_1183763) baseStart_1183763 baseEnd_1183763 := by
    simpa [prefixWord, tailWord_1183763, baseEnd_1183763] using wordTrace_append hprefix tailTrace_1183763
  have hstable : (prefixWord ++ tailWord_1183763).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1183763).length < 2 ^ (prefixWord ++ tailWord_1183763).sum := by decide
  have hdescent : baseEnd_1183763 < baseStart_1183763 := by decide
  rcases family_descends (prefixWord ++ tailWord_1183763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1183924 : List Nat := [2, 5, 3, 1, 2, 1, 1, 6]
def baseStart_1183924 : Nat := 118140960795 + 1183924 * 2 ^ 59
def prefixEnd_1183924 : Nat := 4983230072969 + 3 ^ 40 * 1183924 * 2
def baseEnd_1183924 : Nat := 90062528947219426015591

theorem tailTrace_1183924 : CollatzResearch.WordTrace tailWord_1183924 prefixEnd_1183924 90062528947219426015591 := by
  unfold tailWord_1183924
  simp only [CollatzResearch.WordTrace]
  refine ⟨21590627881426510483247413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28787503841902013977663217 21590627881426510483247413)
  ·
    refine ⟨2024121363883735357804445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21590627881426510483247413 2024121363883735357804445)
    ·
      refine ⟨759045511456400759176667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2024121363883735357804445 759045511456400759176667)
      ·
        refine ⟨1138568267184601138765001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 759045511456400759176667 1138568267184601138765001)
        ·
          refine ⟨853926200388450854073751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1138568267184601138765001 853926200388450854073751)
          ·
            refine ⟨1280889300582676281110627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 853926200388450854073751 1280889300582676281110627)
            ·
              refine ⟨1921333950874014421665941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1280889300582676281110627 1921333950874014421665941)
              ·
                refine ⟨90062528947219426015591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1921333950874014421665941 90062528947219426015591)
                ·
                  rfl

theorem cell21_1183924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 1, 6].length) (baseStart_1183924 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1183924 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1183924 prefixEnd_1183924 := by exact prefixLift 1183924
  have htrace : WordTrace (prefixWord ++ tailWord_1183924) baseStart_1183924 baseEnd_1183924 := by
    simpa [prefixWord, tailWord_1183924, baseEnd_1183924] using wordTrace_append hprefix tailTrace_1183924
  have hstable : (prefixWord ++ tailWord_1183924).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1183924).length < 2 ^ (prefixWord ++ tailWord_1183924).sum := by decide
  have hdescent : baseEnd_1183924 < baseStart_1183924 := by decide
  rcases family_descends (prefixWord ++ tailWord_1183924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1183946 : List Nat := [3, 1, 2, 1, 3, 1, 3, 2, 5]
def baseStart_1183946 : Nat := 118140960795 + 1183946 * 2 ^ 59
def prefixEnd_1183946 : Nat := 4983230072969 + 3 ^ 40 * 1183946 * 2
def baseEnd_1183946 : Nat := 270192607541391128680061

theorem tailTrace_1183946 : CollatzResearch.WordTrace tailWord_1183946 prefixEnd_1183946 270192607541391128680061 := by
  unfold tailWord_1183946
  simp only [CollatzResearch.WordTrace]
  refine ⟨10795514542193329680948923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28788038779182212482530461 10795514542193329680948923)
  ·
    refine ⟨16193271813289994521423385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10795514542193329680948923 16193271813289994521423385)
    ·
      refine ⟨12144953859967495891067539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16193271813289994521423385 12144953859967495891067539)
      ·
        refine ⟨18217430789951243836601309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12144953859967495891067539 18217430789951243836601309)
        ·
          refine ⟨6831536546231716438725491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18217430789951243836601309 6831536546231716438725491)
          ·
            refine ⟨10247304819347574658088237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6831536546231716438725491 10247304819347574658088237)
            ·
              refine ⟨3842739307255340496783089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10247304819347574658088237 3842739307255340496783089)
              ·
                refine ⟨2882054480441505372587317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3842739307255340496783089 2882054480441505372587317)
                ·
                  refine ⟨270192607541391128680061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2882054480441505372587317 270192607541391128680061)
                  ·
                    rfl

theorem cell21_1183946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 2, 5].length) (baseStart_1183946 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1183946 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1183946 prefixEnd_1183946 := by exact prefixLift 1183946
  have htrace : WordTrace (prefixWord ++ tailWord_1183946) baseStart_1183946 baseEnd_1183946 := by
    simpa [prefixWord, tailWord_1183946, baseEnd_1183946] using wordTrace_append hprefix tailTrace_1183946
  have hstable : (prefixWord ++ tailWord_1183946).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1183946).length < 2 ^ (prefixWord ++ tailWord_1183946).sum := by decide
  have hdescent : baseEnd_1183946 < baseStart_1183946 := by decide
  rcases family_descends (prefixWord ++ tailWord_1183946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1183994 : List Nat := [3, 1, 1, 1, 1, 6, 3, 1, 4]
def baseStart_1183994 : Nat := 118140960795 + 1183994 * 2 ^ 59
def prefixEnd_1183994 : Nat := 4983230072969 + 3 ^ 40 * 1183994 * 2
def baseEnd_1183994 : Nat := 270203561795353711879963

theorem tailTrace_1183994 : CollatzResearch.WordTrace tailWord_1183994 prefixEnd_1183994 270203561795353711879963 := by
  unfold tailWord_1183994
  simp only [CollatzResearch.WordTrace]
  refine ⟨10795952218149855730385759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28789205915066281947695357 10795952218149855730385759)
  ·
    refine ⟨16193928327224783595578639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10795952218149855730385759 16193928327224783595578639)
    ·
      refine ⟨24290892490837175393367959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16193928327224783595578639 24290892490837175393367959)
      ·
        refine ⟨36436338736255763090051939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24290892490837175393367959 36436338736255763090051939)
        ·
          refine ⟨54654508104383644635077909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36436338736255763090051939 54654508104383644635077909)
          ·
            refine ⟨2561930067392983342269277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 54654508104383644635077909 2561930067392983342269277)
            ·
              refine ⟨960723775272368753350979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2561930067392983342269277 960723775272368753350979)
              ·
                refine ⟨1441085662908553130026469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 960723775272368753350979 1441085662908553130026469)
                ·
                  refine ⟨270203561795353711879963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1441085662908553130026469 270203561795353711879963)
                  ·
                    rfl

theorem cell21_1183994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 3, 1, 4].length) (baseStart_1183994 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1183994 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1183994 prefixEnd_1183994 := by exact prefixLift 1183994
  have htrace : WordTrace (prefixWord ++ tailWord_1183994) baseStart_1183994 baseEnd_1183994 := by
    simpa [prefixWord, tailWord_1183994, baseEnd_1183994] using wordTrace_append hprefix tailTrace_1183994
  have hstable : (prefixWord ++ tailWord_1183994).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1183994).length < 2 ^ (prefixWord ++ tailWord_1183994).sum := by decide
  have hdescent : baseEnd_1183994 < baseStart_1183994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1183994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1184005 : List Nat := [1, 3, 1, 1, 2, 1, 2, 3, 7]
def baseStart_1184005 : Nat := 118140960795 + 1184005 * 2 ^ 59
def prefixEnd_1184005 : Nat := 4983230072969 + 3 ^ 40 * 1184005 * 2
def baseEnd_1184005 : Nat := 270206072145220137196607

theorem tailTrace_1184005 : CollatzResearch.WordTrace tailWord_1184005 prefixEnd_1184005 270206072145220137196607 := by
  unfold tailWord_1184005
  simp only [CollatzResearch.WordTrace]
  refine ⟨43184210075559571800193469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28789473383706381200128979 43184210075559571800193469)
  ·
    refine ⟨16194078778334839425072551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43184210075559571800193469 16194078778334839425072551)
    ·
      refine ⟨24291118167502259137608827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16194078778334839425072551 24291118167502259137608827)
      ·
        refine ⟨36436677251253388706413241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24291118167502259137608827 36436677251253388706413241)
        ·
          refine ⟨27327507938440041529809931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36436677251253388706413241 27327507938440041529809931)
          ·
            refine ⟨40991261907660062294714897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27327507938440041529809931 40991261907660062294714897)
            ·
              refine ⟨30743446430745046721036173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40991261907660062294714897 30743446430745046721036173)
              ·
                refine ⟨11528792411529392520388565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30743446430745046721036173 11528792411529392520388565)
                ·
                  refine ⟨270206072145220137196607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11528792411529392520388565 270206072145220137196607)
                  ·
                    rfl

theorem cell21_1184005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 3, 7].length) (baseStart_1184005 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1184005 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1184005 prefixEnd_1184005 := by exact prefixLift 1184005
  have htrace : WordTrace (prefixWord ++ tailWord_1184005) baseStart_1184005 baseEnd_1184005 := by
    simpa [prefixWord, tailWord_1184005, baseEnd_1184005] using wordTrace_append hprefix tailTrace_1184005
  have hstable : (prefixWord ++ tailWord_1184005).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1184005).length < 2 ^ (prefixWord ++ tailWord_1184005).sum := by decide
  have hdescent : baseEnd_1184005 < baseStart_1184005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1184005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1184008 : List Nat := [2, 1, 3, 2, 3, 1, 4, 5]
def baseStart_1184008 : Nat := 118140960795 + 1184008 * 2 ^ 59
def prefixEnd_1184008 : Nat := 4983230072969 + 3 ^ 40 * 1184008 * 2
def baseEnd_1184008 : Nat := 90068918928697599548867

theorem tailTrace_1184008 : CollatzResearch.WordTrace tailWord_1184008 prefixEnd_1184008 90068918928697599548867 := by
  unfold tailWord_1184008
  simp only [CollatzResearch.WordTrace]
  refine ⟨21592159747274351656276339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28789546329699135541701785 21592159747274351656276339)
  ·
    refine ⟨32388239620911527484414509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21592159747274351656276339 32388239620911527484414509)
    ·
      refine ⟨12145589857841822806655441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32388239620911527484414509 12145589857841822806655441)
      ·
        refine ⟨9109192393381367104991581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12145589857841822806655441 9109192393381367104991581)
        ·
          refine ⟨3415947147518012664371843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9109192393381367104991581 3415947147518012664371843)
          ·
            refine ⟨5123920721277018996557765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3415947147518012664371843 5123920721277018996557765)
            ·
              refine ⟨960735135239441061854581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5123920721277018996557765 960735135239441061854581)
              ·
                refine ⟨90068918928697599548867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 960735135239441061854581 90068918928697599548867)
                ·
                  rfl

theorem cell21_1184008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 4, 5].length) (baseStart_1184008 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1184008 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1184008 prefixEnd_1184008 := by exact prefixLift 1184008
  have htrace : WordTrace (prefixWord ++ tailWord_1184008) baseStart_1184008 baseEnd_1184008 := by
    simpa [prefixWord, tailWord_1184008, baseEnd_1184008] using wordTrace_append hprefix tailTrace_1184008
  have hstable : (prefixWord ++ tailWord_1184008).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1184008).length < 2 ^ (prefixWord ++ tailWord_1184008).sum := by decide
  have hdescent : baseEnd_1184008 < baseStart_1184008 := by decide
  rcases family_descends (prefixWord ++ tailWord_1184008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1184045 : List Nat := [1, 5, 3, 1, 3, 1, 2, 1, 4]
def baseStart_1184045 : Nat := 118140960795 + 1184045 * 2 ^ 59
def prefixEnd_1184045 : Nat := 4983230072969 + 3 ^ 40 * 1184045 * 2
def baseEnd_1184045 : Nat := 270215200690188956529859

theorem tailTrace_1184045 : CollatzResearch.WordTrace tailWord_1184045 prefixEnd_1184045 270215200690188956529859 := by
  unfold tailWord_1184045
  simp only [CollatzResearch.WordTrace]
  refine ⟨43185668995414658631649589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28790445996943105754433059 43185668995414658631649589)
  ·
    refine ⟨4048656468320124246717149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 43185668995414658631649589 4048656468320124246717149)
    ·
      refine ⟨1518246175620046592518931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4048656468320124246717149 1518246175620046592518931)
      ·
        refine ⟨2277369263430069888778397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1518246175620046592518931 2277369263430069888778397)
        ·
          refine ⟨854013473786276208291899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2277369263430069888778397 854013473786276208291899)
          ·
            refine ⟨1281020210679414312437849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 854013473786276208291899 1281020210679414312437849)
            ·
              refine ⟨960765158009560734328387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1281020210679414312437849 960765158009560734328387)
              ·
                refine ⟨1441147737014341101492581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 960765158009560734328387 1441147737014341101492581)
                ·
                  refine ⟨270215200690188956529859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1441147737014341101492581 270215200690188956529859)
                  ·
                    rfl

theorem cell21_1184045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 2, 1, 4].length) (baseStart_1184045 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1184045 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1184045 prefixEnd_1184045 := by exact prefixLift 1184045
  have htrace : WordTrace (prefixWord ++ tailWord_1184045) baseStart_1184045 baseEnd_1184045 := by
    simpa [prefixWord, tailWord_1184045, baseEnd_1184045] using wordTrace_append hprefix tailTrace_1184045
  have hstable : (prefixWord ++ tailWord_1184045).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1184045).length < 2 ^ (prefixWord ++ tailWord_1184045).sum := by decide
  have hdescent : baseEnd_1184045 < baseStart_1184045 := by decide
  rcases family_descends (prefixWord ++ tailWord_1184045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1184053 : List Nat := [1, 3, 3, 1, 2, 1, 3, 3, 4]
def baseStart_1184053 : Nat := 118140960795 + 1184053 * 2 ^ 59
def prefixEnd_1184053 : Nat := 4983230072969 + 3 ^ 40 * 1184053 * 2
def baseEnd_1184053 : Nat := 270217026399182720396509

theorem tailTrace_1184053 : CollatzResearch.WordTrace tailWord_1184053 prefixEnd_1184053 270217026399182720396509 := by
  unfold tailWord_1184053
  simp only [CollatzResearch.WordTrace]
  refine ⟨43185960779385675997940813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28790640519590450665293875 43185960779385675997940813)
  ·
    refine ⟨16194735292269628499227805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43185960779385675997940813 16194735292269628499227805)
    ·
      refine ⟨6073025734601110687210427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16194735292269628499227805 6073025734601110687210427)
      ·
        refine ⟨9109538601901666030815641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6073025734601110687210427 9109538601901666030815641)
        ·
          refine ⟨6832153951426249523111731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9109538601901666030815641 6832153951426249523111731)
          ·
            refine ⟨10248230927139374284667597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6832153951426249523111731 10248230927139374284667597)
            ·
              refine ⟨3843086597677265356750349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10248230927139374284667597 3843086597677265356750349)
              ·
                refine ⟨1441157474128974508781381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3843086597677265356750349 1441157474128974508781381)
                ·
                  refine ⟨270217026399182720396509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1441157474128974508781381 270217026399182720396509)
                  ·
                    rfl

theorem cell21_1184053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 3, 4].length) (baseStart_1184053 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1184053 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1184053 prefixEnd_1184053 := by exact prefixLift 1184053
  have htrace : WordTrace (prefixWord ++ tailWord_1184053) baseStart_1184053 baseEnd_1184053 := by
    simpa [prefixWord, tailWord_1184053, baseEnd_1184053] using wordTrace_append hprefix tailTrace_1184053
  have hstable : (prefixWord ++ tailWord_1184053).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1184053).length < 2 ^ (prefixWord ++ tailWord_1184053).sum := by decide
  have hdescent : baseEnd_1184053 < baseStart_1184053 := by decide
  rcases family_descends (prefixWord ++ tailWord_1184053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1184118 : List Nat := [5, 1, 1, 4, 1, 1, 3, 5]
def baseStart_1184118 : Nat := 118140960795 + 1184118 * 2 ^ 59
def prefixEnd_1184118 : Nat := 4983230072969 + 3 ^ 40 * 1184118 * 2
def baseEnd_1184118 : Nat := 90077286761585683937681

theorem tailTrace_1184118 : CollatzResearch.WordTrace tailWord_1184118 prefixEnd_1184118 90077286761585683937681 := by
  unfold tailWord_1184118
  simp only [CollatzResearch.WordTrace]
  refine ⟨2699270720259387006191063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28792221016100128066038005 2699270720259387006191063)
  ·
    refine ⟨4048906080389080509286595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2699270720259387006191063 4048906080389080509286595)
    ·
      refine ⟨6073359120583620763929893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4048906080389080509286595 6073359120583620763929893)
      ·
        refine ⟨1138754835109428893236855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6073359120583620763929893 1138754835109428893236855)
        ·
          refine ⟨1708132252664143339855283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1138754835109428893236855 1708132252664143339855283)
          ·
            refine ⟨2562198378996215009782925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1708132252664143339855283 2562198378996215009782925)
            ·
              refine ⟨960824392123580628668597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2562198378996215009782925 960824392123580628668597)
              ·
                refine ⟨90077286761585683937681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 960824392123580628668597 90077286761585683937681)
                ·
                  rfl

theorem cell21_1184118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 3, 5].length) (baseStart_1184118 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1184118 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1184118 prefixEnd_1184118 := by exact prefixLift 1184118
  have htrace : WordTrace (prefixWord ++ tailWord_1184118) baseStart_1184118 baseEnd_1184118 := by
    simpa [prefixWord, tailWord_1184118, baseEnd_1184118] using wordTrace_append hprefix tailTrace_1184118
  have hstable : (prefixWord ++ tailWord_1184118).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1184118).length < 2 ^ (prefixWord ++ tailWord_1184118).sum := by decide
  have hdescent : baseEnd_1184118 < baseStart_1184118 := by decide
  rcases family_descends (prefixWord ++ tailWord_1184118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1184267 : List Nat := [1, 1, 1, 1, 7, 2, 1, 4, 3]
def baseStart_1184267 : Nat := 118140960795 + 1184267 * 2 ^ 59
def prefixEnd_1184267 : Nat := 4983230072969 + 3 ^ 40 * 1184267 * 2
def baseEnd_1184267 : Nat := 270265864114765903829405

theorem tailTrace_1184267 : CollatzResearch.WordTrace tailWord_1184267 prefixEnd_1184267 270265864114765903829405 := by
  unfold tailWord_1184267
  simp only [CollatzResearch.WordTrace]
  refine ⟨43193766000610390546231055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28795844000406927030820703 43193766000610390546231055)
  ·
    refine ⟨64790649000915585819346583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43193766000610390546231055 64790649000915585819346583)
    ·
      refine ⟨97185973501373378729019875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64790649000915585819346583 97185973501373378729019875)
      ·
        refine ⟨145778960252060068093529813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97185973501373378729019875 145778960252060068093529813)
        ·
          refine ⟨3416694380907657845942105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 145778960252060068093529813 3416694380907657845942105)
          ·
            refine ⟨2562520785680743384456579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3416694380907657845942105 2562520785680743384456579)
            ·
              refine ⟨3843781178521115076684869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2562520785680743384456579 3843781178521115076684869)
              ·
                refine ⟨720708970972709076878413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3843781178521115076684869 720708970972709076878413)
                ·
                  refine ⟨270265864114765903829405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 720708970972709076878413 270265864114765903829405)
                  ·
                    rfl

theorem cell21_1184267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 4, 3].length) (baseStart_1184267 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1184267 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1184267 prefixEnd_1184267 := by exact prefixLift 1184267
  have htrace : WordTrace (prefixWord ++ tailWord_1184267) baseStart_1184267 baseEnd_1184267 := by
    simpa [prefixWord, tailWord_1184267, baseEnd_1184267] using wordTrace_append hprefix tailTrace_1184267
  have hstable : (prefixWord ++ tailWord_1184267).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1184267).length < 2 ^ (prefixWord ++ tailWord_1184267).sum := by decide
  have hdescent : baseEnd_1184267 < baseStart_1184267 := by decide
  rcases family_descends (prefixWord ++ tailWord_1184267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1184309 : List Nat := [1, 3, 3, 1, 1, 2, 1, 2, 7]
def baseStart_1184309 : Nat := 118140960795 + 1184309 * 2 ^ 59
def prefixEnd_1184309 : Nat := 4983230072969 + 3 ^ 40 * 1184309 * 2
def baseEnd_1184309 : Nat := 270275449086983164129319

theorem tailTrace_1184309 : CollatzResearch.WordTrace tailWord_1184309 prefixEnd_1184309 270275449086983164129319 := by
  unfold tailWord_1184309
  simp only [CollatzResearch.WordTrace]
  refine ⟨43195297866458231719259981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28796865244305487812839987 43195297866458231719259981)
  ·
    refine ⟨16198236699921836894722493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43195297866458231719259981 16198236699921836894722493)
    ·
      refine ⟨6074338762470688835520935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16198236699921836894722493 6074338762470688835520935)
      ·
        refine ⟨9111508143706033253281403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6074338762470688835520935 9111508143706033253281403)
        ·
          refine ⟨13667262215559049879922105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9111508143706033253281403 13667262215559049879922105)
          ·
            refine ⟨10250446661669287409941579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13667262215559049879922105 10250446661669287409941579)
            ·
              refine ⟨15375669992503931114912369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10250446661669287409941579 15375669992503931114912369)
              ·
                refine ⟨11531752494377948336184277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15375669992503931114912369 11531752494377948336184277)
                ·
                  refine ⟨270275449086983164129319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11531752494377948336184277 270275449086983164129319)
                  ·
                    rfl

theorem cell21_1184309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 2, 7].length) (baseStart_1184309 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1184309 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1184309 prefixEnd_1184309 := by exact prefixLift 1184309
  have htrace : WordTrace (prefixWord ++ tailWord_1184309) baseStart_1184309 baseEnd_1184309 := by
    simpa [prefixWord, tailWord_1184309, baseEnd_1184309] using wordTrace_append hprefix tailTrace_1184309
  have hstable : (prefixWord ++ tailWord_1184309).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1184309).length < 2 ^ (prefixWord ++ tailWord_1184309).sum := by decide
  have hdescent : baseEnd_1184309 < baseStart_1184309 := by decide
  rcases family_descends (prefixWord ++ tailWord_1184309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1184447 : List Nat := [1, 1, 2, 2, 2, 6, 1, 6]
def baseStart_1184447 : Nat := 118140960795 + 1184447 * 2 ^ 59
def prefixEnd_1184447 : Nat := 4983230072969 + 3 ^ 40 * 1184447 * 2
def baseEnd_1184447 : Nat := 90102314189041863609679

theorem tailTrace_1184447 : CollatzResearch.WordTrace tailWord_1184447 prefixEnd_1184447 90102314189041863609679 := by
  unfold tailWord_1184447
  simp only [CollatzResearch.WordTrace]
  refine ⟨43200331139958281287783595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28800220759972187525189063 43200331139958281287783595)
  ·
    refine ⟨64800496709937421931675393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43200331139958281287783595 64800496709937421931675393)
    ·
      refine ⟨48600372532453066448756545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64800496709937421931675393 48600372532453066448756545)
      ·
        refine ⟨36450279399339799836567409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48600372532453066448756545 36450279399339799836567409)
        ·
          refine ⟨27337709549504849877425557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36450279399339799836567409 27337709549504849877425557)
          ·
            refine ⟨1281455135133039838004323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 27337709549504849877425557 1281455135133039838004323)
            ·
              refine ⟨1922182702699559757006485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1281455135133039838004323 1922182702699559757006485)
              ·
                refine ⟨90102314189041863609679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1922182702699559757006485 90102314189041863609679)
                ·
                  rfl

theorem cell21_1184447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 1, 6].length) (baseStart_1184447 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1184447 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1184447 prefixEnd_1184447 := by exact prefixLift 1184447
  have htrace : WordTrace (prefixWord ++ tailWord_1184447) baseStart_1184447 baseEnd_1184447 := by
    simpa [prefixWord, tailWord_1184447, baseEnd_1184447] using wordTrace_append hprefix tailTrace_1184447
  have hstable : (prefixWord ++ tailWord_1184447).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1184447).length < 2 ^ (prefixWord ++ tailWord_1184447).sum := by decide
  have hdescent : baseEnd_1184447 < baseStart_1184447 := by decide
  rcases family_descends (prefixWord ++ tailWord_1184447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1184509 : List Nat := [1, 4, 1, 1, 1, 1, 7, 1, 4]
def baseStart_1184509 : Nat := 118140960795 + 1184509 * 2 ^ 59
def prefixEnd_1184509 : Nat := 4983230072969 + 3 ^ 40 * 1184509 * 2
def baseEnd_1184509 : Nat := 270321091811827260795577

theorem tailTrace_1184509 : CollatzResearch.WordTrace tailWord_1184509 prefixEnd_1184509 270321091811827260795577 := by
  unfold tailWord_1184509
  simp only [CollatzResearch.WordTrace]
  refine ⟨43202592465733665876540581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28801728310489110584360387 43202592465733665876540581)
  ·
    refine ⟨8100486087325062351851359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43202592465733665876540581 8100486087325062351851359)
    ·
      refine ⟨12150729130987593527777039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8100486087325062351851359 12150729130987593527777039)
      ·
        refine ⟨18226093696481390291665559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12150729130987593527777039 18226093696481390291665559)
        ·
          refine ⟨27339140544722085437498339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18226093696481390291665559 27339140544722085437498339)
          ·
            refine ⟨41008710817083128156247509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27339140544722085437498339 41008710817083128156247509)
            ·
              refine ⟨961141659775385816162051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 41008710817083128156247509 961141659775385816162051)
              ·
                refine ⟨1441712489663078724243077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 961141659775385816162051 1441712489663078724243077)
                ·
                  refine ⟨270321091811827260795577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1441712489663078724243077 270321091811827260795577)
                  ·
                    rfl

theorem cell21_1184509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 7, 1, 4].length) (baseStart_1184509 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1184509 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1184509 prefixEnd_1184509 := by exact prefixLift 1184509
  have htrace : WordTrace (prefixWord ++ tailWord_1184509) baseStart_1184509 baseEnd_1184509 := by
    simpa [prefixWord, tailWord_1184509, baseEnd_1184509] using wordTrace_append hprefix tailTrace_1184509
  have hstable : (prefixWord ++ tailWord_1184509).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1184509).length < 2 ^ (prefixWord ++ tailWord_1184509).sum := by decide
  have hdescent : baseEnd_1184509 < baseStart_1184509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1184509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1184557 : List Nat := [1, 5, 3, 2, 1, 1, 2, 6]
def baseStart_1184557 : Nat := 118140960795 + 1184557 * 2 ^ 59
def prefixEnd_1184557 : Nat := 4983230072969 + 3 ^ 40 * 1184557 * 2
def baseEnd_1184557 : Nat := 90110682021929947998493

theorem tailTrace_1184557 : CollatzResearch.WordTrace tailWord_1184557 prefixEnd_1184557 90110682021929947998493 := by
  unfold tailWord_1184557
  simp only [CollatzResearch.WordTrace]
  refine ⟨43204343169559770074287925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28802895446373180049525283 43204343169559770074287925)
  ·
    refine ⟨4050407172146228444464493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 43204343169559770074287925 4050407172146228444464493)
    ·
      refine ⟨1518902689554835666674185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4050407172146228444464493 1518902689554835666674185)
      ·
        refine ⟨1139177017166126750005639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1518902689554835666674185 1139177017166126750005639)
        ·
          refine ⟨1708765525749190125008459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1139177017166126750005639 1708765525749190125008459)
          ·
            refine ⟨2563148288623785187512689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1708765525749190125008459 2563148288623785187512689)
            ·
              refine ⟨1922361216467838890634517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2563148288623785187512689 1922361216467838890634517)
              ·
                refine ⟨90110682021929947998493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1922361216467838890634517 90110682021929947998493)
                ·
                  rfl

theorem cell21_1184557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 2, 6].length) (baseStart_1184557 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1184557 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1184557 prefixEnd_1184557 := by exact prefixLift 1184557
  have htrace : WordTrace (prefixWord ++ tailWord_1184557) baseStart_1184557 baseEnd_1184557 := by
    simpa [prefixWord, tailWord_1184557, baseEnd_1184557] using wordTrace_append hprefix tailTrace_1184557
  have hstable : (prefixWord ++ tailWord_1184557).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1184557).length < 2 ^ (prefixWord ++ tailWord_1184557).sum := by decide
  have hdescent : baseEnd_1184557 < baseStart_1184557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1184557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1184568 : List Nat := [2, 1, 2, 1, 3, 2, 3, 3, 4]
def baseStart_1184568 : Nat := 118140960795 + 1184568 * 2 ^ 59
def prefixEnd_1184568 : Nat := 4983230072969 + 3 ^ 40 * 1184568 * 2
def baseEnd_1184568 : Nat := 270334556415656269312123

theorem tailTrace_1184568 : CollatzResearch.WordTrace tailWord_1184568 prefixEnd_1184568 270334556415656269312123 := by
  unfold tailWord_1184568
  simp only [CollatzResearch.WordTrace]
  refine ⟨21602372186259959476469179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28803162915013279301958905 21602372186259959476469179)
  ·
    refine ⟨32403558279389939214703769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21602372186259959476469179 32403558279389939214703769)
    ·
      refine ⟨24302668709542454411027827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32403558279389939214703769 24302668709542454411027827)
      ·
        refine ⟨36454003064313681616541741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24302668709542454411027827 36454003064313681616541741)
        ·
          refine ⟨13670251149117630606203153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36454003064313681616541741 13670251149117630606203153)
          ·
            refine ⟨10252688361838222954652365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13670251149117630606203153 10252688361838222954652365)
            ·
              refine ⟨3844758135689333607994637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10252688361838222954652365 3844758135689333607994637)
              ·
                refine ⟨1441784300883500102997989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3844758135689333607994637 1441784300883500102997989)
                ·
                  refine ⟨270334556415656269312123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1441784300883500102997989 270334556415656269312123)
                  ·
                    rfl

theorem cell21_1184568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 3, 4].length) (baseStart_1184568 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1184568 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1184568 prefixEnd_1184568 := by exact prefixLift 1184568
  have htrace : WordTrace (prefixWord ++ tailWord_1184568) baseStart_1184568 baseEnd_1184568 := by
    simpa [prefixWord, tailWord_1184568, baseEnd_1184568] using wordTrace_append hprefix tailTrace_1184568
  have hstable : (prefixWord ++ tailWord_1184568).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1184568).length < 2 ^ (prefixWord ++ tailWord_1184568).sum := by decide
  have hdescent : baseEnd_1184568 < baseStart_1184568 := by decide
  rcases family_descends (prefixWord ++ tailWord_1184568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1184630 : List Nat := [5, 1, 1, 3, 1, 1, 1, 1, 7]
def baseStart_1184630 : Nat := 118140960795 + 1184630 * 2 ^ 59
def prefixEnd_1184630 : Nat := 4983230072969 + 3 ^ 40 * 1184630 * 2
def baseEnd_1184630 : Nat := 270348705660357939278663

theorem tailTrace_1184630 : CollatzResearch.WordTrace tailWord_1184630 prefixEnd_1184630 270348705660357939278663 := by
  unfold tailWord_1184630
  simp only [CollatzResearch.WordTrace]
  refine ⟨2700437856143456471355959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28804670465530202361130229 2700437856143456471355959)
  ·
    refine ⟨4050656784215184707033939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2700437856143456471355959 4050656784215184707033939)
    ·
      refine ⟨6075985176322777060550909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4050656784215184707033939 6075985176322777060550909)
      ·
        refine ⟨2278494441121041397706591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6075985176322777060550909 2278494441121041397706591)
        ·
          refine ⟨3417741661681562096559887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2278494441121041397706591 3417741661681562096559887)
          ·
            refine ⟨5126612492522343144839831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3417741661681562096559887 5126612492522343144839831)
            ·
              refine ⟨7689918738783514717259747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5126612492522343144839831 7689918738783514717259747)
              ·
                refine ⟨11534878108175272075889621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7689918738783514717259747 11534878108175272075889621)
                ·
                  refine ⟨270348705660357939278663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11534878108175272075889621 270348705660357939278663)
                  ·
                    rfl

theorem cell21_1184630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 1, 7].length) (baseStart_1184630 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1184630 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1184630 prefixEnd_1184630 := by exact prefixLift 1184630
  have htrace : WordTrace (prefixWord ++ tailWord_1184630) baseStart_1184630 baseEnd_1184630 := by
    simpa [prefixWord, tailWord_1184630, baseEnd_1184630] using wordTrace_append hprefix tailTrace_1184630
  have hstable : (prefixWord ++ tailWord_1184630).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1184630).length < 2 ^ (prefixWord ++ tailWord_1184630).sum := by decide
  have hdescent : baseEnd_1184630 < baseStart_1184630 := by decide
  rcases family_descends (prefixWord ++ tailWord_1184630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1184647 : List Nat := [1, 1, 4, 2, 3, 2, 2, 3, 3]
def baseStart_1184647 : Nat := 118140960795 + 1184647 * 2 ^ 59
def prefixEnd_1184647 : Nat := 4983230072969 + 3 ^ 40 * 1184647 * 2
def baseEnd_1184647 : Nat := 270352585291969687495295

theorem tailTrace_1184647 : CollatzResearch.WordTrace tailWord_1184647 prefixEnd_1184647 270352585291969687495295 := by
  unfold tailWord_1184647
  simp only [CollatzResearch.WordTrace]
  refine ⟨43207625739233715445064195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28805083826155810296709463 43207625739233715445064195)
  ·
    refine ⟨64811438608850573167596293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43207625739233715445064195 64811438608850573167596293)
    ·
      refine ⟨12152144739159482468924305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64811438608850573167596293 12152144739159482468924305)
      ·
        refine ⟨9114108554369611851693229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12152144739159482468924305 9114108554369611851693229)
        ·
          refine ⟨3417790707888604444384961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9114108554369611851693229 3417790707888604444384961)
          ·
            refine ⟨2563343030916453333288721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3417790707888604444384961 2563343030916453333288721)
            ·
              refine ⟨1922507273187339999966541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2563343030916453333288721 1922507273187339999966541)
              ·
                refine ⟨720940227445252499987453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1922507273187339999966541 720940227445252499987453)
                ·
                  refine ⟨270352585291969687495295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 720940227445252499987453 270352585291969687495295)
                  ·
                    rfl

theorem cell21_1184647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 2, 3, 3].length) (baseStart_1184647 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1184647 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1184647 prefixEnd_1184647 := by exact prefixLift 1184647
  have htrace : WordTrace (prefixWord ++ tailWord_1184647) baseStart_1184647 baseEnd_1184647 := by
    simpa [prefixWord, tailWord_1184647, baseEnd_1184647] using wordTrace_append hprefix tailTrace_1184647
  have hstable : (prefixWord ++ tailWord_1184647).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1184647).length < 2 ^ (prefixWord ++ tailWord_1184647).sum := by decide
  have hdescent : baseEnd_1184647 < baseStart_1184647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1184647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1184661 : List Nat := [1, 3, 2, 1, 1, 6, 1, 2, 4]
def baseStart_1184661 : Nat := 118140960795 + 1184661 * 2 ^ 59
def prefixEnd_1184661 : Nat := 4983230072969 + 3 ^ 40 * 1184661 * 2
def baseEnd_1184661 : Nat := 270355780282708774261933

theorem tailTrace_1184661 : CollatzResearch.WordTrace tailWord_1184661 prefixEnd_1184661 270355780282708774261933 := by
  unfold tailWord_1184661
  simp only [CollatzResearch.WordTrace]
  refine ⟨43208136361182995836073837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28805424240788663890715891 43208136361182995836073837)
  ·
    refine ⟨16203051135443623438527689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43208136361182995836073837 16203051135443623438527689)
    ·
      refine ⟨12152288351582717578895767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16203051135443623438527689 12152288351582717578895767)
      ·
        refine ⟨18228432527374076368343651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12152288351582717578895767 18228432527374076368343651)
        ·
          refine ⟨27342648791061114552515477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18228432527374076368343651 27342648791061114552515477)
          ·
            refine ⟨1281686662080989744649163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 27342648791061114552515477 1281686662080989744649163)
            ·
              refine ⟨1922529993121484616973745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1281686662080989744649163 1922529993121484616973745)
              ·
                refine ⟨1441897494841113462730309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1922529993121484616973745 1441897494841113462730309)
                ·
                  refine ⟨270355780282708774261933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1441897494841113462730309 270355780282708774261933)
                  ·
                    rfl

theorem cell21_1184661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 1, 2, 4].length) (baseStart_1184661 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1184661 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1184661 prefixEnd_1184661 := by exact prefixLift 1184661
  have htrace : WordTrace (prefixWord ++ tailWord_1184661) baseStart_1184661 baseEnd_1184661 := by
    simpa [prefixWord, tailWord_1184661, baseEnd_1184661] using wordTrace_append hprefix tailTrace_1184661
  have hstable : (prefixWord ++ tailWord_1184661).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1184661).length < 2 ^ (prefixWord ++ tailWord_1184661).sum := by decide
  have hdescent : baseEnd_1184661 < baseStart_1184661 := by decide
  rcases family_descends (prefixWord ++ tailWord_1184661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1184692 : List Nat := [2, 5, 2, 1, 1, 2, 1, 7]
def baseStart_1184692 : Nat := 118140960795 + 1184692 * 2 ^ 59
def prefixEnd_1184692 : Nat := 4983230072969 + 3 ^ 40 * 1184692 * 2
def baseEnd_1184692 : Nat := 90120951635019869748401

theorem tailTrace_1184692 : CollatzResearch.WordTrace tailWord_1184692 prefixEnd_1184692 90120951635019869748401 := by
  unfold tailWord_1184692
  simp only [CollatzResearch.WordTrace]
  refine ⟨21604633512035344065226165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28806178016047125420301553 21604633512035344065226165)
  ·
    refine ⟨2025434391753313506114953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21604633512035344065226165 2025434391753313506114953)
    ·
      refine ⟨1519075793814985129586215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2025434391753313506114953 1519075793814985129586215)
      ·
        refine ⟨2278613690722477694379323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1519075793814985129586215 2278613690722477694379323)
        ·
          refine ⟨3417920536083716541568985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2278613690722477694379323 3417920536083716541568985)
          ·
            refine ⟨2563440402062787406176739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3417920536083716541568985 2563440402062787406176739)
            ·
              refine ⟨3845160603094181109265109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2563440402062787406176739 3845160603094181109265109)
              ·
                refine ⟨90120951635019869748401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3845160603094181109265109 90120951635019869748401)
                ·
                  rfl

theorem cell21_1184692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 7].length) (baseStart_1184692 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1184692 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1184692 prefixEnd_1184692 := by exact prefixLift 1184692
  have htrace : WordTrace (prefixWord ++ tailWord_1184692) baseStart_1184692 baseEnd_1184692 := by
    simpa [prefixWord, tailWord_1184692, baseEnd_1184692] using wordTrace_append hprefix tailTrace_1184692
  have hstable : (prefixWord ++ tailWord_1184692).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1184692).length < 2 ^ (prefixWord ++ tailWord_1184692).sum := by decide
  have hdescent : baseEnd_1184692 < baseStart_1184692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1184692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1184830 : List Nat := [4, 2, 1, 3, 1, 3, 1, 2, 4]
def baseStart_1184830 : Nat := 118140960795 + 1184830 * 2 ^ 59
def prefixEnd_1184830 : Nat := 4983230072969 + 3 ^ 40 * 1184830 * 2
def baseEnd_1184830 : Nat := 270394348385202035944921

theorem tailTrace_1184830 : CollatzResearch.WordTrace tailWord_1184830 prefixEnd_1184830 270394348385202035944921 := by
  unfold tailWord_1184830
  simp only [CollatzResearch.WordTrace]
  refine ⟨5401787537196342212371993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28809533531713825132650629 5401787537196342212371993)
  ·
    refine ⟨4051340652897256659278995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5401787537196342212371993 4051340652897256659278995)
    ·
      refine ⟨6077010979345884988918493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4051340652897256659278995 6077010979345884988918493)
      ·
        refine ⟨2278879117254706870844435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6077010979345884988918493 2278879117254706870844435)
        ·
          refine ⟨3418318675882060306266653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2278879117254706870844435 3418318675882060306266653)
          ·
            refine ⟨1281869503455772614849995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3418318675882060306266653 1281869503455772614849995)
            ·
              refine ⟨1922804255183658922274993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1281869503455772614849995 1922804255183658922274993)
              ·
                refine ⟨1442103191387744191706245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1922804255183658922274993 1442103191387744191706245)
                ·
                  refine ⟨270394348385202035944921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1442103191387744191706245 270394348385202035944921)
                  ·
                    rfl

theorem cell21_1184830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 1, 2, 4].length) (baseStart_1184830 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1184830 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1184830 prefixEnd_1184830 := by exact prefixLift 1184830
  have htrace : WordTrace (prefixWord ++ tailWord_1184830) baseStart_1184830 baseEnd_1184830 := by
    simpa [prefixWord, tailWord_1184830, baseEnd_1184830] using wordTrace_append hprefix tailTrace_1184830
  have hstable : (prefixWord ++ tailWord_1184830).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1184830).length < 2 ^ (prefixWord ++ tailWord_1184830).sum := by decide
  have hdescent : baseEnd_1184830 < baseStart_1184830 := by decide
  rcases family_descends (prefixWord ++ tailWord_1184830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1184861 : List Nat := [1, 4, 4, 1, 2, 2, 2, 5]
def baseStart_1184861 : Nat := 118140960795 + 1184861 * 2 ^ 59
def prefixEnd_1184861 : Nat := 4983230072969 + 3 ^ 40 * 1184861 * 2
def baseEnd_1184861 : Nat := 90133807669184290309397

theorem tailTrace_1184861 : CollatzResearch.WordTrace tailWord_1184861 prefixEnd_1184861 90133807669184290309397 := by
  unfold tailWord_1184861
  simp only [CollatzResearch.WordTrace]
  refine ⟨43215430960458429993354437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28810287306972286662236291 43215430960458429993354437)
  ·
    refine ⟨8102893305085955623753957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43215430960458429993354437 8102893305085955623753957)
    ·
      refine ⟨1519292494703616679453867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8102893305085955623753957 1519292494703616679453867)
      ·
        refine ⟨2278938742055425019180801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1519292494703616679453867 2278938742055425019180801)
        ·
          refine ⟨1709204056541568764385601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2278938742055425019180801 1709204056541568764385601)
          ·
            refine ⟨1281903042406176573289201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1709204056541568764385601 1281903042406176573289201)
            ·
              refine ⟨961427281804632429966901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1281903042406176573289201 961427281804632429966901)
              ·
                refine ⟨90133807669184290309397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 961427281804632429966901 90133807669184290309397)
                ·
                  rfl

theorem cell21_1184861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 2, 5].length) (baseStart_1184861 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1184861 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1184861 prefixEnd_1184861 := by exact prefixLift 1184861
  have htrace : WordTrace (prefixWord ++ tailWord_1184861) baseStart_1184861 baseEnd_1184861 := by
    simpa [prefixWord, tailWord_1184861, baseEnd_1184861] using wordTrace_append hprefix tailTrace_1184861
  have hstable : (prefixWord ++ tailWord_1184861).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1184861).length < 2 ^ (prefixWord ++ tailWord_1184861).sum := by decide
  have hdescent : baseEnd_1184861 < baseStart_1184861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1184861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185010 : List Nat := [3, 2, 1, 3, 3, 1, 2, 1, 5]
def baseStart_1185010 : Nat := 118140960795 + 1185010 * 2 ^ 59
def prefixEnd_1185010 : Nat := 4983230072969 + 3 ^ 40 * 1185010 * 2
def baseEnd_1185010 : Nat := 270435426837561722944553

theorem tailTrace_1185010 : CollatzResearch.WordTrace tailWord_1185010 prefixEnd_1185010 270435426837561722944553 := by
  unfold tailWord_1185010
  simp only [CollatzResearch.WordTrace]
  refine ⟨10805216359229657110132121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28813910291279085627018989 10805216359229657110132121)
  ·
    refine ⟨8103912269422242832599091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10805216359229657110132121 8103912269422242832599091)
    ·
      refine ⟨12155868404133364248898637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8103912269422242832599091 12155868404133364248898637)
      ·
        refine ⟨4558450651550011593336989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12155868404133364248898637 4558450651550011593336989)
        ·
          refine ⟨1709418994331254347501371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4558450651550011593336989 1709418994331254347501371)
          ·
            refine ⟨2564128491496881521252057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1709418994331254347501371 2564128491496881521252057)
            ·
              refine ⟨1923096368622661140939043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2564128491496881521252057 1923096368622661140939043)
              ·
                refine ⟨2884644552933991711408565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1923096368622661140939043 2884644552933991711408565)
                ·
                  refine ⟨270435426837561722944553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2884644552933991711408565 270435426837561722944553)
                  ·
                    rfl

theorem cell21_1185010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 2, 1, 5].length) (baseStart_1185010 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1185010 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1185010 prefixEnd_1185010 := by exact prefixLift 1185010
  have htrace : WordTrace (prefixWord ++ tailWord_1185010) baseStart_1185010 baseEnd_1185010 := by
    simpa [prefixWord, tailWord_1185010, baseEnd_1185010] using wordTrace_append hprefix tailTrace_1185010
  have hstable : (prefixWord ++ tailWord_1185010).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185010).length < 2 ^ (prefixWord ++ tailWord_1185010).sum := by decide
  have hdescent : baseEnd_1185010 < baseStart_1185010 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185038 : List Nat := [4, 1, 1, 2, 1, 4, 1, 7]
def baseStart_1185038 : Nat := 118140960795 + 1185038 * 2 ^ 59
def prefixEnd_1185038 : Nat := 4983230072969 + 3 ^ 40 * 1185038 * 2
def baseEnd_1185038 : Nat := 90147272273013298825943

theorem tailTrace_1185038 : CollatzResearch.WordTrace tailWord_1185038 prefixEnd_1185038 90147272273013298825943 := by
  unfold tailWord_1185038
  simp only [CollatzResearch.WordTrace]
  refine ⟨5402735835102148652818471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28814591120544792815031845 5402735835102148652818471)
  ·
    refine ⟨8104103752653222979227707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5402735835102148652818471 8104103752653222979227707)
    ·
      refine ⟨12156155628979834468841561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8104103752653222979227707 12156155628979834468841561)
      ·
        refine ⟨9117116721734875851631171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12156155628979834468841561 9117116721734875851631171)
        ·
          refine ⟨13675675082602313777446757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9117116721734875851631171 13675675082602313777446757)
          ·
            refine ⟨2564189077987933833271267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13675675082602313777446757 2564189077987933833271267)
            ·
              refine ⟨3846283616981900749906901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2564189077987933833271267 3846283616981900749906901)
              ·
                refine ⟨90147272273013298825943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3846283616981900749906901 90147272273013298825943)
                ·
                  rfl

theorem cell21_1185038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 7].length) (baseStart_1185038 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1185038 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1185038 prefixEnd_1185038 := by exact prefixLift 1185038
  have htrace : WordTrace (prefixWord ++ tailWord_1185038) baseStart_1185038 baseEnd_1185038 := by
    simpa [prefixWord, tailWord_1185038, baseEnd_1185038] using wordTrace_append hprefix tailTrace_1185038
  have hstable : (prefixWord ++ tailWord_1185038).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185038).length < 2 ^ (prefixWord ++ tailWord_1185038).sum := by decide
  have hdescent : baseEnd_1185038 < baseStart_1185038 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185052 : List Nat := [2, 2, 3, 1, 1, 1, 2, 2, 7]
def baseStart_1185052 : Nat := 118140960795 + 1185052 * 2 ^ 59
def prefixEnd_1185052 : Nat := 4983230072969 + 3 ^ 40 * 1185052 * 2
def baseEnd_1185052 : Nat := 270445011809778983244467

theorem tailTrace_1185052 : CollatzResearch.WordTrace tailWord_1185052 prefixEnd_1185052 270445011809778983244467 := by
  unfold tailWord_1185052
  simp only [CollatzResearch.WordTrace]
  refine ⟨21611198651383234806778705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28814931535177646409038273 21611198651383234806778705)
  ·
    refine ⟨16208398988537426105084029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21611198651383234806778705 16208398988537426105084029)
    ·
      refine ⟨6078149620701534789406511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16208398988537426105084029 6078149620701534789406511)
      ·
        refine ⟨9117224431052302184109767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6078149620701534789406511 9117224431052302184109767)
        ·
          refine ⟨13675836646578453276164651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9117224431052302184109767 13675836646578453276164651)
          ·
            refine ⟨20513754969867679914246977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13675836646578453276164651 20513754969867679914246977)
            ·
              refine ⟨15385316227400759935685233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20513754969867679914246977 15385316227400759935685233)
              ·
                refine ⟨11538987170550569951763925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15385316227400759935685233 11538987170550569951763925)
                ·
                  refine ⟨270445011809778983244467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11538987170550569951763925 270445011809778983244467)
                  ·
                    rfl

theorem cell21_1185052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 2, 7].length) (baseStart_1185052 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1185052 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1185052 prefixEnd_1185052 := by exact prefixLift 1185052
  have htrace : WordTrace (prefixWord ++ tailWord_1185052) baseStart_1185052 baseEnd_1185052 := by
    simpa [prefixWord, tailWord_1185052, baseEnd_1185052] using wordTrace_append hprefix tailTrace_1185052
  have hstable : (prefixWord ++ tailWord_1185052).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185052).length < 2 ^ (prefixWord ++ tailWord_1185052).sum := by decide
  have hdescent : baseEnd_1185052 < baseStart_1185052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185055 : List Nat := [1, 1, 2, 4, 5, 1, 7]
def baseStart_1185055 : Nat := 118140960795 + 1185055 * 2 ^ 59
def prefixEnd_1185055 : Nat := 4983230072969 + 3 ^ 40 * 1185055 * 2
def baseEnd_1185055 : Nat := 30049521827850182743829

theorem tailTrace_1185055 : CollatzResearch.WordTrace tailWord_1185055 prefixEnd_1185055 30049521827850182743829 := by
  unfold tailWord_1185055
  simp only [CollatzResearch.WordTrace]
  refine ⟨43222506721755601125916619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28815004481170400750611079 43222506721755601125916619)
  ·
    refine ⟨64833760082633401688874929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43222506721755601125916619 64833760082633401688874929)
    ·
      refine ⟨48625320061975051266656197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64833760082633401688874929 48625320061975051266656197)
      ·
        refine ⟨9117247511620322112498037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48625320061975051266656197 9117247511620322112498037)
        ·
          refine ⟨854741954214405198046691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9117247511620322112498037 854741954214405198046691)
          ·
            refine ⟨1282112931321607797070037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 854741954214405198046691 1282112931321607797070037)
            ·
              refine ⟨30049521827850182743829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1282112931321607797070037 30049521827850182743829)
              ·
                rfl

theorem cell21_1185055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 7].length) (baseStart_1185055 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1185055 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1185055 prefixEnd_1185055 := by exact prefixLift 1185055
  have htrace : WordTrace (prefixWord ++ tailWord_1185055) baseStart_1185055 baseEnd_1185055 := by
    simpa [prefixWord, tailWord_1185055, baseEnd_1185055] using wordTrace_append hprefix tailTrace_1185055
  have hstable : (prefixWord ++ tailWord_1185055).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185055).length < 2 ^ (prefixWord ++ tailWord_1185055).sum := by decide
  have hdescent : baseEnd_1185055 < baseStart_1185055 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185097 : List Nat := [1, 2, 1, 1, 2, 3, 4, 7]
def baseStart_1185097 : Nat := 118140960795 + 1185097 * 2 ^ 59
def prefixEnd_1185097 : Nat := 4983230072969 + 3 ^ 40 * 1185097 * 2
def baseEnd_1185097 : Nat := 90151760474289634998125

theorem tailTrace_1185097 : CollatzResearch.WordTrace tailWord_1185097 prefixEnd_1185097 90151760474289634998125 := by
  unfold tailWord_1185097
  simp only [CollatzResearch.WordTrace]
  refine ⟨43224038587603442298945545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28816025725068961532630363 43224038587603442298945545)
  ·
    refine ⟨32418028940702581724209159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43224038587603442298945545 32418028940702581724209159)
    ·
      refine ⟨48627043411053872586313739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32418028940702581724209159 48627043411053872586313739)
      ·
        refine ⟨72940565116580808879470609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48627043411053872586313739 72940565116580808879470609)
        ·
          refine ⟨54705423837435606659602957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 72940565116580808879470609 54705423837435606659602957)
          ·
            refine ⟨20514533939038352497351109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54705423837435606659602957 20514533939038352497351109)
            ·
              refine ⟨3846475113569691093253333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20514533939038352497351109 3846475113569691093253333)
              ·
                refine ⟨90151760474289634998125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3846475113569691093253333 90151760474289634998125)
                ·
                  rfl

theorem cell21_1185097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 7].length) (baseStart_1185097 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1185097 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1185097 prefixEnd_1185097 := by exact prefixLift 1185097
  have htrace : WordTrace (prefixWord ++ tailWord_1185097) baseStart_1185097 baseEnd_1185097 := by
    simpa [prefixWord, tailWord_1185097, baseEnd_1185097] using wordTrace_append hprefix tailTrace_1185097
  have hstable : (prefixWord ++ tailWord_1185097).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185097).length < 2 ^ (prefixWord ++ tailWord_1185097).sum := by decide
  have hdescent : baseEnd_1185097 < baseStart_1185097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185176 : List Nat := [2, 1, 2, 5, 2, 1, 1, 1, 6]
def baseStart_1185176 : Nat := 118140960795 + 1185176 * 2 ^ 59
def prefixEnd_1185176 : Nat := 4983230072969 + 3 ^ 40 * 1185176 * 2
def baseEnd_1185176 : Nat := 270473310299182323177547

theorem tailTrace_1185176 : CollatzResearch.WordTrace tailWord_1185176 prefixEnd_1185176 270473310299182323177547 := by
  unfold tailWord_1185176
  simp only [CollatzResearch.WordTrace]
  refine ⟨21613459977158619395535691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28817946636211492527380921 21613459977158619395535691)
  ·
    refine ⟨32420189965737929093303537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21613459977158619395535691 32420189965737929093303537)
    ·
      refine ⟨24315142474303446819977653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32420189965737929093303537 24315142474303446819977653)
      ·
        refine ⟨2279544606965948139372905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24315142474303446819977653 2279544606965948139372905)
        ·
          refine ⟨1709658455224461104529679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2279544606965948139372905 1709658455224461104529679)
          ·
            refine ⟨2564487682836691656794519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1709658455224461104529679 2564487682836691656794519)
            ·
              refine ⟨3846731524255037485191779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2564487682836691656794519 3846731524255037485191779)
              ·
                refine ⟨5770097286382556227787669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3846731524255037485191779 5770097286382556227787669)
                ·
                  refine ⟨270473310299182323177547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5770097286382556227787669 270473310299182323177547)
                  ·
                    rfl

theorem cell21_1185176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 1, 6].length) (baseStart_1185176 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1185176 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1185176 prefixEnd_1185176 := by exact prefixLift 1185176
  have htrace : WordTrace (prefixWord ++ tailWord_1185176) baseStart_1185176 baseEnd_1185176 := by
    simpa [prefixWord, tailWord_1185176, baseEnd_1185176] using wordTrace_append hprefix tailTrace_1185176
  have hstable : (prefixWord ++ tailWord_1185176).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185176).length < 2 ^ (prefixWord ++ tailWord_1185176).sum := by decide
  have hdescent : baseEnd_1185176 < baseStart_1185176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185238 : List Nat := [5, 2, 1, 1, 1, 2, 3, 1, 5]
def baseStart_1185238 : Nat := 118140960795 + 1185238 * 2 ^ 59
def prefixEnd_1185238 : Nat := 4983230072969 + 3 ^ 40 * 1185238 * 2
def baseEnd_1185238 : Nat := 270487459543883993144087

theorem tailTrace_1185238 : CollatzResearch.WordTrace tailWord_1185238 prefixEnd_1185238 270487459543883993144087 := by
  unfold tailWord_1185238
  simp only [CollatzResearch.WordTrace]
  refine ⟨2701823830005788961239273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28819454186728415586552245 2701823830005788961239273)
  ·
    refine ⟨2026367872504341720929455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2701823830005788961239273 2026367872504341720929455)
    ·
      refine ⟨3039551808756512581394183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2026367872504341720929455 3039551808756512581394183)
      ·
        refine ⟨4559327713134768872091275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3039551808756512581394183 4559327713134768872091275)
        ·
          refine ⟨6838991569702153308136913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4559327713134768872091275 6838991569702153308136913)
          ·
            refine ⟨5129243677276614981102685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6838991569702153308136913 5129243677276614981102685)
            ·
              refine ⟨1923466378978730617913507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5129243677276614981102685 1923466378978730617913507)
              ·
                refine ⟨2885199568468095926870261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1923466378978730617913507 2885199568468095926870261)
                ·
                  refine ⟨270487459543883993144087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2885199568468095926870261 270487459543883993144087)
                  ·
                    rfl

theorem cell21_1185238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_1185238 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1185238 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1185238 prefixEnd_1185238 := by exact prefixLift 1185238
  have htrace : WordTrace (prefixWord ++ tailWord_1185238) baseStart_1185238 baseEnd_1185238 := by
    simpa [prefixWord, tailWord_1185238, baseEnd_1185238] using wordTrace_append hprefix tailTrace_1185238
  have hstable : (prefixWord ++ tailWord_1185238).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185238).length < 2 ^ (prefixWord ++ tailWord_1185238).sum := by decide
  have hdescent : baseEnd_1185238 < baseStart_1185238 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185249 : List Nat := [1, 2, 3, 1, 2, 3, 1, 8]
def baseStart_1185249 : Nat := 118140960795 + 1185249 * 2 ^ 59
def prefixEnd_1185249 : Nat := 4983230072969 + 3 ^ 40 * 1185249 * 2
def baseEnd_1185249 : Nat := 90163323297916806153577

theorem tailTrace_1185249 : CollatzResearch.WordTrace tailWord_1185249 prefixEnd_1185249 90163323297916806153577 := by
  unfold tailWord_1185249
  simp only [CollatzResearch.WordTrace]
  refine ⟨43229582483052772258478801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28819721655368514838985867 43229582483052772258478801)
  ·
    refine ⟨32422186862289579193859101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43229582483052772258478801 32422186862289579193859101)
    ·
      refine ⟨12158320073358592197697163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32422186862289579193859101 12158320073358592197697163)
      ·
        refine ⟨18237480110037888296545745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12158320073358592197697163 18237480110037888296545745)
        ·
          refine ⟨13678110082528416222409309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18237480110037888296545745 13678110082528416222409309)
          ·
            refine ⟨5129291280948156083403491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13678110082528416222409309 5129291280948156083403491)
            ·
              refine ⟨7693936921422234125105237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5129291280948156083403491 7693936921422234125105237)
              ·
                refine ⟨90163323297916806153577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7693936921422234125105237 90163323297916806153577)
                ·
                  rfl

theorem cell21_1185249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 8].length) (baseStart_1185249 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1185249 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1185249 prefixEnd_1185249 := by exact prefixLift 1185249
  have htrace : WordTrace (prefixWord ++ tailWord_1185249) baseStart_1185249 baseEnd_1185249 := by
    simpa [prefixWord, tailWord_1185249, baseEnd_1185249] using wordTrace_append hprefix tailTrace_1185249
  have hstable : (prefixWord ++ tailWord_1185249).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185249).length < 2 ^ (prefixWord ++ tailWord_1185249).sum := by decide
  have hdescent : baseEnd_1185249 < baseStart_1185249 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185266 : List Nat := [3, 2, 1, 4, 1, 1, 2, 7]
def baseStart_1185266 : Nat := 118140960795 + 1185266 * 2 ^ 59
def prefixEnd_1185266 : Nat := 4983230072969 + 3 ^ 40 * 1185266 * 2
def baseEnd_1185266 : Nat := 90164616508454055559121

theorem tailTrace_1185266 : CollatzResearch.WordTrace tailWord_1185266 prefixEnd_1185266 90164616508454055559121 := by
  unfold tailWord_1185266
  simp only [CollatzResearch.WordTrace]
  refine ⟨10807550630997796040461913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28820135015994122774565101 10807550630997796040461913)
  ·
    refine ⟨8105662973248347030346435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10807550630997796040461913 8105662973248347030346435)
    ·
      refine ⟨12158494459872520545519653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8105662973248347030346435 12158494459872520545519653)
      ·
        refine ⟨2279717711226097602284935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12158494459872520545519653 2279717711226097602284935)
        ·
          refine ⟨3419576566839146403427403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2279717711226097602284935 3419576566839146403427403)
          ·
            refine ⟨5129364850258719605141105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3419576566839146403427403 5129364850258719605141105)
            ·
              refine ⟨3847023637694039703855829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5129364850258719605141105 3847023637694039703855829)
              ·
                refine ⟨90164616508454055559121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3847023637694039703855829 90164616508454055559121)
                ·
                  rfl

theorem cell21_1185266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 7].length) (baseStart_1185266 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1185266 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1185266 prefixEnd_1185266 := by exact prefixLift 1185266
  have htrace : WordTrace (prefixWord ++ tailWord_1185266) baseStart_1185266 baseEnd_1185266 := by
    simpa [prefixWord, tailWord_1185266, baseEnd_1185266] using wordTrace_append hprefix tailTrace_1185266
  have hstable : (prefixWord ++ tailWord_1185266).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185266).length < 2 ^ (prefixWord ++ tailWord_1185266).sum := by decide
  have hdescent : baseEnd_1185266 < baseStart_1185266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185297 : List Nat := [1, 2, 2, 1, 1, 2, 5, 4, 3]
def baseStart_1185297 : Nat := 118140960795 + 1185297 * 2 ^ 59
def prefixEnd_1185297 : Nat := 4983230072969 + 3 ^ 40 * 1185297 * 2
def baseEnd_1185297 : Nat := 270500924147713001660633

theorem tailTrace_1185297 : CollatzResearch.WordTrace tailWord_1185297 prefixEnd_1185297 270500924147713001660633 := by
  unfold tailWord_1185297
  simp only [CollatzResearch.WordTrace]
  refine ⟨43231333186878876456226145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28820888791252584304150763 43231333186878876456226145)
  ·
    refine ⟨32423499890159157342169609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43231333186878876456226145 32423499890159157342169609)
    ·
      refine ⟨24317624917619368006627207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32423499890159157342169609 24317624917619368006627207)
      ·
        refine ⟨36476437376429052009940811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24317624917619368006627207 36476437376429052009940811)
        ·
          refine ⟨54714656064643578014911217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36476437376429052009940811 54714656064643578014911217)
          ·
            refine ⟨41035992048482683511183413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54714656064643578014911217 41035992048482683511183413)
            ·
              refine ⟨3847124254545251579173445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41035992048482683511183413 3847124254545251579173445)
              ·
                refine ⟨721335797727234671095021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3847124254545251579173445 721335797727234671095021)
                ·
                  refine ⟨270500924147713001660633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 721335797727234671095021 270500924147713001660633)
                  ·
                    rfl

theorem cell21_1185297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 5, 4, 3].length) (baseStart_1185297 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1185297 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1185297 prefixEnd_1185297 := by exact prefixLift 1185297
  have htrace : WordTrace (prefixWord ++ tailWord_1185297) baseStart_1185297 baseEnd_1185297 := by
    simpa [prefixWord, tailWord_1185297, baseEnd_1185297] using wordTrace_append hprefix tailTrace_1185297
  have hstable : (prefixWord ++ tailWord_1185297).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185297).length < 2 ^ (prefixWord ++ tailWord_1185297).sum := by decide
  have hdescent : baseEnd_1185297 < baseStart_1185297 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185300 : List Nat := [2, 4, 3, 1, 2, 2, 1, 6]
def baseStart_1185300 : Nat := 118140960795 + 1185300 * 2 ^ 59
def prefixEnd_1185300 : Nat := 4983230072969 + 3 ^ 40 * 1185300 * 2
def baseEnd_1185300 : Nat := 90167202929528554370209

theorem tailTrace_1185300 : CollatzResearch.WordTrace tailWord_1185300 prefixEnd_1185300 90167202929528554370209 := by
  unfold tailWord_1185300
  simp only [CollatzResearch.WordTrace]
  refine ⟨21615721302934003984292677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28820961737245338645723569 21615721302934003984292677)
  ·
    refine ⟨4052947744300125747054877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21615721302934003984292677 4052947744300125747054877)
    ·
      refine ⟨1519855404112547155145579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4052947744300125747054877 1519855404112547155145579)
      ·
        refine ⟨2279783106168820732718369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1519855404112547155145579 2279783106168820732718369)
        ·
          refine ⟨1709837329626615549538777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2279783106168820732718369 1709837329626615549538777)
          ·
            refine ⟨1282377997219961662154083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1709837329626615549538777 1282377997219961662154083)
            ·
              refine ⟨1923566995829942493231125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1282377997219961662154083 1923566995829942493231125)
              ·
                refine ⟨90167202929528554370209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1923566995829942493231125 90167202929528554370209)
                ·
                  rfl

theorem cell21_1185300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 1, 6].length) (baseStart_1185300 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1185300 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1185300 prefixEnd_1185300 := by exact prefixLift 1185300
  have htrace : WordTrace (prefixWord ++ tailWord_1185300) baseStart_1185300 baseEnd_1185300 := by
    simpa [prefixWord, tailWord_1185300, baseEnd_1185300] using wordTrace_append hprefix tailTrace_1185300
  have hstable : (prefixWord ++ tailWord_1185300).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185300).length < 2 ^ (prefixWord ++ tailWord_1185300).sum := by decide
  have hdescent : baseEnd_1185300 < baseStart_1185300 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185311 : List Nat := [1, 1, 2, 4, 1, 1, 4, 3, 4]
def baseStart_1185311 : Nat := 118140960795 + 1185311 * 2 ^ 59
def prefixEnd_1185311 : Nat := 4983230072969 + 3 ^ 40 * 1185311 * 2
def baseEnd_1185311 : Nat := 270504119138452088427271

theorem tailTrace_1185311 : CollatzResearch.WordTrace tailWord_1185311 prefixEnd_1185311 270504119138452088427271 := by
  unfold tailWord_1185311
  simp only [CollatzResearch.WordTrace]
  refine ⟨43231843808828156847235787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28821229205885437898157191 43231843808828156847235787)
  ·
    refine ⟨64847765713242235270853681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43231843808828156847235787 64847765713242235270853681)
    ·
      refine ⟨48635824284931676453140261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64847765713242235270853681 48635824284931676453140261)
      ·
        refine ⟨9119217053424689334963799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48635824284931676453140261 9119217053424689334963799)
        ·
          refine ⟨13678825580137034002445699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9119217053424689334963799 13678825580137034002445699)
          ·
            refine ⟨20518238370205551003668549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13678825580137034002445699 20518238370205551003668549)
            ·
              refine ⟨3847169694413540813187853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20518238370205551003668549 3847169694413540813187853)
              ·
                refine ⟨1442688635405077804945445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3847169694413540813187853 1442688635405077804945445)
                ·
                  refine ⟨270504119138452088427271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1442688635405077804945445 270504119138452088427271)
                  ·
                    rfl

theorem cell21_1185311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 3, 4].length) (baseStart_1185311 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1185311 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1185311 prefixEnd_1185311 := by exact prefixLift 1185311
  have htrace : WordTrace (prefixWord ++ tailWord_1185311) baseStart_1185311 baseEnd_1185311 := by
    simpa [prefixWord, tailWord_1185311, baseEnd_1185311] using wordTrace_append hprefix tailTrace_1185311
  have hstable : (prefixWord ++ tailWord_1185311).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185311).length < 2 ^ (prefixWord ++ tailWord_1185311).sum := by decide
  have hdescent : baseEnd_1185311 < baseStart_1185311 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185356 : List Nat := [2, 2, 1, 3, 1, 3, 1, 3, 5]
def baseStart_1185356 : Nat := 118140960795 + 1185356 * 2 ^ 59
def prefixEnd_1185356 : Nat := 4983230072969 + 3 ^ 40 * 1185356 * 2
def baseEnd_1185356 : Nat := 270514388751542010177179

theorem tailTrace_1185356 : CollatzResearch.WordTrace tailWord_1185356 prefixEnd_1185356 270514388751542010177179 := by
  unfold tailWord_1185356
  simp only [CollatzResearch.WordTrace]
  refine ⟨21616742546832564766311961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28822323395776753021749281 21616742546832564766311961)
  ·
    refine ⟨16212556910124423574733971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21616742546832564766311961 16212556910124423574733971)
    ·
      refine ⟨24318835365186635362100957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16212556910124423574733971 24318835365186635362100957)
      ·
        refine ⟨9119563261944988260787859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24318835365186635362100957 9119563261944988260787859)
        ·
          refine ⟨13679344892917482391181789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9119563261944988260787859 13679344892917482391181789)
          ·
            refine ⟨5129754334844055896693171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13679344892917482391181789 5129754334844055896693171)
            ·
              refine ⟨7694631502266083845039757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5129754334844055896693171 7694631502266083845039757)
              ·
                refine ⟨2885486813349781441889909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7694631502266083845039757 2885486813349781441889909)
                ·
                  refine ⟨270514388751542010177179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2885486813349781441889909 270514388751542010177179)
                  ·
                    rfl

theorem cell21_1185356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 3, 5].length) (baseStart_1185356 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1185356 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1185356 prefixEnd_1185356 := by exact prefixLift 1185356
  have htrace : WordTrace (prefixWord ++ tailWord_1185356) baseStart_1185356 baseEnd_1185356 := by
    simpa [prefixWord, tailWord_1185356, baseEnd_1185356] using wordTrace_append hprefix tailTrace_1185356
  have hstable : (prefixWord ++ tailWord_1185356).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185356).length < 2 ^ (prefixWord ++ tailWord_1185356).sum := by decide
  have hdescent : baseEnd_1185356 < baseStart_1185356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185418 : List Nat := [3, 1, 2, 3, 2, 2, 2, 6]
def baseStart_1185418 : Nat := 118140960795 + 1185418 * 2 ^ 59
def prefixEnd_1185418 : Nat := 4983230072969 + 3 ^ 40 * 1185418 * 2
def baseEnd_1185418 : Nat := 90176179332081226714573

theorem tailTrace_1185418 : CollatzResearch.WordTrace tailWord_1185418 prefixEnd_1185418 90176179332081226714573 := by
  unfold tailWord_1185418
  simp only [CollatzResearch.WordTrace]
  refine ⟨10808936604860128530345227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28823830946293676080920605 10808936604860128530345227)
  ·
    refine ⟨16213404907290192795517841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10808936604860128530345227 16213404907290192795517841)
    ·
      refine ⟨12160053680467644596638381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16213404907290192795517841 12160053680467644596638381)
      ·
        refine ⟨4560020130175366723739393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12160053680467644596638381 4560020130175366723739393)
        ·
          refine ⟨3420015097631525042804545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4560020130175366723739393 3420015097631525042804545)
          ·
            refine ⟨2565011323223643782103409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3420015097631525042804545 2565011323223643782103409)
            ·
              refine ⟨1923758492417732836577557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2565011323223643782103409 1923758492417732836577557)
              ·
                refine ⟨90176179332081226714573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1923758492417732836577557 90176179332081226714573)
                ·
                  rfl

theorem cell21_1185418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 2, 6].length) (baseStart_1185418 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1185418 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1185418 prefixEnd_1185418 := by exact prefixLift 1185418
  have htrace : WordTrace (prefixWord ++ tailWord_1185418) baseStart_1185418 baseEnd_1185418 := by
    simpa [prefixWord, tailWord_1185418, baseEnd_1185418] using wordTrace_append hprefix tailTrace_1185418
  have hstable : (prefixWord ++ tailWord_1185418).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185418).length < 2 ^ (prefixWord ++ tailWord_1185418).sum := by decide
  have hdescent : baseEnd_1185418 < baseStart_1185418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185463 : List Nat := [1, 1, 3, 1, 5, 1, 1, 4, 4]
def baseStart_1185463 : Nat := 118140960795 + 1185463 * 2 ^ 59
def prefixEnd_1185463 : Nat := 4983230072969 + 3 ^ 40 * 1185463 * 2
def baseEnd_1185463 : Nat := 270538807609333601893627

theorem tailTrace_1185463 : CollatzResearch.WordTrace tailWord_1185463 prefixEnd_1185463 270538807609333601893627 := by
  unfold tailWord_1185463
  simp only [CollatzResearch.WordTrace]
  refine ⟨43237387704277486806769043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28824925136184991204512695 43237387704277486806769043)
  ·
    refine ⟨64856081556416230210153565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43237387704277486806769043 64856081556416230210153565)
    ·
      refine ⟨24321030583656086328807587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64856081556416230210153565 24321030583656086328807587)
      ·
        refine ⟨36481545875484129493211381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24321030583656086328807587 36481545875484129493211381)
        ·
          refine ⟨3420144925826637139988567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36481545875484129493211381 3420144925826637139988567)
          ·
            refine ⟨5130217388739955709982851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3420144925826637139988567 5130217388739955709982851)
            ·
              refine ⟨7695326083109933564974277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5130217388739955709982851 7695326083109933564974277)
              ·
                refine ⟨1442873640583112543432677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7695326083109933564974277 1442873640583112543432677)
                ·
                  refine ⟨270538807609333601893627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1442873640583112543432677 270538807609333601893627)
                  ·
                    rfl

theorem cell21_1185463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 4, 4].length) (baseStart_1185463 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1185463 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1185463 prefixEnd_1185463 := by exact prefixLift 1185463
  have htrace : WordTrace (prefixWord ++ tailWord_1185463) baseStart_1185463 baseEnd_1185463 := by
    simpa [prefixWord, tailWord_1185463, baseEnd_1185463] using wordTrace_append hprefix tailTrace_1185463
  have hstable : (prefixWord ++ tailWord_1185463).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185463).length < 2 ^ (prefixWord ++ tailWord_1185463).sum := by decide
  have hdescent : baseEnd_1185463 < baseStart_1185463 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185466 : List Nat := [3, 1, 1, 1, 2, 4, 4, 2, 3]
def baseStart_1185466 : Nat := 118140960795 + 1185466 * 2 ^ 59
def prefixEnd_1185466 : Nat := 4983230072969 + 3 ^ 40 * 1185466 * 2
def baseEnd_1185466 : Nat := 270539492250206263343621

theorem tailTrace_1185466 : CollatzResearch.WordTrace tailWord_1185466 prefixEnd_1185466 270539492250206263343621 := by
  unfold tailWord_1185466
  simp only [CollatzResearch.WordTrace]
  refine ⟨10809374280816654579782063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28824998082177745546085501 10809374280816654579782063)
  ·
    refine ⟨16214061421224981869673095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10809374280816654579782063 16214061421224981869673095)
    ·
      refine ⟨24321092131837472804509643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16214061421224981869673095 24321092131837472804509643)
      ·
        refine ⟨36481638197756209206764465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24321092131837472804509643 36481638197756209206764465)
        ·
          refine ⟨27361228648317156905073349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36481638197756209206764465 27361228648317156905073349)
          ·
            refine ⟨5130230371559466919701253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27361228648317156905073349 5130230371559466919701253)
            ·
              refine ⟨961918194667400047443985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5130230371559466919701253 961918194667400047443985)
              ·
                refine ⟨721438646000550035582989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 961918194667400047443985 721438646000550035582989)
                ·
                  refine ⟨270539492250206263343621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 721438646000550035582989 270539492250206263343621)
                  ·
                    rfl

theorem cell21_1185466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 4, 2, 3].length) (baseStart_1185466 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1185466 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1185466 prefixEnd_1185466 := by exact prefixLift 1185466
  have htrace : WordTrace (prefixWord ++ tailWord_1185466) baseStart_1185466 baseEnd_1185466 := by
    simpa [prefixWord, tailWord_1185466, baseEnd_1185466] using wordTrace_append hprefix tailTrace_1185466
  have hstable : (prefixWord ++ tailWord_1185466).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185466).length < 2 ^ (prefixWord ++ tailWord_1185466).sum := by decide
  have hdescent : baseEnd_1185466 < baseStart_1185466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185590 : List Nat := [5, 1, 2, 2, 1, 3, 2, 1, 4]
def baseStart_1185590 : Nat := 118140960795 + 1185590 * 2 ^ 59
def prefixEnd_1185590 : Nat := 4983230072969 + 3 ^ 40 * 1185590 * 2
def baseEnd_1185590 : Nat := 270567790739609603276701

theorem tailTrace_1185590 : CollatzResearch.WordTrace tailWord_1185590 prefixEnd_1185590 270567790739609603276701 := by
  unfold tailWord_1185590
  simp only [CollatzResearch.WordTrace]
  refine ⟨2702626235926086718540139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28828013183211591664428149 2702626235926086718540139)
  ·
    refine ⟨4053939353889130077810209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2702626235926086718540139 4053939353889130077810209)
    ·
      refine ⟨3040454515416847558357657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4053939353889130077810209 3040454515416847558357657)
      ·
        refine ⟨2280340886562635668768243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3040454515416847558357657 2280340886562635668768243)
        ·
          refine ⟨3420511329843953503152365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2280340886562635668768243 3420511329843953503152365)
          ·
            refine ⟨1282691748691482563682137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3420511329843953503152365 1282691748691482563682137)
            ·
              refine ⟨962018811518611922761603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1282691748691482563682137 962018811518611922761603)
              ·
                refine ⟨1443028217277917884142405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 962018811518611922761603 1443028217277917884142405)
                ·
                  refine ⟨270567790739609603276701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1443028217277917884142405 270567790739609603276701)
                  ·
                    rfl

theorem cell21_1185590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 2, 1, 4].length) (baseStart_1185590 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1185590 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1185590 prefixEnd_1185590 := by exact prefixLift 1185590
  have htrace : WordTrace (prefixWord ++ tailWord_1185590) baseStart_1185590 baseEnd_1185590 := by
    simpa [prefixWord, tailWord_1185590, baseEnd_1185590] using wordTrace_append hprefix tailTrace_1185590
  have hstable : (prefixWord ++ tailWord_1185590).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185590).length < 2 ^ (prefixWord ++ tailWord_1185590).sum := by decide
  have hdescent : baseEnd_1185590 < baseStart_1185590 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185635 : List Nat := [1, 1, 1, 5, 4, 2, 2, 2, 3]
def baseStart_1185635 : Nat := 118140960795 + 1185635 * 2 ^ 59
def prefixEnd_1185635 : Nat := 4983230072969 + 3 ^ 40 * 1185635 * 2
def baseEnd_1185635 : Nat := 270578060352699525026609

theorem tailTrace_1185635 : CollatzResearch.WordTrace tailWord_1185635 prefixEnd_1185635 270578060352699525026609 := by
  unfold tailWord_1185635
  simp only [CollatzResearch.WordTrace]
  refine ⟨43243661059654360182030359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28829107373102906788020239 43243661059654360182030359)
  ·
    refine ⟨64865491589481540273045539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43243661059654360182030359 64865491589481540273045539)
    ·
      refine ⟨97298237384222310409568309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64865491589481540273045539 97298237384222310409568309)
      ·
        refine ⟨9121709754770841600897029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 97298237384222310409568309 9121709754770841600897029)
        ·
          refine ⟨1710320579019532800168193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9121709754770841600897029 1710320579019532800168193)
          ·
            refine ⟨1282740434264649600126145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1710320579019532800168193 1282740434264649600126145)
            ·
              refine ⟨962055325698487200094609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1282740434264649600126145 962055325698487200094609)
              ·
                refine ⟨721541494273865400070957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 962055325698487200094609 721541494273865400070957)
                ·
                  refine ⟨270578060352699525026609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 721541494273865400070957 270578060352699525026609)
                  ·
                    rfl

theorem cell21_1185635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 2, 2, 3].length) (baseStart_1185635 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1185635 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1185635 prefixEnd_1185635 := by exact prefixLift 1185635
  have htrace : WordTrace (prefixWord ++ tailWord_1185635) baseStart_1185635 baseEnd_1185635 := by
    simpa [prefixWord, tailWord_1185635, baseEnd_1185635] using wordTrace_append hprefix tailTrace_1185635
  have hstable : (prefixWord ++ tailWord_1185635).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185635).length < 2 ^ (prefixWord ++ tailWord_1185635).sum := by decide
  have hdescent : baseEnd_1185635 < baseStart_1185635 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185643 : List Nat := [1, 1, 1, 1, 2, 2, 3, 5, 5]
def baseStart_1185643 : Nat := 118140960795 + 1185643 * 2 ^ 59
def prefixEnd_1185643 : Nat := 4983230072969 + 3 ^ 40 * 1185643 * 2
def baseEnd_1185643 : Nat := 270579886061693288893259

theorem tailTrace_1185643 : CollatzResearch.WordTrace tailWord_1185643 prefixEnd_1185643 270579886061693288893259 := by
  unfold tailWord_1185643
  simp only [CollatzResearch.WordTrace]
  refine ⟨43243952843625377548321583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28829301895750251698881055 43243952843625377548321583)
  ·
    refine ⟨64865929265438066322482375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43243952843625377548321583 64865929265438066322482375)
    ·
      refine ⟨97298893898157099483723563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64865929265438066322482375 97298893898157099483723563)
      ·
        refine ⟨145948340847235649225585345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97298893898157099483723563 145948340847235649225585345)
        ·
          refine ⟨109461255635426736919189009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 145948340847235649225585345 109461255635426736919189009)
          ·
            refine ⟨82095941726570052689391757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 109461255635426736919189009 82095941726570052689391757)
            ·
              refine ⟨30785978147463769758521909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82095941726570052689391757 30785978147463769758521909)
              ·
                refine ⟨2886185451324728414861429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30785978147463769758521909 2886185451324728414861429)
                ·
                  refine ⟨270579886061693288893259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2886185451324728414861429 270579886061693288893259)
                  ·
                    rfl

theorem cell21_1185643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 5, 5].length) (baseStart_1185643 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1185643 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1185643 prefixEnd_1185643 := by exact prefixLift 1185643
  have htrace : WordTrace (prefixWord ++ tailWord_1185643) baseStart_1185643 baseEnd_1185643 := by
    simpa [prefixWord, tailWord_1185643, baseEnd_1185643] using wordTrace_append hprefix tailTrace_1185643
  have hstable : (prefixWord ++ tailWord_1185643).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185643).length < 2 ^ (prefixWord ++ tailWord_1185643).sum := by decide
  have hdescent : baseEnd_1185643 < baseStart_1185643 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185646 : List Nat := [4, 1, 2, 3, 1, 1, 3, 6]
def baseStart_1185646 : Nat := 118140960795 + 1185646 * 2 ^ 59
def prefixEnd_1185646 : Nat := 4983230072969 + 3 ^ 40 * 1185646 * 2
def baseEnd_1185646 : Nat := 90193523567521983447751

theorem tailTrace_1185646 : CollatzResearch.WordTrace tailWord_1185646 prefixEnd_1185646 90193523567521983447751 := by
  unfold tailWord_1185646
  simp only [CollatzResearch.WordTrace]
  refine ⟨5405507782826813632585099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28829374841743006040453861 5405507782826813632585099)
  ·
    refine ⟨8108261674240220448877649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5405507782826813632585099 8108261674240220448877649)
    ·
      refine ⟨6081196255680165336658237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8108261674240220448877649 6081196255680165336658237)
      ·
        refine ⟨2280448595880062001246839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6081196255680165336658237 2280448595880062001246839)
        ·
          refine ⟨3420672893820093001870259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2280448595880062001246839 3420672893820093001870259)
          ·
            refine ⟨5131009340730139502805389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3420672893820093001870259 5131009340730139502805389)
            ·
              refine ⟨1924128502773802313552021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5131009340730139502805389 1924128502773802313552021)
              ·
                refine ⟨90193523567521983447751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1924128502773802313552021 90193523567521983447751)
                ·
                  rfl

theorem cell21_1185646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 3, 6].length) (baseStart_1185646 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1185646 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1185646 prefixEnd_1185646 := by exact prefixLift 1185646
  have htrace : WordTrace (prefixWord ++ tailWord_1185646) baseStart_1185646 baseEnd_1185646 := by
    simpa [prefixWord, tailWord_1185646, baseEnd_1185646] using wordTrace_append hprefix tailTrace_1185646
  have hstable : (prefixWord ++ tailWord_1185646).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185646).length < 2 ^ (prefixWord ++ tailWord_1185646).sum := by decide
  have hdescent : baseEnd_1185646 < baseStart_1185646 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185753 : List Nat := [1, 2, 1, 2, 6, 2, 1, 1, 5]
def baseStart_1185753 : Nat := 118140960795 + 1185753 * 2 ^ 59
def prefixEnd_1185753 : Nat := 4983230072969 + 3 ^ 40 * 1185753 * 2
def baseEnd_1185753 : Nat := 270604989560357542059701

theorem tailTrace_1185753 : CollatzResearch.WordTrace tailWord_1185753 prefixEnd_1185753 270604989560357542059701 := by
  unfold tailWord_1185753
  simp only [CollatzResearch.WordTrace]
  refine ⟨43247964873226866334825913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28831976582151244223217275 43247964873226866334825913)
  ·
    refine ⟨32435973654920149751119435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43247964873226866334825913 32435973654920149751119435)
    ·
      refine ⟨48653960482380224626679153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32435973654920149751119435 48653960482380224626679153)
      ·
        refine ⟨36490470361785168470009365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48653960482380224626679153 36490470361785168470009365)
        ·
          refine ⟨1710490798208679772031689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 36490470361785168470009365 1710490798208679772031689)
          ·
            refine ⟨1282868098656509829023767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1710490798208679772031689 1282868098656509829023767)
            ·
              refine ⟨1924302147984764743535651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1282868098656509829023767 1924302147984764743535651)
              ·
                refine ⟨2886453221977147115303477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1924302147984764743535651 2886453221977147115303477)
                ·
                  refine ⟨270604989560357542059701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2886453221977147115303477 270604989560357542059701)
                  ·
                    rfl

theorem cell21_1185753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 1, 1, 5].length) (baseStart_1185753 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1185753 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1185753 prefixEnd_1185753 := by exact prefixLift 1185753
  have htrace : WordTrace (prefixWord ++ tailWord_1185753) baseStart_1185753 baseEnd_1185753 := by
    simpa [prefixWord, tailWord_1185753, baseEnd_1185753] using wordTrace_append hprefix tailTrace_1185753
  have hstable : (prefixWord ++ tailWord_1185753).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185753).length < 2 ^ (prefixWord ++ tailWord_1185753).sum := by decide
  have hdescent : baseEnd_1185753 < baseStart_1185753 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185756 : List Nat := [2, 2, 6, 1, 1, 1, 2, 6]
def baseStart_1185756 : Nat := 118140960795 + 1185756 * 2 ^ 59
def prefixEnd_1185756 : Nat := 4983230072969 + 3 ^ 40 * 1185756 * 2
def baseEnd_1185756 : Nat := 90201891400410067836565

theorem tailTrace_1185756 : CollatzResearch.WordTrace tailWord_1185756 prefixEnd_1185756 90201891400410067836565 := by
  unfold tailWord_1185756
  simp only [CollatzResearch.WordTrace]
  refine ⟨21624037146107998923592561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28832049528143998564790081 21624037146107998923592561)
  ·
    refine ⟨16218027859580999192694421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21624037146107998923592561 16218027859580999192694421)
    ·
      refine ⟨760220055917859337157551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 16218027859580999192694421 760220055917859337157551)
      ·
        refine ⟨1140330083876789005736327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 760220055917859337157551 1140330083876789005736327)
        ·
          refine ⟨1710495125815183508604491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1140330083876789005736327 1710495125815183508604491)
          ·
            refine ⟨2565742688722775262906737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1710495125815183508604491 2565742688722775262906737)
            ·
              refine ⟨1924307016542081447180053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2565742688722775262906737 1924307016542081447180053)
              ·
                refine ⟨90201891400410067836565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1924307016542081447180053 90201891400410067836565)
                ·
                  rfl

theorem cell21_1185756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 2, 6].length) (baseStart_1185756 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1185756 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1185756 prefixEnd_1185756 := by exact prefixLift 1185756
  have htrace : WordTrace (prefixWord ++ tailWord_1185756) baseStart_1185756 baseEnd_1185756 := by
    simpa [prefixWord, tailWord_1185756, baseEnd_1185756] using wordTrace_append hprefix tailTrace_1185756
  have hstable : (prefixWord ++ tailWord_1185756).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185756).length < 2 ^ (prefixWord ++ tailWord_1185756).sum := by decide
  have hdescent : baseEnd_1185756 < baseStart_1185756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185815 : List Nat := [1, 1, 3, 5, 3, 1, 1, 6]
def baseStart_1185815 : Nat := 118140960795 + 1185815 * 2 ^ 59
def prefixEnd_1185815 : Nat := 4983230072969 + 3 ^ 40 * 1185815 * 2
def baseEnd_1185815 : Nat := 90206379601686404008747

theorem tailTrace_1185815 : CollatzResearch.WordTrace tailWord_1185815 prefixEnd_1185815 90206379601686404008747 := by
  unfold tailWord_1185815
  simp only [CollatzResearch.WordTrace]
  refine ⟨43250226199002250923582899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28833484132668167282388599 43250226199002250923582899)
  ·
    refine ⟨64875339298503376385374349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43250226199002250923582899 64875339298503376385374349)
    ·
      refine ⟨24328252236938766144515381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 64875339298503376385374349 24328252236938766144515381)
      ·
        refine ⟨2280773647213009326048317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24328252236938766144515381 2280773647213009326048317)
        ·
          refine ⟨855290117704878497268119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2280773647213009326048317 855290117704878497268119)
          ·
            refine ⟨1282935176557317745902179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 855290117704878497268119 1282935176557317745902179)
            ·
              refine ⟨1924402764835976618853269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1282935176557317745902179 1924402764835976618853269)
              ·
                refine ⟨90206379601686404008747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1924402764835976618853269 90206379601686404008747)
                ·
                  rfl

theorem cell21_1185815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 1, 6].length) (baseStart_1185815 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1185815 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1185815 prefixEnd_1185815 := by exact prefixLift 1185815
  have htrace : WordTrace (prefixWord ++ tailWord_1185815) baseStart_1185815 baseEnd_1185815 := by
    simpa [prefixWord, tailWord_1185815, baseEnd_1185815] using wordTrace_append hprefix tailTrace_1185815
  have hstable : (prefixWord ++ tailWord_1185815).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185815).length < 2 ^ (prefixWord ++ tailWord_1185815).sum := by decide
  have hdescent : baseEnd_1185815 < baseStart_1185815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185846 : List Nat := [5, 1, 2, 1, 1, 1, 4, 3, 3]
def baseStart_1185846 : Nat := 118140960795 + 1185846 * 2 ^ 59
def prefixEnd_1185846 : Nat := 4983230072969 + 3 ^ 40 * 1185846 * 2
def baseEnd_1185846 : Nat := 270626213427410047009511

theorem tailTrace_1185846 : CollatzResearch.WordTrace tailWord_1185846 prefixEnd_1185846 270626213427410047009511 := by
  unfold tailWord_1185846
  simp only [CollatzResearch.WordTrace]
  refine ⟨2703209803868121451122587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28834237907926628811974261 2703209803868121451122587)
  ·
    refine ⟨4054814705802182176683881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2703209803868121451122587 4054814705802182176683881)
    ·
      refine ⟨3041111029351636632512911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4054814705802182176683881 3041111029351636632512911)
      ·
        refine ⟨4561666544027454948769367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3041111029351636632512911 4561666544027454948769367)
        ·
          refine ⟨6842499816041182423154051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4561666544027454948769367 6842499816041182423154051)
          ·
            refine ⟨10263749724061773634731077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6842499816041182423154051 10263749724061773634731077)
            ·
              refine ⟨1924453073261582556512077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10263749724061773634731077 1924453073261582556512077)
              ·
                refine ⟨721669902473093458692029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1924453073261582556512077 721669902473093458692029)
                ·
                  refine ⟨270626213427410047009511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 721669902473093458692029 270626213427410047009511)
                  ·
                    rfl

theorem cell21_1185846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 4, 3, 3].length) (baseStart_1185846 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1185846 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1185846 prefixEnd_1185846 := by exact prefixLift 1185846
  have htrace : WordTrace (prefixWord ++ tailWord_1185846) baseStart_1185846 baseEnd_1185846 := by
    simpa [prefixWord, tailWord_1185846, baseEnd_1185846] using wordTrace_append hprefix tailTrace_1185846
  have hstable : (prefixWord ++ tailWord_1185846).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185846).length < 2 ^ (prefixWord ++ tailWord_1185846).sum := by decide
  have hdescent : baseEnd_1185846 < baseStart_1185846 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185857 : List Nat := [1, 2, 5, 1, 2, 2, 8]
def baseStart_1185857 : Nat := 118140960795 + 1185857 * 2 ^ 59
def prefixEnd_1185857 : Nat := 4983230072969 + 3 ^ 40 * 1185857 * 2
def baseEnd_1185857 : Nat := 30069858197475163591795

theorem tailTrace_1185857 : CollatzResearch.WordTrace tailWord_1185857 prefixEnd_1185857 30069858197475163591795 := by
  unfold tailWord_1185857
  simp only [CollatzResearch.WordTrace]
  refine ⟨43251758064850092096611825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28834505376566728064407883 43251758064850092096611825)
  ·
    refine ⟨32438818548637569072458869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43251758064850092096611825 32438818548637569072458869)
    ·
      refine ⟨3041139238934772100543019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 32438818548637569072458869 3041139238934772100543019)
      ·
        refine ⟨4561708858402158150814529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3041139238934772100543019 4561708858402158150814529)
        ·
          refine ⟨3421281643801618613110897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4561708858402158150814529 3421281643801618613110897)
          ·
            refine ⟨2565961232851213959833173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3421281643801618613110897 2565961232851213959833173)
            ·
              refine ⟨30069858197475163591795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2565961232851213959833173 30069858197475163591795)
              ·
                rfl

theorem cell21_1185857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 8].length) (baseStart_1185857 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1185857 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1185857 prefixEnd_1185857 := by exact prefixLift 1185857
  have htrace : WordTrace (prefixWord ++ tailWord_1185857) baseStart_1185857 baseEnd_1185857 := by
    simpa [prefixWord, tailWord_1185857, baseEnd_1185857] using wordTrace_append hprefix tailTrace_1185857
  have hstable : (prefixWord ++ tailWord_1185857).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185857).length < 2 ^ (prefixWord ++ tailWord_1185857).sum := by decide
  have hdescent : baseEnd_1185857 < baseStart_1185857 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185902 : List Nat := [4, 1, 2, 2, 1, 1, 1, 1, 8]
def baseStart_1185902 : Nat := 118140960795 + 1185902 * 2 ^ 59
def prefixEnd_1185902 : Nat := 4983230072969 + 3 ^ 40 * 1185902 * 2
def baseEnd_1185902 : Nat := 270638993390366394076063

theorem tailTrace_1185902 : CollatzResearch.WordTrace tailWord_1185902 prefixEnd_1185902 270638993390366394076063 := by
  unfold tailWord_1185902
  simp only [CollatzResearch.WordTrace]
  refine ⟨5406674918710883097749995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28835599566458043187999973 5406674918710883097749995)
  ·
    refine ⟨8110012378066324646624993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5406674918710883097749995 8110012378066324646624993)
    ·
      refine ⟨6082509283549743484968745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8110012378066324646624993 6082509283549743484968745)
      ·
        refine ⟨4561881962662307613726559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6082509283549743484968745 4561881962662307613726559)
        ·
          refine ⟨6842822943993461420589839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4561881962662307613726559 6842822943993461420589839)
          ·
            refine ⟨10264234415990192130884759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6842822943993461420589839 10264234415990192130884759)
            ·
              refine ⟨15396351623985288196327139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10264234415990192130884759 15396351623985288196327139)
              ·
                refine ⟨23094527435977932294490709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15396351623985288196327139 23094527435977932294490709)
                ·
                  refine ⟨270638993390366394076063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23094527435977932294490709 270638993390366394076063)
                  ·
                    rfl

theorem cell21_1185902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 8].length) (baseStart_1185902 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1185902 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1185902 prefixEnd_1185902 := by exact prefixLift 1185902
  have htrace : WordTrace (prefixWord ++ tailWord_1185902) baseStart_1185902 baseEnd_1185902 := by
    simpa [prefixWord, tailWord_1185902, baseEnd_1185902] using wordTrace_append hprefix tailTrace_1185902
  have hstable : (prefixWord ++ tailWord_1185902).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185902).length < 2 ^ (prefixWord ++ tailWord_1185902).sum := by decide
  have hdescent : baseEnd_1185902 < baseStart_1185902 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185916 : List Nat := [2, 2, 2, 1, 1, 4, 9]
def baseStart_1185916 : Nat := 118140960795 + 1185916 * 2 ^ 59
def prefixEnd_1185916 : Nat := 4983230072969 + 3 ^ 40 * 1185916 * 2
def baseEnd_1185916 : Nat := 30071354264567275649189

theorem tailTrace_1185916 : CollatzResearch.WordTrace tailWord_1185916 prefixEnd_1185916 30071354264567275649189 := by
  unfold tailWord_1185916
  simp only [CollatzResearch.WordTrace]
  refine ⟨21626954985818172586504801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28835939981090896782006401 21626954985818172586504801)
  ·
    refine ⟨16220216239363629439878601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21626954985818172586504801 16220216239363629439878601)
    ·
      refine ⟨12165162179522722079908951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16220216239363629439878601 12165162179522722079908951)
      ·
        refine ⟨18247743269284083119863427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12165162179522722079908951 18247743269284083119863427)
        ·
          refine ⟨27371614903926124679795141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18247743269284083119863427 27371614903926124679795141)
          ·
            refine ⟨5132177794486148377461589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27371614903926124679795141 5132177794486148377461589)
            ·
              refine ⟨30071354264567275649189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5132177794486148377461589 30071354264567275649189)
              ·
                rfl

theorem cell21_1185916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 9].length) (baseStart_1185916 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1185916 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1185916 prefixEnd_1185916 := by exact prefixLift 1185916
  have htrace : WordTrace (prefixWord ++ tailWord_1185916) baseStart_1185916 baseEnd_1185916 := by
    simpa [prefixWord, tailWord_1185916, baseEnd_1185916] using wordTrace_append hprefix tailTrace_1185916
  have hstable : (prefixWord ++ tailWord_1185916).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185916).length < 2 ^ (prefixWord ++ tailWord_1185916).sum := by decide
  have hdescent : baseEnd_1185916 < baseStart_1185916 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1185978 : List Nat := [3, 1, 1, 1, 2, 2, 3, 4, 4]
def baseStart_1185978 : Nat := 118140960795 + 1185978 * 2 ^ 59
def prefixEnd_1185978 : Nat := 4983230072969 + 3 ^ 40 * 1185978 * 2
def baseEnd_1185978 : Nat := 270656337625807150809241

theorem tailTrace_1185978 : CollatzResearch.WordTrace tailWord_1185978 prefixEnd_1185978 270656337625807150809241 := by
  unfold tailWord_1185978
  simp only [CollatzResearch.WordTrace]
  refine ⟨10814042824352932440441647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28837447531607819841177725 10814042824352932440441647)
  ·
    refine ⟨16221064236529398660662471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10814042824352932440441647 16221064236529398660662471)
    ·
      refine ⟨24331596354794097990993707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16221064236529398660662471 24331596354794097990993707)
      ·
        refine ⟨36497394532191146986490561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24331596354794097990993707 36497394532191146986490561)
        ·
          refine ⟨27373045899143360239867921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36497394532191146986490561 27373045899143360239867921)
          ·
            refine ⟨20529784424357520179900941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27373045899143360239867921 20529784424357520179900941)
            ·
              refine ⟨7698669159134070067462853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20529784424357520179900941 7698669159134070067462853)
              ·
                refine ⟨1443500467337638137649285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7698669159134070067462853 1443500467337638137649285)
                ·
                  refine ⟨270656337625807150809241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1443500467337638137649285 270656337625807150809241)
                  ·
                    rfl

theorem cell21_1185978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 4, 4].length) (baseStart_1185978 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1185978 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1185978 prefixEnd_1185978 := by exact prefixLift 1185978
  have htrace : WordTrace (prefixWord ++ tailWord_1185978) baseStart_1185978 baseEnd_1185978 := by
    simpa [prefixWord, tailWord_1185978, baseEnd_1185978] using wordTrace_append hprefix tailTrace_1185978
  have hstable : (prefixWord ++ tailWord_1185978).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1185978).length < 2 ^ (prefixWord ++ tailWord_1185978).sum := by decide
  have hdescent : baseEnd_1185978 < baseStart_1185978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1185978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1186029 : List Nat := [1, 5, 1, 2, 4, 1, 1, 2, 4]
def baseStart_1186029 : Nat := 118140960795 + 1186029 * 2 ^ 59
def prefixEnd_1186029 : Nat := 4983230072969 + 3 ^ 40 * 1186029 * 2
def baseEnd_1186029 : Nat := 270667976520642395459137

theorem tailTrace_1186029 : CollatzResearch.WordTrace tailWord_1186029 prefixEnd_1186029 270667976520642395459137 := by
  unfold tailWord_1186029
  simp only [CollatzResearch.WordTrace]
  refine ⟨43258031420226965471873141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28838687613484643647915427 43258031420226965471873141)
  ·
    refine ⟨4055440445646278012988107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 43258031420226965471873141 4055440445646278012988107)
    ·
      refine ⟨6083160668469417019482161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4055440445646278012988107 6083160668469417019482161)
      ·
        refine ⟨4562370501352062764611621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6083160668469417019482161 4562370501352062764611621)
        ·
          refine ⟨855444469003511768364679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4562370501352062764611621 855444469003511768364679)
          ·
            refine ⟨1283166703505267652547019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 855444469003511768364679 1283166703505267652547019)
            ·
              refine ⟨1924750055257901478820529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1283166703505267652547019 1924750055257901478820529)
              ·
                refine ⟨1443562541443426109115397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1924750055257901478820529 1443562541443426109115397)
                ·
                  refine ⟨270667976520642395459137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1443562541443426109115397 270667976520642395459137)
                  ·
                    rfl

theorem cell21_1186029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 1, 2, 4].length) (baseStart_1186029 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1186029 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1186029 prefixEnd_1186029 := by exact prefixLift 1186029
  have htrace : WordTrace (prefixWord ++ tailWord_1186029) baseStart_1186029 baseEnd_1186029 := by
    simpa [prefixWord, tailWord_1186029, baseEnd_1186029] using wordTrace_append hprefix tailTrace_1186029
  have hstable : (prefixWord ++ tailWord_1186029).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1186029).length < 2 ^ (prefixWord ++ tailWord_1186029).sum := by decide
  have hdescent : baseEnd_1186029 < baseStart_1186029 := by decide
  rcases family_descends (prefixWord ++ tailWord_1186029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1186074 : List Nat := [3, 1, 1, 3, 4, 2, 1, 3, 3]
def baseStart_1186074 : Nat := 118140960795 + 1186074 * 2 ^ 59
def prefixEnd_1186074 : Nat := 4983230072969 + 3 ^ 40 * 1186074 * 2
def baseEnd_1186074 : Nat := 270678246133732317209045

theorem tailTrace_1186074 : CollatzResearch.WordTrace tailWord_1186074 prefixEnd_1186074 270678246133732317209045 := by
  unfold tailWord_1186074
  simp only [CollatzResearch.WordTrace]
  refine ⟨10814918176265984539315319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28839781803375958771507517 10814918176265984539315319)
  ·
    refine ⟨16222377264398976808972979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10814918176265984539315319 16222377264398976808972979)
    ·
      refine ⟨24333565896598465213459469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16222377264398976808972979 24333565896598465213459469)
      ·
        refine ⟨9125087211224424455047301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24333565896598465213459469 9125087211224424455047301)
        ·
          refine ⟨1710953852104579585321369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9125087211224424455047301 1710953852104579585321369)
          ·
            refine ⟨1283215389078434688991027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1710953852104579585321369 1283215389078434688991027)
            ·
              refine ⟨1924823083617652033486541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1283215389078434688991027 1924823083617652033486541)
              ·
                refine ⟨721808656356619512557453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1924823083617652033486541 721808656356619512557453)
                ·
                  refine ⟨270678246133732317209045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 721808656356619512557453 270678246133732317209045)
                  ·
                    rfl

theorem cell21_1186074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 1, 3, 3].length) (baseStart_1186074 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1186074 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1186074 prefixEnd_1186074 := by exact prefixLift 1186074
  have htrace : WordTrace (prefixWord ++ tailWord_1186074) baseStart_1186074 baseEnd_1186074 := by
    simpa [prefixWord, tailWord_1186074, baseEnd_1186074] using wordTrace_append hprefix tailTrace_1186074
  have hstable : (prefixWord ++ tailWord_1186074).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1186074).length < 2 ^ (prefixWord ++ tailWord_1186074).sum := by decide
  have hdescent : baseEnd_1186074 < baseStart_1186074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1186074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1186085 : List Nat := [1, 3, 1, 2, 5, 2, 7]
def baseStart_1186085 : Nat := 118140960795 + 1186085 * 2 ^ 59
def prefixEnd_1186085 : Nat := 4983230072969 + 3 ^ 40 * 1186085 * 2
def baseEnd_1186085 : Nat := 30075639609288749169521

theorem tailTrace_1186085 : CollatzResearch.WordTrace tailWord_1186085 prefixEnd_1186085 30075639609288749169521 := by
  unfold tailWord_1186085
  simp only [CollatzResearch.WordTrace]
  refine ⟨43260073908024087035911709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28840049272016058023941139 43260073908024087035911709)
  ·
    refine ⟨16222527715509032638466891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43260073908024087035911709 16222527715509032638466891)
    ·
      refine ⟨24333791573263548957700337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16222527715509032638466891 24333791573263548957700337)
      ·
        refine ⟨18250343679947661718275253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24333791573263548957700337 18250343679947661718275253)
        ·
          refine ⟨1710969719995093286088305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18250343679947661718275253 1710969719995093286088305)
          ·
            refine ⟨1283227289996319964566229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1710969719995093286088305 1283227289996319964566229)
            ·
              refine ⟨30075639609288749169521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1283227289996319964566229 30075639609288749169521)
              ·
                rfl

theorem cell21_1186085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 7].length) (baseStart_1186085 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1186085 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1186085 prefixEnd_1186085 := by exact prefixLift 1186085
  have htrace : WordTrace (prefixWord ++ tailWord_1186085) baseStart_1186085 baseEnd_1186085 := by
    simpa [prefixWord, tailWord_1186085, baseEnd_1186085] using wordTrace_append hprefix tailTrace_1186085
  have hstable : (prefixWord ++ tailWord_1186085).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1186085).length < 2 ^ (prefixWord ++ tailWord_1186085).sum := by decide
  have hdescent : baseEnd_1186085 < baseStart_1186085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1186085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1186142 : List Nat := [4, 4, 2, 1, 1, 2, 2, 2, 3]
def baseStart_1186142 : Nat := 118140960795 + 1186142 * 2 ^ 59
def prefixEnd_1186142 : Nat := 4983230072969 + 3 ^ 40 * 1186142 * 2
def baseEnd_1186142 : Nat := 270693764660179310075573

theorem tailTrace_1186142 : CollatzResearch.WordTrace tailWord_1186142 prefixEnd_1186142 270693764660179310075573 := by
  unfold tailWord_1186142
  simp only [CollatzResearch.WordTrace]
  refine ⟨5407769108602198221342085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28841435245878390513824453 5407769108602198221342085)
  ·
    refine ⟨1013956707862912166501641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5407769108602198221342085 1013956707862912166501641)
    ·
      refine ⟨760467530897184124876231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1013956707862912166501641 760467530897184124876231)
      ·
        refine ⟨1140701296345776187314347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 760467530897184124876231 1140701296345776187314347)
        ·
          refine ⟨1711051944518664280971521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1140701296345776187314347 1711051944518664280971521)
          ·
            refine ⟨1283288958388998210728641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1711051944518664280971521 1283288958388998210728641)
            ·
              refine ⟨962466718791748658046481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1283288958388998210728641 962466718791748658046481)
              ·
                refine ⟨721850039093811493534861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 962466718791748658046481 721850039093811493534861)
                ·
                  refine ⟨270693764660179310075573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 721850039093811493534861 270693764660179310075573)
                  ·
                    rfl

theorem cell21_1186142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_1186142 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1186142 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1186142 prefixEnd_1186142 := by exact prefixLift 1186142
  have htrace : WordTrace (prefixWord ++ tailWord_1186142) baseStart_1186142 baseEnd_1186142 := by
    simpa [prefixWord, tailWord_1186142, baseEnd_1186142] using wordTrace_append hprefix tailTrace_1186142
  have hstable : (prefixWord ++ tailWord_1186142).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1186142).length < 2 ^ (prefixWord ++ tailWord_1186142).sum := by decide
  have hdescent : baseEnd_1186142 < baseStart_1186142 := by decide
  rcases family_descends (prefixWord ++ tailWord_1186142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1186144 : List Nat := [2, 1, 1, 3, 5, 9]
def baseStart_1186144 : Nat := 118140960795 + 1186144 * 2 ^ 59
def prefixEnd_1186144 : Nat := 4983230072969 + 3 ^ 40 * 1186144 * 2
def baseEnd_1186144 : Nat := 10025711892126953742305

theorem tailTrace_1186144 : CollatzResearch.WordTrace tailWord_1186144 prefixEnd_1186144 10025711892126953742305 := by
  unfold tailWord_1186144
  simp only [CollatzResearch.WordTrace]
  refine ⟨21631112907405170056154743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28841483876540226741539657 21631112907405170056154743)
  ·
    refine ⟨32446669361107755084232115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21631112907405170056154743 32446669361107755084232115)
    ·
      refine ⟨48670004041661632626348173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32446669361107755084232115 48670004041661632626348173)
      ·
        refine ⟨18251251515623112234880565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48670004041661632626348173 18251251515623112234880565)
        ·
          refine ⟨1711054829589666772020053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18251251515623112234880565 1711054829589666772020053)
          ·
            refine ⟨10025711892126953742305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1711054829589666772020053 10025711892126953742305)
            ·
              rfl

theorem cell21_1186144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 9].length) (baseStart_1186144 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1186144 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1186144 prefixEnd_1186144 := by exact prefixLift 1186144
  have htrace : WordTrace (prefixWord ++ tailWord_1186144) baseStart_1186144 baseEnd_1186144 := by
    simpa [prefixWord, tailWord_1186144, baseEnd_1186144] using wordTrace_append hprefix tailTrace_1186144
  have hstable : (prefixWord ++ tailWord_1186144).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1186144).length < 2 ^ (prefixWord ++ tailWord_1186144).sum := by decide
  have hdescent : baseEnd_1186144 < baseStart_1186144 := by decide
  rcases family_descends (prefixWord ++ tailWord_1186144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1186209 : List Nat := [1, 2, 3, 5, 1, 1, 2, 1, 5]
def baseStart_1186209 : Nat := 118140960795 + 1186209 * 2 ^ 59
def prefixEnd_1186209 : Nat := 4983230072969 + 3 ^ 40 * 1186209 * 2
def baseEnd_1186209 : Nat := 270709054973002082458769

theorem tailTrace_1186209 : CollatzResearch.WordTrace tailWord_1186209 prefixEnd_1186209 270709054973002082458769 := by
  unfold tailWord_1186209
  simp only [CollatzResearch.WordTrace]
  refine ⟨43264596559574856213425681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28843064373049904142283787 43264596559574856213425681)
  ·
    refine ⟨32448447419681142160069261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43264596559574856213425681 32448447419681142160069261)
    ·
      refine ⟨12168167782380428310025973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32448447419681142160069261 12168167782380428310025973)
      ·
        refine ⟨1140765729598165154064935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12168167782380428310025973 1140765729598165154064935)
        ·
          refine ⟨1711148594397247731097403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1140765729598165154064935 1711148594397247731097403)
          ·
            refine ⟨2566722891595871596646105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1711148594397247731097403 2566722891595871596646105)
            ·
              refine ⟨1925042168696903697484579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2566722891595871596646105 1925042168696903697484579)
              ·
                refine ⟨2887563253045355546226869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1925042168696903697484579 2887563253045355546226869)
                ·
                  refine ⟨270709054973002082458769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2887563253045355546226869 270709054973002082458769)
                  ·
                    rfl

theorem cell21_1186209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 2, 1, 5].length) (baseStart_1186209 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1186209 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1186209 prefixEnd_1186209 := by exact prefixLift 1186209
  have htrace : WordTrace (prefixWord ++ tailWord_1186209) baseStart_1186209 baseEnd_1186209 := by
    simpa [prefixWord, tailWord_1186209, baseEnd_1186209] using wordTrace_append hprefix tailTrace_1186209
  have hstable : (prefixWord ++ tailWord_1186209).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1186209).length < 2 ^ (prefixWord ++ tailWord_1186209).sum := by decide
  have hdescent : baseEnd_1186209 < baseStart_1186209 := by decide
  rcases family_descends (prefixWord ++ tailWord_1186209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1186237 : List Nat := [1, 4, 1, 2, 2, 2, 4, 5]
def baseStart_1186237 : Nat := 118140960795 + 1186237 * 2 ^ 59
def prefixEnd_1186237 : Nat := 4983230072969 + 3 ^ 40 * 1186237 * 2
def baseEnd_1186237 : Nat := 90238481651493418664015

theorem tailTrace_1186237 : CollatzResearch.WordTrace tailWord_1186237 prefixEnd_1186237 90238481651493418664015 := by
  unfold tailWord_1186237
  simp only [CollatzResearch.WordTrace]
  refine ⟨43265617803473416995444965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28843745202315611330296643 43265617803473416995444965)
  ·
    refine ⟨8112303338151265686645931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43265617803473416995444965 8112303338151265686645931)
    ·
      refine ⟨12168455007226898529968897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8112303338151265686645931 12168455007226898529968897)
      ·
        refine ⟨9126341255420173897476673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12168455007226898529968897 9126341255420173897476673)
        ·
          refine ⟨6844755941565130423107505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9126341255420173897476673 6844755941565130423107505)
          ·
            refine ⟨5133566956173847817330629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6844755941565130423107505 5133566956173847817330629)
            ·
              refine ⟨962543804282596465749493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5133566956173847817330629 962543804282596465749493)
              ·
                refine ⟨90238481651493418664015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 962543804282596465749493 90238481651493418664015)
                ·
                  rfl

theorem cell21_1186237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 4, 5].length) (baseStart_1186237 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1186237 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1186237 prefixEnd_1186237 := by exact prefixLift 1186237
  have htrace : WordTrace (prefixWord ++ tailWord_1186237) baseStart_1186237 baseEnd_1186237 := by
    simpa [prefixWord, tailWord_1186237, baseEnd_1186237] using wordTrace_append hprefix tailTrace_1186237
  have hstable : (prefixWord ++ tailWord_1186237).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1186237).length < 2 ^ (prefixWord ++ tailWord_1186237).sum := by decide
  have hdescent : baseEnd_1186237 < baseStart_1186237 := by decide
  rcases family_descends (prefixWord ++ tailWord_1186237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1186265 : List Nat := [1, 2, 1, 2, 4, 1, 1, 3, 6]
def baseStart_1186265 : Nat := 118140960795 + 1186265 * 2 ^ 59
def prefixEnd_1186265 : Nat := 4983230072969 + 3 ^ 40 * 1186265 * 2
def baseEnd_1186265 : Nat := 270721834935958429525321

theorem tailTrace_1186265 : CollatzResearch.WordTrace tailWord_1186265 prefixEnd_1186265 270721834935958429525321 := by
  unfold tailWord_1186265
  simp only [CollatzResearch.WordTrace]
  refine ⟨43266639047371977777464249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28844426031581318518309499 43266639047371977777464249)
  ·
    refine ⟨32449979285528983333098187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43266639047371977777464249 32449979285528983333098187)
    ·
      refine ⟨48674968928293474999647281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32449979285528983333098187 48674968928293474999647281)
      ·
        refine ⟨36506226696220106249735461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48674968928293474999647281 36506226696220106249735461)
        ·
          refine ⟨6844917505541269921825399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36506226696220106249735461 6844917505541269921825399)
          ·
            refine ⟨10267376258311904882738099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6844917505541269921825399 10267376258311904882738099)
            ·
              refine ⟨15401064387467857324107149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10267376258311904882738099 15401064387467857324107149)
              ·
                refine ⟨5775399145300446496540181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15401064387467857324107149 5775399145300446496540181)
                ·
                  refine ⟨270721834935958429525321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5775399145300446496540181 270721834935958429525321)
                  ·
                    rfl

theorem cell21_1186265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 3, 6].length) (baseStart_1186265 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1186265 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1186265 prefixEnd_1186265 := by exact prefixLift 1186265
  have htrace : WordTrace (prefixWord ++ tailWord_1186265) baseStart_1186265 baseEnd_1186265 := by
    simpa [prefixWord, tailWord_1186265, baseEnd_1186265] using wordTrace_append hprefix tailTrace_1186265
  have hstable : (prefixWord ++ tailWord_1186265).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1186265).length < 2 ^ (prefixWord ++ tailWord_1186265).sum := by decide
  have hdescent : baseEnd_1186265 < baseStart_1186265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1186265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1186274 : List Nat := [3, 3, 3, 2, 1, 2, 2, 1, 4]
def baseStart_1186274 : Nat := 118140960795 + 1186274 * 2 ^ 59
def prefixEnd_1186274 : Nat := 4983230072969 + 3 ^ 40 * 1186274 * 2
def baseEnd_1186274 : Nat := 270723888858576413875303

theorem tailTrace_1186274 : CollatzResearch.WordTrace tailWord_1186274 prefixEnd_1186274 270723888858576413875303 := by
  unfold tailWord_1186274
  simp only [CollatzResearch.WordTrace]
  refine ⟨10816741826084843078635469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28844644869559581543027917 10816741826084843078635469)
  ·
    refine ⟨4056278184781816154488301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10816741826084843078635469 4056278184781816154488301)
    ·
      refine ⟨1521104319293181057933113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4056278184781816154488301 1521104319293181057933113)
      ·
        refine ⟨1140828239469885793449835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1521104319293181057933113 1140828239469885793449835)
        ·
          refine ⟨1711242359204828690174753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1140828239469885793449835 1711242359204828690174753)
          ·
            refine ⟨1283431769403621517631065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1711242359204828690174753 1283431769403621517631065)
            ·
              refine ⟨962573827052716138223299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1283431769403621517631065 962573827052716138223299)
              ·
                refine ⟨1443860740579074207334949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 962573827052716138223299 1443860740579074207334949)
                ·
                  refine ⟨270723888858576413875303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1443860740579074207334949 270723888858576413875303)
                  ·
                    rfl

theorem cell21_1186274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 2, 1, 4].length) (baseStart_1186274 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1186274 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1186274 prefixEnd_1186274 := by exact prefixLift 1186274
  have htrace : WordTrace (prefixWord ++ tailWord_1186274) baseStart_1186274 baseEnd_1186274 := by
    simpa [prefixWord, tailWord_1186274, baseEnd_1186274] using wordTrace_append hprefix tailTrace_1186274
  have hstable : (prefixWord ++ tailWord_1186274).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1186274).length < 2 ^ (prefixWord ++ tailWord_1186274).sum := by decide
  have hdescent : baseEnd_1186274 < baseStart_1186274 := by decide
  rcases family_descends (prefixWord ++ tailWord_1186274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1186344 : List Nat := [2, 1, 5, 2, 1, 2, 1, 2, 5]
def baseStart_1186344 : Nat := 118140960795 + 1186344 * 2 ^ 59
def prefixEnd_1186344 : Nat := 4983230072969 + 3 ^ 40 * 1186344 * 2
def baseEnd_1186344 : Nat := 270739863812271847708493

theorem tailTrace_1186344 : CollatzResearch.WordTrace tailWord_1186344 prefixEnd_1186344 270739863812271847708493 := by
  unfold tailWord_1186344
  simp only [CollatzResearch.WordTrace]
  refine ⟨21634760207042887134795043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28846346942723849513060057 21634760207042887134795043)
  ·
    refine ⟨32452140310564330702192565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21634760207042887134795043 32452140310564330702192565)
    ·
      refine ⟨3042388154115406003330553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 32452140310564330702192565 3042388154115406003330553)
      ·
        refine ⟨2281791115586554502497915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3042388154115406003330553 2281791115586554502497915)
        ·
          refine ⟨3422686673379831753746873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2281791115586554502497915 3422686673379831753746873)
          ·
            refine ⟨2567015005034873815310155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3422686673379831753746873 2567015005034873815310155)
            ·
              refine ⟨3850522507552310722965233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2567015005034873815310155 3850522507552310722965233)
              ·
                refine ⟨2887891880664233042223925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3850522507552310722965233 2887891880664233042223925)
                ·
                  refine ⟨270739863812271847708493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2887891880664233042223925 270739863812271847708493)
                  ·
                    rfl

theorem cell21_1186344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 2, 5].length) (baseStart_1186344 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1186344 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1186344 prefixEnd_1186344 := by exact prefixLift 1186344
  have htrace : WordTrace (prefixWord ++ tailWord_1186344) baseStart_1186344 baseEnd_1186344 := by
    simpa [prefixWord, tailWord_1186344, baseEnd_1186344] using wordTrace_append hprefix tailTrace_1186344
  have hstable : (prefixWord ++ tailWord_1186344).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1186344).length < 2 ^ (prefixWord ++ tailWord_1186344).sum := by decide
  have hdescent : baseEnd_1186344 < baseStart_1186344 := by decide
  rcases family_descends (prefixWord ++ tailWord_1186344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1186375 : List Nat := [1, 1, 4, 1, 4, 3, 1, 2, 4]
def baseStart_1186375 : Nat := 118140960795 + 1186375 * 2 ^ 59
def prefixEnd_1186375 : Nat := 4983230072969 + 3 ^ 40 * 1186375 * 2
def baseEnd_1186375 : Nat := 270746938434622682691763

theorem tailTrace_1186375 : CollatzResearch.WordTrace tailWord_1186375 prefixEnd_1186375 270746938434622682691763 := by
  unfold tailWord_1186375
  simp only [CollatzResearch.WordTrace]
  refine ⟨43270651076973466563968579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28847100717982311042645719 43270651076973466563968579)
  ·
    refine ⟨64905976615460199845952869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43270651076973466563968579 64905976615460199845952869)
    ·
      refine ⟨12169870615398787471116163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64905976615460199845952869 12169870615398787471116163)
      ·
        refine ⟨18254805923098181206674245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12169870615398787471116163 18254805923098181206674245)
        ·
          refine ⟨3422776110580908976251421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18254805923098181206674245 3422776110580908976251421)
          ·
            refine ⟨1283541041467840866094283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3422776110580908976251421 1283541041467840866094283)
            ·
              refine ⟨1925311562201761299141425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1283541041467840866094283 1925311562201761299141425)
              ·
                refine ⟨1443983671651320974356069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1925311562201761299141425 1443983671651320974356069)
                ·
                  refine ⟨270746938434622682691763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1443983671651320974356069 270746938434622682691763)
                  ·
                    rfl

theorem cell21_1186375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 1, 2, 4].length) (baseStart_1186375 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1186375 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1186375 prefixEnd_1186375 := by exact prefixLift 1186375
  have htrace : WordTrace (prefixWord ++ tailWord_1186375) baseStart_1186375 baseEnd_1186375 := by
    simpa [prefixWord, tailWord_1186375, baseEnd_1186375] using wordTrace_append hprefix tailTrace_1186375
  have hstable : (prefixWord ++ tailWord_1186375).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1186375).length < 2 ^ (prefixWord ++ tailWord_1186375).sum := by decide
  have hdescent : baseEnd_1186375 < baseStart_1186375 := by decide
  rcases family_descends (prefixWord ++ tailWord_1186375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1186437 : List Nat := [1, 3, 1, 1, 4, 3, 3, 2, 3]
def baseStart_1186437 : Nat := 118140960795 + 1186437 * 2 ^ 59
def prefixEnd_1186437 : Nat := 4983230072969 + 3 ^ 40 * 1186437 * 2
def baseEnd_1186437 : Nat := 270761087679324352658303

theorem tailTrace_1186437 : CollatzResearch.WordTrace tailWord_1186437 prefixEnd_1186437 270761087679324352658303 := by
  unfold tailWord_1186437
  simp only [CollatzResearch.WordTrace]
  refine ⟨43272912402748851152725565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28848608268499234101817043 43272912402748851152725565)
  ·
    refine ⟨16227342151030819182272087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43272912402748851152725565 16227342151030819182272087)
    ·
      refine ⟨24341013226546228773408131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16227342151030819182272087 24341013226546228773408131)
      ·
        refine ⟨36511519839819343160112197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24341013226546228773408131 36511519839819343160112197)
        ·
          refine ⟨6845909969966126842521037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36511519839819343160112197 6845909969966126842521037)
          ·
            refine ⟨2567216238737297565945389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6845909969966126842521037 2567216238737297565945389)
            ·
              refine ⟨962706089526486587229521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2567216238737297565945389 962706089526486587229521)
              ·
                refine ⟨722029567144864940422141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 962706089526486587229521 722029567144864940422141)
                ·
                  refine ⟨270761087679324352658303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 722029567144864940422141 270761087679324352658303)
                  ·
                    rfl

theorem cell21_1186437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 3, 2, 3].length) (baseStart_1186437 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1186437 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1186437 prefixEnd_1186437 := by exact prefixLift 1186437
  have htrace : WordTrace (prefixWord ++ tailWord_1186437) baseStart_1186437 baseEnd_1186437 := by
    simpa [prefixWord, tailWord_1186437, baseEnd_1186437] using wordTrace_append hprefix tailTrace_1186437
  have hstable : (prefixWord ++ tailWord_1186437).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1186437).length < 2 ^ (prefixWord ++ tailWord_1186437).sum := by decide
  have hdescent : baseEnd_1186437 < baseStart_1186437 := by decide
  rcases family_descends (prefixWord ++ tailWord_1186437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1186496 : List Nat := [2, 1, 1, 2, 4, 3, 1, 4, 3]
def baseStart_1186496 : Nat := 118140960795 + 1186496 * 2 ^ 59
def prefixEnd_1186496 : Nat := 4983230072969 + 3 ^ 40 * 1186496 * 2
def baseEnd_1186496 : Nat := 270774552283153361174849

theorem tailTrace_1186496 : CollatzResearch.WordTrace tailWord_1186496 prefixEnd_1186496 270774552283153361174849 := by
  unfold tailWord_1186496
  simp only [CollatzResearch.WordTrace]
  refine ⟨21637532154767552114561671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28850042873023402819415561 21637532154767552114561671)
  ·
    refine ⟨32456298232151328171842507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21637532154767552114561671 32456298232151328171842507)
    ·
      refine ⟨48684447348226992257763761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32456298232151328171842507 48684447348226992257763761)
      ·
        refine ⟨36513335511170244193322821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48684447348226992257763761 36513335511170244193322821)
        ·
          refine ⟨6846250408344420786248029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36513335511170244193322821 6846250408344420786248029)
          ·
            refine ⟨2567343903129157794843011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6846250408344420786248029 2567343903129157794843011)
            ·
              refine ⟨3851015854693736692264517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2567343903129157794843011 3851015854693736692264517)
              ·
                refine ⟨722065472755075629799597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3851015854693736692264517 722065472755075629799597)
                ·
                  refine ⟨270774552283153361174849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 722065472755075629799597 270774552283153361174849)
                  ·
                    rfl

theorem cell21_1186496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 1, 4, 3].length) (baseStart_1186496 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1186496 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1186496 prefixEnd_1186496 := by exact prefixLift 1186496
  have htrace : WordTrace (prefixWord ++ tailWord_1186496) baseStart_1186496 baseEnd_1186496 := by
    simpa [prefixWord, tailWord_1186496, baseEnd_1186496] using wordTrace_append hprefix tailTrace_1186496
  have hstable : (prefixWord ++ tailWord_1186496).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1186496).length < 2 ^ (prefixWord ++ tailWord_1186496).sum := by decide
  have hdescent : baseEnd_1186496 < baseStart_1186496 := by decide
  rcases family_descends (prefixWord ++ tailWord_1186496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1186510 : List Nat := [4, 1, 1, 1, 3, 2, 2, 3, 4]
def baseStart_1186510 : Nat := 118140960795 + 1186510 * 2 ^ 59
def prefixEnd_1186510 : Nat := 4983230072969 + 3 ^ 40 * 1186510 * 2
def baseEnd_1186510 : Nat := 270777747273892447941487

theorem tailTrace_1186510 : CollatzResearch.WordTrace tailWord_1186510 prefixEnd_1186510 270777747273892447941487 := by
  unfold tailWord_1186510
  simp only [CollatzResearch.WordTrace]
  refine ⟨5409446866435548077516623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28850383287656256413421989 5409446866435548077516623)
  ·
    refine ⟨8114170299653322116274935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5409446866435548077516623 8114170299653322116274935)
    ·
      refine ⟨12171255449479983174412403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8114170299653322116274935 12171255449479983174412403)
      ·
        refine ⟨18256883174219974761618605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12171255449479983174412403 18256883174219974761618605)
        ·
          refine ⟨6846331190332490535606977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18256883174219974761618605 6846331190332490535606977)
          ·
            refine ⟨5134748392749367901705233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6846331190332490535606977 5134748392749367901705233)
            ·
              refine ⟨3851061294562025926278925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5134748392749367901705233 3851061294562025926278925)
              ·
                refine ⟨1444147985460759722354597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3851061294562025926278925 1444147985460759722354597)
                ·
                  refine ⟨270777747273892447941487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1444147985460759722354597 270777747273892447941487)
                  ·
                    rfl

theorem cell21_1186510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 3, 4].length) (baseStart_1186510 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1186510 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1186510 prefixEnd_1186510 := by exact prefixLift 1186510
  have htrace : WordTrace (prefixWord ++ tailWord_1186510) baseStart_1186510 baseEnd_1186510 := by
    simpa [prefixWord, tailWord_1186510, baseEnd_1186510] using wordTrace_append hprefix tailTrace_1186510
  have hstable : (prefixWord ++ tailWord_1186510).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1186510).length < 2 ^ (prefixWord ++ tailWord_1186510).sum := by decide
  have hdescent : baseEnd_1186510 < baseStart_1186510 := by decide
  rcases family_descends (prefixWord ++ tailWord_1186510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1186538 : List Nat := [3, 1, 3, 1, 1, 1, 1, 1, 9]
def baseStart_1186538 : Nat := 118140960795 + 1186538 * 2 ^ 59
def prefixEnd_1186538 : Nat := 4983230072969 + 3 ^ 40 * 1186538 * 2
def baseEnd_1186538 : Nat := 270784137255370621474763

theorem tailTrace_1186538 : CollatzResearch.WordTrace tailWord_1186538 prefixEnd_1186538 270784137255370621474763 := by
  unfold tailWord_1186538
  simp only [CollatzResearch.WordTrace]
  refine ⟨10819149043845736350538067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28851064116921963601434845 10819149043845736350538067)
  ·
    refine ⟨16228723565768604525807101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10819149043845736350538067 16228723565768604525807101)
    ·
      refine ⟨6085771337163226697177663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16228723565768604525807101 6085771337163226697177663)
      ·
        refine ⟨9128657005744840045766495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6085771337163226697177663 9128657005744840045766495)
        ·
          refine ⟨13692985508617260068649743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9128657005744840045766495 13692985508617260068649743)
          ·
            refine ⟨20539478262925890102974615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13692985508617260068649743 20539478262925890102974615)
            ·
              refine ⟨30809217394388835154461923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20539478262925890102974615 30809217394388835154461923)
              ·
                refine ⟨46213826091583252731692885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30809217394388835154461923 46213826091583252731692885)
                ·
                  refine ⟨270784137255370621474763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 46213826091583252731692885 270784137255370621474763)
                  ·
                    rfl

theorem cell21_1186538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 9].length) (baseStart_1186538 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1186538 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1186538 prefixEnd_1186538 := by exact prefixLift 1186538
  have htrace : WordTrace (prefixWord ++ tailWord_1186538) baseStart_1186538 baseEnd_1186538 := by
    simpa [prefixWord, tailWord_1186538, baseEnd_1186538] using wordTrace_append hprefix tailTrace_1186538
  have hstable : (prefixWord ++ tailWord_1186538).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1186538).length < 2 ^ (prefixWord ++ tailWord_1186538).sum := by decide
  have hdescent : baseEnd_1186538 < baseStart_1186538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1186538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1186569 : List Nat := [1, 2, 1, 1, 3, 2, 2, 5, 4]
def baseStart_1186569 : Nat := 118140960795 + 1186569 * 2 ^ 59
def prefixEnd_1186569 : Nat := 4983230072969 + 3 ^ 40 * 1186569 * 2
def baseEnd_1186569 : Nat := 270791211877721456458033

theorem tailTrace_1186569 : CollatzResearch.WordTrace tailWord_1186569 prefixEnd_1186569 270791211877721456458033 := by
  unfold tailWord_1186569
  simp only [CollatzResearch.WordTrace]
  refine ⟨43277726838270637696530761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28851817892180425131020507 43277726838270637696530761)
  ·
    refine ⟨32458295128702978272398071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43277726838270637696530761 32458295128702978272398071)
    ·
      refine ⟨48687442693054467408597107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32458295128702978272398071 48687442693054467408597107)
      ·
        refine ⟨73031164039581701112895661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48687442693054467408597107 73031164039581701112895661)
        ·
          refine ⟨27386686514843137917335873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73031164039581701112895661 27386686514843137917335873)
          ·
            refine ⟨20540014886132353438001905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27386686514843137917335873 20540014886132353438001905)
            ·
              refine ⟨15405011164599265078501429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20540014886132353438001905 15405011164599265078501429)
              ·
                refine ⟨1444219796681181101109509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15405011164599265078501429 1444219796681181101109509)
                ·
                  refine ⟨270791211877721456458033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1444219796681181101109509 270791211877721456458033)
                  ·
                    rfl

theorem cell21_1186569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 5, 4].length) (baseStart_1186569 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1186569 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1186569 prefixEnd_1186569 := by exact prefixLift 1186569
  have htrace : WordTrace (prefixWord ++ tailWord_1186569) baseStart_1186569 baseEnd_1186569 := by
    simpa [prefixWord, tailWord_1186569, baseEnd_1186569] using wordTrace_append hprefix tailTrace_1186569
  have hstable : (prefixWord ++ tailWord_1186569).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1186569).length < 2 ^ (prefixWord ++ tailWord_1186569).sum := by decide
  have hdescent : baseEnd_1186569 < baseStart_1186569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1186569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1186606 : List Nat := [4, 1, 3, 2, 1, 2, 3, 2, 3]
def baseStart_1186606 : Nat := 118140960795 + 1186606 * 2 ^ 59
def prefixEnd_1186606 : Nat := 4983230072969 + 3 ^ 40 * 1186606 * 2
def baseEnd_1186606 : Nat := 270799655781817614341291

theorem tailTrace_1186606 : CollatzResearch.WordTrace tailWord_1186606 prefixEnd_1186606 270799655781817614341291 := by
  unfold tailWord_1186606
  simp only [CollatzResearch.WordTrace]
  refine ⟨5409884542392074126953459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28852717559424395343751781 5409884542392074126953459)
  ·
    refine ⟨8114826813588111190430189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5409884542392074126953459 8114826813588111190430189)
    ·
      refine ⟨3043060055095541696411321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8114826813588111190430189 3043060055095541696411321)
      ·
        refine ⟨2282295041321656272308491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3043060055095541696411321 2282295041321656272308491)
        ·
          refine ⟨3423442561982484408462737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2282295041321656272308491 3423442561982484408462737)
          ·
            refine ⟨2567581921486863306347053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3423442561982484408462737 2567581921486863306347053)
            ·
              refine ⟨962843220557573739880145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2567581921486863306347053 962843220557573739880145)
              ·
                refine ⟨722132415418180304910109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 962843220557573739880145 722132415418180304910109)
                ·
                  refine ⟨270799655781817614341291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 722132415418180304910109 270799655781817614341291)
                  ·
                    rfl

theorem cell21_1186606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 3, 2, 3].length) (baseStart_1186606 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1186606 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1186606 prefixEnd_1186606 := by exact prefixLift 1186606
  have htrace : WordTrace (prefixWord ++ tailWord_1186606) baseStart_1186606 baseEnd_1186606 := by
    simpa [prefixWord, tailWord_1186606, baseEnd_1186606] using wordTrace_append hprefix tailTrace_1186606
  have hstable : (prefixWord ++ tailWord_1186606).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1186606).length < 2 ^ (prefixWord ++ tailWord_1186606).sum := by decide
  have hdescent : baseEnd_1186606 < baseStart_1186606 := by decide
  rcases family_descends (prefixWord ++ tailWord_1186606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1186659 : List Nat := [1, 1, 1, 5, 3, 10]
def baseStart_1186659 : Nat := 118140960795 + 1186659 * 2 ^ 59
def prefixEnd_1186659 : Nat := 4983230072969 + 3 ^ 40 * 1186659 * 2
def baseEnd_1186659 : Nat := 10030064855700048146587

theorem tailTrace_1186659 : CollatzResearch.WordTrace tailWord_1186659 prefixEnd_1186659 10030064855700048146587 := by
  unfold tailWord_1186659
  simp only [CollatzResearch.WordTrace]
  refine ⟨43281009407944583067307031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28854006271963055378204687 43281009407944583067307031)
  ·
    refine ⟨64921514111916874600960547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43281009407944583067307031 64921514111916874600960547)
    ·
      refine ⟨97382271167875311901440821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64921514111916874600960547 97382271167875311901440821)
      ·
        refine ⟨9129587921988310490760077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 97382271167875311901440821 9129587921988310490760077)
        ·
          refine ⟨3423595470745616434035029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9129587921988310490760077 3423595470745616434035029)
          ·
            refine ⟨10030064855700048146587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3423595470745616434035029 10030064855700048146587)
            ·
              rfl

theorem cell21_1186659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 10].length) (baseStart_1186659 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1186659 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1186659 prefixEnd_1186659 := by exact prefixLift 1186659
  have htrace : WordTrace (prefixWord ++ tailWord_1186659) baseStart_1186659 baseEnd_1186659 := by
    simpa [prefixWord, tailWord_1186659, baseEnd_1186659] using wordTrace_append hprefix tailTrace_1186659
  have hstable : (prefixWord ++ tailWord_1186659).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1186659).length < 2 ^ (prefixWord ++ tailWord_1186659).sum := by decide
  have hdescent : baseEnd_1186659 < baseStart_1186659 := by decide
  rcases family_descends (prefixWord ++ tailWord_1186659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1186710 : List Nat := [5, 3, 1, 1, 1, 2, 8]
def baseStart_1186710 : Nat := 118140960795 + 1186710 * 2 ^ 59
def prefixEnd_1186710 : Nat := 4983230072969 + 3 ^ 40 * 1186710 * 2
def baseEnd_1186710 : Nat := 30091487777637393845305

theorem tailTrace_1186710 : CollatzResearch.WordTrace tailWord_1186710 prefixEnd_1186710 30091487777637393845305 := by
  unfold tailWord_1186710
  simp only [CollatzResearch.WordTrace]
  refine ⟨2705179345672488673588349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28855246353839879184942389 2705179345672488673588349)
  ·
    refine ⟨1014442254627183252595631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2705179345672488673588349 1014442254627183252595631)
    ·
      refine ⟨1521663381940774878893447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1014442254627183252595631 1521663381940774878893447)
      ·
        refine ⟨2282495072911162318340171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1521663381940774878893447 2282495072911162318340171)
        ·
          refine ⟨3423742609366743477510257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2282495072911162318340171 3423742609366743477510257)
          ·
            refine ⟨2567806957025057608132693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3423742609366743477510257 2567806957025057608132693)
            ·
              refine ⟨30091487777637393845305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2567806957025057608132693 30091487777637393845305)
              ·
                rfl

theorem cell21_1186710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 8].length) (baseStart_1186710 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1186710 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1186710 prefixEnd_1186710 := by exact prefixLift 1186710
  have htrace : WordTrace (prefixWord ++ tailWord_1186710) baseStart_1186710 baseEnd_1186710 := by
    simpa [prefixWord, tailWord_1186710, baseEnd_1186710] using wordTrace_append hprefix tailTrace_1186710
  have hstable : (prefixWord ++ tailWord_1186710).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1186710).length < 2 ^ (prefixWord ++ tailWord_1186710).sum := by decide
  have hdescent : baseEnd_1186710 < baseStart_1186710 := by decide
  rcases family_descends (prefixWord ++ tailWord_1186710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1186752 : List Nat := [2, 1, 1, 2, 3, 3, 4, 5]
def baseStart_1186752 : Nat := 118140960795 + 1186752 * 2 ^ 59
def prefixEnd_1186752 : Nat := 4983230072969 + 3 ^ 40 * 1186752 * 2
def baseEnd_1186752 : Nat := 90277658323651268302553

theorem tailTrace_1186752 : CollatzResearch.WordTrace tailWord_1186752 prefixEnd_1186752 90277658323651268302553 := by
  unfold tailWord_1186752
  simp only [CollatzResearch.WordTrace]
  refine ⟨21642200698303829975221255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28856267597738439966961673 21642200698303829975221255)
  ·
    refine ⟨32463301047455744962831883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21642200698303829975221255 32463301047455744962831883)
    ·
      refine ⟨48694951571183617444247825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32463301047455744962831883 48694951571183617444247825)
      ·
        refine ⟨36521213678387713083185869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48694951571183617444247825 36521213678387713083185869)
        ·
          refine ⟨13695455129395392406194701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36521213678387713083185869 13695455129395392406194701)
          ·
            refine ⟨5135795673523272152323013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13695455129395392406194701 5135795673523272152323013)
            ·
              refine ⟨962961688785613528560565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5135795673523272152323013 962961688785613528560565)
              ·
                refine ⟨90277658323651268302553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 962961688785613528560565 90277658323651268302553)
                ·
                  rfl

theorem cell21_1186752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 4, 5].length) (baseStart_1186752 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1186752 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1186752 prefixEnd_1186752 := by exact prefixLift 1186752
  have htrace : WordTrace (prefixWord ++ tailWord_1186752) baseStart_1186752 baseEnd_1186752 := by
    simpa [prefixWord, tailWord_1186752, baseEnd_1186752] using wordTrace_append hprefix tailTrace_1186752
  have hstable : (prefixWord ++ tailWord_1186752).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1186752).length < 2 ^ (prefixWord ++ tailWord_1186752).sum := by decide
  have hdescent : baseEnd_1186752 < baseStart_1186752 := by decide
  rcases family_descends (prefixWord ++ tailWord_1186752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1186789 : List Nat := [1, 3, 1, 6, 2, 1, 2, 1, 4]
def baseStart_1186789 : Nat := 118140960795 + 1186789 * 2 ^ 59
def prefixEnd_1186789 : Nat := 4983230072969 + 3 ^ 40 * 1186789 * 2
def baseEnd_1186789 : Nat := 270841418875049962790917

theorem tailTrace_1186789 : CollatzResearch.WordTrace tailWord_1186789 prefixEnd_1186789 270841418875049962790917 := by
  unfold tailWord_1186789
  simp only [CollatzResearch.WordTrace]
  refine ⟨43285750897473615269539421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28857167264982410179692947 43285750897473615269539421)
  ·
    refine ⟨16232156586552605726077283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43285750897473615269539421 16232156586552605726077283)
    ·
      refine ⟨24348234879828908589115925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16232156586552605726077283 24348234879828908589115925)
      ·
        refine ⟨1141323509991980090114809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 24348234879828908589115925 1141323509991980090114809)
        ·
          refine ⟨855992632493985067586107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1141323509991980090114809 855992632493985067586107)
          ·
            refine ⟨1283988948740977601379161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 855992632493985067586107 1283988948740977601379161)
            ·
              refine ⟨962991711555733201034371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1283988948740977601379161 962991711555733201034371)
              ·
                refine ⟨1444487567333599801551557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 962991711555733201034371 1444487567333599801551557)
                ·
                  refine ⟨270841418875049962790917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1444487567333599801551557 270841418875049962790917)
                  ·
                    rfl

theorem cell21_1186789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 2, 1, 4].length) (baseStart_1186789 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1186789 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1186789 prefixEnd_1186789 := by exact prefixLift 1186789
  have htrace : WordTrace (prefixWord ++ tailWord_1186789) baseStart_1186789 baseEnd_1186789 := by
    simpa [prefixWord, tailWord_1186789, baseEnd_1186789] using wordTrace_append hprefix tailTrace_1186789
  have hstable : (prefixWord ++ tailWord_1186789).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1186789).length < 2 ^ (prefixWord ++ tailWord_1186789).sum := by decide
  have hdescent : baseEnd_1186789 < baseStart_1186789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1186789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1186842 : List Nat := [3, 1, 1, 3, 1, 2, 2, 3, 5]
def baseStart_1186842 : Nat := 118140960795 + 1186842 * 2 ^ 59
def prefixEnd_1186842 : Nat := 4983230072969 + 3 ^ 40 * 1186842 * 2
def baseEnd_1186842 : Nat := 270853514197133648407475

theorem tailTrace_1186842 : CollatzResearch.WordTrace tailWord_1186842 prefixEnd_1186842 270853514197133648407475 := by
  unfold tailWord_1186842
  simp only [CollatzResearch.WordTrace]
  refine ⟨10821920991570401330304695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28858455977521070214145853 10821920991570401330304695)
  ·
    refine ⟨16232881487355601995457043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10821920991570401330304695 16232881487355601995457043)
    ·
      refine ⟨24349322231033402993185565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16232881487355601995457043 24349322231033402993185565)
      ·
        refine ⟨9130995836637526122444587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24349322231033402993185565 9130995836637526122444587)
        ·
          refine ⟨13696493754956289183666881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9130995836637526122444587 13696493754956289183666881)
          ·
            refine ⟨10272370316217216887750161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13696493754956289183666881 10272370316217216887750161)
            ·
              refine ⟨7704277737162912665812621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10272370316217216887750161 7704277737162912665812621)
              ·
                refine ⟨2889104151436092249679733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7704277737162912665812621 2889104151436092249679733)
                ·
                  refine ⟨270853514197133648407475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2889104151436092249679733 270853514197133648407475)
                  ·
                    rfl

theorem cell21_1186842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 3, 5].length) (baseStart_1186842 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1186842 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1186842 prefixEnd_1186842 := by exact prefixLift 1186842
  have htrace : WordTrace (prefixWord ++ tailWord_1186842) baseStart_1186842 baseEnd_1186842 := by
    simpa [prefixWord, tailWord_1186842, baseEnd_1186842] using wordTrace_append hprefix tailTrace_1186842
  have hstable : (prefixWord ++ tailWord_1186842).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1186842).length < 2 ^ (prefixWord ++ tailWord_1186842).sum := by decide
  have hdescent : baseEnd_1186842 < baseStart_1186842 := by decide
  rcases family_descends (prefixWord ++ tailWord_1186842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1186845 : List Nat := [1, 4, 2, 2, 3, 2, 1, 6]
def baseStart_1186845 : Nat := 118140960795 + 1186845 * 2 ^ 59
def prefixEnd_1186845 : Nat := 4983230072969 + 3 ^ 40 * 1186845 * 2
def baseEnd_1186845 : Nat := 90284732946002103285823

theorem tailTrace_1186845 : CollatzResearch.WordTrace tailWord_1186845 prefixEnd_1186845 90284732946002103285823 := by
  unfold tailWord_1186845
  simp only [CollatzResearch.WordTrace]
  refine ⟨43287793385270736833577989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28858528923513824555718659 43287793385270736833577989)
  ·
    refine ⟨8116461259738263156295873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43287793385270736833577989 8116461259738263156295873)
    ·
      refine ⟨6087345944803697367221905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8116461259738263156295873 6087345944803697367221905)
      ·
        refine ⟨4565509458602773025416429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6087345944803697367221905 4565509458602773025416429)
        ·
          refine ⟨1712066046976039884531161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4565509458602773025416429 1712066046976039884531161)
          ·
            refine ⟨1284049535232029913398371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1712066046976039884531161 1284049535232029913398371)
            ·
              refine ⟨1926074302848044870097557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1284049535232029913398371 1926074302848044870097557)
              ·
                refine ⟨90284732946002103285823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1926074302848044870097557 90284732946002103285823)
                ·
                  rfl

theorem cell21_1186845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 1, 6].length) (baseStart_1186845 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1186845 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1186845 prefixEnd_1186845 := by exact prefixLift 1186845
  have htrace : WordTrace (prefixWord ++ tailWord_1186845) baseStart_1186845 baseEnd_1186845 := by
    simpa [prefixWord, tailWord_1186845, baseEnd_1186845] using wordTrace_append hprefix tailTrace_1186845
  have hstable : (prefixWord ++ tailWord_1186845).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1186845).length < 2 ^ (prefixWord ++ tailWord_1186845).sum := by decide
  have hdescent : baseEnd_1186845 < baseStart_1186845 := by decide
  rcases family_descends (prefixWord ++ tailWord_1186845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1186876 : List Nat := [2, 2, 2, 2, 2, 3, 2, 3, 3]
def baseStart_1186876 : Nat := 118140960795 + 1186876 * 2 ^ 59
def prefixEnd_1186876 : Nat := 4983230072969 + 3 ^ 40 * 1186876 * 2
def baseEnd_1186876 : Nat := 270861273460357144840739

theorem tailTrace_1186876 : CollatzResearch.WordTrace tailWord_1186876 prefixEnd_1186876 270861273460357144840739 := by
  unfold tailWord_1186876
  simp only [CollatzResearch.WordTrace]
  refine ⟨21644462024079214563978241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28859282698772286085304321 21644462024079214563978241)
  ·
    refine ⟨16233346518059410922983681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21644462024079214563978241 16233346518059410922983681)
    ·
      refine ⟨12175009888544558192237761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16233346518059410922983681 12175009888544558192237761)
      ·
        refine ⟨9131257416408418644178321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12175009888544558192237761 9131257416408418644178321)
        ·
          refine ⟨6848443062306313983133741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9131257416408418644178321 6848443062306313983133741)
          ·
            refine ⟨2568166148364867743675153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6848443062306313983133741 2568166148364867743675153)
            ·
              refine ⟨1926124611273650807756365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2568166148364867743675153 1926124611273650807756365)
              ·
                refine ⟨722296729227619052908637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1926124611273650807756365 722296729227619052908637)
                ·
                  refine ⟨270861273460357144840739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 722296729227619052908637 270861273460357144840739)
                  ·
                    rfl

theorem cell21_1186876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 2, 3, 3].length) (baseStart_1186876 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1186876 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1186876 prefixEnd_1186876 := by exact prefixLift 1186876
  have htrace : WordTrace (prefixWord ++ tailWord_1186876) baseStart_1186876 baseEnd_1186876 := by
    simpa [prefixWord, tailWord_1186876, baseEnd_1186876] using wordTrace_append hprefix tailTrace_1186876
  have hstable : (prefixWord ++ tailWord_1186876).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1186876).length < 2 ^ (prefixWord ++ tailWord_1186876).sum := by decide
  have hdescent : baseEnd_1186876 < baseStart_1186876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1186876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1186887 : List Nat := [1, 1, 4, 1, 3, 3, 8]
def baseStart_1186887 : Nat := 118140960795 + 1186887 * 2 ^ 59
def prefixEnd_1186887 : Nat := 4983230072969 + 3 ^ 40 * 1186887 * 2
def baseEnd_1186887 : Nat := 30095975978913730017487

theorem tailTrace_1186887 : CollatzResearch.WordTrace tailWord_1186887 prefixEnd_1186887 30095975978913730017487 := by
  unfold tailWord_1186887
  simp only [CollatzResearch.WordTrace]
  refine ⟨43289325251118578006606915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28859550167412385337737943 43289325251118578006606915)
  ·
    refine ⟨64933987876677867009910373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43289325251118578006606915 64933987876677867009910373)
    ·
      refine ⟨12175122726877100064358195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 64933987876677867009910373 12175122726877100064358195)
      ·
        refine ⟨18262684090315650096537293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12175122726877100064358195 18262684090315650096537293)
        ·
          refine ⟨6848506533868368786201485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18262684090315650096537293 6848506533868368786201485)
          ·
            refine ⟨2568189950200638294825557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6848506533868368786201485 2568189950200638294825557)
            ·
              refine ⟨30095975978913730017487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2568189950200638294825557 30095975978913730017487)
              ·
                rfl

theorem cell21_1186887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 8].length) (baseStart_1186887 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1186887 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1186887 prefixEnd_1186887 := by exact prefixLift 1186887
  have htrace : WordTrace (prefixWord ++ tailWord_1186887) baseStart_1186887 baseEnd_1186887 := by
    simpa [prefixWord, tailWord_1186887, baseEnd_1186887] using wordTrace_append hprefix tailTrace_1186887
  have hstable : (prefixWord ++ tailWord_1186887).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1186887).length < 2 ^ (prefixWord ++ tailWord_1186887).sum := by decide
  have hdescent : baseEnd_1186887 < baseStart_1186887 := by decide
  rcases family_descends (prefixWord ++ tailWord_1186887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1186952 : List Nat := [2, 1, 3, 4, 2, 2, 1, 1, 5]
def baseStart_1186952 : Nat := 118140960795 + 1186952 * 2 ^ 59
def prefixEnd_1186952 : Nat := 4983230072969 + 3 ^ 40 * 1186952 * 2
def baseEnd_1186952 : Nat := 270878617695797901573917

theorem tailTrace_1186952 : CollatzResearch.WordTrace tailWord_1186952 prefixEnd_1186952 270878617695797901573917 := by
  unfold tailWord_1186952
  simp only [CollatzResearch.WordTrace]
  refine ⟨21645847997941547053861555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28861130663922062738482073 21645847997941547053861555)
  ·
    refine ⟨32468771996912320580792333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21645847997941547053861555 32468771996912320580792333)
    ·
      refine ⟨12175789498842120217797125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32468771996912320580792333 12175789498842120217797125)
      ·
        refine ⟨2282960531032897540836961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12175789498842120217797125 2282960531032897540836961)
        ·
          refine ⟨1712220398274673155627721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2282960531032897540836961 1712220398274673155627721)
          ·
            refine ⟨1284165298706004866720791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1712220398274673155627721 1284165298706004866720791)
            ·
              refine ⟨1926247948059007300081187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1284165298706004866720791 1926247948059007300081187)
              ·
                refine ⟨2889371922088510950121781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1926247948059007300081187 2889371922088510950121781)
                ·
                  refine ⟨270878617695797901573917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2889371922088510950121781 270878617695797901573917)
                  ·
                    rfl

theorem cell21_1186952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 1, 1, 5].length) (baseStart_1186952 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1186952 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1186952 prefixEnd_1186952 := by exact prefixLift 1186952
  have htrace : WordTrace (prefixWord ++ tailWord_1186952) baseStart_1186952 baseEnd_1186952 := by
    simpa [prefixWord, tailWord_1186952, baseEnd_1186952] using wordTrace_append hprefix tailTrace_1186952
  have hstable : (prefixWord ++ tailWord_1186952).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1186952).length < 2 ^ (prefixWord ++ tailWord_1186952).sum := by decide
  have hdescent : baseEnd_1186952 < baseStart_1186952 := by decide
  rcases family_descends (prefixWord ++ tailWord_1186952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1187028 : List Nat := [2, 4, 1, 4, 1, 1, 1, 2, 5]
def baseStart_1187028 : Nat := 118140960795 + 1187028 * 2 ^ 59
def prefixEnd_1187028 : Nat := 4983230072969 + 3 ^ 40 * 1187028 * 2
def baseEnd_1187028 : Nat := 270895961931238658307095

theorem tailTrace_1187028 : CollatzResearch.WordTrace tailWord_1187028 prefixEnd_1187028 270895961931238658307095 := by
  unfold tailWord_1187028
  simp only [CollatzResearch.WordTrace]
  refine ⟨21647233971803879543744869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28862978629071839391659825 21647233971803879543744869)
  ·
    refine ⟨4058856369713227414452163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21647233971803879543744869 4058856369713227414452163)
    ·
      refine ⟨6088284554569841121678245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4058856369713227414452163 6088284554569841121678245)
      ·
        refine ⟨1141553353981845210314671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6088284554569841121678245 1141553353981845210314671)
        ·
          refine ⟨1712330030972767815472007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1141553353981845210314671 1712330030972767815472007)
          ·
            refine ⟨2568495046459151723208011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1712330030972767815472007 2568495046459151723208011)
            ·
              refine ⟨3852742569688727584812017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2568495046459151723208011 3852742569688727584812017)
              ·
                refine ⟨2889556927266545688609013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3852742569688727584812017 2889556927266545688609013)
                ·
                  refine ⟨270895961931238658307095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2889556927266545688609013 270895961931238658307095)
                  ·
                    rfl

theorem cell21_1187028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 2, 5].length) (baseStart_1187028 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1187028 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1187028 prefixEnd_1187028 := by exact prefixLift 1187028
  have htrace : WordTrace (prefixWord ++ tailWord_1187028) baseStart_1187028 baseEnd_1187028 := by
    simpa [prefixWord, tailWord_1187028, baseEnd_1187028] using wordTrace_append hprefix tailTrace_1187028
  have hstable : (prefixWord ++ tailWord_1187028).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1187028).length < 2 ^ (prefixWord ++ tailWord_1187028).sum := by decide
  have hdescent : baseEnd_1187028 < baseStart_1187028 := by decide
  rcases family_descends (prefixWord ++ tailWord_1187028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1187101 : List Nat := [1, 4, 2, 3, 1, 1, 1, 2, 6]
def baseStart_1187101 : Nat := 118140960795 + 1187101 * 2 ^ 59
def prefixEnd_1187101 : Nat := 4983230072969 + 3 ^ 40 * 1187101 * 2
def baseEnd_1187101 : Nat := 270912621525806753590279

theorem tailTrace_1187101 : CollatzResearch.WordTrace tailWord_1187101 prefixEnd_1187101 270912621525806753590279 := by
  unfold tailWord_1187101
  simp only [CollatzResearch.WordTrace]
  refine ⟨43297130472343292554897157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28864753648228861703264771 43297130472343292554897157)
  ·
    refine ⟨8118211963564367354043217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43297130472343292554897157 8118211963564367354043217)
    ·
      refine ⟨6088658972673275515532413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8118211963564367354043217 6088658972673275515532413)
      ·
        refine ⟨2283247114752478318324655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6088658972673275515532413 2283247114752478318324655)
        ·
          refine ⟨3424870672128717477486983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2283247114752478318324655 3424870672128717477486983)
          ·
            refine ⟨5137306008193076216230475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3424870672128717477486983 5137306008193076216230475)
            ·
              refine ⟨7705959012289614324345713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5137306008193076216230475 7705959012289614324345713)
              ·
                refine ⟨5779469259217210743259285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7705959012289614324345713 5779469259217210743259285)
                ·
                  refine ⟨270912621525806753590279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5779469259217210743259285 270912621525806753590279)
                  ·
                    rfl

theorem cell21_1187101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 2, 6].length) (baseStart_1187101 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1187101 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1187101 prefixEnd_1187101 := by exact prefixLift 1187101
  have htrace : WordTrace (prefixWord ++ tailWord_1187101) baseStart_1187101 baseEnd_1187101 := by
    simpa [prefixWord, tailWord_1187101, baseEnd_1187101] using wordTrace_append hprefix tailTrace_1187101
  have hstable : (prefixWord ++ tailWord_1187101).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1187101).length < 2 ^ (prefixWord ++ tailWord_1187101).sum := by decide
  have hdescent : baseEnd_1187101 < baseStart_1187101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1187101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1187180 : List Nat := [2, 2, 1, 1, 5, 1, 4, 2, 3]
def baseStart_1187180 : Nat := 118140960795 + 1187180 * 2 ^ 59
def prefixEnd_1187180 : Nat := 4983230072969 + 3 ^ 40 * 1187180 * 2
def baseEnd_1187180 : Nat := 270930650402120171773451

theorem tailTrace_1187180 : CollatzResearch.WordTrace tailWord_1187180 prefixEnd_1187180 270930650402120171773451 := by
  unfold tailWord_1187180
  simp only [CollatzResearch.WordTrace]
  refine ⟨21650005919528544523511497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28866674559371392698015329 21650005919528544523511497)
  ·
    refine ⟨16237504439646408392633623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21650005919528544523511497 16237504439646408392633623)
    ·
      refine ⟨24356256659469612588950435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16237504439646408392633623 24356256659469612588950435)
      ·
        refine ⟨36534384989204418883425653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24356256659469612588950435 36534384989204418883425653)
        ·
          refine ⟨3425098592737914270321155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36534384989204418883425653 3425098592737914270321155)
          ·
            refine ⟨5137647889106871405481733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3425098592737914270321155 5137647889106871405481733)
            ·
              refine ⟨963308979207538388527825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5137647889106871405481733 963308979207538388527825)
              ·
                refine ⟨722481734405653791395869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 963308979207538388527825 722481734405653791395869)
                ·
                  refine ⟨270930650402120171773451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 722481734405653791395869 270930650402120171773451)
                  ·
                    rfl

theorem cell21_1187180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 4, 2, 3].length) (baseStart_1187180 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1187180 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1187180 prefixEnd_1187180 := by exact prefixLift 1187180
  have htrace : WordTrace (prefixWord ++ tailWord_1187180) baseStart_1187180 baseEnd_1187180 := by
    simpa [prefixWord, tailWord_1187180, baseEnd_1187180] using wordTrace_append hprefix tailTrace_1187180
  have hstable : (prefixWord ++ tailWord_1187180).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1187180).length < 2 ^ (prefixWord ++ tailWord_1187180).sum := by decide
  have hdescent : baseEnd_1187180 < baseStart_1187180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1187180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1187205 : List Nat := [1, 3, 1, 1, 3, 1, 3, 1, 7]
def baseStart_1187205 : Nat := 118140960795 + 1187205 * 2 ^ 59
def prefixEnd_1187205 : Nat := 4983230072969 + 3 ^ 40 * 1187205 * 2
def baseEnd_1187205 : Nat := 270936355742725683856733

theorem tailTrace_1187205 : CollatzResearch.WordTrace tailWord_1187205 prefixEnd_1187205 270936355742725683856733 := by
  unfold tailWord_1187205
  simp only [CollatzResearch.WordTrace]
  refine ⟨43300923663966518316683069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28867282442644345544455379 43300923663966518316683069)
  ·
    refine ⟨16237846373987444368756151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43300923663966518316683069 16237846373987444368756151)
    ·
      refine ⟨24356769560981166553134227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16237846373987444368756151 24356769560981166553134227)
      ·
        refine ⟨36535154341471749829701341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24356769560981166553134227 36535154341471749829701341)
        ·
          refine ⟨13700682878051906186138003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36535154341471749829701341 13700682878051906186138003)
          ·
            refine ⟨20551024317077859279207005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13700682878051906186138003 20551024317077859279207005)
            ·
              refine ⟨7706634118904197229702627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20551024317077859279207005 7706634118904197229702627)
              ·
                refine ⟨11559951178356295844553941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7706634118904197229702627 11559951178356295844553941)
                ·
                  refine ⟨270936355742725683856733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11559951178356295844553941 270936355742725683856733)
                  ·
                    rfl

theorem cell21_1187205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 1, 7].length) (baseStart_1187205 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1187205 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1187205 prefixEnd_1187205 := by exact prefixLift 1187205
  have htrace : WordTrace (prefixWord ++ tailWord_1187205) baseStart_1187205 baseEnd_1187205 := by
    simpa [prefixWord, tailWord_1187205, baseEnd_1187205] using wordTrace_append hprefix tailTrace_1187205
  have hstable : (prefixWord ++ tailWord_1187205).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1187205).length < 2 ^ (prefixWord ++ tailWord_1187205).sum := by decide
  have hdescent : baseEnd_1187205 < baseStart_1187205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1187205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1187208 : List Nat := [2, 1, 3, 3, 1, 3, 3, 5]
def baseStart_1187208 : Nat := 118140960795 + 1187208 * 2 ^ 59
def prefixEnd_1187208 : Nat := 4983230072969 + 3 ^ 40 * 1187208 * 2
def baseEnd_1187208 : Nat := 90312346794532781768909

theorem tailTrace_1187208 : CollatzResearch.WordTrace tailWord_1187208 prefixEnd_1187208 90312346794532781768909 := by
  unfold tailWord_1187208
  simp only [CollatzResearch.WordTrace]
  refine ⟨21650516541477824914521139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28867355388637099886028185 21650516541477824914521139)
  ·
    refine ⟨32475774812216737371781709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21650516541477824914521139 32475774812216737371781709)
    ·
      refine ⟨12178415554581276514418141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32475774812216737371781709 12178415554581276514418141)
      ·
        refine ⟨4566905832967978692906803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12178415554581276514418141 4566905832967978692906803)
        ·
          refine ⟨6850358749451968039360205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4566905832967978692906803 6850358749451968039360205)
          ·
            refine ⟨2568884531044488014760077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6850358749451968039360205 2568884531044488014760077)
            ·
              refine ⟨963331699141683005535029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2568884531044488014760077 963331699141683005535029)
              ·
                refine ⟨90312346794532781768909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 963331699141683005535029 90312346794532781768909)
                ·
                  rfl

theorem cell21_1187208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 3, 5].length) (baseStart_1187208 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1187208 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1187208 prefixEnd_1187208 := by exact prefixLift 1187208
  have htrace : WordTrace (prefixWord ++ tailWord_1187208) baseStart_1187208 baseEnd_1187208 := by
    simpa [prefixWord, tailWord_1187208, baseEnd_1187208] using wordTrace_append hprefix tailTrace_1187208
  have hstable : (prefixWord ++ tailWord_1187208).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1187208).length < 2 ^ (prefixWord ++ tailWord_1187208).sum := by decide
  have hdescent : baseEnd_1187208 < baseStart_1187208 := by decide
  rcases family_descends (prefixWord ++ tailWord_1187208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1187228 : List Nat := [2, 2, 3, 4, 2, 1, 1, 2, 4]
def baseStart_1187228 : Nat := 118140960795 + 1187228 * 2 ^ 59
def prefixEnd_1187228 : Nat := 4983230072969 + 3 ^ 40 * 1187228 * 2
def baseEnd_1187228 : Nat := 270941604656082754973353

theorem tailTrace_1187228 : CollatzResearch.WordTrace tailWord_1187228 prefixEnd_1187228 270941604656082754973353 := by
  unfold tailWord_1187228
  simp only [CollatzResearch.WordTrace]
  refine ⟨21650881271441596622385169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28867841695255462163180225 21650881271441596622385169)
  ·
    refine ⟨16238160953581197466788877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21650881271441596622385169 16238160953581197466788877)
    ·
      refine ⟨6089310357592949050045829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16238160953581197466788877 6089310357592949050045829)
      ·
        refine ⟨1141745692048677946883593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6089310357592949050045829 1141745692048677946883593)
        ·
          refine ⟨856309269036508460162695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1141745692048677946883593 856309269036508460162695)
          ·
            refine ⟨1284463903554762690244043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 856309269036508460162695 1284463903554762690244043)
            ·
              refine ⟨1926695855332144035366065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1284463903554762690244043 1926695855332144035366065)
              ·
                refine ⟨1445021891499108026524549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1926695855332144035366065 1445021891499108026524549)
                ·
                  refine ⟨270941604656082754973353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1445021891499108026524549 270941604656082754973353)
                  ·
                    rfl

theorem cell21_1187228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 1, 2, 4].length) (baseStart_1187228 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1187228 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1187228 prefixEnd_1187228 := by exact prefixLift 1187228
  have htrace : WordTrace (prefixWord ++ tailWord_1187228) baseStart_1187228 baseEnd_1187228 := by
    simpa [prefixWord, tailWord_1187228, baseEnd_1187228] using wordTrace_append hprefix tailTrace_1187228
  have hstable : (prefixWord ++ tailWord_1187228).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1187228).length < 2 ^ (prefixWord ++ tailWord_1187228).sum := by decide
  have hdescent : baseEnd_1187228 < baseStart_1187228 := by decide
  rcases family_descends (prefixWord ++ tailWord_1187228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1187239 : List Nat := [1, 1, 6, 1, 1, 1, 1, 6, 3]
def baseStart_1187239 : Nat := 118140960795 + 1187239 * 2 ^ 59
def prefixEnd_1187239 : Nat := 4983230072969 + 3 ^ 40 * 1187239 * 2
def baseEnd_1187239 : Nat := 270944115005949180289997

theorem tailTrace_1187239 : CollatzResearch.WordTrace tailWord_1187239 prefixEnd_1187239 270944115005949180289997 := by
  unfold tailWord_1187239
  simp only [CollatzResearch.WordTrace]
  refine ⟨43302163745843342123420771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28868109163895561415613847 43302163745843342123420771)
  ·
    refine ⟨64953245618765013185131157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43302163745843342123420771 64953245618765013185131157)
    ·
      refine ⟨3044683388379609993053023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 64953245618765013185131157 3044683388379609993053023)
      ·
        refine ⟨4567025082569414989579535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3044683388379609993053023 4567025082569414989579535)
        ·
          refine ⟨6850537623854122484369303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4567025082569414989579535 6850537623854122484369303)
          ·
            refine ⟨10275806435781183726553955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6850537623854122484369303 10275806435781183726553955)
            ·
              refine ⟨15413709653671775589830933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10275806435781183726553955 15413709653671775589830933)
              ·
                refine ⟨722517640015864480773325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 15413709653671775589830933 722517640015864480773325)
                ·
                  refine ⟨270944115005949180289997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 722517640015864480773325 270944115005949180289997)
                  ·
                    rfl

theorem cell21_1187239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 6, 3].length) (baseStart_1187239 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1187239 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1187239 prefixEnd_1187239 := by exact prefixLift 1187239
  have htrace : WordTrace (prefixWord ++ tailWord_1187239) baseStart_1187239 baseEnd_1187239 := by
    simpa [prefixWord, tailWord_1187239, baseEnd_1187239] using wordTrace_append hprefix tailTrace_1187239
  have hstable : (prefixWord ++ tailWord_1187239).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1187239).length < 2 ^ (prefixWord ++ tailWord_1187239).sum := by decide
  have hdescent : baseEnd_1187239 < baseStart_1187239 := by decide
  rcases family_descends (prefixWord ++ tailWord_1187239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1187267 : List Nat := [1, 1, 1, 3, 1, 1, 8, 5]
def baseStart_1187267 : Nat := 118140960795 + 1187267 * 2 ^ 59
def prefixEnd_1187267 : Nat := 4983230072969 + 3 ^ 40 * 1187267 * 2
def baseEnd_1187267 : Nat := 90316834995809117941091

theorem tailTrace_1187267 : CollatzResearch.WordTrace tailWord_1187267 prefixEnd_1187267 90316834995809117941091 := by
  unfold tailWord_1187267
  simp only [CollatzResearch.WordTrace]
  refine ⟨43303184989741902905440055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28868789993161268603626703 43303184989741902905440055)
  ·
    refine ⟨64954777484612854358160083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43303184989741902905440055 64954777484612854358160083)
    ·
      refine ⟨97432166226919281537240125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64954777484612854358160083 97432166226919281537240125)
      ·
        refine ⟨36537062335094730576465047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97432166226919281537240125 36537062335094730576465047)
        ·
          refine ⟨54805593502642095864697571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36537062335094730576465047 54805593502642095864697571)
          ·
            refine ⟨82208390253963143797046357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54805593502642095864697571 82208390253963143797046357)
            ·
              refine ⟨963379573288630591371637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 82208390253963143797046357 963379573288630591371637)
              ·
                refine ⟨90316834995809117941091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 963379573288630591371637 90316834995809117941091)
                ·
                  rfl

theorem cell21_1187267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 8, 5].length) (baseStart_1187267 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1187267 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1187267 prefixEnd_1187267 := by exact prefixLift 1187267
  have htrace : WordTrace (prefixWord ++ tailWord_1187267) baseStart_1187267 baseEnd_1187267 := by
    simpa [prefixWord, tailWord_1187267, baseEnd_1187267] using wordTrace_append hprefix tailTrace_1187267
  have hstable : (prefixWord ++ tailWord_1187267).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1187267).length < 2 ^ (prefixWord ++ tailWord_1187267).sum := by decide
  have hdescent : baseEnd_1187267 < baseStart_1187267 := by decide
  rcases family_descends (prefixWord ++ tailWord_1187267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1187284 : List Nat := [2, 4, 1, 2, 3, 2, 7]
def baseStart_1187284 : Nat := 118140960795 + 1187284 * 2 ^ 59
def prefixEnd_1187284 : Nat := 4983230072969 + 3 ^ 40 * 1187284 * 2
def baseEnd_1187284 : Nat := 30106042735448789115545

theorem tailTrace_1187284 : CollatzResearch.WordTrace tailWord_1187284 prefixEnd_1187284 30106042735448789115545 := by
  unfold tailWord_1187284
  simp only [CollatzResearch.WordTrace]
  refine ⟨21651902515340157404404453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28869203353786876539205937 21651902515340157404404453)
  ·
    refine ⟨4059731721626279513325835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21651902515340157404404453 4059731721626279513325835)
    ·
      refine ⟨6089597582439419269988753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4059731721626279513325835 6089597582439419269988753)
      ·
        refine ⟨4567198186829564452491565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6089597582439419269988753 4567198186829564452491565)
        ·
          refine ⟨1712699320061086669684337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4567198186829564452491565 1712699320061086669684337)
          ·
            refine ⟨1284524490045815002263253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1712699320061086669684337 1284524490045815002263253)
            ·
              refine ⟨30106042735448789115545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1284524490045815002263253 30106042735448789115545)
              ·
                rfl

theorem cell21_1187284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 7].length) (baseStart_1187284 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1187284 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1187284 prefixEnd_1187284 := by exact prefixLift 1187284
  have htrace : WordTrace (prefixWord ++ tailWord_1187284) baseStart_1187284 baseEnd_1187284 := by
    simpa [prefixWord, tailWord_1187284, baseEnd_1187284] using wordTrace_append hprefix tailTrace_1187284
  have hstable : (prefixWord ++ tailWord_1187284).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1187284).length < 2 ^ (prefixWord ++ tailWord_1187284).sum := by decide
  have hdescent : baseEnd_1187284 < baseStart_1187284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1187284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1187360 : List Nat := [2, 1, 1, 6, 1, 3, 1, 6]
def baseStart_1187360 : Nat := 118140960795 + 1187360 * 2 ^ 59
def prefixEnd_1187360 : Nat := 4983230072969 + 3 ^ 40 * 1187360 * 2
def baseEnd_1187360 : Nat := 90323909618159952924361

theorem tailTrace_1187360 : CollatzResearch.WordTrace tailWord_1187360 prefixEnd_1187360 90323909618159952924361 := by
  unfold tailWord_1187360
  simp only [CollatzResearch.WordTrace]
  refine ⟨21653288489202489894287767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28871051318936653192383689 21653288489202489894287767)
  ·
    refine ⟨32479932733803734841431651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21653288489202489894287767 32479932733803734841431651)
    ·
      refine ⟨48719899100705602262147477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32479932733803734841431651 48719899100705602262147477)
      ·
        refine ⟨2283745270345575106038163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 48719899100705602262147477 2283745270345575106038163)
        ·
          refine ⟨3425617905518362659057245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2283745270345575106038163 3425617905518362659057245)
          ·
            refine ⟨1284606714569385997146467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3425617905518362659057245 1284606714569385997146467)
            ·
              refine ⟨1926910071854078995719701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1284606714569385997146467 1926910071854078995719701)
              ·
                refine ⟨90323909618159952924361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1926910071854078995719701 90323909618159952924361)
                ·
                  rfl

theorem cell21_1187360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 1, 6].length) (baseStart_1187360 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1187360 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1187360 prefixEnd_1187360 := by exact prefixLift 1187360
  have htrace : WordTrace (prefixWord ++ tailWord_1187360) baseStart_1187360 baseEnd_1187360 := by
    simpa [prefixWord, tailWord_1187360, baseEnd_1187360] using wordTrace_append hprefix tailTrace_1187360
  have hstable : (prefixWord ++ tailWord_1187360).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1187360).length < 2 ^ (prefixWord ++ tailWord_1187360).sum := by decide
  have hdescent : baseEnd_1187360 < baseStart_1187360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1187360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1187371 : List Nat := [1, 1, 1, 1, 2, 1, 3, 1, 10]
def baseStart_1187371 : Nat := 118140960795 + 1187371 * 2 ^ 59
def prefixEnd_1187371 : Nat := 4983230072969 + 3 ^ 40 * 1187371 * 2
def baseEnd_1187371 : Nat := 270974239204346284089727

theorem tailTrace_1187371 : CollatzResearch.WordTrace tailWord_1187371 prefixEnd_1187371 270974239204346284089727 := by
  unfold tailWord_1187371
  simp only [CollatzResearch.WordTrace]
  refine ⟨43306978181365128667225967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28871318787576752444817311 43306978181365128667225967)
  ·
    refine ⟨64960467272047693000838951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43306978181365128667225967 64960467272047693000838951)
    ·
      refine ⟨97440700908071539501258427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64960467272047693000838951 97440700908071539501258427)
      ·
        refine ⟨146161051362107309251887641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97440700908071539501258427 146161051362107309251887641)
        ·
          refine ⟨109620788521580481938915731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146161051362107309251887641 109620788521580481938915731)
          ·
            refine ⟨164431182782370722908373597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109620788521580481938915731 164431182782370722908373597)
            ·
              refine ⟨61661693543389021090640099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 164431182782370722908373597 61661693543389021090640099)
              ·
                refine ⟨92492540315083531635960149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61661693543389021090640099 92492540315083531635960149)
                ·
                  refine ⟨270974239204346284089727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 92492540315083531635960149 270974239204346284089727)
                  ·
                    rfl

theorem cell21_1187371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 10].length) (baseStart_1187371 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1187371 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1187371 prefixEnd_1187371 := by exact prefixLift 1187371
  have htrace : WordTrace (prefixWord ++ tailWord_1187371) baseStart_1187371 baseEnd_1187371 := by
    simpa [prefixWord, tailWord_1187371, baseEnd_1187371] using wordTrace_append hprefix tailTrace_1187371
  have hstable : (prefixWord ++ tailWord_1187371).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1187371).length < 2 ^ (prefixWord ++ tailWord_1187371).sum := by decide
  have hdescent : baseEnd_1187371 < baseStart_1187371 := by decide
  rcases family_descends (prefixWord ++ tailWord_1187371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1187374 : List Nat := [4, 1, 3, 1, 2, 1, 1, 1, 7]
def baseStart_1187374 : Nat := 118140960795 + 1187374 * 2 ^ 59
def prefixEnd_1187374 : Nat := 4983230072969 + 3 ^ 40 * 1187374 * 2
def baseEnd_1187374 : Nat := 270974923845218945539721

theorem tailTrace_1187374 : CollatzResearch.WordTrace tailWord_1187374 prefixEnd_1187374 270974923845218945539721 := by
  unfold tailWord_1187374
  simp only [CollatzResearch.WordTrace]
  refine ⟨5413385950044282522448147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28871391733569506786390117 5413385950044282522448147)
  ·
    refine ⟨8120078925066423783672221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5413385950044282522448147 8120078925066423783672221)
    ·
      refine ⟨3045029596899908918877083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8120078925066423783672221 3045029596899908918877083)
      ·
        refine ⟨4567544395349863378315625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3045029596899908918877083 4567544395349863378315625)
        ·
          refine ⟨3425658296512397533736719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4567544395349863378315625 3425658296512397533736719)
          ·
            refine ⟨5138487444768596300605079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3425658296512397533736719 5138487444768596300605079)
            ·
              refine ⟨7707731167152894450907619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5138487444768596300605079 7707731167152894450907619)
              ·
                refine ⟨11561596750729341676361429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7707731167152894450907619 11561596750729341676361429)
                ·
                  refine ⟨270974923845218945539721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11561596750729341676361429 270974923845218945539721)
                  ·
                    rfl

theorem cell21_1187374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 1, 7].length) (baseStart_1187374 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1187374 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1187374 prefixEnd_1187374 := by exact prefixLift 1187374
  have htrace : WordTrace (prefixWord ++ tailWord_1187374) baseStart_1187374 baseEnd_1187374 := by
    simpa [prefixWord, tailWord_1187374, baseEnd_1187374] using wordTrace_append hprefix tailTrace_1187374
  have hstable : (prefixWord ++ tailWord_1187374).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1187374).length < 2 ^ (prefixWord ++ tailWord_1187374).sum := by decide
  have hdescent : baseEnd_1187374 < baseStart_1187374 := by decide
  rcases family_descends (prefixWord ++ tailWord_1187374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1187391 : List Nat := [1, 1, 2, 2, 3, 4, 2, 3, 3]
def baseStart_1187391 : Nat := 118140960795 + 1187391 * 2 ^ 59
def prefixEnd_1187391 : Nat := 4983230072969 + 3 ^ 40 * 1187391 * 2
def baseEnd_1187391 : Nat := 270978803476830693756353

theorem tailTrace_1187391 : CollatzResearch.WordTrace tailWord_1187391 prefixEnd_1187391 270978803476830693756353 := by
  unfold tailWord_1187391
  simp only [CollatzResearch.WordTrace]
  refine ⟨43307707641292672082954027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28871805094195114721969351 43307707641292672082954027)
  ·
    refine ⟨64961561461939008124431041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43307707641292672082954027 64961561461939008124431041)
    ·
      refine ⟨48721171096454256093323281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64961561461939008124431041 48721171096454256093323281)
      ·
        refine ⟨36540878322340692069992461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48721171096454256093323281 36540878322340692069992461)
        ·
          refine ⟨13702829370877759526247173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36540878322340692069992461 13702829370877759526247173)
          ·
            refine ⟨2569280507039579911171345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13702829370877759526247173 2569280507039579911171345)
            ·
              refine ⟨1926960380279684933378509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2569280507039579911171345 1926960380279684933378509)
              ·
                refine ⟨722610142604881850016941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1926960380279684933378509 722610142604881850016941)
                ·
                  refine ⟨270978803476830693756353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 722610142604881850016941 270978803476830693756353)
                  ·
                    rfl

theorem cell21_1187391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 2, 3, 3].length) (baseStart_1187391 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1187391 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1187391 prefixEnd_1187391 := by exact prefixLift 1187391
  have htrace : WordTrace (prefixWord ++ tailWord_1187391) baseStart_1187391 baseEnd_1187391 := by
    simpa [prefixWord, tailWord_1187391, baseEnd_1187391] using wordTrace_append hprefix tailTrace_1187391
  have hstable : (prefixWord ++ tailWord_1187391).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1187391).length < 2 ^ (prefixWord ++ tailWord_1187391).sum := by decide
  have hdescent : baseEnd_1187391 < baseStart_1187391 := by decide
  rcases family_descends (prefixWord ++ tailWord_1187391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1187402 : List Nat := [3, 1, 2, 1, 1, 3, 10]
def baseStart_1187402 : Nat := 118140960795 + 1187402 * 2 ^ 59
def prefixEnd_1187402 : Nat := 4983230072969 + 3 ^ 40 * 1187402 * 2
def baseEnd_1187402 : Nat := 30109034869633013230333

theorem tailTrace_1187402 : CollatzResearch.WordTrace tailWord_1187402 prefixEnd_1187402 30109034869633013230333 := by
  unfold tailWord_1187402
  simp only [CollatzResearch.WordTrace]
  refine ⟨10827027211063205240401115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28872072562835213974402973 10827027211063205240401115)
  ·
    refine ⟨16240540816594807860601673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10827027211063205240401115 16240540816594807860601673)
    ·
      refine ⟨12180405612446105895451255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16240540816594807860601673 12180405612446105895451255)
      ·
        refine ⟨18270608418669158843176883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12180405612446105895451255 18270608418669158843176883)
        ·
          refine ⟨27405912628003738264765325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18270608418669158843176883 27405912628003738264765325)
          ·
            refine ⟨10277217235501401849286997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27405912628003738264765325 10277217235501401849286997)
            ·
              refine ⟨30109034869633013230333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 10277217235501401849286997 30109034869633013230333)
              ·
                rfl

theorem cell21_1187402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 10].length) (baseStart_1187402 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1187402 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1187402 prefixEnd_1187402 := by exact prefixLift 1187402
  have htrace : WordTrace (prefixWord ++ tailWord_1187402) baseStart_1187402 baseEnd_1187402 := by
    simpa [prefixWord, tailWord_1187402, baseEnd_1187402] using wordTrace_append hprefix tailTrace_1187402
  have hstable : (prefixWord ++ tailWord_1187402).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1187402).length < 2 ^ (prefixWord ++ tailWord_1187402).sum := by decide
  have hdescent : baseEnd_1187402 < baseStart_1187402 := by decide
  rcases family_descends (prefixWord ++ tailWord_1187402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1187433 : List Nat := [1, 2, 1, 1, 1, 4, 4, 2, 5]
def baseStart_1187433 : Nat := 118140960795 + 1187433 * 2 ^ 59
def prefixEnd_1187433 : Nat := 4983230072969 + 3 ^ 40 * 1187433 * 2
def baseEnd_1187433 : Nat := 270988388449047954056267

theorem tailTrace_1187433 : CollatzResearch.WordTrace tailWord_1187433 prefixEnd_1187433 270988388449047954056267 := by
  unfold tailWord_1187433
  simp only [CollatzResearch.WordTrace]
  refine ⟨43309239507140513255982953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28872826338093675503988635 43309239507140513255982953)
  ·
    refine ⟨32481929630355384941987215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43309239507140513255982953 32481929630355384941987215)
    ·
      refine ⟨48722894445533077412980823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32481929630355384941987215 48722894445533077412980823)
      ·
        refine ⟨73084341668299616119471235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48722894445533077412980823 73084341668299616119471235)
        ·
          refine ⟨109626512502449424179206853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73084341668299616119471235 109626512502449424179206853)
          ·
            refine ⟨20554971094209267033601285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 109626512502449424179206853 20554971094209267033601285)
            ·
              refine ⟨3854057080164237568800241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20554971094209267033601285 3854057080164237568800241)
              ·
                refine ⟨2890542810123178176600181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3854057080164237568800241 2890542810123178176600181)
                ·
                  refine ⟨270988388449047954056267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2890542810123178176600181 270988388449047954056267)
                  ·
                    rfl

theorem cell21_1187433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 2, 5].length) (baseStart_1187433 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1187433 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1187433 prefixEnd_1187433 := by exact prefixLift 1187433
  have htrace : WordTrace (prefixWord ++ tailWord_1187433) baseStart_1187433 baseEnd_1187433 := by
    simpa [prefixWord, tailWord_1187433, baseEnd_1187433] using wordTrace_append hprefix tailTrace_1187433
  have hstable : (prefixWord ++ tailWord_1187433).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1187433).length < 2 ^ (prefixWord ++ tailWord_1187433).sum := by decide
  have hdescent : baseEnd_1187433 < baseStart_1187433 := by decide
  rcases family_descends (prefixWord ++ tailWord_1187433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1187450 : List Nat := [3, 1, 1, 1, 1, 1, 1, 9, 3]
def baseStart_1187450 : Nat := 118140960795 + 1187450 * 2 ^ 59
def prefixEnd_1187450 : Nat := 4983230072969 + 3 ^ 40 * 1187450 * 2
def baseEnd_1187450 : Nat := 270992268080659702272899

theorem tailTrace_1187450 : CollatzResearch.WordTrace tailWord_1187450 prefixEnd_1187450 270992268080659702272899 := by
  unfold tailWord_1187450
  simp only [CollatzResearch.WordTrace]
  refine ⟨10827464887019731289837951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28873239698719283439567869 10827464887019731289837951)
  ·
    refine ⟨16241197330529596934756927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10827464887019731289837951 16241197330529596934756927)
    ·
      refine ⟨24361795995794395402135391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16241197330529596934756927 24361795995794395402135391)
      ·
        refine ⟨36542693993691593103203087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24361795995794395402135391 36542693993691593103203087)
        ·
          refine ⟨54814040990537389654804631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36542693993691593103203087 54814040990537389654804631)
          ·
            refine ⟨82221061485806084482206947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54814040990537389654804631 82221061485806084482206947)
            ·
              refine ⟨123331592228709126723310421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82221061485806084482206947 123331592228709126723310421)
              ·
                refine ⟨722646048215092539394397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 123331592228709126723310421 722646048215092539394397)
                ·
                  refine ⟨270992268080659702272899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 722646048215092539394397 270992268080659702272899)
                  ·
                    rfl

theorem cell21_1187450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 9, 3].length) (baseStart_1187450 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1187450 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1187450 prefixEnd_1187450 := by exact prefixLift 1187450
  have htrace : WordTrace (prefixWord ++ tailWord_1187450) baseStart_1187450 baseEnd_1187450 := by
    simpa [prefixWord, tailWord_1187450, baseEnd_1187450] using wordTrace_append hprefix tailTrace_1187450
  have hstable : (prefixWord ++ tailWord_1187450).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1187450).length < 2 ^ (prefixWord ++ tailWord_1187450).sum := by decide
  have hdescent : baseEnd_1187450 < baseStart_1187450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1187450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1187467 : List Nat := [1, 1, 1, 1, 4, 1, 7, 2, 3]
def baseStart_1187467 : Nat := 118140960795 + 1187467 * 2 ^ 59
def prefixEnd_1187467 : Nat := 4983230072969 + 3 ^ 40 * 1187467 * 2
def baseEnd_1187467 : Nat := 270996147712271450489531

theorem tailTrace_1187467 : CollatzResearch.WordTrace tailWord_1187467 prefixEnd_1187467 270996147712271450489531 := by
  unfold tailWord_1187467
  simp only [CollatzResearch.WordTrace]
  refine ⟨43310479589017337062720655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28873653059344891375147103 43310479589017337062720655)
  ·
    refine ⟨64965719383526005594080983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43310479589017337062720655 64965719383526005594080983)
    ·
      refine ⟨97448579075289008391121475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 64965719383526005594080983 97448579075289008391121475)
      ·
        refine ⟨146172868612933512586682213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97448579075289008391121475 146172868612933512586682213)
        ·
          refine ⟨27407412864925033610002915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 146172868612933512586682213 27407412864925033610002915)
          ·
            refine ⟨41111119297387550415004373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27407412864925033610002915 41111119297387550415004373)
            ·
              refine ⟨963541858532520712851665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 41111119297387550415004373 963541858532520712851665)
              ·
                refine ⟨722656393899390534638749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 963541858532520712851665 722656393899390534638749)
                ·
                  refine ⟨270996147712271450489531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 722656393899390534638749 270996147712271450489531)
                  ·
                    rfl

theorem cell21_1187467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 7, 2, 3].length) (baseStart_1187467 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1187467 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1187467 prefixEnd_1187467 := by exact prefixLift 1187467
  have htrace : WordTrace (prefixWord ++ tailWord_1187467) baseStart_1187467 baseEnd_1187467 := by
    simpa [prefixWord, tailWord_1187467, baseEnd_1187467] using wordTrace_append hprefix tailTrace_1187467
  have hstable : (prefixWord ++ tailWord_1187467).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1187467).length < 2 ^ (prefixWord ++ tailWord_1187467).sum := by decide
  have hdescent : baseEnd_1187467 < baseStart_1187467 := by decide
  rcases family_descends (prefixWord ++ tailWord_1187467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1187574 : List Nat := [5, 1, 1, 1, 1, 5, 1, 2, 4]
def baseStart_1187574 : Nat := 118140960795 + 1187574 * 2 ^ 59
def prefixEnd_1187574 : Nat := 4983230072969 + 3 ^ 40 * 1187574 * 2
def baseEnd_1187574 : Nat := 271020566570063042205979

theorem tailTrace_1187574 : CollatzResearch.WordTrace tailWord_1187574 prefixEnd_1187574 271020566570063042205979 := by
  unfold tailWord_1187574
  simp only [CollatzResearch.WordTrace]
  refine ⟨2707148887476855896054111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 28876254799753129557910517 2707148887476855896054111)
  ·
    refine ⟨4060723331215283844081167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2707148887476855896054111 4060723331215283844081167)
    ·
      refine ⟨6091084996822925766121751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4060723331215283844081167 6091084996822925766121751)
      ·
        refine ⟨9136627495234388649182627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6091084996822925766121751 9136627495234388649182627)
        ·
          refine ⟨13704941242851582973773941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9136627495234388649182627 13704941242851582973773941)
          ·
            refine ⟨1284838241517335903791307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13704941242851582973773941 1284838241517335903791307)
            ·
              refine ⟨1927257362276003855686961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1284838241517335903791307 1927257362276003855686961)
              ·
                refine ⟨1445443021707002891765221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1927257362276003855686961 1445443021707002891765221)
                ·
                  refine ⟨271020566570063042205979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1445443021707002891765221 271020566570063042205979)
                  ·
                    rfl

theorem cell21_1187574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 1, 2, 4].length) (baseStart_1187574 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1187574 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1187574 prefixEnd_1187574 := by exact prefixLift 1187574
  have htrace : WordTrace (prefixWord ++ tailWord_1187574) baseStart_1187574 baseEnd_1187574 := by
    simpa [prefixWord, tailWord_1187574, baseEnd_1187574] using wordTrace_append hprefix tailTrace_1187574
  have hstable : (prefixWord ++ tailWord_1187574).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1187574).length < 2 ^ (prefixWord ++ tailWord_1187574).sum := by decide
  have hdescent : baseEnd_1187574 < baseStart_1187574 := by decide
  rcases family_descends (prefixWord ++ tailWord_1187574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1187585 : List Nat := [1, 2, 4, 1, 1, 1, 3, 3, 5]
def baseStart_1187585 : Nat := 118140960795 + 1187585 * 2 ^ 59
def prefixEnd_1187585 : Nat := 4983230072969 + 3 ^ 40 * 1187585 * 2
def baseEnd_1187585 : Nat := 271023076919929467522623

theorem tailTrace_1187585 : CollatzResearch.WordTrace tailWord_1187585 prefixEnd_1187585 271023076919929467522623 := by
  unfold tailWord_1187585
  simp only [CollatzResearch.WordTrace]
  refine ⟨43314783402589843215516209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28876522268393228810344139 43314783402589843215516209)
  ·
    refine ⟨32486087551942382411637157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43314783402589843215516209 32486087551942382411637157)
    ·
      refine ⟨6091141415989196702181967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32486087551942382411637157 6091141415989196702181967)
      ·
        refine ⟨9136712123983795053272951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6091141415989196702181967 9136712123983795053272951)
        ·
          refine ⟨13705068185975692579909427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9136712123983795053272951 13705068185975692579909427)
          ·
            refine ⟨20557602278963538869864141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13705068185975692579909427 20557602278963538869864141)
            ·
              refine ⟨7709100854611327076199053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20557602278963538869864141 7709100854611327076199053)
              ·
                refine ⟨2890912820479247653574645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7709100854611327076199053 2890912820479247653574645)
                ·
                  refine ⟨271023076919929467522623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2890912820479247653574645 271023076919929467522623)
                  ·
                    rfl

theorem cell21_1187585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 3, 5].length) (baseStart_1187585 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1187585 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1187585 prefixEnd_1187585 := by exact prefixLift 1187585
  have htrace : WordTrace (prefixWord ++ tailWord_1187585) baseStart_1187585 baseEnd_1187585 := by
    simpa [prefixWord, tailWord_1187585, baseEnd_1187585] using wordTrace_append hprefix tailTrace_1187585
  have hstable : (prefixWord ++ tailWord_1187585).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1187585).length < 2 ^ (prefixWord ++ tailWord_1187585).sum := by decide
  have hdescent : baseEnd_1187585 < baseStart_1187585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1187585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1187647 : List Nat := [1, 1, 2, 2, 6, 1, 2, 6]
def baseStart_1187647 : Nat := 118140960795 + 1187647 * 2 ^ 59
def prefixEnd_1187647 : Nat := 4983230072969 + 3 ^ 40 * 1187647 * 2
def baseEnd_1187647 : Nat := 90345742054877045829721

theorem tailTrace_1187647 : CollatzResearch.WordTrace tailWord_1187647 prefixEnd_1187647 90345742054877045829721 := by
  unfold tailWord_1187647
  simp only [CollatzResearch.WordTrace]
  refine ⟨43317044728365227804273195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28878029818910151869515463 43317044728365227804273195)
  ·
    refine ⟨64975567092547841706409793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43317044728365227804273195 64975567092547841706409793)
    ·
      refine ⟨48731675319410881279807345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64975567092547841706409793 48731675319410881279807345)
      ·
        refine ⟨36548756489558160959855509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48731675319410881279807345 36548756489558160959855509)
        ·
          refine ⟨1713222960448038794993227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 36548756489558160959855509 1713222960448038794993227)
          ·
            refine ⟨2569834440672058192489841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1713222960448038794993227 2569834440672058192489841)
            ·
              refine ⟨1927375830504043644367381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2569834440672058192489841 1927375830504043644367381)
              ·
                refine ⟨90345742054877045829721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1927375830504043644367381 90345742054877045829721)
                ·
                  rfl

theorem cell21_1187647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 2, 6].length) (baseStart_1187647 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1187647 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1187647 prefixEnd_1187647 := by exact prefixLift 1187647
  have htrace : WordTrace (prefixWord ++ tailWord_1187647) baseStart_1187647 baseEnd_1187647 := by
    simpa [prefixWord, tailWord_1187647, baseEnd_1187647] using wordTrace_append hprefix tailTrace_1187647
  have hstable : (prefixWord ++ tailWord_1187647).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1187647).length < 2 ^ (prefixWord ++ tailWord_1187647).sum := by decide
  have hdescent : baseEnd_1187647 < baseStart_1187647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1187647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1187692 : List Nat := [2, 2, 1, 1, 4, 2, 1, 4, 4]
def baseStart_1187692 : Nat := 118140960795 + 1187692 * 2 ^ 59
def prefixEnd_1187692 : Nat := 4983230072969 + 3 ^ 40 * 1187692 * 2
def baseEnd_1187692 : Nat := 271047495777721059239071

theorem tailTrace_1187692 : CollatzResearch.WordTrace tailWord_1187692 prefixEnd_1187692 271047495777721059239071 := by
  unfold tailWord_1187692
  simp only [CollatzResearch.WordTrace]
  refine ⟨21659343006601100244830665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28879124008801466993107553 21659343006601100244830665)
  ·
    refine ⟨16244507254950825183622999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21659343006601100244830665 16244507254950825183622999)
    ·
      refine ⟨24366760882426237775434499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16244507254950825183622999 24366760882426237775434499)
      ·
        refine ⟨36550141323639356663151749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24366760882426237775434499 36550141323639356663151749)
        ·
          refine ⟨6853151498182379374340953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36550141323639356663151749 6853151498182379374340953)
          ·
            refine ⟨5139863623636784530755715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6853151498182379374340953 5139863623636784530755715)
            ·
              refine ⟨7709795435455176796133573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5139863623636784530755715 7709795435455176796133573)
              ·
                refine ⟨1445586644147845649275045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7709795435455176796133573 1445586644147845649275045)
                ·
                  refine ⟨271047495777721059239071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1445586644147845649275045 271047495777721059239071)
                  ·
                    rfl

theorem cell21_1187692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 4].length) (baseStart_1187692 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1187692 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1187692 prefixEnd_1187692 := by exact prefixLift 1187692
  have htrace : WordTrace (prefixWord ++ tailWord_1187692) baseStart_1187692 baseEnd_1187692 := by
    simpa [prefixWord, tailWord_1187692, baseEnd_1187692] using wordTrace_append hprefix tailTrace_1187692
  have hstable : (prefixWord ++ tailWord_1187692).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1187692).length < 2 ^ (prefixWord ++ tailWord_1187692).sum := by decide
  have hdescent : baseEnd_1187692 < baseStart_1187692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1187692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1187706 : List Nat := [3, 1, 1, 1, 1, 1, 7, 6]
def baseStart_1187706 : Nat := 118140960795 + 1187706 * 2 ^ 59
def prefixEnd_1187706 : Nat := 4983230072969 + 3 ^ 40 * 1187706 * 2
def baseEnd_1187706 : Nat := 90350230256153382001903

theorem tailTrace_1187706 : CollatzResearch.WordTrace tailWord_1187706 prefixEnd_1187706 90350230256153382001903 := by
  unfold tailWord_1187706
  simp only [CollatzResearch.WordTrace]
  refine ⟨10829799158787870220167743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28879464423434320587113981 10829799158787870220167743)
  ·
    refine ⟨16244698738181805330251615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10829799158787870220167743 16244698738181805330251615)
    ·
      refine ⟨24367048107272707995377423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16244698738181805330251615 24367048107272707995377423)
      ·
        refine ⟨36550572160909061993066135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24367048107272707995377423 36550572160909061993066135)
        ·
          refine ⟨54825858241363592989599203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36550572160909061993066135 54825858241363592989599203)
          ·
            refine ⟨82238787362045389484398805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54825858241363592989599203 82238787362045389484398805)
            ·
              refine ⟨1927471578797938816040597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 82238787362045389484398805 1927471578797938816040597)
              ·
                refine ⟨90350230256153382001903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1927471578797938816040597 90350230256153382001903)
                ·
                  rfl

theorem cell21_1187706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 7, 6].length) (baseStart_1187706 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1187706 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1187706 prefixEnd_1187706 := by exact prefixLift 1187706
  have htrace : WordTrace (prefixWord ++ tailWord_1187706) baseStart_1187706 baseEnd_1187706 := by
    simpa [prefixWord, tailWord_1187706, baseEnd_1187706] using wordTrace_append hprefix tailTrace_1187706
  have hstable : (prefixWord ++ tailWord_1187706).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1187706).length < 2 ^ (prefixWord ++ tailWord_1187706).sum := by decide
  have hdescent : baseEnd_1187706 < baseStart_1187706 := by decide
  rcases family_descends (prefixWord ++ tailWord_1187706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1187861 : List Nat := [1, 3, 2, 1, 5, 1, 2, 2, 4]
def baseStart_1187861 : Nat := 118140960795 + 1187861 * 2 ^ 59
def prefixEnd_1187861 : Nat := 4983230072969 + 3 ^ 40 * 1187861 * 2
def baseEnd_1187861 : Nat := 271086063880214320922059

theorem tailTrace_1187861 : CollatzResearch.WordTrace tailWord_1187861 prefixEnd_1187861 271086063880214320922059 := by
  unfold tailWord_1187861
  simp only [CollatzResearch.WordTrace]
  refine ⟨43324849949589942352563437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28883233299726628235042291 43324849949589942352563437)
  ·
    refine ⟨16246818731096228382211289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43324849949589942352563437 16246818731096228382211289)
    ·
      refine ⟨12185114048322171286658467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16246818731096228382211289 12185114048322171286658467)
      ·
        refine ⟨18277671072483256929987701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12185114048322171286658467 18277671072483256929987701)
        ·
          refine ⟨1713531663045305337186347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18277671072483256929987701 1713531663045305337186347)
          ·
            refine ⟨2570297494567958005779521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1713531663045305337186347 2570297494567958005779521)
            ·
              refine ⟨1927723120925968504334641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2570297494567958005779521 1927723120925968504334641)
              ·
                refine ⟨1445792340694476378250981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1927723120925968504334641 1445792340694476378250981)
                ·
                  refine ⟨271086063880214320922059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1445792340694476378250981 271086063880214320922059)
                  ·
                    rfl

theorem cell21_1187861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 2, 2, 4].length) (baseStart_1187861 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1187861 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1187861 prefixEnd_1187861 := by exact prefixLift 1187861
  have htrace : WordTrace (prefixWord ++ tailWord_1187861) baseStart_1187861 baseEnd_1187861 := by
    simpa [prefixWord, tailWord_1187861, baseEnd_1187861] using wordTrace_append hprefix tailTrace_1187861
  have hstable : (prefixWord ++ tailWord_1187861).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1187861).length < 2 ^ (prefixWord ++ tailWord_1187861).sum := by decide
  have hdescent : baseEnd_1187861 < baseStart_1187861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1187861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1187889 : List Nat := [1, 2, 2, 3, 1, 4, 1, 2, 5]
def baseStart_1187889 : Nat := 118140960795 + 1187889 * 2 ^ 59
def prefixEnd_1187889 : Nat := 4983230072969 + 3 ^ 40 * 1187889 * 2
def baseEnd_1187889 : Nat := 271092453861692494455335

theorem tailTrace_1187889 : CollatzResearch.WordTrace tailWord_1187889 prefixEnd_1187889 271092453861692494455335 := by
  unfold tailWord_1187889
  simp only [CollatzResearch.WordTrace]
  refine ⟨43325871193488503134582721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28883914128992335423055147 43325871193488503134582721)
  ·
    refine ⟨32494403395116377350937041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43325871193488503134582721 32494403395116377350937041)
    ·
      refine ⟨24370802546337283013202781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32494403395116377350937041 24370802546337283013202781)
      ·
        refine ⟨9139050954876481129951043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24370802546337283013202781 9139050954876481129951043)
        ·
          refine ⟨13708576432314721694926565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9139050954876481129951043 13708576432314721694926565)
          ·
            refine ⟨2570358081059010317798731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13708576432314721694926565 2570358081059010317798731)
            ·
              refine ⟨3855537121588515476698097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2570358081059010317798731 3855537121588515476698097)
              ·
                refine ⟨2891652841191386607523573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3855537121588515476698097 2891652841191386607523573)
                ·
                  refine ⟨271092453861692494455335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2891652841191386607523573 271092453861692494455335)
                  ·
                    rfl

theorem cell21_1187889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 2, 5].length) (baseStart_1187889 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1187889 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1187889 prefixEnd_1187889 := by exact prefixLift 1187889
  have htrace : WordTrace (prefixWord ++ tailWord_1187889) baseStart_1187889 baseEnd_1187889 := by
    simpa [prefixWord, tailWord_1187889, baseEnd_1187889] using wordTrace_append hprefix tailTrace_1187889
  have hstable : (prefixWord ++ tailWord_1187889).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1187889).length < 2 ^ (prefixWord ++ tailWord_1187889).sum := by decide
  have hdescent : baseEnd_1187889 < baseStart_1187889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1187889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1187951 : List Nat := [1, 1, 2, 1, 3, 6, 2, 5]
def baseStart_1187951 : Nat := 118140960795 + 1187951 * 2 ^ 59
def prefixEnd_1187951 : Nat := 4983230072969 + 3 ^ 40 * 1187951 * 2
def baseEnd_1187951 : Nat := 90368867702131388140625

theorem tailTrace_1187951 : CollatzResearch.WordTrace tailWord_1187951 prefixEnd_1187951 90368867702131388140625 := by
  unfold tailWord_1187951
  simp only [CollatzResearch.WordTrace]
  refine ⟨43328132519263887723339707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28885421679509258482226471 43328132519263887723339707)
  ·
    refine ⟨64992198778895831585009561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43328132519263887723339707 64992198778895831585009561)
    ·
      refine ⟨48744149084171873688757171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 64992198778895831585009561 48744149084171873688757171)
      ·
        refine ⟨73116223626257810533135757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48744149084171873688757171 73116223626257810533135757)
        ·
          refine ⟨27418583859846678949925909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73116223626257810533135757 27418583859846678949925909)
          ·
            refine ⟨1285246118430313075777777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 27418583859846678949925909 1285246118430313075777777)
            ·
              refine ⟨963934588822734806833333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1285246118430313075777777 963934588822734806833333)
              ·
                refine ⟨90368867702131388140625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 963934588822734806833333 90368867702131388140625)
                ·
                  rfl

theorem cell21_1187951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 2, 5].length) (baseStart_1187951 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1187951 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1187951 prefixEnd_1187951 := by exact prefixLift 1187951
  have htrace : WordTrace (prefixWord ++ tailWord_1187951) baseStart_1187951 baseEnd_1187951 := by
    simpa [prefixWord, tailWord_1187951, baseEnd_1187951] using wordTrace_append hprefix tailTrace_1187951
  have hstable : (prefixWord ++ tailWord_1187951).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1187951).length < 2 ^ (prefixWord ++ tailWord_1187951).sum := by decide
  have hdescent : baseEnd_1187951 < baseStart_1187951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1187951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1187988 : List Nat := [2, 4, 2, 3, 2, 1, 2, 1, 4]
def baseStart_1187988 : Nat := 118140960795 + 1187988 * 2 ^ 59
def prefixEnd_1187988 : Nat := 4983230072969 + 3 ^ 40 * 1187988 * 2
def baseEnd_1187988 : Nat := 271115047010490322305133

theorem tailTrace_1187988 : CollatzResearch.WordTrace tailWord_1187988 prefixEnd_1187988 271115047010490322305133 := by
  unfold tailWord_1187988
  simp only [CollatzResearch.WordTrace]
  refine ⟨21664741010064921521218309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28886321346753228694957745 21664741010064921521218309)
  ·
    refine ⟨4062138939387172785228433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21664741010064921521218309 4062138939387172785228433)
    ·
      refine ⟨3046604204540379588921325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4062138939387172785228433 3046604204540379588921325)
      ·
        refine ⟨1142476576702642345845497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3046604204540379588921325 1142476576702642345845497)
        ·
          refine ⟨856857432526981759384123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1142476576702642345845497 856857432526981759384123)
          ·
            refine ⟨1285286148790472639076185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 856857432526981759384123 1285286148790472639076185)
            ·
              refine ⟨963964611592854479307139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1285286148790472639076185 963964611592854479307139)
              ·
                refine ⟨1445946917389281718960709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 963964611592854479307139 1445946917389281718960709)
                ·
                  refine ⟨271115047010490322305133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1445946917389281718960709 271115047010490322305133)
                  ·
                    rfl

theorem cell21_1187988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 2, 1, 4].length) (baseStart_1187988 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1187988 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1187988 prefixEnd_1187988 := by exact prefixLift 1187988
  have htrace : WordTrace (prefixWord ++ tailWord_1187988) baseStart_1187988 baseEnd_1187988 := by
    simpa [prefixWord, tailWord_1187988, baseEnd_1187988] using wordTrace_append hprefix tailTrace_1187988
  have hstable : (prefixWord ++ tailWord_1187988).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1187988).length < 2 ^ (prefixWord ++ tailWord_1187988).sum := by decide
  have hdescent : baseEnd_1187988 < baseStart_1187988 := by decide
  rcases family_descends (prefixWord ++ tailWord_1187988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1187996 : List Nat := [2, 2, 3, 2, 1, 1, 3, 3, 4]
def baseStart_1187996 : Nat := 118140960795 + 1187996 * 2 ^ 59
def prefixEnd_1187996 : Nat := 4983230072969 + 3 ^ 40 * 1187996 * 2
def baseEnd_1187996 : Nat := 271116872719484086171783

theorem tailTrace_1187996 : CollatzResearch.WordTrace tailWord_1187996 prefixEnd_1187996 271116872719484086171783 := by
  unfold tailWord_1187996
  simp only [CollatzResearch.WordTrace]
  refine ⟨21664886902050430204363921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28886515869400573605818561 21664886902050430204363921)
  ·
    refine ⟨16248665176537822653272941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21664886902050430204363921 16248665176537822653272941)
    ·
      refine ⟨6093249441201683494977353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16248665176537822653272941 6093249441201683494977353)
      ·
        refine ⟨4569937080901262621233015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6093249441201683494977353 4569937080901262621233015)
        ·
          refine ⟨6854905621351893931849523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4569937080901262621233015 6854905621351893931849523)
          ·
            refine ⟨10282358432027840897774285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6854905621351893931849523 10282358432027840897774285)
            ·
              refine ⟨3855884412010440336665357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10282358432027840897774285 3855884412010440336665357)
              ·
                refine ⟨1445956654503915126249509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3855884412010440336665357 1445956654503915126249509)
                ·
                  refine ⟨271116872719484086171783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1445956654503915126249509 271116872719484086171783)
                  ·
                    rfl

theorem cell21_1187996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 3, 4].length) (baseStart_1187996 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1187996 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1187996 prefixEnd_1187996 := by exact prefixLift 1187996
  have htrace : WordTrace (prefixWord ++ tailWord_1187996) baseStart_1187996 baseEnd_1187996 := by
    simpa [prefixWord, tailWord_1187996, baseEnd_1187996] using wordTrace_append hprefix tailTrace_1187996
  have hstable : (prefixWord ++ tailWord_1187996).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1187996).length < 2 ^ (prefixWord ++ tailWord_1187996).sum := by decide
  have hdescent : baseEnd_1187996 < baseStart_1187996 := by decide
  rcases family_descends (prefixWord ++ tailWord_1187996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1188033 : List Nat := [1, 2, 6, 1, 2, 2, 2, 2, 3]
def baseStart_1188033 : Nat := 118140960795 + 1188033 * 2 ^ 59
def prefixEnd_1188033 : Nat := 4983230072969 + 3 ^ 40 * 1188033 * 2
def baseEnd_1188033 : Nat := 271125316623580244055041

theorem tailTrace_1188033 : CollatzResearch.WordTrace tailWord_1188033 prefixEnd_1188033 271125316623580244055041 := by
  unfold tailWord_1188033
  simp only [CollatzResearch.WordTrace]
  refine ⟨43331123304966815727824753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28887415536644543818549835 43331123304966815727824753)
  ·
    refine ⟨32498342478725111795868565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43331123304966815727824753 32498342478725111795868565)
    ·
      refine ⟨1523359803690239615431339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 32498342478725111795868565 1523359803690239615431339)
      ·
        refine ⟨2285039705535359423147009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1523359803690239615431339 2285039705535359423147009)
        ·
          refine ⟨1713779779151519567360257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2285039705535359423147009 1713779779151519567360257)
          ·
            refine ⟨1285334834363639675520193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1713779779151519567360257 1285334834363639675520193)
            ·
              refine ⟨964001125772729756640145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1285334834363639675520193 964001125772729756640145)
              ·
                refine ⟨723000844329547317480109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 964001125772729756640145 723000844329547317480109)
                ·
                  refine ⟨271125316623580244055041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 723000844329547317480109 271125316623580244055041)
                  ·
                    rfl

theorem cell21_1188033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 2, 2, 3].length) (baseStart_1188033 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1188033 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1188033 prefixEnd_1188033 := by exact prefixLift 1188033
  have htrace : WordTrace (prefixWord ++ tailWord_1188033) baseStart_1188033 baseEnd_1188033 := by
    simpa [prefixWord, tailWord_1188033, baseEnd_1188033] using wordTrace_append hprefix tailTrace_1188033
  have hstable : (prefixWord ++ tailWord_1188033).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1188033).length < 2 ^ (prefixWord ++ tailWord_1188033).sum := by decide
  have hdescent : baseEnd_1188033 < baseStart_1188033 := by decide
  rcases family_descends (prefixWord ++ tailWord_1188033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1188044 : List Nat := [2, 2, 1, 6, 1, 2, 1, 6]
def baseStart_1188044 : Nat := 118140960795 + 1188044 * 2 ^ 59
def prefixEnd_1188044 : Nat := 4983230072969 + 3 ^ 40 * 1188044 * 2
def baseEnd_1188044 : Nat := 90375942324482223123895

theorem tailTrace_1188044 : CollatzResearch.WordTrace tailWord_1188044 prefixEnd_1188044 90375942324482223123895 := by
  unfold tailWord_1188044
  simp only [CollatzResearch.WordTrace]
  refine ⟨21665762253963482303237593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28887683005284643070983457 21665762253963482303237593)
  ·
    refine ⟨16249321690472611727428195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21665762253963482303237593 16249321690472611727428195)
    ·
      refine ⟨24373982535708917591142293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16249321690472611727428195 24373982535708917591142293)
      ·
        refine ⟨1142530431361355512084795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 24373982535708917591142293 1142530431361355512084795)
        ·
          refine ⟨1713795647042033268127193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1142530431361355512084795 1713795647042033268127193)
          ·
            refine ⟨1285346735281524951095395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1713795647042033268127193 1285346735281524951095395)
            ·
              refine ⟨1928020102922287426643093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1285346735281524951095395 1928020102922287426643093)
              ·
                refine ⟨90375942324482223123895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1928020102922287426643093 90375942324482223123895)
                ·
                  rfl

theorem cell21_1188044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 1, 6].length) (baseStart_1188044 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1188044 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1188044 prefixEnd_1188044 := by exact prefixLift 1188044
  have htrace : WordTrace (prefixWord ++ tailWord_1188044) baseStart_1188044 baseEnd_1188044 := by
    simpa [prefixWord, tailWord_1188044, baseEnd_1188044] using wordTrace_append hprefix tailTrace_1188044
  have hstable : (prefixWord ++ tailWord_1188044).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1188044).length < 2 ^ (prefixWord ++ tailWord_1188044).sum := by decide
  have hdescent : baseEnd_1188044 < baseStart_1188044 := by decide
  rcases family_descends (prefixWord ++ tailWord_1188044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1188148 : List Nat := [2, 5, 1, 1, 1, 2, 2, 1, 6]
def baseStart_1188148 : Nat := 118140960795 + 1188148 * 2 ^ 59
def prefixEnd_1188148 : Nat := 4983230072969 + 3 ^ 40 * 1188148 * 2
def baseEnd_1188148 : Nat := 271151561190365599638139

theorem tailTrace_1188148 : CollatzResearch.WordTrace tailWord_1188148 prefixEnd_1188148 271151561190365599638139 := by
  unfold tailWord_1188148
  simp only [CollatzResearch.WordTrace]
  refine ⟨21667658849775095184130549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28890211799700126912174065 21667658849775095184130549)
  ·
    refine ⟨2031343017166415173512239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21667658849775095184130549 2031343017166415173512239)
    ·
      refine ⟨3047014525749622760268359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2031343017166415173512239 3047014525749622760268359)
      ·
        refine ⟨4570521788624434140402539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3047014525749622760268359 4570521788624434140402539)
        ·
          refine ⟨6855782682936651210603809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4570521788624434140402539 6855782682936651210603809)
          ·
            refine ⟨5141837012202488407952857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6855782682936651210603809 5141837012202488407952857)
            ·
              refine ⟨3856377759151866305964643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5141837012202488407952857 3856377759151866305964643)
              ·
                refine ⟨5784566638727799458946965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3856377759151866305964643 5784566638727799458946965)
                ·
                  refine ⟨271151561190365599638139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5784566638727799458946965 271151561190365599638139)
                  ·
                    rfl

theorem cell21_1188148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_1188148 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1188148 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1188148 prefixEnd_1188148 := by exact prefixLift 1188148
  have htrace : WordTrace (prefixWord ++ tailWord_1188148) baseStart_1188148 baseEnd_1188148 := by
    simpa [prefixWord, tailWord_1188148, baseEnd_1188148] using wordTrace_append hprefix tailTrace_1188148
  have hstable : (prefixWord ++ tailWord_1188148).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1188148).length < 2 ^ (prefixWord ++ tailWord_1188148).sum := by decide
  have hdescent : baseEnd_1188148 < baseStart_1188148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1188148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1188210 : List Nat := [3, 2, 1, 2, 1, 4, 1, 4, 3]
def baseStart_1188210 : Nat := 118140960795 + 1188210 * 2 ^ 59
def prefixEnd_1188210 : Nat := 4983230072969 + 3 ^ 40 * 1188210 * 2
def baseEnd_1188210 : Nat := 271165710435067269604679

theorem tailTrace_1188210 : CollatzResearch.WordTrace tailWord_1188210 prefixEnd_1188210 271165710435067269604679 := by
  unfold tailWord_1188210
  simp only [CollatzResearch.WordTrace]
  refine ⟨10834394756331393739254521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28891719350217049971345389 10834394756331393739254521)
  ·
    refine ⟨8125796067248545304440891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10834394756331393739254521 8125796067248545304440891)
    ·
      refine ⟨12188694100872817956661337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8125796067248545304440891 12188694100872817956661337)
      ·
        refine ⟨9141520575654613467496003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12188694100872817956661337 9141520575654613467496003)
        ·
          refine ⟨13712280863481920201244005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9141520575654613467496003 13712280863481920201244005)
          ·
            refine ⟨2571052661902860037733251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13712280863481920201244005 2571052661902860037733251)
            ·
              refine ⟨3856578992854290056599877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2571052661902860037733251 3856578992854290056599877)
              ·
                refine ⟨723108561160179385612477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3856578992854290056599877 723108561160179385612477)
                ·
                  refine ⟨271165710435067269604679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 723108561160179385612477 271165710435067269604679)
                  ·
                    rfl

theorem cell21_1188210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 4, 3].length) (baseStart_1188210 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1188210 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1188210 prefixEnd_1188210 := by exact prefixLift 1188210
  have htrace : WordTrace (prefixWord ++ tailWord_1188210) baseStart_1188210 baseEnd_1188210 := by
    simpa [prefixWord, tailWord_1188210, baseEnd_1188210] using wordTrace_append hprefix tailTrace_1188210
  have hstable : (prefixWord ++ tailWord_1188210).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1188210).length < 2 ^ (prefixWord ++ tailWord_1188210).sum := by decide
  have hdescent : baseEnd_1188210 < baseStart_1188210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1188210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1188376 : List Nat := [2, 1, 2, 3, 3, 2, 2, 2, 4]
def baseStart_1188376 : Nat := 118140960795 + 1188376 * 2 ^ 59
def prefixEnd_1188376 : Nat := 4983230072969 + 3 ^ 40 * 1188376 * 2
def baseEnd_1188376 : Nat := 271203593896687869837673

theorem tailTrace_1188376 : CollatzResearch.WordTrace tailWord_1188376 prefixEnd_1188376 271203593896687869837673 := by
  unfold tailWord_1188376
  simp only [CollatzResearch.WordTrace]
  refine ⟨21671816771362092653780491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28895755695149456871707321 21671816771362092653780491)
  ·
    refine ⟨32507725157043138980670737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21671816771362092653780491 32507725157043138980670737)
    ·
      refine ⟨24380793867782354235503053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32507725157043138980670737 24380793867782354235503053)
      ·
        refine ⟨9142797700418382838313645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24380793867782354235503053 9142797700418382838313645)
        ·
          refine ⟨3428549137656893564367617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9142797700418382838313645 3428549137656893564367617)
          ·
            refine ⟨2571411853242670173275713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3428549137656893564367617 2571411853242670173275713)
            ·
              refine ⟨1928558889932002629956785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2571411853242670173275713 1928558889932002629956785)
              ·
                refine ⟨1446419167449001972467589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1928558889932002629956785 1446419167449001972467589)
                ·
                  refine ⟨271203593896687869837673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1446419167449001972467589 271203593896687869837673)
                  ·
                    rfl

theorem cell21_1188376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 2, 2, 4].length) (baseStart_1188376 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1188376 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1188376 prefixEnd_1188376 := by exact prefixLift 1188376
  have htrace : WordTrace (prefixWord ++ tailWord_1188376) baseStart_1188376 baseEnd_1188376 := by
    simpa [prefixWord, tailWord_1188376, baseEnd_1188376] using wordTrace_append hprefix tailTrace_1188376
  have hstable : (prefixWord ++ tailWord_1188376).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1188376).length < 2 ^ (prefixWord ++ tailWord_1188376).sum := by decide
  have hdescent : baseEnd_1188376 < baseStart_1188376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1188376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1188421 : List Nat := [1, 3, 1, 1, 1, 5, 1, 5, 3]
def baseStart_1188421 : Nat := 118140960795 + 1188421 * 2 ^ 59
def prefixEnd_1188421 : Nat := 4983230072969 + 3 ^ 40 * 1188421 * 2
def baseEnd_1188421 : Nat := 271213863509777791587581

theorem tailTrace_1188421 : CollatzResearch.WordTrace tailWord_1188421 prefixEnd_1188421 271213863509777791587581 := by
  unfold tailWord_1188421
  simp only [CollatzResearch.WordTrace]
  refine ⟨43345274827561157992949117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28896849885040771995299411 43345274827561157992949117)
  ·
    refine ⟨16254478060335434247355919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43345274827561157992949117 16254478060335434247355919)
    ·
      refine ⟨24381717090503151371033879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16254478060335434247355919 24381717090503151371033879)
      ·
        refine ⟨36572575635754727056550819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24381717090503151371033879 36572575635754727056550819)
        ·
          refine ⟨54858863453632090584826229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36572575635754727056550819 54858863453632090584826229)
          ·
            refine ⟨5143018448778008492327459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 54858863453632090584826229 5143018448778008492327459)
            ·
              refine ⟨7714527673167012738491189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5143018448778008492327459 7714527673167012738491189)
              ·
                refine ⟨723236969359407444233549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7714527673167012738491189 723236969359407444233549)
                ·
                  refine ⟨271213863509777791587581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 723236969359407444233549 271213863509777791587581)
                  ·
                    rfl

theorem cell21_1188421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 5, 3].length) (baseStart_1188421 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1188421 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1188421 prefixEnd_1188421 := by exact prefixLift 1188421
  have htrace : WordTrace (prefixWord ++ tailWord_1188421) baseStart_1188421 baseEnd_1188421 := by
    simpa [prefixWord, tailWord_1188421, baseEnd_1188421] using wordTrace_append hprefix tailTrace_1188421
  have hstable : (prefixWord ++ tailWord_1188421).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1188421).length < 2 ^ (prefixWord ++ tailWord_1188421).sum := by decide
  have hdescent : baseEnd_1188421 < baseStart_1188421 := by decide
  rcases family_descends (prefixWord ++ tailWord_1188421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1188452 : List Nat := [2, 3, 1, 1, 2, 2, 5, 1, 4]
def baseStart_1188452 : Nat := 118140960795 + 1188452 * 2 ^ 59
def prefixEnd_1188452 : Nat := 4983230072969 + 3 ^ 40 * 1188452 * 2
def baseEnd_1188452 : Nat := 271220938132128626570851

theorem tailTrace_1188452 : CollatzResearch.WordTrace tailWord_1188452 prefixEnd_1188452 271220938132128626570851 := by
  unfold tailWord_1188452
  simp only [CollatzResearch.WordTrace]
  refine ⟨21673202745224425143663805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28897603660299233524885073 21673202745224425143663805)
  ·
    refine ⟨8127451029459159428873927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21673202745224425143663805 8127451029459159428873927)
    ·
      refine ⟨12191176544188739143310891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8127451029459159428873927 12191176544188739143310891)
      ·
        refine ⟨18286764816283108714966337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12191176544188739143310891 18286764816283108714966337)
        ·
          refine ⟨13715073612212331536224753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18286764816283108714966337 13715073612212331536224753)
          ·
            refine ⟨10286305209159248652168565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13715073612212331536224753 10286305209159248652168565)
            ·
              refine ⟨964341113358679561140803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10286305209159248652168565 964341113358679561140803)
              ·
                refine ⟨1446511670038019341711205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 964341113358679561140803 1446511670038019341711205)
                ·
                  refine ⟨271220938132128626570851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1446511670038019341711205 271220938132128626570851)
                  ·
                    rfl

theorem cell21_1188452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 5, 1, 4].length) (baseStart_1188452 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1188452 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1188452 prefixEnd_1188452 := by exact prefixLift 1188452
  have htrace : WordTrace (prefixWord ++ tailWord_1188452) baseStart_1188452 baseEnd_1188452 := by
    simpa [prefixWord, tailWord_1188452, baseEnd_1188452] using wordTrace_append hprefix tailTrace_1188452
  have hstable : (prefixWord ++ tailWord_1188452).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1188452).length < 2 ^ (prefixWord ++ tailWord_1188452).sum := by decide
  have hdescent : baseEnd_1188452 < baseStart_1188452 := by decide
  rcases family_descends (prefixWord ++ tailWord_1188452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1188466 : List Nat := [3, 2, 1, 2, 4, 1, 1, 7]
def baseStart_1188466 : Nat := 118140960795 + 1188466 * 2 ^ 59
def prefixEnd_1188466 : Nat := 4983230072969 + 3 ^ 40 * 1188466 * 2
def baseEnd_1188466 : Nat := 90408044374289237779163

theorem tailTrace_1188466 : CollatzResearch.WordTrace tailWord_1188466 prefixEnd_1188466 90408044374289237779163 := by
  unfold tailWord_1188466
  simp only [CollatzResearch.WordTrace]
  refine ⟨10836729028099532669584313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28897944074932087118891501 10836729028099532669584313)
  ·
    refine ⟨8127546771074649502188235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10836729028099532669584313 8127546771074649502188235)
    ·
      refine ⟨12191320156611974253282353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8127546771074649502188235 12191320156611974253282353)
      ·
        refine ⟨9143490117458980689961765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12191320156611974253282353 9143490117458980689961765)
        ·
          refine ⟨1714404397023558879367831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9143490117458980689961765 1714404397023558879367831)
          ·
            refine ⟨2571606595535338319051747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1714404397023558879367831 2571606595535338319051747)
            ·
              refine ⟨3857409893303007478577621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2571606595535338319051747 3857409893303007478577621)
              ·
                refine ⟨90408044374289237779163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3857409893303007478577621 90408044374289237779163)
                ·
                  rfl

theorem cell21_1188466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 7].length) (baseStart_1188466 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1188466 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1188466 prefixEnd_1188466 := by exact prefixLift 1188466
  have htrace : WordTrace (prefixWord ++ tailWord_1188466) baseStart_1188466 baseEnd_1188466 := by
    simpa [prefixWord, tailWord_1188466, baseEnd_1188466] using wordTrace_append hprefix tailTrace_1188466
  have hstable : (prefixWord ++ tailWord_1188466).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1188466).length < 2 ^ (prefixWord ++ tailWord_1188466).sum := by decide
  have hdescent : baseEnd_1188466 < baseStart_1188466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1188466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1188590 : List Nat := [4, 1, 2, 1, 1, 4, 2, 3, 3]
def baseStart_1188590 : Nat := 118140960795 + 1188590 * 2 ^ 59
def prefixEnd_1188590 : Nat := 4983230072969 + 3 ^ 40 * 1188590 * 2
def baseEnd_1188590 : Nat := 271252431612271053270569

theorem tailTrace_1188590 : CollatzResearch.WordTrace tailWord_1188590 prefixEnd_1188590 271252431612271053270569 := by
  unfold tailWord_1188590
  simp only [CollatzResearch.WordTrace]
  refine ⟨5418929845493612481981403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28900959175965933237234149 5418929845493612481981403)
  ·
    refine ⟨8128394768240418722972105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5418929845493612481981403 8128394768240418722972105)
    ·
      refine ⟨6096296076180314042229079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8128394768240418722972105 6096296076180314042229079)
      ·
        refine ⟨9144444114270471063343619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6096296076180314042229079 9144444114270471063343619)
        ·
          refine ⟨13716666171405706595015429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9144444114270471063343619 13716666171405706595015429)
          ·
            refine ⟨2571874907138569986565393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13716666171405706595015429 2571874907138569986565393)
            ·
              refine ⟨1928906180353927489924045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2571874907138569986565393 1928906180353927489924045)
              ·
                refine ⟨723339817632722808721517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1928906180353927489924045 723339817632722808721517)
                ·
                  refine ⟨271252431612271053270569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 723339817632722808721517 271252431612271053270569)
                  ·
                    rfl

theorem cell21_1188590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 2, 3, 3].length) (baseStart_1188590 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1188590 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1188590 prefixEnd_1188590 := by exact prefixLift 1188590
  have htrace : WordTrace (prefixWord ++ tailWord_1188590) baseStart_1188590 baseEnd_1188590 := by
    simpa [prefixWord, tailWord_1188590, baseEnd_1188590] using wordTrace_append hprefix tailTrace_1188590
  have hstable : (prefixWord ++ tailWord_1188590).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1188590).length < 2 ^ (prefixWord ++ tailWord_1188590).sum := by decide
  have hdescent : baseEnd_1188590 < baseStart_1188590 := by decide
  rcases family_descends (prefixWord ++ tailWord_1188590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1188604 : List Nat := [2, 2, 2, 1, 3, 4, 1, 2, 4]
def baseStart_1188604 : Nat := 118140960795 + 1188604 * 2 ^ 59
def prefixEnd_1188604 : Nat := 4983230072969 + 3 ^ 40 * 1188604 * 2
def baseEnd_1188604 : Nat := 271255626603010140037207

theorem tailTrace_1188604 : CollatzResearch.WordTrace tailWord_1188604 prefixEnd_1188604 271255626603010140037207 := by
  unfold tailWord_1188604
  simp only [CollatzResearch.WordTrace]
  refine ⟨21675974692949090123430433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28901299590598786831240577 21675974692949090123430433)
  ·
    refine ⟨16256981019711817592572825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21675974692949090123430433 16256981019711817592572825)
    ·
      refine ⟨12192735764783863194429619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16256981019711817592572825 12192735764783863194429619)
      ·
        refine ⟨18289103647175794791644429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12192735764783863194429619 18289103647175794791644429)
        ·
          refine ⟨6858413867690923046866661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18289103647175794791644429 6858413867690923046866661)
          ·
            refine ⟨1285952600192048071287499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6858413867690923046866661 1285952600192048071287499)
            ·
              refine ⟨1928928900288072106931249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1285952600192048071287499 1928928900288072106931249)
              ·
                refine ⟨1446696675216054080198437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1928928900288072106931249 1446696675216054080198437)
                ·
                  refine ⟨271255626603010140037207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1446696675216054080198437 271255626603010140037207)
                  ·
                    rfl

theorem cell21_1188604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 1, 2, 4].length) (baseStart_1188604 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1188604 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1188604 prefixEnd_1188604 := by exact prefixLift 1188604
  have htrace : WordTrace (prefixWord ++ tailWord_1188604) baseStart_1188604 baseEnd_1188604 := by
    simpa [prefixWord, tailWord_1188604, baseEnd_1188604] using wordTrace_append hprefix tailTrace_1188604
  have hstable : (prefixWord ++ tailWord_1188604).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1188604).length < 2 ^ (prefixWord ++ tailWord_1188604).sum := by decide
  have hdescent : baseEnd_1188604 < baseStart_1188604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1188604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1188666 : List Nat := [3, 1, 1, 1, 7, 1, 1, 1, 5]
def baseStart_1188666 : Nat := 118140960795 + 1188666 * 2 ^ 59
def prefixEnd_1188666 : Nat := 4983230072969 + 3 ^ 40 * 1188666 * 2
def baseEnd_1188666 : Nat := 271269775847711810003747

theorem tailTrace_1188666 : CollatzResearch.WordTrace tailWord_1188666 prefixEnd_1188666 271269775847711810003747 := by
  unfold tailWord_1188666
  simp only [CollatzResearch.WordTrace]
  refine ⟨10838552677918391208904463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28902807141115709890411901 10838552677918391208904463)
  ·
    refine ⟨16257829016877586813356695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10838552677918391208904463 16257829016877586813356695)
    ·
      refine ⟨24386743525316380220035043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16257829016877586813356695 24386743525316380220035043)
      ·
        refine ⟨36580115287974570330052565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24386743525316380220035043 36580115287974570330052565)
        ·
          refine ⟨857346452061903992110607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 36580115287974570330052565 857346452061903992110607)
          ·
            refine ⟨1286019678092855988165911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 857346452061903992110607 1286019678092855988165911)
            ·
              refine ⟨1929029517139283982248867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1286019678092855988165911 1929029517139283982248867)
              ·
                refine ⟨2893544275708925973373301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1929029517139283982248867 2893544275708925973373301)
                ·
                  refine ⟨271269775847711810003747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2893544275708925973373301 271269775847711810003747)
                  ·
                    rfl

theorem cell21_1188666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 1, 1, 5].length) (baseStart_1188666 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1188666 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1188666 prefixEnd_1188666 := by exact prefixLift 1188666
  have htrace : WordTrace (prefixWord ++ tailWord_1188666) baseStart_1188666 baseEnd_1188666 := by
    simpa [prefixWord, tailWord_1188666, baseEnd_1188666] using wordTrace_append hprefix tailTrace_1188666
  have hstable : (prefixWord ++ tailWord_1188666).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1188666).length < 2 ^ (prefixWord ++ tailWord_1188666).sum := by decide
  have hdescent : baseEnd_1188666 < baseStart_1188666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1188666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1188691 : List Nat := [1, 1, 1, 2, 1, 1, 3, 6, 5]
def baseStart_1188691 : Nat := 118140960795 + 1188691 * 2 ^ 59
def prefixEnd_1188691 : Nat := 4983230072969 + 3 ^ 40 * 1188691 * 2
def baseEnd_1188691 : Nat := 271275481188317322087029

theorem tailTrace_1188691 : CollatzResearch.WordTrace tailWord_1188691 prefixEnd_1188691 271275481188317322087029 := by
  unfold tailWord_1188691
  simp only [CollatzResearch.WordTrace]
  refine ⟨43355122536582994105277927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28903415024388662736851951 43355122536582994105277927)
  ·
    refine ⟨65032683804874491157916891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43355122536582994105277927 65032683804874491157916891)
    ·
      refine ⟨97549025707311736736875337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65032683804874491157916891 97549025707311736736875337)
      ·
        refine ⟨73161769280483802552656503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97549025707311736736875337 73161769280483802552656503)
        ·
          refine ⟨109742653920725703828984755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73161769280483802552656503 109742653920725703828984755)
          ·
            refine ⟨164613980881088555743477133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109742653920725703828984755 164613980881088555743477133)
            ·
              refine ⟨61730242830408208403803925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 164613980881088555743477133 61730242830408208403803925)
              ·
                refine ⟨2893605132675384768928309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 61730242830408208403803925 2893605132675384768928309)
                ·
                  refine ⟨271275481188317322087029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2893605132675384768928309 271275481188317322087029)
                  ·
                    rfl

theorem cell21_1188691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 6, 5].length) (baseStart_1188691 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1188691 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1188691 prefixEnd_1188691 := by exact prefixLift 1188691
  have htrace : WordTrace (prefixWord ++ tailWord_1188691) baseStart_1188691 baseEnd_1188691 := by
    simpa [prefixWord, tailWord_1188691, baseEnd_1188691] using wordTrace_append hprefix tailTrace_1188691
  have hstable : (prefixWord ++ tailWord_1188691).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1188691).length < 2 ^ (prefixWord ++ tailWord_1188691).sum := by decide
  have hdescent : baseEnd_1188691 < baseStart_1188691 := by decide
  rcases family_descends (prefixWord ++ tailWord_1188691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1188722 : List Nat := [3, 2, 1, 2, 1, 1, 2, 3, 6]
def baseStart_1188722 : Nat := 118140960795 + 1188722 * 2 ^ 59
def prefixEnd_1188722 : Nat := 4983230072969 + 3 ^ 40 * 1188722 * 2
def baseEnd_1188722 : Nat := 271282555810668157070299

theorem tailTrace_1188722 : CollatzResearch.WordTrace tailWord_1188722 prefixEnd_1188722 271282555810668157070299 := by
  unfold tailWord_1188722
  simp only [CollatzResearch.WordTrace]
  refine ⟨10839063299867671599914105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28904168799647124266437613 10839063299867671599914105)
  ·
    refine ⟨8129297474900753699935579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10839063299867671599914105 8129297474900753699935579)
    ·
      refine ⟨12193946212351130549903369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8129297474900753699935579 12193946212351130549903369)
      ·
        refine ⟨9145459659263347912427527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12193946212351130549903369 9145459659263347912427527)
        ·
          refine ⟨13718189488895021868641291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9145459659263347912427527 13718189488895021868641291)
          ·
            refine ⟨20577284233342532802961937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13718189488895021868641291 20577284233342532802961937)
            ·
              refine ⟨15432963175006899602221453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20577284233342532802961937 15432963175006899602221453)
              ·
                refine ⟨5787361190627587350833045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15432963175006899602221453 5787361190627587350833045)
                ·
                  refine ⟨271282555810668157070299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5787361190627587350833045 271282555810668157070299)
                  ·
                    rfl

theorem cell21_1188722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 3, 6].length) (baseStart_1188722 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1188722 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1188722 prefixEnd_1188722 := by exact prefixLift 1188722
  have htrace : WordTrace (prefixWord ++ tailWord_1188722) baseStart_1188722 baseEnd_1188722 := by
    simpa [prefixWord, tailWord_1188722, baseEnd_1188722] using wordTrace_append hprefix tailTrace_1188722
  have hstable : (prefixWord ++ tailWord_1188722).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1188722).length < 2 ^ (prefixWord ++ tailWord_1188722).sum := by decide
  have hdescent : baseEnd_1188722 < baseStart_1188722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1188722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1188736 : List Nat := [2, 1, 1, 2, 1, 2, 2, 10]
def baseStart_1188736 : Nat := 118140960795 + 1188736 * 2 ^ 59
def prefixEnd_1188736 : Nat := 4983230072969 + 3 ^ 40 * 1188736 * 2
def baseEnd_1188736 : Nat := 90428583600469081278979

theorem tailTrace_1188736 : CollatzResearch.WordTrace tailWord_1188736 prefixEnd_1188736 90428583600469081278979 := by
  unfold tailWord_1188736
  simp only [CollatzResearch.WordTrace]
  refine ⟨21678381910709983395333031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28904509214279977860444041 21678381910709983395333031)
  ·
    refine ⟨32517572866064975092999547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21678381910709983395333031 32517572866064975092999547)
    ·
      refine ⟨48776359299097462639499321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32517572866064975092999547 48776359299097462639499321)
      ·
        refine ⟨36582269474323096979624491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48776359299097462639499321 36582269474323096979624491)
        ·
          refine ⟨54873404211484645469436737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36582269474323096979624491 54873404211484645469436737)
          ·
            refine ⟨41155053158613484102077553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54873404211484645469436737 41155053158613484102077553)
            ·
              refine ⟨30866289868960113076558165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41155053158613484102077553 30866289868960113076558165)
              ·
                refine ⟨90428583600469081278979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 30866289868960113076558165 90428583600469081278979)
                ·
                  rfl

theorem cell21_1188736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 10].length) (baseStart_1188736 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1188736 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1188736 prefixEnd_1188736 := by exact prefixLift 1188736
  have htrace : WordTrace (prefixWord ++ tailWord_1188736) baseStart_1188736 baseEnd_1188736 := by
    simpa [prefixWord, tailWord_1188736, baseEnd_1188736] using wordTrace_append hprefix tailTrace_1188736
  have hstable : (prefixWord ++ tailWord_1188736).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1188736).length < 2 ^ (prefixWord ++ tailWord_1188736).sum := by decide
  have hdescent : baseEnd_1188736 < baseStart_1188736 := by decide
  rcases family_descends (prefixWord ++ tailWord_1188736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1188804 : List Nat := [2, 3, 3, 3, 1, 2, 2, 5]
def baseStart_1188804 : Nat := 118140960795 + 1188804 * 2 ^ 59
def prefixEnd_1188804 : Nat := 4983230072969 + 3 ^ 40 * 1188804 * 2
def baseEnd_1188804 : Nat := 90433756442618078901155

theorem tailTrace_1188804 : CollatzResearch.WordTrace tailWord_1188804 prefixEnd_1188804 90433756442618078901155 := by
  unfold tailWord_1188804
  simp only [CollatzResearch.WordTrace]
  refine ⟨21679621992586807202070733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28906162656782409602760977 21679621992586807202070733)
  ·
    refine ⟨8129858247220052700776525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21679621992586807202070733 8129858247220052700776525)
    ·
      refine ⟨3048696842707519762791197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8129858247220052700776525 3048696842707519762791197)
      ·
        refine ⟨1143261316015319911046699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3048696842707519762791197 1143261316015319911046699)
        ·
          refine ⟨1714891974022979866570049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1143261316015319911046699 1714891974022979866570049)
          ·
            refine ⟨1286168980517234899927537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1714891974022979866570049 1286168980517234899927537)
            ·
              refine ⟨964626735387926174945653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1286168980517234899927537 964626735387926174945653)
              ·
                refine ⟨90433756442618078901155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 964626735387926174945653 90433756442618078901155)
                ·
                  rfl

theorem cell21_1188804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 2, 5].length) (baseStart_1188804 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1188804 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1188804 prefixEnd_1188804 := by exact prefixLift 1188804
  have htrace : WordTrace (prefixWord ++ tailWord_1188804) baseStart_1188804 baseEnd_1188804 := by
    simpa [prefixWord, tailWord_1188804, baseEnd_1188804] using wordTrace_append hprefix tailTrace_1188804
  have hstable : (prefixWord ++ tailWord_1188804).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1188804).length < 2 ^ (prefixWord ++ tailWord_1188804).sum := by decide
  have hdescent : baseEnd_1188804 < baseStart_1188804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1188804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1188818 : List Nat := [3, 2, 2, 3, 1, 1, 3, 3, 3]
def baseStart_1188818 : Nat := 118140960795 + 1188818 * 2 ^ 59
def prefixEnd_1188818 : Nat := 4983230072969 + 3 ^ 40 * 1188818 * 2
def baseEnd_1188818 : Nat := 271304464318593323470103

theorem tailTrace_1188818 : CollatzResearch.WordTrace tailWord_1188818 prefixEnd_1188818 271304464318593323470103 := by
  unfold tailWord_1188818
  simp only [CollatzResearch.WordTrace]
  refine ⟨10839938651780723698787777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28906503071415263196767405 10839938651780723698787777)
  ·
    refine ⟨8129953988835542774090833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10839938651780723698787777 8129953988835542774090833)
    ·
      refine ⟨6097465491626657080568125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8129953988835542774090833 6097465491626657080568125)
      ·
        refine ⟨2286549559359996405213047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6097465491626657080568125 2286549559359996405213047)
        ·
          refine ⟨3429824339039994607819571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2286549559359996405213047 3429824339039994607819571)
          ·
            refine ⟨5144736508559991911729357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3429824339039994607819571 5144736508559991911729357)
            ·
              refine ⟨1929276190709996966898509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5144736508559991911729357 1929276190709996966898509)
              ·
                refine ⟨723478571516248862586941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1929276190709996966898509 723478571516248862586941)
                ·
                  refine ⟨271304464318593323470103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 723478571516248862586941 271304464318593323470103)
                  ·
                    rfl

theorem cell21_1188818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 3, 3, 3].length) (baseStart_1188818 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1188818 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1188818 prefixEnd_1188818 := by exact prefixLift 1188818
  have htrace : WordTrace (prefixWord ++ tailWord_1188818) baseStart_1188818 baseEnd_1188818 := by
    simpa [prefixWord, tailWord_1188818, baseEnd_1188818] using wordTrace_append hprefix tailTrace_1188818
  have hstable : (prefixWord ++ tailWord_1188818).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1188818).length < 2 ^ (prefixWord ++ tailWord_1188818).sum := by decide
  have hdescent : baseEnd_1188818 < baseStart_1188818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1188818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1188829 : List Nat := [1, 4, 3, 1, 2, 1, 9]
def baseStart_1188829 : Nat := 118140960795 + 1188829 * 2 ^ 59
def prefixEnd_1188829 : Nat := 4983230072969 + 3 ^ 40 * 1188829 * 2
def baseEnd_1188829 : Nat := 30145219407606638754083

theorem tailTrace_1188829 : CollatzResearch.WordTrace tailWord_1188829 prefixEnd_1188829 30145219407606638754083 := by
  unfold tailWord_1188829
  simp only [CollatzResearch.WordTrace]
  refine ⟨43360155810083043673801541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28906770540055362449201027 43360155810083043673801541)
  ·
    refine ⟨8130029214390570688837789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43360155810083043673801541 8130029214390570688837789)
    ·
      refine ⟨3048760955396464008314171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8130029214390570688837789 3048760955396464008314171)
      ·
        refine ⟨4573141433094696012471257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3048760955396464008314171 4573141433094696012471257)
        ·
          refine ⟨3429856074821022009353443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4573141433094696012471257 3429856074821022009353443)
          ·
            refine ⟨5144784112231533014030165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3429856074821022009353443 5144784112231533014030165)
            ·
              refine ⟨30145219407606638754083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5144784112231533014030165 30145219407606638754083)
              ·
                rfl

theorem cell21_1188829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 9].length) (baseStart_1188829 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1188829 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1188829 prefixEnd_1188829 := by exact prefixLift 1188829
  have htrace : WordTrace (prefixWord ++ tailWord_1188829) baseStart_1188829 baseEnd_1188829 := by
    simpa [prefixWord, tailWord_1188829, baseEnd_1188829] using wordTrace_append hprefix tailTrace_1188829
  have hstable : (prefixWord ++ tailWord_1188829).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1188829).length < 2 ^ (prefixWord ++ tailWord_1188829).sum := by decide
  have hdescent : baseEnd_1188829 < baseStart_1188829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1188829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1188846 : List Nat := [4, 1, 2, 1, 4, 1, 2, 6]
def baseStart_1188846 : Nat := 118140960795 + 1188846 * 2 ^ 59
def prefixEnd_1188846 : Nat := 4983230072969 + 3 ^ 40 * 1188846 * 2
def baseEnd_1188846 : Nat := 90436951433357165667793

theorem tailTrace_1188846 : CollatzResearch.WordTrace tailWord_1188846 prefixEnd_1188846 90436951433357165667793 := by
  unfold tailWord_1188846
  simp only [CollatzResearch.WordTrace]
  refine ⟨5420096981377681947146299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 28907183900680970384780261 5420096981377681947146299)
  ·
    refine ⟨8130145472066522920719449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5420096981377681947146299 8130145472066522920719449)
    ·
      refine ⟨6097609104049892190539587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8130145472066522920719449 6097609104049892190539587)
      ·
        refine ⟨9146413656074838285809381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6097609104049892190539587 9146413656074838285809381)
        ·
          refine ⟨1714952560514032178589259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9146413656074838285809381 1714952560514032178589259)
          ·
            refine ⟨2572428840771048267883889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1714952560514032178589259 2572428840771048267883889)
            ·
              refine ⟨1929321630578286200912917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2572428840771048267883889 1929321630578286200912917)
              ·
                refine ⟨90436951433357165667793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1929321630578286200912917 90436951433357165667793)
                ·
                  rfl

theorem cell21_1188846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 2, 6].length) (baseStart_1188846 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1188846 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1188846 prefixEnd_1188846 := by exact prefixLift 1188846
  have htrace : WordTrace (prefixWord ++ tailWord_1188846) baseStart_1188846 baseEnd_1188846 := by
    simpa [prefixWord, tailWord_1188846, baseEnd_1188846] using wordTrace_append hprefix tailTrace_1188846
  have hstable : (prefixWord ++ tailWord_1188846).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1188846).length < 2 ^ (prefixWord ++ tailWord_1188846).sum := by decide
  have hdescent : baseEnd_1188846 < baseStart_1188846 := by decide
  rcases family_descends (prefixWord ++ tailWord_1188846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1188888 : List Nat := [2, 1, 2, 3, 2, 11]
def baseStart_1188888 : Nat := 118140960795 + 1188888 * 2 ^ 59
def prefixEnd_1188888 : Nat := 4983230072969 + 3 ^ 40 * 1188888 * 2
def baseEnd_1188888 : Nat := 10048905158232916937159

theorem tailTrace_1188888 : CollatzResearch.WordTrace tailWord_1188888 prefixEnd_1188888 10048905158232916937159 := by
  unfold tailWord_1188888
  simp only [CollatzResearch.WordTrace]
  refine ⟨21681153858434648375099659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28908205144579531166799545 21681153858434648375099659)
  ·
    refine ⟨32521730787651972562649489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21681153858434648375099659 32521730787651972562649489)
    ·
      refine ⟨24391298090738979421987117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32521730787651972562649489 24391298090738979421987117)
      ·
        refine ⟨9146736784027117283245169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24391298090738979421987117 9146736784027117283245169)
        ·
          refine ⟨6860052588020337962433877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9146736784027117283245169 6860052588020337962433877)
          ·
            refine ⟨10048905158232916937159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 6860052588020337962433877 10048905158232916937159)
            ·
              rfl

theorem cell21_1188888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 11].length) (baseStart_1188888 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1188888 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1188888 prefixEnd_1188888 := by exact prefixLift 1188888
  have htrace : WordTrace (prefixWord ++ tailWord_1188888) baseStart_1188888 baseEnd_1188888 := by
    simpa [prefixWord, tailWord_1188888, baseEnd_1188888] using wordTrace_append hprefix tailTrace_1188888
  have hstable : (prefixWord ++ tailWord_1188888).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1188888).length < 2 ^ (prefixWord ++ tailWord_1188888).sum := by decide
  have hdescent : baseEnd_1188888 < baseStart_1188888 := by decide
  rcases family_descends (prefixWord ++ tailWord_1188888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1188964 : List Nat := [2, 3, 1, 1, 2, 1, 1, 10]
def baseStart_1188964 : Nat := 118140960795 + 1188964 * 2 ^ 59
def prefixEnd_1188964 : Nat := 4983230072969 + 3 ^ 40 * 1188964 * 2
def baseEnd_1188964 : Nat := 90445927835909838012157

theorem tailTrace_1188964 : CollatzResearch.WordTrace tailWord_1188964 prefixEnd_1188964 90445927835909838012157 := by
  unfold tailWord_1188964
  simp only [CollatzResearch.WordTrace]
  refine ⟨21682539832296980864982973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28910053109729307819977297 21682539832296980864982973)
  ·
    refine ⟨8130952437111367824368615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21682539832296980864982973 8130952437111367824368615)
    ·
      refine ⟨12196428655667051736552923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8130952437111367824368615 12196428655667051736552923)
      ·
        refine ⟨18294642983500577604829385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12196428655667051736552923 18294642983500577604829385)
        ·
          refine ⟨13720982237625433203622039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18294642983500577604829385 13720982237625433203622039)
          ·
            refine ⟨20581473356438149805433059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13720982237625433203622039 20581473356438149805433059)
            ·
              refine ⟨30872210034657224708149589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20581473356438149805433059 30872210034657224708149589)
              ·
                refine ⟨90445927835909838012157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 30872210034657224708149589 90445927835909838012157)
                ·
                  rfl

theorem cell21_1188964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 10].length) (baseStart_1188964 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1188964 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1188964 prefixEnd_1188964 := by exact prefixLift 1188964
  have htrace : WordTrace (prefixWord ++ tailWord_1188964) baseStart_1188964 baseEnd_1188964 := by
    simpa [prefixWord, tailWord_1188964, baseEnd_1188964] using wordTrace_append hprefix tailTrace_1188964
  have hstable : (prefixWord ++ tailWord_1188964).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1188964).length < 2 ^ (prefixWord ++ tailWord_1188964).sum := by decide
  have hdescent : baseEnd_1188964 < baseStart_1188964 := by decide
  rcases family_descends (prefixWord ++ tailWord_1188964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1189057 : List Nat := [1, 2, 6, 1, 1, 10]
def baseStart_1189057 : Nat := 118140960795 + 1189057 * 2 ^ 59
def prefixEnd_1189057 : Nat := 4983230072969 + 3 ^ 40 * 1189057 * 2
def baseEnd_1189057 : Nat := 10050333606473408110603

theorem tailTrace_1189057 : CollatzResearch.WordTrace tailWord_1189057 prefixEnd_1189057 10050333606473408110603 := by
  unfold tailWord_1189057
  simp only [CollatzResearch.WordTrace]
  refine ⟨43368471653257038613101425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28912314435504692408734283 43368471653257038613101425)
  ·
    refine ⟨32526353739942778959826069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43368471653257038613101425 32526353739942778959826069)
    ·
      refine ⟨1524672831559817763741847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 32526353739942778959826069 1524672831559817763741847)
      ·
        refine ⟨2287009247339726645612771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1524672831559817763741847 2287009247339726645612771)
        ·
          refine ⟨3430513871009589968419157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2287009247339726645612771 3430513871009589968419157)
          ·
            refine ⟨10050333606473408110603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3430513871009589968419157 10050333606473408110603)
            ·
              rfl

theorem cell21_1189057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 10].length) (baseStart_1189057 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1189057 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1189057 prefixEnd_1189057 := by exact prefixLift 1189057
  have htrace : WordTrace (prefixWord ++ tailWord_1189057) baseStart_1189057 baseEnd_1189057 := by
    simpa [prefixWord, tailWord_1189057, baseEnd_1189057] using wordTrace_append hprefix tailTrace_1189057
  have hstable : (prefixWord ++ tailWord_1189057).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1189057).length < 2 ^ (prefixWord ++ tailWord_1189057).sum := by decide
  have hdescent : baseEnd_1189057 < baseStart_1189057 := by decide
  rcases family_descends (prefixWord ++ tailWord_1189057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1189060 : List Nat := [2, 3, 3, 1, 3, 1, 2, 2, 4]
def baseStart_1189060 : Nat := 118140960795 + 1189060 * 2 ^ 59
def prefixEnd_1189060 : Nat := 4983230072969 + 3 ^ 40 * 1189060 * 2
def baseEnd_1189060 : Nat := 271359692015654680436275

theorem tailTrace_1189060 : CollatzResearch.WordTrace tailWord_1189060 prefixEnd_1189060 271359692015654680436275 := by
  unfold tailWord_1189060
  simp only [CollatzResearch.WordTrace]
  refine ⟨21684290536123085062730317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28912387381497446750307089 21684290536123085062730317)
  ·
    refine ⟨8131608951046156898523869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21684290536123085062730317 8131608951046156898523869)
    ·
      refine ⟨3049353356642308836946451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8131608951046156898523869 3049353356642308836946451)
      ·
        refine ⟨4574030034963463255419677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3049353356642308836946451 4574030034963463255419677)
        ·
          refine ⟨1715261263111298720782379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4574030034963463255419677 1715261263111298720782379)
          ·
            refine ⟨2572891894666948081173569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1715261263111298720782379 2572891894666948081173569)
            ·
              refine ⟨1929668921000211060880177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2572891894666948081173569 1929668921000211060880177)
              ·
                refine ⟨1447251690750158295660133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1929668921000211060880177 1447251690750158295660133)
                ·
                  refine ⟨271359692015654680436275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1447251690750158295660133 271359692015654680436275)
                  ·
                    rfl

theorem cell21_1189060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 2, 2, 4].length) (baseStart_1189060 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1189060 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1189060 prefixEnd_1189060 := by exact prefixLift 1189060
  have htrace : WordTrace (prefixWord ++ tailWord_1189060) baseStart_1189060 baseEnd_1189060 := by
    simpa [prefixWord, tailWord_1189060, baseEnd_1189060] using wordTrace_append hprefix tailTrace_1189060
  have hstable : (prefixWord ++ tailWord_1189060).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1189060).length < 2 ^ (prefixWord ++ tailWord_1189060).sum := by decide
  have hdescent : baseEnd_1189060 < baseStart_1189060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1189060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1189119 : List Nat := [1, 1, 2, 2, 1, 7, 1, 2, 4]
def baseStart_1189119 : Nat := 118140960795 + 1189119 * 2 ^ 59
def prefixEnd_1189119 : Nat := 4983230072969 + 3 ^ 40 * 1189119 * 2
def baseEnd_1189119 : Nat := 271373156619483688952821

theorem tailTrace_1189119 : CollatzResearch.WordTrace tailWord_1189119 prefixEnd_1189119 271373156619483688952821 := by
  unfold tailWord_1189119
  simp only [CollatzResearch.WordTrace]
  refine ⟨43370732979032423201858411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28913821986021615467905607 43370732979032423201858411)
  ·
    refine ⟨65056099468548634802787617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43370732979032423201858411 65056099468548634802787617)
    ·
      refine ⟨48792074601411476102090713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65056099468548634802787617 48792074601411476102090713)
      ·
        refine ⟨36594055951058607076568035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48792074601411476102090713 36594055951058607076568035)
        ·
          refine ⟨54891083926587910614852053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36594055951058607076568035 54891083926587910614852053)
          ·
            refine ⟨1286509779529404155035595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 54891083926587910614852053 1286509779529404155035595)
            ·
              refine ⟨1929764669294106232553393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1286509779529404155035595 1929764669294106232553393)
              ·
                refine ⟨1447323501970579674415045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1929764669294106232553393 1447323501970579674415045)
                ·
                  refine ⟨271373156619483688952821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1447323501970579674415045 271373156619483688952821)
                  ·
                    rfl

theorem cell21_1189119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 1, 2, 4].length) (baseStart_1189119 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1189119 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1189119 prefixEnd_1189119 := by exact prefixLift 1189119
  have htrace : WordTrace (prefixWord ++ tailWord_1189119) baseStart_1189119 baseEnd_1189119 := by
    simpa [prefixWord, tailWord_1189119, baseEnd_1189119] using wordTrace_append hprefix tailTrace_1189119
  have hstable : (prefixWord ++ tailWord_1189119).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1189119).length < 2 ^ (prefixWord ++ tailWord_1189119).sum := by decide
  have hdescent : baseEnd_1189119 < baseStart_1189119 := by decide
  rcases family_descends (prefixWord ++ tailWord_1189119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1189178 : List Nat := [3, 1, 1, 1, 4, 1, 2, 4, 4]
def baseStart_1189178 : Nat := 118140960795 + 1189178 * 2 ^ 59
def prefixEnd_1189178 : Nat := 4983230072969 + 3 ^ 40 * 1189178 * 2
def baseEnd_1189178 : Nat := 271386621223312697469367

theorem tailTrace_1189178 : CollatzResearch.WordTrace tailWord_1189178 prefixEnd_1189178 271386621223312697469367 := by
  unfold tailWord_1189178
  simp only [CollatzResearch.WordTrace]
  refine ⟨10843221221454669069564047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28915256590545784185504125 10843221221454669069564047)
  ·
    refine ⟨16264831832182003604346071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10843221221454669069564047 16264831832182003604346071)
    ·
      refine ⟨24397247748273005406519107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16264831832182003604346071 24397247748273005406519107)
      ·
        refine ⟨36595871622409508109778661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24397247748273005406519107 36595871622409508109778661)
        ·
          refine ⟨6861725929201782770583499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36595871622409508109778661 6861725929201782770583499)
          ·
            refine ⟨10292588893802674155875249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6861725929201782770583499 10292588893802674155875249)
            ·
              refine ⟨7719441670352005616906437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10292588893802674155875249 7719441670352005616906437)
              ·
                refine ⟨1447395313191001053169957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7719441670352005616906437 1447395313191001053169957)
                ·
                  refine ⟨271386621223312697469367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1447395313191001053169957 271386621223312697469367)
                  ·
                    rfl

theorem cell21_1189178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 4, 4].length) (baseStart_1189178 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1189178 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1189178 prefixEnd_1189178 := by exact prefixLift 1189178
  have htrace : WordTrace (prefixWord ++ tailWord_1189178) baseStart_1189178 baseEnd_1189178 := by
    simpa [prefixWord, tailWord_1189178, baseEnd_1189178] using wordTrace_append hprefix tailTrace_1189178
  have hstable : (prefixWord ++ tailWord_1189178).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1189178).length < 2 ^ (prefixWord ++ tailWord_1189178).sum := by decide
  have hdescent : baseEnd_1189178 < baseStart_1189178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1189178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1189316 : List Nat := [2, 3, 3, 2, 1, 1, 2, 2, 5]
def baseStart_1189316 : Nat := 118140960795 + 1189316 * 2 ^ 59
def prefixEnd_1189316 : Nat := 4983230072969 + 3 ^ 40 * 1189316 * 2
def baseEnd_1189316 : Nat := 271418114703455124169085

theorem tailTrace_1189316 : CollatzResearch.WordTrace tailWord_1189316 prefixEnd_1189316 271418114703455124169085 := by
  unfold tailWord_1189316
  simp only [CollatzResearch.WordTrace]
  refine ⟨21688959079659362923389901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28918612106212483897853201 21688959079659362923389901)
  ·
    refine ⟨8133359654872261096271213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21688959079659362923389901 8133359654872261096271213)
    ·
      refine ⟨3050009870577097911101705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8133359654872261096271213 3050009870577097911101705)
      ·
        refine ⟨2287507402932823433326279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3050009870577097911101705 2287507402932823433326279)
        ·
          refine ⟨3431261104399235149989419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2287507402932823433326279 3431261104399235149989419)
          ·
            refine ⟨5146891656598852724984129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3431261104399235149989419 5146891656598852724984129)
            ·
              refine ⟨3860168742449139543738097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5146891656598852724984129 3860168742449139543738097)
              ·
                refine ⟨2895126556836854657803573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3860168742449139543738097 2895126556836854657803573)
                ·
                  refine ⟨271418114703455124169085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2895126556836854657803573 271418114703455124169085)
                  ·
                    rfl

theorem cell21_1189316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 2, 5].length) (baseStart_1189316 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1189316 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1189316 prefixEnd_1189316 := by exact prefixLift 1189316
  have htrace : WordTrace (prefixWord ++ tailWord_1189316) baseStart_1189316 baseEnd_1189316 := by
    simpa [prefixWord, tailWord_1189316, baseEnd_1189316] using wordTrace_append hprefix tailTrace_1189316
  have hstable : (prefixWord ++ tailWord_1189316).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1189316).length < 2 ^ (prefixWord ++ tailWord_1189316).sum := by decide
  have hdescent : baseEnd_1189316 < baseStart_1189316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1189316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1189409 : List Nat := [1, 2, 3, 2, 2, 2, 4, 2, 3]
def baseStart_1189409 : Nat := 118140960795 + 1189409 * 2 ^ 59
def prefixEnd_1189409 : Nat := 4983230072969 + 3 ^ 40 * 1189409 * 2
def baseEnd_1189409 : Nat := 271439338570507629118895

theorem tailTrace_1189409 : CollatzResearch.WordTrace tailWord_1189409 prefixEnd_1189409 271439338570507629118895 := by
  unfold tailWord_1189409
  simp only [CollatzResearch.WordTrace]
  refine ⟨43381310147981802729915281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28920873431987868486610187 43381310147981802729915281)
  ·
    refine ⟨32535982610986352047436461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43381310147981802729915281 32535982610986352047436461)
    ·
      refine ⟨12200993479119882017788673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32535982610986352047436461 12200993479119882017788673)
      ·
        refine ⟨9150745109339911513341505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12200993479119882017788673 9150745109339911513341505)
        ·
          refine ⟨6863058832004933635006129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9150745109339911513341505 6863058832004933635006129)
          ·
            refine ⟨5147294124003700226254597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6863058832004933635006129 5147294124003700226254597)
            ·
              refine ⟨965117648250693792422737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5147294124003700226254597 965117648250693792422737)
              ·
                refine ⟨723838236188020344317053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 965117648250693792422737 723838236188020344317053)
                ·
                  refine ⟨271439338570507629118895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 723838236188020344317053 271439338570507629118895)
                  ·
                    rfl

theorem cell21_1189409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 4, 2, 3].length) (baseStart_1189409 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1189409 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1189409 prefixEnd_1189409 := by exact prefixLift 1189409
  have htrace : WordTrace (prefixWord ++ tailWord_1189409) baseStart_1189409 baseEnd_1189409 := by
    simpa [prefixWord, tailWord_1189409, baseEnd_1189409] using wordTrace_append hprefix tailTrace_1189409
  have hstable : (prefixWord ++ tailWord_1189409).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1189409).length < 2 ^ (prefixWord ++ tailWord_1189409).sum := by decide
  have hdescent : baseEnd_1189409 < baseStart_1189409 := by decide
  rcases family_descends (prefixWord ++ tailWord_1189409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1189468 : List Nat := [2, 2, 4, 1, 2, 2, 2, 1, 5]
def baseStart_1189468 : Nat := 118140960795 + 1189468 * 2 ^ 59
def prefixEnd_1189468 : Nat := 4983230072969 + 3 ^ 40 * 1189468 * 2
def baseEnd_1189468 : Nat := 271452803174336637635441

theorem tailTrace_1189468 : CollatzResearch.WordTrace tailWord_1189468 prefixEnd_1189468 271452803174336637635441 := by
  unfold tailWord_1189468
  simp only [CollatzResearch.WordTrace]
  refine ⟨21691731027384027903156529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 28922308036512037204208705 21691731027384027903156529)
  ·
    refine ⟨16268798270538020927367397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21691731027384027903156529 16268798270538020927367397)
    ·
      refine ⟨3050399675725878923881387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16268798270538020927367397 3050399675725878923881387)
      ·
        refine ⟨4575599513588818385822081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3050399675725878923881387 4575599513588818385822081)
        ·
          refine ⟨3431699635191613789366561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4575599513588818385822081 3431699635191613789366561)
          ·
            refine ⟨2573774726393710342024921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3431699635191613789366561 2573774726393710342024921)
            ·
              refine ⟨1930331044795282756518691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2573774726393710342024921 1930331044795282756518691)
              ·
                refine ⟨2895496567192924134778037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1930331044795282756518691 2895496567192924134778037)
                ·
                  refine ⟨271452803174336637635441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2895496567192924134778037 271452803174336637635441)
                  ·
                    rfl

theorem cell21_1189468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 2, 1, 5].length) (baseStart_1189468 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1189468 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1189468 prefixEnd_1189468 := by exact prefixLift 1189468
  have htrace : WordTrace (prefixWord ++ tailWord_1189468) baseStart_1189468 baseEnd_1189468 := by
    simpa [prefixWord, tailWord_1189468, baseEnd_1189468] using wordTrace_append hprefix tailTrace_1189468
  have hstable : (prefixWord ++ tailWord_1189468).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1189468).length < 2 ^ (prefixWord ++ tailWord_1189468).sum := by decide
  have hdescent : baseEnd_1189468 < baseStart_1189468 := by decide
  rcases family_descends (prefixWord ++ tailWord_1189468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1189527 : List Nat := [1, 1, 3, 3, 2, 2, 3, 1, 5]
def baseStart_1189527 : Nat := 118140960795 + 1189527 * 2 ^ 59
def prefixEnd_1189527 : Nat := 4983230072969 + 3 ^ 40 * 1189527 * 2
def baseEnd_1189527 : Nat := 271466267778165646151987

theorem tailTrace_1189527 : CollatzResearch.WordTrace tailWord_1189527 prefixEnd_1189527 271466267778165646151987 := by
  unfold tailWord_1189527
  simp only [CollatzResearch.WordTrace]
  refine ⟨43385613961554308882710835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28923742641036205921807223 43385613961554308882710835)
  ·
    refine ⟨65078420942331463324066253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43385613961554308882710835 65078420942331463324066253)
    ·
      refine ⟨24404407853374298746524845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65078420942331463324066253 24404407853374298746524845)
      ·
        refine ⟨9151652945015362029946817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24404407853374298746524845 9151652945015362029946817)
        ·
          refine ⟨6863739708761521522460113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9151652945015362029946817 6863739708761521522460113)
          ·
            refine ⟨5147804781571141141845085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6863739708761521522460113 5147804781571141141845085)
            ·
              refine ⟨1930426793089177928191907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5147804781571141141845085 1930426793089177928191907)
              ·
                refine ⟨2895640189633766892287861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1930426793089177928191907 2895640189633766892287861)
                ·
                  refine ⟨271466267778165646151987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2895640189633766892287861 271466267778165646151987)
                  ·
                    rfl

theorem cell21_1189527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 3, 1, 5].length) (baseStart_1189527 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1189527 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1189527 prefixEnd_1189527 := by exact prefixLift 1189527
  have htrace : WordTrace (prefixWord ++ tailWord_1189527) baseStart_1189527 baseEnd_1189527 := by
    simpa [prefixWord, tailWord_1189527, baseEnd_1189527] using wordTrace_append hprefix tailTrace_1189527
  have hstable : (prefixWord ++ tailWord_1189527).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1189527).length < 2 ^ (prefixWord ++ tailWord_1189527).sum := by decide
  have hdescent : baseEnd_1189527 < baseStart_1189527 := by decide
  rcases family_descends (prefixWord ++ tailWord_1189527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1189555 : List Nat := [1, 1, 1, 2, 3, 3, 1, 9]
def baseStart_1189555 : Nat := 118140960795 + 1189555 * 2 ^ 59
def prefixEnd_1189555 : Nat := 4983230072969 + 3 ^ 40 * 1189555 * 2
def baseEnd_1189555 : Nat := 90490885919881273228421

theorem tailTrace_1189555 : CollatzResearch.WordTrace tailWord_1189555 prefixEnd_1189555 90490885919881273228421 := by
  unfold tailWord_1189555
  simp only [CollatzResearch.WordTrace]
  refine ⟨43386635205452869664730119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 28924423470301913109820079 43386635205452869664730119)
  ·
    refine ⟨65079952808179304497095179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43386635205452869664730119 65079952808179304497095179)
    ·
      refine ⟨97619929212268956745642769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65079952808179304497095179 97619929212268956745642769)
      ·
        refine ⟨73214946909201717559232077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97619929212268956745642769 73214946909201717559232077)
        ·
          refine ⟨27455605090950644084712029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73214946909201717559232077 27455605090950644084712029)
          ·
            refine ⟨10295851909106491531767011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27455605090950644084712029 10295851909106491531767011)
            ·
              refine ⟨15443777863659737297650517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10295851909106491531767011 15443777863659737297650517)
              ·
                refine ⟨90490885919881273228421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15443777863659737297650517 90490885919881273228421)
                ·
                  rfl

theorem cell21_1189555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 9].length) (baseStart_1189555 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1189555 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1189555 prefixEnd_1189555 := by exact prefixLift 1189555
  have htrace : WordTrace (prefixWord ++ tailWord_1189555) baseStart_1189555 baseEnd_1189555 := by
    simpa [prefixWord, tailWord_1189555, baseEnd_1189555] using wordTrace_append hprefix tailTrace_1189555
  have hstable : (prefixWord ++ tailWord_1189555).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1189555).length < 2 ^ (prefixWord ++ tailWord_1189555).sum := by decide
  have hdescent : baseEnd_1189555 < baseStart_1189555 := by decide
  rcases family_descends (prefixWord ++ tailWord_1189555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1189578 : List Nat := [3, 1, 2, 1, 5, 2, 2, 2, 3]
def baseStart_1189578 : Nat := 118140960795 + 1189578 * 2 ^ 59
def prefixEnd_1189578 : Nat := 4983230072969 + 3 ^ 40 * 1189578 * 2
def baseEnd_1189578 : Nat := 271477906673000890801883

theorem tailTrace_1189578 : CollatzResearch.WordTrace tailWord_1189578 prefixEnd_1189578 271477906673000890801883 := by
  unfold tailWord_1189578
  simp only [CollatzResearch.WordTrace]
  refine ⟨10846868521092386148204347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 28924982722913029728544925 10846868521092386148204347)
  ·
    refine ⟨16270302781638579222306521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10846868521092386148204347 16270302781638579222306521)
    ·
      refine ⟨12202727086228934416729891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16270302781638579222306521 12202727086228934416729891)
      ·
        refine ⟨18304090629343401625094837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12202727086228934416729891 18304090629343401625094837)
        ·
          refine ⟨1716008496500943902352641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18304090629343401625094837 1716008496500943902352641)
          ·
            refine ⟨1287006372375707926764481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1716008496500943902352641 1287006372375707926764481)
            ·
              refine ⟨965254779281780945073361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1287006372375707926764481 965254779281780945073361)
              ·
                refine ⟨723941084461335708805021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 965254779281780945073361 723941084461335708805021)
                ·
                  refine ⟨271477906673000890801883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 723941084461335708805021 271477906673000890801883)
                  ·
                    rfl

theorem cell21_1189578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 2, 2, 3].length) (baseStart_1189578 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1189578 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1189578 prefixEnd_1189578 := by exact prefixLift 1189578
  have htrace : WordTrace (prefixWord ++ tailWord_1189578) baseStart_1189578 baseEnd_1189578 := by
    simpa [prefixWord, tailWord_1189578, baseEnd_1189578] using wordTrace_append hprefix tailTrace_1189578
  have hstable : (prefixWord ++ tailWord_1189578).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1189578).length < 2 ^ (prefixWord ++ tailWord_1189578).sum := by decide
  have hdescent : baseEnd_1189578 < baseStart_1189578 := by decide
  rcases family_descends (prefixWord ++ tailWord_1189578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
