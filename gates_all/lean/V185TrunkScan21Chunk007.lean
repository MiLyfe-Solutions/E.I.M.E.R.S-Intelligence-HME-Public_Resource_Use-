import V185TrunkScan21Chunk006

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_84850 : List Nat := [3, 2, 1, 2, 1, 1, 4, 2, 5]
def baseStart_84850 : Nat := 118140960795 + 84850 * 2 ^ 59
def prefixEnd_84850 : Nat := 4983230072969 + 3 ^ 40 * 84850 * 2
def baseEnd_84850 : Nat := 19363926015154781193239

theorem tailTrace_84850 : CollatzResearch.WordTrace tailWord_84850 prefixEnd_84850 19363926015154781193239 := by
  unfold tailWord_84850
  simp only [CollatzResearch.WordTrace]
  refine ⟨773683435652604017851001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2063155828406944047602669 773683435652604017851001)
  ·
    refine ⟨580262576739453013388251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 773683435652604017851001 580262576739453013388251)
    ·
      refine ⟨870393865109179520082377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 580262576739453013388251 870393865109179520082377)
      ·
        refine ⟨652795398831884640061783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 870393865109179520082377 652795398831884640061783)
        ·
          refine ⟨979193098247826960092675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 652795398831884640061783 979193098247826960092675)
          ·
            refine ⟨1468789647371740440139013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 979193098247826960092675 1468789647371740440139013)
            ·
              refine ⟨275398058882201332526065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1468789647371740440139013 275398058882201332526065)
              ·
                refine ⟨206548544161650999394549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 275398058882201332526065 206548544161650999394549)
                ·
                  refine ⟨19363926015154781193239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 206548544161650999394549 19363926015154781193239)
                  ·
                    rfl

theorem cell21_84850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 2, 5].length) (baseStart_84850 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_84850 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_84850 prefixEnd_84850 := by exact prefixLift 84850
  have htrace : WordTrace (prefixWord ++ tailWord_84850) baseStart_84850 baseEnd_84850 := by
    simpa [prefixWord, tailWord_84850, baseEnd_84850] using wordTrace_append hprefix tailTrace_84850
  have hstable : (prefixWord ++ tailWord_84850).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84850).length < 2 ^ (prefixWord ++ tailWord_84850).sum := by decide
  have hdescent : baseEnd_84850 < baseStart_84850 := by decide
  rcases family_descends (prefixWord ++ tailWord_84850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84853 : List Nat := [1, 3, 4, 1, 1, 4, 2, 5]
def baseStart_84853 : Nat := 118140960795 + 84853 * 2 ^ 59
def prefixEnd_84853 : Nat := 4983230072969 + 3 ^ 40 * 84853 * 2
def baseEnd_84853 : Nat := 6454870218675814214411

theorem tailTrace_84853 : CollatzResearch.WordTrace tailWord_84853 prefixEnd_84853 6454870218675814214411 := by
  unfold tailWord_84853
  simp only [CollatzResearch.WordTrace]
  refine ⟨3094843161599547583763213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2063228774399698389175475 3094843161599547583763213)
  ·
    refine ⟨1160566185599830343911205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3094843161599547583763213 1160566185599830343911205)
    ·
      refine ⟨217606159799968189483351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1160566185599830343911205 217606159799968189483351)
      ·
        refine ⟨326409239699952284225027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217606159799968189483351 326409239699952284225027)
        ·
          refine ⟨489613859549928426337541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 326409239699952284225027 489613859549928426337541)
          ·
            refine ⟨91802598665611579938289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 489613859549928426337541 91802598665611579938289)
            ·
              refine ⟨68851948999208684953717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91802598665611579938289 68851948999208684953717)
              ·
                refine ⟨6454870218675814214411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 68851948999208684953717 6454870218675814214411)
                ·
                  rfl

theorem cell21_84853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 2, 5].length) (baseStart_84853 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_84853 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_84853 prefixEnd_84853 := by exact prefixLift 84853
  have htrace : WordTrace (prefixWord ++ tailWord_84853) baseStart_84853 baseEnd_84853 := by
    simpa [prefixWord, tailWord_84853, baseEnd_84853] using wordTrace_append hprefix tailTrace_84853
  have hstable : (prefixWord ++ tailWord_84853).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84853).length < 2 ^ (prefixWord ++ tailWord_84853).sum := by decide
  have hdescent : baseEnd_84853 < baseStart_84853 := by decide
  rcases family_descends (prefixWord ++ tailWord_84853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84895 : List Nat := [1, 1, 2, 5, 2, 1, 1, 8]
def baseStart_84895 : Nat := 118140960795 + 84895 * 2 ^ 59
def prefixEnd_84895 : Nat := 4983230072969 + 3 ^ 40 * 84895 * 2
def baseEnd_84895 : Nat := 6458065209414900981049

theorem tailTrace_84895 : CollatzResearch.WordTrace tailWord_84895 prefixEnd_84895 6458065209414900981049 := by
  unfold tailWord_84895
  simp only [CollatzResearch.WordTrace]
  refine ⟨3096375027447388756792139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2064250018298259171194759 3096375027447388756792139)
  ·
    refine ⟨4644562541171083135188209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3096375027447388756792139 4644562541171083135188209)
    ·
      refine ⟨3483421905878312351391157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4644562541171083135188209 3483421905878312351391157)
      ·
        refine ⟨326570803676091782942921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3483421905878312351391157 326570803676091782942921)
        ·
          refine ⟨244928102757068837207191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 326570803676091782942921 244928102757068837207191)
          ·
            refine ⟨367392154135603255810787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 244928102757068837207191 367392154135603255810787)
            ·
              refine ⟨551088231203404883716181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 367392154135603255810787 551088231203404883716181)
              ·
                refine ⟨6458065209414900981049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 551088231203404883716181 6458065209414900981049)
                ·
                  rfl

theorem cell21_84895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 8].length) (baseStart_84895 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_84895 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_84895 prefixEnd_84895 := by exact prefixLift 84895
  have htrace : WordTrace (prefixWord ++ tailWord_84895) baseStart_84895 baseEnd_84895 := by
    simpa [prefixWord, tailWord_84895, baseEnd_84895] using wordTrace_append hprefix tailTrace_84895
  have hstable : (prefixWord ++ tailWord_84895).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84895).length < 2 ^ (prefixWord ++ tailWord_84895).sum := by decide
  have hdescent : baseEnd_84895 < baseStart_84895 := by decide
  rcases family_descends (prefixWord ++ tailWord_84895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84898 : List Nat := [3, 3, 1, 2, 2, 2, 1, 3, 4]
def baseStart_84898 : Nat := 118140960795 + 84898 * 2 ^ 59
def prefixEnd_84898 : Nat := 4983230072969 + 3 ^ 40 * 84898 * 2
def baseEnd_84898 : Nat := 19374880269117364393141

theorem tailTrace_84898 : CollatzResearch.WordTrace tailWord_84898 prefixEnd_84898 19374880269117364393141 := by
  unfold tailWord_84898
  simp only [CollatzResearch.WordTrace]
  refine ⟨774121111609130067287837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2064322964291013512767565 774121111609130067287837)
  ·
    refine ⟨290295416853423775232939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 774121111609130067287837 290295416853423775232939)
    ·
      refine ⟨435443125280135662849409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 290295416853423775232939 435443125280135662849409)
      ·
        refine ⟨326582343960101747137057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 435443125280135662849409 326582343960101747137057)
        ·
          refine ⟨244936757970076310352793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 326582343960101747137057 244936757970076310352793)
          ·
            refine ⟨183702568477557232764595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 244936757970076310352793 183702568477557232764595)
            ·
              refine ⟨275553852716335849146893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 183702568477557232764595 275553852716335849146893)
              ·
                refine ⟨103332694768625943430085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 275553852716335849146893 103332694768625943430085)
                ·
                  refine ⟨19374880269117364393141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 103332694768625943430085 19374880269117364393141)
                  ·
                    rfl

theorem cell21_84898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 3, 4].length) (baseStart_84898 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_84898 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_84898 prefixEnd_84898 := by exact prefixLift 84898
  have htrace : WordTrace (prefixWord ++ tailWord_84898) baseStart_84898 baseEnd_84898 := by
    simpa [prefixWord, tailWord_84898, baseEnd_84898] using wordTrace_append hprefix tailTrace_84898
  have hstable : (prefixWord ++ tailWord_84898).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84898).length < 2 ^ (prefixWord ++ tailWord_84898).sum := by decide
  have hdescent : baseEnd_84898 < baseStart_84898 := by decide
  rcases family_descends (prefixWord ++ tailWord_84898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84943 : List Nat := [1, 1, 2, 1, 1, 7, 1, 4, 3]
def baseStart_84943 : Nat := 118140960795 + 84943 * 2 ^ 59
def prefixEnd_84943 : Nat := 4983230072969 + 3 ^ 40 * 84943 * 2
def baseEnd_84943 : Nat := 19385149882207286143049

theorem tailTrace_84943 : CollatzResearch.WordTrace tailWord_84943 prefixEnd_84943 19385149882207286143049 := by
  unfold tailWord_84943
  simp only [CollatzResearch.WordTrace]
  refine ⟨3098125731273492954539483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2065417154182328636359655 3098125731273492954539483)
  ·
    refine ⟨4647188596910239431809225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3098125731273492954539483 4647188596910239431809225)
    ·
      refine ⟨3485391447682679573856919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4647188596910239431809225 3485391447682679573856919)
      ·
        refine ⟨5228087171524019360785379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3485391447682679573856919 5228087171524019360785379)
        ·
          refine ⟨7842130757286029041178069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5228087171524019360785379 7842130757286029041178069)
          ·
            refine ⟨183799939623891305652611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 7842130757286029041178069 183799939623891305652611)
            ·
              refine ⟨275699909435836958478917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 183799939623891305652611 275699909435836958478917)
              ·
                refine ⟨51693733019219429714797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 275699909435836958478917 51693733019219429714797)
                ·
                  refine ⟨19385149882207286143049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51693733019219429714797 19385149882207286143049)
                  ·
                    rfl

theorem cell21_84943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 4, 3].length) (baseStart_84943 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_84943 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_84943 prefixEnd_84943 := by exact prefixLift 84943
  have htrace : WordTrace (prefixWord ++ tailWord_84943) baseStart_84943 baseEnd_84943 := by
    simpa [prefixWord, tailWord_84943, baseEnd_84943] using wordTrace_append hprefix tailTrace_84943
  have hstable : (prefixWord ++ tailWord_84943).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84943).length < 2 ^ (prefixWord ++ tailWord_84943).sum := by decide
  have hdescent : baseEnd_84943 < baseStart_84943 := by decide
  rcases family_descends (prefixWord ++ tailWord_84943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84985 : List Nat := [1, 2, 1, 3, 1, 3, 1, 2, 7]
def baseStart_84985 : Nat := 118140960795 + 84985 * 2 ^ 59
def prefixEnd_84985 : Nat := 4983230072969 + 3 ^ 40 * 84985 * 2
def baseEnd_84985 : Nat := 19394734854424546442963

theorem tailTrace_84985 : CollatzResearch.WordTrace tailWord_84985 prefixEnd_84985 19394734854424546442963 := by
  unfold tailWord_84985
  simp only [CollatzResearch.WordTrace]
  refine ⟨3099657597121334127568409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2066438398080889418378939 3099657597121334127568409)
  ·
    refine ⟨2324743197841000595676307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3099657597121334127568409 2324743197841000595676307)
    ·
      refine ⟨3487114796761500893514461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2324743197841000595676307 3487114796761500893514461)
      ·
        refine ⟨1307668048785562835067923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3487114796761500893514461 1307668048785562835067923)
        ·
          refine ⟨1961502073178344252601885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1307668048785562835067923 1961502073178344252601885)
          ·
            refine ⟨735563277441879094725707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1961502073178344252601885 735563277441879094725707)
            ·
              refine ⟨1103344916162818642088561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 735563277441879094725707 1103344916162818642088561)
              ·
                refine ⟨827508687122113981566421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1103344916162818642088561 827508687122113981566421)
                ·
                  refine ⟨19394734854424546442963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 827508687122113981566421 19394734854424546442963)
                  ·
                    rfl

theorem cell21_84985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 2, 7].length) (baseStart_84985 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_84985 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_84985 prefixEnd_84985 := by exact prefixLift 84985
  have htrace : WordTrace (prefixWord ++ tailWord_84985) baseStart_84985 baseEnd_84985 := by
    simpa [prefixWord, tailWord_84985, baseEnd_84985] using wordTrace_append hprefix tailTrace_84985
  have hstable : (prefixWord ++ tailWord_84985).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84985).length < 2 ^ (prefixWord ++ tailWord_84985).sum := by decide
  have hdescent : baseEnd_84985 < baseStart_84985 := by decide
  rcases family_descends (prefixWord ++ tailWord_84985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85002 : List Nat := [3, 1, 2, 2, 3, 1, 1, 3, 5]
def baseStart_85002 : Nat := 118140960795 + 85002 * 2 ^ 59
def prefixEnd_85002 : Nat := 4983230072969 + 3 ^ 40 * 85002 * 2
def baseEnd_85002 : Nat := 19398614486036294659595

theorem tailTrace_85002 : CollatzResearch.WordTrace tailWord_85002 prefixEnd_85002 19398614486036294659595 := by
  unfold tailWord_85002
  simp only [CollatzResearch.WordTrace]
  refine ⟨775069409514936507734315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2066851758706497353958173 775069409514936507734315)
  ·
    refine ⟨1162604114272404761601473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 775069409514936507734315 1162604114272404761601473)
    ·
      refine ⟨871953085704303571201105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1162604114272404761601473 871953085704303571201105)
      ·
        refine ⟨653964814278227678400829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 871953085704303571201105 653964814278227678400829)
        ·
          refine ⟨245236805354335379400311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 653964814278227678400829 245236805354335379400311)
          ·
            refine ⟨367855208031503069100467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 245236805354335379400311 367855208031503069100467)
            ·
              refine ⟨551782812047254603650701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 367855208031503069100467 551782812047254603650701)
              ·
                refine ⟨206918554517720476369013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 551782812047254603650701 206918554517720476369013)
                ·
                  refine ⟨19398614486036294659595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 206918554517720476369013 19398614486036294659595)
                  ·
                    rfl

theorem cell21_85002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 3, 5].length) (baseStart_85002 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_85002 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_85002 prefixEnd_85002 := by exact prefixLift 85002
  have htrace : WordTrace (prefixWord ++ tailWord_85002) baseStart_85002 baseEnd_85002 := by
    simpa [prefixWord, tailWord_85002, baseEnd_85002] using wordTrace_append hprefix tailTrace_85002
  have hstable : (prefixWord ++ tailWord_85002).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85002).length < 2 ^ (prefixWord ++ tailWord_85002).sum := by decide
  have hdescent : baseEnd_85002 < baseStart_85002 := by decide
  rcases family_descends (prefixWord ++ tailWord_85002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85230 : List Nat := [4, 1, 2, 1, 1, 1, 5, 1, 5]
def baseStart_85230 : Nat := 118140960795 + 85230 * 2 ^ 59
def prefixEnd_85230 : Nat := 4983230072969 + 3 ^ 40 * 85230 * 2
def baseEnd_85230 : Nat := 19450647192358564859129

theorem tailTrace_85230 : CollatzResearch.WordTrace tailWord_85230 prefixEnd_85230 19450647192358564859129 := by
  unfold tailWord_85230
  simp only [CollatzResearch.WordTrace]
  refine ⟨388574185154217621279643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2072395654155827313491429 388574185154217621279643)
  ·
    refine ⟨582861277731326431919465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 388574185154217621279643 582861277731326431919465)
    ·
      refine ⟨437145958298494823939599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 582861277731326431919465 437145958298494823939599)
      ·
        refine ⟨655718937447742235909399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 437145958298494823939599 655718937447742235909399)
        ·
          refine ⟨983578406171613353864099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 655718937447742235909399 983578406171613353864099)
          ·
            refine ⟨1475367609257420030796149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 983578406171613353864099 1475367609257420030796149)
            ·
              refine ⟨138315713367883127887139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1475367609257420030796149 138315713367883127887139)
              ·
                refine ⟨207473570051824691830709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 138315713367883127887139 207473570051824691830709)
                ·
                  refine ⟨19450647192358564859129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 207473570051824691830709 19450647192358564859129)
                  ·
                    rfl

theorem cell21_85230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 5, 1, 5].length) (baseStart_85230 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_85230 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_85230 prefixEnd_85230 := by exact prefixLift 85230
  have htrace : WordTrace (prefixWord ++ tailWord_85230) baseStart_85230 baseEnd_85230 := by
    simpa [prefixWord, tailWord_85230, baseEnd_85230] using wordTrace_append hprefix tailTrace_85230
  have hstable : (prefixWord ++ tailWord_85230).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85230).length < 2 ^ (prefixWord ++ tailWord_85230).sum := by decide
  have hdescent : baseEnd_85230 < baseStart_85230 := by decide
  rcases family_descends (prefixWord ++ tailWord_85230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85236 : List Nat := [2, 6, 1, 2, 1, 1, 1, 3, 4]
def baseStart_85236 : Nat := 118140960795 + 85236 * 2 ^ 59
def prefixEnd_85236 : Nat := 4983230072969 + 3 ^ 40 * 85236 * 2
def baseEnd_85236 : Nat := 19452016474103887759117

theorem tailTrace_85236 : CollatzResearch.WordTrace tailWord_85236 prefixEnd_85236 19452016474103887759117 := by
  unfold tailWord_85236
  simp only [CollatzResearch.WordTrace]
  refine ⟨1554406159606001997477781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2072541546141335996637041 1554406159606001997477781)
  ·
    refine ⟨72862788731531343631771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 1554406159606001997477781 72862788731531343631771)
    ·
      refine ⟨109294183097297015447657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72862788731531343631771 109294183097297015447657)
      ·
        refine ⟨81970637322972761585743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109294183097297015447657 81970637322972761585743)
        ·
          refine ⟨122955955984459142378615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81970637322972761585743 122955955984459142378615)
          ·
            refine ⟨184433933976688713567923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122955955984459142378615 184433933976688713567923)
            ·
              refine ⟨276650900965033070351885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 184433933976688713567923 276650900965033070351885)
              ·
                refine ⟨103744087861887401381957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 276650900965033070351885 103744087861887401381957)
                ·
                  refine ⟨19452016474103887759117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 103744087861887401381957 19452016474103887759117)
                  ·
                    rfl

theorem cell21_85236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_85236 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_85236 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_85236 prefixEnd_85236 := by exact prefixLift 85236
  have htrace : WordTrace (prefixWord ++ tailWord_85236) baseStart_85236 baseEnd_85236 := by
    simpa [prefixWord, tailWord_85236, baseEnd_85236] using wordTrace_append hprefix tailTrace_85236
  have hstable : (prefixWord ++ tailWord_85236).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85236).length < 2 ^ (prefixWord ++ tailWord_85236).sum := by decide
  have hdescent : baseEnd_85236 < baseStart_85236 := by decide
  rcases family_descends (prefixWord ++ tailWord_85236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85303 : List Nat := [1, 1, 3, 1, 2, 1, 1, 1, 10]
def baseStart_85303 : Nat := 118140960795 + 85303 * 2 ^ 59
def prefixEnd_85303 : Nat := 4983230072969 + 3 ^ 40 * 85303 * 2
def baseEnd_85303 : Nat := 19467306786926660142313

theorem tailTrace_85303 : CollatzResearch.WordTrace tailWord_85303 prefixEnd_85303 19467306786926660142313 := by
  unfold tailWord_85303
  simp only [CollatzResearch.WordTrace]
  refine ⟨3111256009969274437644563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2074170673312849625096375 3111256009969274437644563)
  ·
    refine ⟨4666884014953911656466845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3111256009969274437644563 4666884014953911656466845)
    ·
      refine ⟨1750081505607716871175067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4666884014953911656466845 1750081505607716871175067)
      ·
        refine ⟨2625122258411575306762601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1750081505607716871175067 2625122258411575306762601)
        ·
          refine ⟨1968841693808681480071951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2625122258411575306762601 1968841693808681480071951)
          ·
            refine ⟨2953262540713022220107927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1968841693808681480071951 2953262540713022220107927)
            ·
              refine ⟨4429893811069533330161891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2953262540713022220107927 4429893811069533330161891)
              ·
                refine ⟨6644840716604299995242837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4429893811069533330161891 6644840716604299995242837)
                ·
                  refine ⟨19467306786926660142313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 6644840716604299995242837 19467306786926660142313)
                  ·
                    rfl

theorem cell21_85303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 10].length) (baseStart_85303 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_85303 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_85303 prefixEnd_85303 := by exact prefixLift 85303
  have htrace : WordTrace (prefixWord ++ tailWord_85303) baseStart_85303 baseEnd_85303 := by
    simpa [prefixWord, tailWord_85303, baseEnd_85303] using wordTrace_append hprefix tailTrace_85303
  have hstable : (prefixWord ++ tailWord_85303).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85303).length < 2 ^ (prefixWord ++ tailWord_85303).sum := by decide
  have hdescent : baseEnd_85303 < baseStart_85303 := by decide
  rcases family_descends (prefixWord ++ tailWord_85303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85309 : List Nat := [1, 4, 1, 5, 1, 1, 3, 5]
def baseStart_85309 : Nat := 118140960795 + 85309 * 2 ^ 59
def prefixEnd_85309 : Nat := 4983230072969 + 3 ^ 40 * 85309 * 2
def baseEnd_85309 : Nat := 6489558689557327680767

theorem tailTrace_85309 : CollatzResearch.WordTrace tailWord_85309 prefixEnd_85309 6489558689557327680767 := by
  unfold tailWord_85309
  simp only [CollatzResearch.WordTrace]
  refine ⟨3111474847947537462362981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2074316565298358308241987 3111474847947537462362981)
  ·
    refine ⟨583401533990163274193059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3111474847947537462362981 583401533990163274193059)
    ·
      refine ⟨875102300985244911289589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 583401533990163274193059 875102300985244911289589)
      ·
        refine ⟨82040840717366710433399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 875102300985244911289589 82040840717366710433399)
        ·
          refine ⟨123061261076050065650099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82040840717366710433399 123061261076050065650099)
          ·
            refine ⟨184591891614075098475149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123061261076050065650099 184591891614075098475149)
            ·
              refine ⟨69221959355278161928181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 184591891614075098475149 69221959355278161928181)
              ·
                refine ⟨6489558689557327680767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 69221959355278161928181 6489558689557327680767)
                ·
                  rfl

theorem cell21_85309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 3, 5].length) (baseStart_85309 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_85309 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_85309 prefixEnd_85309 := by exact prefixLift 85309
  have htrace : WordTrace (prefixWord ++ tailWord_85309) baseStart_85309 baseEnd_85309 := by
    simpa [prefixWord, tailWord_85309, baseEnd_85309] using wordTrace_append hprefix tailTrace_85309
  have hstable : (prefixWord ++ tailWord_85309).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85309).length < 2 ^ (prefixWord ++ tailWord_85309).sum := by decide
  have hdescent : baseEnd_85309 < baseStart_85309 := by decide
  rcases family_descends (prefixWord ++ tailWord_85309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85374 : List Nat := [4, 2, 3, 2, 1, 2, 1, 3, 3]
def baseStart_85374 : Nat := 118140960795 + 85374 * 2 ^ 59
def prefixEnd_85374 : Nat := 4983230072969 + 3 ^ 40 * 85374 * 2
def baseEnd_85374 : Nat := 19483509954246314458835

theorem tailTrace_85374 : CollatzResearch.WordTrace tailWord_85374 prefixEnd_85374 19483509954246314458835 := by
  unfold tailWord_85374
  simp only [CollatzResearch.WordTrace]
  refine ⟨389230699089006695434897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2075897061808035708986117 389230699089006695434897)
  ·
    refine ⟨291923024316755021576173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 389230699089006695434897 291923024316755021576173)
    ·
      refine ⟨109471134118783133091065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 291923024316755021576173 109471134118783133091065)
      ·
        refine ⟨82103350589087349818299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109471134118783133091065 82103350589087349818299)
        ·
          refine ⟨123155025883631024727449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82103350589087349818299 123155025883631024727449)
          ·
            refine ⟨92366269412723268545587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123155025883631024727449 92366269412723268545587)
            ·
              refine ⟨138549404119084902818381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92366269412723268545587 138549404119084902818381)
              ·
                refine ⟨51956026544656838556893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 138549404119084902818381 51956026544656838556893)
                ·
                  refine ⟨19483509954246314458835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51956026544656838556893 19483509954246314458835)
                  ·
                    rfl

theorem cell21_85374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 1, 3, 3].length) (baseStart_85374 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_85374 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_85374 prefixEnd_85374 := by exact prefixLift 85374
  have htrace : WordTrace (prefixWord ++ tailWord_85374) baseStart_85374 baseEnd_85374 := by
    simpa [prefixWord, tailWord_85374, baseEnd_85374] using wordTrace_append hprefix tailTrace_85374
  have hstable : (prefixWord ++ tailWord_85374).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85374).length < 2 ^ (prefixWord ++ tailWord_85374).sum := by decide
  have hdescent : baseEnd_85374 < baseStart_85374 := by decide
  rcases family_descends (prefixWord ++ tailWord_85374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85455 : List Nat := [1, 1, 2, 1, 1, 4, 2, 3, 6]
def baseStart_85455 : Nat := 118140960795 + 85455 * 2 ^ 59
def prefixEnd_85455 : Nat := 4983230072969 + 3 ^ 40 * 85455 * 2
def baseEnd_85455 : Nat := 19501995257808173608669

theorem tailTrace_85455 : CollatzResearch.WordTrace tailWord_85455 prefixEnd_85455 19501995257808173608669 := by
  unfold tailWord_85455
  simp only [CollatzResearch.WordTrace]
  refine ⟨3116799905418604397177819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2077866603612402931451879 3116799905418604397177819)
  ·
    refine ⟨4675199858127906595766729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3116799905418604397177819 4675199858127906595766729)
    ·
      refine ⟨3506399893595929946825047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4675199858127906595766729 3506399893595929946825047)
      ·
        refine ⟨5259599840393894920237571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3506399893595929946825047 5259599840393894920237571)
        ·
          refine ⟨7889399760590842380356357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5259599840393894920237571 7889399760590842380356357)
          ·
            refine ⟨1479262455110782946316817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7889399760590842380356357 1479262455110782946316817)
            ·
              refine ⟨1109446841333087209737613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1479262455110782946316817 1109446841333087209737613)
              ·
                refine ⟨416042565499907703651605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1109446841333087209737613 416042565499907703651605)
                ·
                  refine ⟨19501995257808173608669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 416042565499907703651605 19501995257808173608669)
                  ·
                    rfl

theorem cell21_85455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 3, 6].length) (baseStart_85455 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_85455 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_85455 prefixEnd_85455 := by exact prefixLift 85455
  have htrace : WordTrace (prefixWord ++ tailWord_85455) baseStart_85455 baseEnd_85455 := by
    simpa [prefixWord, tailWord_85455, baseEnd_85455] using wordTrace_append hprefix tailTrace_85455
  have hstable : (prefixWord ++ tailWord_85455).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85455).length < 2 ^ (prefixWord ++ tailWord_85455).sum := by decide
  have hdescent : baseEnd_85455 < baseStart_85455 := by decide
  rcases family_descends (prefixWord ++ tailWord_85455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85506 : List Nat := [3, 4, 1, 2, 1, 1, 3, 2, 4]
def baseStart_85506 : Nat := 118140960795 + 85506 * 2 ^ 59
def prefixEnd_85506 : Nat := 4983230072969 + 3 ^ 40 * 85506 * 2
def baseEnd_85506 : Nat := 19513634152643418258565

theorem tailTrace_85506 : CollatzResearch.WordTrace tailWord_85506 prefixEnd_85506 19513634152643418258565 := by
  unfold tailWord_85506
  simp only [CollatzResearch.WordTrace]
  refine ⟨779665007058460026821093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2079106685489226738189581 779665007058460026821093)
  ·
    refine ⟨146187188823461255028955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 779665007058460026821093 146187188823461255028955)
    ·
      refine ⟨219280783235191882543433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146187188823461255028955 219280783235191882543433)
      ·
        refine ⟨164460587426393911907575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 219280783235191882543433 164460587426393911907575)
        ·
          refine ⟨246690881139590867861363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164460587426393911907575 246690881139590867861363)
          ·
            refine ⟨370036321709386301792045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 246690881139590867861363 370036321709386301792045)
            ·
              refine ⟨138763620641019863172017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 370036321709386301792045 138763620641019863172017)
              ·
                refine ⟨104072715480764897379013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 138763620641019863172017 104072715480764897379013)
                ·
                  refine ⟨19513634152643418258565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 104072715480764897379013 19513634152643418258565)
                  ·
                    rfl

theorem cell21_85506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_85506 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_85506 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_85506 prefixEnd_85506 := by exact prefixLift 85506
  have htrace : WordTrace (prefixWord ++ tailWord_85506) baseStart_85506 baseEnd_85506 := by
    simpa [prefixWord, tailWord_85506, baseEnd_85506] using wordTrace_append hprefix tailTrace_85506
  have hstable : (prefixWord ++ tailWord_85506).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85506).length < 2 ^ (prefixWord ++ tailWord_85506).sum := by decide
  have hdescent : baseEnd_85506 < baseStart_85506 := by decide
  rcases family_descends (prefixWord ++ tailWord_85506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85607 : List Nat := [1, 1, 5, 1, 1, 1, 2, 1, 8]
def baseStart_85607 : Nat := 118140960795 + 85607 * 2 ^ 59
def prefixEnd_85607 : Nat := 4983230072969 + 3 ^ 40 * 85607 * 2
def baseEnd_85607 : Nat := 19536683728689687075025

theorem tailTrace_85607 : CollatzResearch.WordTrace tailWord_85607 prefixEnd_85607 19536683728689687075025 := by
  unfold tailWord_85607
  simp only [CollatzResearch.WordTrace]
  refine ⟨3122343800867934356711075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2081562533911956237807383 3122343800867934356711075)
  ·
    refine ⟨4683515701301901535066613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3122343800867934356711075 4683515701301901535066613)
    ·
      refine ⟨439079596997053268912495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4683515701301901535066613 439079596997053268912495)
      ·
        refine ⟨658619395495579903368743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 439079596997053268912495 658619395495579903368743)
        ·
          refine ⟨987929093243369855053115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 658619395495579903368743 987929093243369855053115)
          ·
            refine ⟨1481893639865054782579673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 987929093243369855053115 1481893639865054782579673)
            ·
              refine ⟨1111420229898791086934755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1481893639865054782579673 1111420229898791086934755)
              ·
                refine ⟨1667130344848186630402133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1111420229898791086934755 1667130344848186630402133)
                ·
                  refine ⟨19536683728689687075025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1667130344848186630402133 19536683728689687075025)
                  ·
                    rfl

theorem cell21_85607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 8].length) (baseStart_85607 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_85607 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_85607 prefixEnd_85607 := by exact prefixLift 85607
  have htrace : WordTrace (prefixWord ++ tailWord_85607) baseStart_85607 baseEnd_85607 := by
    simpa [prefixWord, tailWord_85607, baseEnd_85607] using wordTrace_append hprefix tailTrace_85607
  have hstable : (prefixWord ++ tailWord_85607).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85607).length < 2 ^ (prefixWord ++ tailWord_85607).sum := by decide
  have hdescent : baseEnd_85607 < baseStart_85607 := by decide
  rcases family_descends (prefixWord ++ tailWord_85607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85655 : List Nat := [1, 1, 3, 3, 2, 3, 3, 5]
def baseStart_85655 : Nat := 118140960795 + 85655 * 2 ^ 59
def prefixEnd_85655 : Nat := 4983230072969 + 3 ^ 40 * 85655 * 2
def baseEnd_85655 : Nat := 6515879327550756758309

theorem tailTrace_85655 : CollatzResearch.WordTrace tailWord_85655 prefixEnd_85655 6515879327550756758309 := by
  unfold tailWord_85655
  simp only [CollatzResearch.WordTrace]
  refine ⟨3124094504694038554458419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2082729669796025702972279 3124094504694038554458419)
  ·
    refine ⟨4686141757041057831687629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3124094504694038554458419 4686141757041057831687629)
    ·
      refine ⟨1757303158890396686882861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4686141757041057831687629 1757303158890396686882861)
      ·
        refine ⟨658988684583898757581073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1757303158890396686882861 658988684583898757581073)
        ·
          refine ⟨494241513437924068185805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 658988684583898757581073 494241513437924068185805)
          ·
            refine ⟨185340567539221525569677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 494241513437924068185805 185340567539221525569677)
            ·
              refine ⟨69502712827208072088629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 185340567539221525569677 69502712827208072088629)
              ·
                refine ⟨6515879327550756758309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 69502712827208072088629 6515879327550756758309)
                ·
                  rfl

theorem cell21_85655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 3, 5].length) (baseStart_85655 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_85655 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_85655 prefixEnd_85655 := by exact prefixLift 85655
  have htrace : WordTrace (prefixWord ++ tailWord_85655) baseStart_85655 baseEnd_85655 := by
    simpa [prefixWord, tailWord_85655, baseEnd_85655] using wordTrace_append hprefix tailTrace_85655
  have hstable : (prefixWord ++ tailWord_85655).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85655).length < 2 ^ (prefixWord ++ tailWord_85655).sum := by decide
  have hdescent : baseEnd_85655 < baseStart_85655 := by decide
  rcases family_descends (prefixWord ++ tailWord_85655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85683 : List Nat := [1, 1, 1, 2, 3, 3, 3, 1, 6]
def baseStart_85683 : Nat := 118140960795 + 85683 * 2 ^ 59
def prefixEnd_85683 : Nat := 4983230072969 + 3 ^ 40 * 85683 * 2
def baseEnd_85683 : Nat := 19554027964130443808203

theorem tailTrace_85683 : CollatzResearch.WordTrace tailWord_85683 prefixEnd_85683 19554027964130443808203 := by
  unfold tailWord_85683
  simp only [CollatzResearch.WordTrace]
  refine ⟨3125115748592599336477703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2083410499061732890985135 3125115748592599336477703)
  ·
    refine ⟨4687673622888899004716555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3125115748592599336477703 4687673622888899004716555)
    ·
      refine ⟨7031510434333348507074833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4687673622888899004716555 7031510434333348507074833)
      ·
        refine ⟨5273632825750011380306125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7031510434333348507074833 5273632825750011380306125)
        ·
          refine ⟨1977612309656254267614797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5273632825750011380306125 1977612309656254267614797)
          ·
            refine ⟨741604616121095350355549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1977612309656254267614797 741604616121095350355549)
            ·
              refine ⟨278101731045410756383331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 741604616121095350355549 278101731045410756383331)
              ·
                refine ⟨417152596568116134574997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 278101731045410756383331 417152596568116134574997)
                ·
                  refine ⟨19554027964130443808203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 417152596568116134574997 19554027964130443808203)
                  ·
                    rfl

theorem cell21_85683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 1, 6].length) (baseStart_85683 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_85683 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_85683 prefixEnd_85683 := by exact prefixLift 85683
  have htrace : WordTrace (prefixWord ++ tailWord_85683) baseStart_85683 baseEnd_85683 := by
    simpa [prefixWord, tailWord_85683, baseEnd_85683] using wordTrace_append hprefix tailTrace_85683
  have hstable : (prefixWord ++ tailWord_85683).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85683).length < 2 ^ (prefixWord ++ tailWord_85683).sum := by decide
  have hdescent : baseEnd_85683 < baseStart_85683 := by decide
  rcases family_descends (prefixWord ++ tailWord_85683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85728 : List Nat := [2, 1, 1, 3, 1, 2, 2, 2, 7]
def baseStart_85728 : Nat := 118140960795 + 85728 * 2 ^ 59
def prefixEnd_85728 : Nat := 4983230072969 + 3 ^ 40 * 85728 * 2
def baseEnd_85728 : Nat := 19564297577220365558111

theorem tailTrace_85728 : CollatzResearch.WordTrace tailWord_85728 prefixEnd_85728 19564297577220365558111 := by
  unfold tailWord_85728
  simp only [CollatzResearch.WordTrace]
  refine ⟨1563378516714786010932919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2084504688953048014577225 1563378516714786010932919)
  ·
    refine ⟨2345067775072179016399379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1563378516714786010932919 2345067775072179016399379)
    ·
      refine ⟨3517601662608268524599069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2345067775072179016399379 3517601662608268524599069)
      ·
        refine ⟨1319100623478100696724651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3517601662608268524599069 1319100623478100696724651)
        ·
          refine ⟨1978650935217151045086977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1319100623478100696724651 1978650935217151045086977)
          ·
            refine ⟨1483988201412863283815233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1978650935217151045086977 1483988201412863283815233)
            ·
              refine ⟨1112991151059647462861425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1483988201412863283815233 1112991151059647462861425)
              ·
                refine ⟨834743363294735597146069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1112991151059647462861425 834743363294735597146069)
                ·
                  refine ⟨19564297577220365558111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 834743363294735597146069 19564297577220365558111)
                  ·
                    rfl

theorem cell21_85728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 2, 7].length) (baseStart_85728 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_85728 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_85728 prefixEnd_85728 := by exact prefixLift 85728
  have htrace : WordTrace (prefixWord ++ tailWord_85728) baseStart_85728 baseEnd_85728 := by
    simpa [prefixWord, tailWord_85728, baseEnd_85728] using wordTrace_append hprefix tailTrace_85728
  have hstable : (prefixWord ++ tailWord_85728).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85728).length < 2 ^ (prefixWord ++ tailWord_85728).sum := by decide
  have hdescent : baseEnd_85728 < baseStart_85728 := by decide
  rcases family_descends (prefixWord ++ tailWord_85728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85731 : List Nat := [1, 1, 1, 7, 2, 2, 7]
def baseStart_85731 : Nat := 118140960795 + 85731 * 2 ^ 59
def prefixEnd_85731 : Nat := 4983230072969 + 3 ^ 40 * 85731 * 2
def baseEnd_85731 : Nat := 2173886913121447445345

theorem tailTrace_85731 : CollatzResearch.WordTrace tailWord_85731 prefixEnd_85731 2173886913121447445345 := by
  unfold tailWord_85731
  simp only [CollatzResearch.WordTrace]
  refine ⟨3126866452418703534225047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2084577634945802356150031 3126866452418703534225047)
  ·
    refine ⟨4690299678628055301337571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3126866452418703534225047 4690299678628055301337571)
    ·
      refine ⟨7035449517942082952006357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4690299678628055301337571 7035449517942082952006357)
      ·
        refine ⟨164893348076767569187649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 7035449517942082952006357 164893348076767569187649)
        ·
          refine ⟨123670011057575676890737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 164893348076767569187649 123670011057575676890737)
          ·
            refine ⟨92752508293181757668053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123670011057575676890737 92752508293181757668053)
            ·
              refine ⟨2173886913121447445345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 92752508293181757668053 2173886913121447445345)
              ·
                rfl

theorem cell21_85731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 7].length) (baseStart_85731 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_85731 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_85731 prefixEnd_85731 := by exact prefixLift 85731
  have htrace : WordTrace (prefixWord ++ tailWord_85731) baseStart_85731 baseEnd_85731 := by
    simpa [prefixWord, tailWord_85731, baseEnd_85731] using wordTrace_append hprefix tailTrace_85731
  have hstable : (prefixWord ++ tailWord_85731).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85731).length < 2 ^ (prefixWord ++ tailWord_85731).sum := by decide
  have hdescent : baseEnd_85731 < baseStart_85731 := by decide
  rcases family_descends (prefixWord ++ tailWord_85731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85745 : List Nat := [1, 2, 2, 2, 2, 3, 3, 1, 5]
def baseStart_85745 : Nat := 118140960795 + 85745 * 2 ^ 59
def prefixEnd_85745 : Nat := 4983230072969 + 3 ^ 40 * 85745 * 2
def baseEnd_85745 : Nat := 19568177208832113774743

theorem tailTrace_85745 : CollatzResearch.WordTrace tailWord_85745 prefixEnd_85745 19568177208832113774743 := by
  unfold tailWord_85745
  simp only [CollatzResearch.WordTrace]
  refine ⟨3127377074367983925234689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2084918049578655950156459 3127377074367983925234689)
  ·
    refine ⟨2345532805775987943926017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3127377074367983925234689 2345532805775987943926017)
    ·
      refine ⟨1759149604331990957944513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2345532805775987943926017 1759149604331990957944513)
      ·
        refine ⟨1319362203248993218458385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1759149604331990957944513 1319362203248993218458385)
        ·
          refine ⟨989521652436744913843789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1319362203248993218458385 989521652436744913843789)
          ·
            refine ⟨371070619663779342691421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 989521652436744913843789 371070619663779342691421)
            ·
              refine ⟨139151482373917253509283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 371070619663779342691421 139151482373917253509283)
              ·
                refine ⟨208727223560875880263925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 139151482373917253509283 208727223560875880263925)
                ·
                  refine ⟨19568177208832113774743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 208727223560875880263925 19568177208832113774743)
                  ·
                    rfl

theorem cell21_85745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 3, 1, 5].length) (baseStart_85745 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_85745 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_85745 prefixEnd_85745 := by exact prefixLift 85745
  have htrace : WordTrace (prefixWord ++ tailWord_85745) baseStart_85745 baseEnd_85745 := by
    simpa [prefixWord, tailWord_85745, baseEnd_85745] using wordTrace_append hprefix tailTrace_85745
  have hstable : (prefixWord ++ tailWord_85745).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85745).length < 2 ^ (prefixWord ++ tailWord_85745).sum := by decide
  have hdescent : baseEnd_85745 < baseStart_85745 := by decide
  rcases family_descends (prefixWord ++ tailWord_85745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85748 : List Nat := [2, 6, 1, 1, 1, 1, 1, 8]
def baseStart_85748 : Nat := 118140960795 + 85748 * 2 ^ 59
def prefixEnd_85748 : Nat := 4983230072969 + 3 ^ 40 * 85748 * 2
def baseEnd_85748 : Nat := 6522953949901591741579

theorem tailTrace_85748 : CollatzResearch.WordTrace tailWord_85748 prefixEnd_85748 6522953949901591741579 := by
  unfold tailWord_85748
  simp only [CollatzResearch.WordTrace]
  refine ⟨1563743246678557718796949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2084990995571410291729265 1563743246678557718796949)
  ·
    refine ⟨73300464688057393068607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 1563743246678557718796949 73300464688057393068607)
    ·
      refine ⟨109950697032086089602911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73300464688057393068607 109950697032086089602911)
      ·
        refine ⟨164926045548129134404367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109950697032086089602911 164926045548129134404367)
        ·
          refine ⟨247389068322193701606551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164926045548129134404367 247389068322193701606551)
          ·
            refine ⟨371083602483290552409827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 247389068322193701606551 371083602483290552409827)
            ·
              refine ⟨556625403724935828614741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 371083602483290552409827 556625403724935828614741)
              ·
                refine ⟨6522953949901591741579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 556625403724935828614741 6522953949901591741579)
                ·
                  rfl

theorem cell21_85748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 8].length) (baseStart_85748 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_85748 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_85748 prefixEnd_85748 := by exact prefixLift 85748
  have htrace : WordTrace (prefixWord ++ tailWord_85748) baseStart_85748 baseEnd_85748 := by
    simpa [prefixWord, tailWord_85748, baseEnd_85748] using wordTrace_append hprefix tailTrace_85748
  have hstable : (prefixWord ++ tailWord_85748).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85748).length < 2 ^ (prefixWord ++ tailWord_85748).sum := by decide
  have hdescent : baseEnd_85748 < baseStart_85748 := by decide
  rcases family_descends (prefixWord ++ tailWord_85748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85796 : List Nat := [2, 3, 1, 3, 2, 3, 2, 2, 3]
def baseStart_85796 : Nat := 118140960795 + 85796 * 2 ^ 59
def prefixEnd_85796 : Nat := 4983230072969 + 3 ^ 40 * 85796 * 2
def baseEnd_85796 : Nat := 19579816103667358424639

theorem tailTrace_85796 : CollatzResearch.WordTrace tailWord_85796 prefixEnd_85796 19579816103667358424639 := by
  unfold tailWord_85796
  simp only [CollatzResearch.WordTrace]
  refine ⟨1564618598591609817670621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2086158131455479756894161 1564618598591609817670621)
  ·
    refine ⟨586731974471853681626483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1564618598591609817670621 586731974471853681626483)
    ·
      refine ⟨880097961707780522439725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 586731974471853681626483 880097961707780522439725)
      ·
        refine ⟨330036735640417695914897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 880097961707780522439725 330036735640417695914897)
        ·
          refine ⟨247527551730313271936173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 330036735640417695914897 247527551730313271936173)
          ·
            refine ⟨92822831898867476976065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 247527551730313271936173 92822831898867476976065)
            ·
              refine ⟨69617123924150607732049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92822831898867476976065 69617123924150607732049)
              ·
                refine ⟨52212842943112955799037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69617123924150607732049 52212842943112955799037)
                ·
                  refine ⟨19579816103667358424639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52212842943112955799037 19579816103667358424639)
                  ·
                    rfl

theorem cell21_85796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 2, 2, 3].length) (baseStart_85796 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_85796 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_85796 prefixEnd_85796 := by exact prefixLift 85796
  have htrace : WordTrace (prefixWord ++ tailWord_85796) baseStart_85796 baseEnd_85796 := by
    simpa [prefixWord, tailWord_85796, baseEnd_85796] using wordTrace_append hprefix tailTrace_85796
  have hstable : (prefixWord ++ tailWord_85796).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85796).length < 2 ^ (prefixWord ++ tailWord_85796).sum := by decide
  have hdescent : baseEnd_85796 < baseStart_85796 := by decide
  rcases family_descends (prefixWord ++ tailWord_85796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85821 : List Nat := [1, 4, 1, 4, 1, 1, 1, 1, 7]
def baseStart_85821 : Nat := 118140960795 + 85821 * 2 ^ 59
def prefixEnd_85821 : Nat := 4983230072969 + 3 ^ 40 * 85821 * 2
def baseEnd_85821 : Nat := 19585521444272870507921

theorem tailTrace_85821 : CollatzResearch.WordTrace tailWord_85821 prefixEnd_85821 19585521444272870507921 := by
  unfold tailWord_85821
  simp only [CollatzResearch.WordTrace]
  refine ⟨3130149022092648905001317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2086766014728432603334211 3130149022092648905001317)
  ·
    refine ⟨586902941642371669687747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3130149022092648905001317 586902941642371669687747)
    ·
      refine ⟨880354412463557504531621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 586902941642371669687747 880354412463557504531621)
      ·
        refine ⟨165066452336917032099679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 880354412463557504531621 165066452336917032099679)
        ·
          refine ⟨247599678505375548149519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 165066452336917032099679 247599678505375548149519)
          ·
            refine ⟨371399517758063322224279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 247599678505375548149519 371399517758063322224279)
            ·
              refine ⟨557099276637094983336419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 371399517758063322224279 557099276637094983336419)
              ·
                refine ⟨835648914955642475004629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 557099276637094983336419 835648914955642475004629)
                ·
                  refine ⟨19585521444272870507921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 835648914955642475004629 19585521444272870507921)
                  ·
                    rfl

theorem cell21_85821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 1, 7].length) (baseStart_85821 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_85821 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_85821 prefixEnd_85821 := by exact prefixLift 85821
  have htrace : WordTrace (prefixWord ++ tailWord_85821) baseStart_85821 baseEnd_85821 := by
    simpa [prefixWord, tailWord_85821, baseEnd_85821] using wordTrace_append hprefix tailTrace_85821
  have hstable : (prefixWord ++ tailWord_85821).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85821).length < 2 ^ (prefixWord ++ tailWord_85821).sum := by decide
  have hdescent : baseEnd_85821 < baseStart_85821 := by decide
  rcases family_descends (prefixWord ++ tailWord_85821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85849 : List Nat := [1, 2, 1, 2, 2, 3, 10]
def baseStart_85849 : Nat := 118140960795 + 85849 * 2 ^ 59
def prefixEnd_85849 : Nat := 4983230072969 + 3 ^ 40 * 85849 * 2
def baseEnd_85849 : Nat := 2176879047305671560133

theorem tailTrace_85849 : CollatzResearch.WordTrace tailWord_85849 prefixEnd_85849 2176879047305671560133 := by
  unfold tailWord_85849
  simp only [CollatzResearch.WordTrace]
  refine ⟨3131170265991209687020601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2087446843994139791347067 3131170265991209687020601)
  ·
    refine ⟨2348377699493407265265451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3131170265991209687020601 2348377699493407265265451)
    ·
      refine ⟨3522566549240110897898177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2348377699493407265265451 3522566549240110897898177)
      ·
        refine ⟨2641924911930083173423633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3522566549240110897898177 2641924911930083173423633)
        ·
          refine ⟨1981443683947562380067725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2641924911930083173423633 1981443683947562380067725)
          ·
            refine ⟨743041381480335892525397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1981443683947562380067725 743041381480335892525397)
            ·
              refine ⟨2176879047305671560133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 743041381480335892525397 2176879047305671560133)
              ·
                rfl

theorem cell21_85849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 10].length) (baseStart_85849 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_85849 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_85849 prefixEnd_85849 := by exact prefixLift 85849
  have htrace : WordTrace (prefixWord ++ tailWord_85849) baseStart_85849 baseEnd_85849 := by
    simpa [prefixWord, tailWord_85849, baseEnd_85849] using wordTrace_append hprefix tailTrace_85849
  have hstable : (prefixWord ++ tailWord_85849).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85849).length < 2 ^ (prefixWord ++ tailWord_85849).sum := by decide
  have hdescent : baseEnd_85849 < baseStart_85849 := by decide
  rcases family_descends (prefixWord ++ tailWord_85849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85889 : List Nat := [1, 2, 4, 4, 2, 1, 1, 3, 3]
def baseStart_85889 : Nat := 118140960795 + 85889 * 2 ^ 59
def prefixEnd_85889 : Nat := 4983230072969 + 3 ^ 40 * 85889 * 2
def baseEnd_85889 : Nat := 19601039970719863374449

theorem tailTrace_85889 : CollatzResearch.WordTrace tailWord_85889 prefixEnd_85889 19601039970719863374449 := by
  unfold tailWord_85889
  simp only [CollatzResearch.WordTrace]
  refine ⟨3132629185846296518476721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2088419457230864345651147 3132629185846296518476721)
  ·
    refine ⟨2349471889384722388857541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3132629185846296518476721 2349471889384722388857541)
    ·
      refine ⟨440525979259635447910789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2349471889384722388857541 440525979259635447910789)
      ·
        refine ⟨82598621111181646483273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 440525979259635447910789 82598621111181646483273)
        ·
          refine ⟨61948965833386234862455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82598621111181646483273 61948965833386234862455)
          ·
            refine ⟨92923448750079352293683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61948965833386234862455 92923448750079352293683)
            ·
              refine ⟨139385173125119028440525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92923448750079352293683 139385173125119028440525)
              ·
                refine ⟨52269439921919635665197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 139385173125119028440525 52269439921919635665197)
                ·
                  refine ⟨19601039970719863374449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52269439921919635665197 19601039970719863374449)
                  ·
                    rfl

theorem cell21_85889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 1, 3, 3].length) (baseStart_85889 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_85889 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_85889 prefixEnd_85889 := by exact prefixLift 85889
  have htrace : WordTrace (prefixWord ++ tailWord_85889) baseStart_85889 baseEnd_85889 := by
    simpa [prefixWord, tailWord_85889, baseEnd_85889] using wordTrace_append hprefix tailTrace_85889
  have hstable : (prefixWord ++ tailWord_85889).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85889).length < 2 ^ (prefixWord ++ tailWord_85889).sum := by decide
  have hdescent : baseEnd_85889 < baseStart_85889 := by decide
  rcases family_descends (prefixWord ++ tailWord_85889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85911 : List Nat := [1, 1, 3, 3, 1, 3, 2, 1, 6]
def baseStart_85911 : Nat := 118140960795 + 85911 * 2 ^ 59
def prefixEnd_85911 : Nat := 4983230072969 + 3 ^ 40 * 85911 * 2
def baseEnd_85911 : Nat := 19606060670452714007737

theorem tailTrace_85911 : CollatzResearch.WordTrace tailWord_85911 prefixEnd_85911 19606060670452714007737 := by
  unfold tailWord_85911
  simp only [CollatzResearch.WordTrace]
  refine ⟨3133431591766594275777587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2088954394511062850518391 3133431591766594275777587)
  ·
    refine ⟨4700147387649891413666381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3133431591766594275777587 4700147387649891413666381)
    ·
      refine ⟨1762555270368709280124893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4700147387649891413666381 1762555270368709280124893)
      ·
        refine ⟨660958226388265980046835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1762555270368709280124893 660958226388265980046835)
        ·
          refine ⟨991437339582398970070253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 660958226388265980046835 991437339582398970070253)
          ·
            refine ⟨371789002343399613776345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 991437339582398970070253 371789002343399613776345)
            ·
              refine ⟨278841751757549710332259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 371789002343399613776345 278841751757549710332259)
              ·
                refine ⟨418262627636324565498389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 278841751757549710332259 418262627636324565498389)
                ·
                  refine ⟨19606060670452714007737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 418262627636324565498389 19606060670452714007737)
                  ·
                    rfl

theorem cell21_85911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 1, 6].length) (baseStart_85911 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_85911 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_85911 prefixEnd_85911 := by exact prefixLift 85911
  have htrace : WordTrace (prefixWord ++ tailWord_85911) baseStart_85911 baseEnd_85911 := by
    simpa [prefixWord, tailWord_85911, baseEnd_85911] using wordTrace_append hprefix tailTrace_85911
  have hstable : (prefixWord ++ tailWord_85911).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85911).length < 2 ^ (prefixWord ++ tailWord_85911).sum := by decide
  have hdescent : baseEnd_85911 < baseStart_85911 := by decide
  rcases family_descends (prefixWord ++ tailWord_85911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_85914 : List Nat := [3, 1, 1, 4, 2, 3, 1, 1, 5]
def baseStart_85914 : Nat := 118140960795 + 85914 * 2 ^ 59
def prefixEnd_85914 : Nat := 4983230072969 + 3 ^ 40 * 85914 * 2
def baseEnd_85914 : Nat := 19606745311325375457731

theorem tailTrace_85914 : CollatzResearch.WordTrace tailWord_85914 prefixEnd_85914 19606745311325375457731 := by
  unfold tailWord_85914
  simp only [CollatzResearch.WordTrace]
  refine ⟨783385252688931447034199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2089027340503817192091197 783385252688931447034199)
  ·
    refine ⟨1175077879033397170551299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 783385252688931447034199 1175077879033397170551299)
    ·
      refine ⟨1762616818550095755826949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1175077879033397170551299 1762616818550095755826949)
      ·
        refine ⟨330490653478142954217553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1762616818550095755826949 330490653478142954217553)
        ·
          refine ⟨247867990108607215663165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 330490653478142954217553 247867990108607215663165)
          ·
            refine ⟨92950496290727705873687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 247867990108607215663165 92950496290727705873687)
            ·
              refine ⟨139425744436091558810531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92950496290727705873687 139425744436091558810531)
              ·
                refine ⟨209138616654137338215797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 139425744436091558810531 209138616654137338215797)
                ·
                  refine ⟨19606745311325375457731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 209138616654137338215797 19606745311325375457731)
                  ·
                    rfl

theorem cell21_85914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 1, 1, 5].length) (baseStart_85914 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_85914 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_85914 prefixEnd_85914 := by exact prefixLift 85914
  have htrace : WordTrace (prefixWord ++ tailWord_85914) baseStart_85914 baseEnd_85914 := by
    simpa [prefixWord, tailWord_85914, baseEnd_85914] using wordTrace_append hprefix tailTrace_85914
  have hstable : (prefixWord ++ tailWord_85914).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_85914).length < 2 ^ (prefixWord ++ tailWord_85914).sum := by decide
  have hdescent : baseEnd_85914 < baseStart_85914 := by decide
  rcases family_descends (prefixWord ++ tailWord_85914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86052 : List Nat := [2, 3, 1, 4, 2, 2, 2, 5]
def baseStart_86052 : Nat := 118140960795 + 86052 * 2 ^ 59
def prefixEnd_86052 : Nat := 4983230072969 + 3 ^ 40 * 86052 * 2
def baseEnd_86052 : Nat := 6546079597155934052483

theorem tailTrace_86052 : CollatzResearch.WordTrace tailWord_86052 prefixEnd_86052 6546079597155934052483 := by
  unfold tailWord_86052
  simp only [CollatzResearch.WordTrace]
  refine ⟨1569287142127887678330205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2092382856170516904440273 1569287142127887678330205)
  ·
    refine ⟨588482678297957879373827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1569287142127887678330205 588482678297957879373827)
    ·
      refine ⟨882724017446936819060741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 588482678297957879373827 882724017446936819060741)
      ·
        refine ⟨165510753271300653573889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 882724017446936819060741 165510753271300653573889)
        ·
          refine ⟨124133064953475490180417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 165510753271300653573889 124133064953475490180417)
          ·
            refine ⟨93099798715106617635313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124133064953475490180417 93099798715106617635313)
            ·
              refine ⟨69824849036329963226485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93099798715106617635313 69824849036329963226485)
              ·
                refine ⟨6546079597155934052483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 69824849036329963226485 6546079597155934052483)
                ·
                  rfl

theorem cell21_86052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 2, 5].length) (baseStart_86052 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_86052 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_86052 prefixEnd_86052 := by exact prefixLift 86052
  have htrace : WordTrace (prefixWord ++ tailWord_86052) baseStart_86052 baseEnd_86052 := by
    simpa [prefixWord, tailWord_86052, baseEnd_86052] using wordTrace_append hprefix tailTrace_86052
  have hstable : (prefixWord ++ tailWord_86052).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86052).length < 2 ^ (prefixWord ++ tailWord_86052).sum := by decide
  have hdescent : baseEnd_86052 < baseStart_86052 := by decide
  rcases family_descends (prefixWord ++ tailWord_86052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86066 : List Nat := [3, 2, 1, 1, 2, 3, 3, 3, 3]
def baseStart_86066 : Nat := 118140960795 + 86066 * 2 ^ 59
def prefixEnd_86066 : Nat := 4983230072969 + 3 ^ 40 * 86066 * 2
def baseEnd_86066 : Nat := 19641433782206888924087

theorem tailTrace_86066 : CollatzResearch.WordTrace tailWord_86066 prefixEnd_86066 19641433782206888924087 := by
  unfold tailWord_86066
  simp only [CollatzResearch.WordTrace]
  refine ⟨784771226551263936917513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2092723270803370498446701 784771226551263936917513)
  ·
    refine ⟨588578419913447952688135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 784771226551263936917513 588578419913447952688135)
    ·
      refine ⟨882867629870171929032203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 588578419913447952688135 882867629870171929032203)
      ·
        refine ⟨1324301444805257893548305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 882867629870171929032203 1324301444805257893548305)
        ·
          refine ⟨993226083603943420161229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1324301444805257893548305 993226083603943420161229)
          ·
            refine ⟨372459781351478782560461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 993226083603943420161229 372459781351478782560461)
            ·
              refine ⟨139672418006804543460173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 372459781351478782560461 139672418006804543460173)
              ·
                refine ⟨52377156752551703797565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 139672418006804543460173 52377156752551703797565)
                ·
                  refine ⟨19641433782206888924087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52377156752551703797565 19641433782206888924087)
                  ·
                    rfl

theorem cell21_86066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 3, 3, 3].length) (baseStart_86066 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_86066 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_86066 prefixEnd_86066 := by exact prefixLift 86066
  have htrace : WordTrace (prefixWord ++ tailWord_86066) baseStart_86066 baseEnd_86066 := by
    simpa [prefixWord, tailWord_86066, baseEnd_86066] using wordTrace_append hprefix tailTrace_86066
  have hstable : (prefixWord ++ tailWord_86066).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86066).length < 2 ^ (prefixWord ++ tailWord_86066).sum := by decide
  have hdescent : baseEnd_86066 < baseStart_86066 := by decide
  rcases family_descends (prefixWord ++ tailWord_86066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86094 : List Nat := [4, 1, 1, 1, 1, 5, 2, 6]
def baseStart_86094 : Nat := 118140960795 + 86094 * 2 ^ 59
def prefixEnd_86094 : Nat := 4983230072969 + 3 ^ 40 * 86094 * 2
def baseEnd_86094 : Nat := 6549274587895020819121

theorem tailTrace_86094 : CollatzResearch.WordTrace tailWord_86094 prefixEnd_86094 6549274587895020819121 := by
  unfold tailWord_86094
  simp only [CollatzResearch.WordTrace]
  refine ⟨392513268762952066211167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2093404100069077686459557 392513268762952066211167)
  ·
    refine ⟨588769903144428099316751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 392513268762952066211167 588769903144428099316751)
    ·
      refine ⟨883154854716642148975127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 588769903144428099316751 883154854716642148975127)
      ·
        refine ⟨1324732282074963223462691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 883154854716642148975127 1324732282074963223462691)
        ·
          refine ⟨1987098423112444835194037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1324732282074963223462691 1987098423112444835194037)
          ·
            refine ⟨186290477166791703299441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1987098423112444835194037 186290477166791703299441)
            ·
              refine ⟨139717857875093777474581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 186290477166791703299441 139717857875093777474581)
              ·
                refine ⟨6549274587895020819121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 139717857875093777474581 6549274587895020819121)
                ·
                  rfl

theorem cell21_86094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 2, 6].length) (baseStart_86094 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_86094 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_86094 prefixEnd_86094 := by exact prefixLift 86094
  have htrace : WordTrace (prefixWord ++ tailWord_86094) baseStart_86094 baseEnd_86094 := by
    simpa [prefixWord, tailWord_86094, baseEnd_86094] using wordTrace_append hprefix tailTrace_86094
  have hstable : (prefixWord ++ tailWord_86094).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86094).length < 2 ^ (prefixWord ++ tailWord_86094).sum := by decide
  have hdescent : baseEnd_86094 < baseStart_86094 := by decide
  rcases family_descends (prefixWord ++ tailWord_86094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86201 : List Nat := [1, 2, 1, 4, 1, 2, 1, 6, 3]
def baseStart_86201 : Nat := 118140960795 + 86201 * 2 ^ 59
def prefixEnd_86201 : Nat := 4983230072969 + 3 ^ 40 * 86201 * 2
def baseEnd_86201 : Nat := 19672242621476654173811

theorem tailTrace_86201 : CollatzResearch.WordTrace tailWord_86201 prefixEnd_86201 19672242621476654173811 := by
  unfold tailWord_86201
  simp only [CollatzResearch.WordTrace]
  refine ⟨3144008760715973803834457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2096005840477315869222971 3144008760715973803834457)
  ·
    refine ⟨2358006570536980352875843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3144008760715973803834457 2358006570536980352875843)
    ·
      refine ⟨3537009855805470529313765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2358006570536980352875843 3537009855805470529313765)
      ·
        refine ⟨663189347963525724246331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3537009855805470529313765 663189347963525724246331)
        ·
          refine ⟨994784021945288586369497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 663189347963525724246331 994784021945288586369497)
          ·
            refine ⟨746088016458966439777123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 994784021945288586369497 746088016458966439777123)
            ·
              refine ⟨1119132024688449659665685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 746088016458966439777123 1119132024688449659665685)
              ·
                refine ⟨52459313657271077796829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1119132024688449659665685 52459313657271077796829)
                ·
                  refine ⟨19672242621476654173811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52459313657271077796829 19672242621476654173811)
                  ·
                    rfl

theorem cell21_86201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 6, 3].length) (baseStart_86201 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_86201 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_86201 prefixEnd_86201 := by exact prefixLift 86201
  have htrace : WordTrace (prefixWord ++ tailWord_86201) baseStart_86201 baseEnd_86201 := by
    simpa [prefixWord, tailWord_86201, baseEnd_86201] using wordTrace_append hprefix tailTrace_86201
  have hstable : (prefixWord ++ tailWord_86201).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86201).length < 2 ^ (prefixWord ++ tailWord_86201).sum := by decide
  have hdescent : baseEnd_86201 < baseStart_86201 := by decide
  rcases family_descends (prefixWord ++ tailWord_86201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86308 : List Nat := [2, 3, 1, 3, 1, 3, 2, 2, 4]
def baseStart_86308 : Nat := 118140960795 + 86308 * 2 ^ 59
def prefixEnd_86308 : Nat := 4983230072969 + 3 ^ 40 * 86308 * 2
def baseEnd_86308 : Nat := 19696661479268245890259

theorem tailTrace_86308 : CollatzResearch.WordTrace tailWord_86308 prefixEnd_86308 19696661479268245890259 := by
  unfold tailWord_86308
  simp only [CollatzResearch.WordTrace]
  refine ⟨1573955685664165538989789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2098607580885554051986385 1573955685664165538989789)
  ·
    refine ⟨590233382124062077121171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1573955685664165538989789 590233382124062077121171)
    ·
      refine ⟨885350073186093115681757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 590233382124062077121171 885350073186093115681757)
      ·
        refine ⟨332006277444784918380659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 885350073186093115681757 332006277444784918380659)
        ·
          refine ⟨498009416167177377570989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 332006277444784918380659 498009416167177377570989)
          ·
            refine ⟨186753531062691516589121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 498009416167177377570989 186753531062691516589121)
            ·
              refine ⟨140065148297018637441841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 186753531062691516589121 140065148297018637441841)
              ·
                refine ⟨105048861222763978081381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 140065148297018637441841 105048861222763978081381)
                ·
                  refine ⟨19696661479268245890259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 105048861222763978081381 19696661479268245890259)
                  ·
                    rfl

theorem cell21_86308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 2, 2, 4].length) (baseStart_86308 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_86308 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_86308 prefixEnd_86308 := by exact prefixLift 86308
  have htrace : WordTrace (prefixWord ++ tailWord_86308) baseStart_86308 baseEnd_86308 := by
    simpa [prefixWord, tailWord_86308, baseEnd_86308] using wordTrace_append hprefix tailTrace_86308
  have hstable : (prefixWord ++ tailWord_86308).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86308).length < 2 ^ (prefixWord ++ tailWord_86308).sum := by decide
  have hdescent : baseEnd_86308 < baseStart_86308 := by decide
  rcases family_descends (prefixWord ++ tailWord_86308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86353 : List Nat := [1, 2, 2, 1, 4, 2, 1, 5, 3]
def baseStart_86353 : Nat := 118140960795 + 86353 * 2 ^ 59
def prefixEnd_86353 : Nat := 4983230072969 + 3 ^ 40 * 86353 * 2
def baseEnd_86353 : Nat := 19706931092358167640167

theorem tailTrace_86353 : CollatzResearch.WordTrace tailWord_86353 prefixEnd_86353 19706931092358167640167 := by
  unfold tailWord_86353
  simp only [CollatzResearch.WordTrace]
  refine ⟨3149552656165303763367713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2099701770776869175578475 3149552656165303763367713)
  ·
    refine ⟨2362164492123977822525785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3149552656165303763367713 2362164492123977822525785)
    ·
      refine ⟨1771623369092983366894339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2362164492123977822525785 1771623369092983366894339)
      ·
        refine ⟨2657435053639475050341509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1771623369092983366894339 2657435053639475050341509)
        ·
          refine ⟨498269072557401571939033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2657435053639475050341509 498269072557401571939033)
          ·
            refine ⟨373701804418051178954275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 498269072557401571939033 373701804418051178954275)
            ·
              refine ⟨560552706627076768431413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 373701804418051178954275 560552706627076768431413)
              ·
                refine ⟨52551816246288447040445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 560552706627076768431413 52551816246288447040445)
                ·
                  refine ⟨19706931092358167640167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52551816246288447040445 19706931092358167640167)
                  ·
                    rfl

theorem cell21_86353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 5, 3].length) (baseStart_86353 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_86353 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_86353 prefixEnd_86353 := by exact prefixLift 86353
  have htrace : WordTrace (prefixWord ++ tailWord_86353) baseStart_86353 baseEnd_86353 := by
    simpa [prefixWord, tailWord_86353, baseEnd_86353] using wordTrace_append hprefix tailTrace_86353
  have hstable : (prefixWord ++ tailWord_86353).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86353).length < 2 ^ (prefixWord ++ tailWord_86353).sum := by decide
  have hdescent : baseEnd_86353 < baseStart_86353 := by decide
  rcases family_descends (prefixWord ++ tailWord_86353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86367 : List Nat := [1, 1, 2, 3, 1, 2, 5, 2, 4]
def baseStart_86367 : Nat := 118140960795 + 86367 * 2 ^ 59
def prefixEnd_86367 : Nat := 4983230072969 + 3 ^ 40 * 86367 * 2
def baseEnd_86367 : Nat := 19710126083097254406805

theorem tailTrace_86367 : CollatzResearch.WordTrace tailWord_86367 prefixEnd_86367 19710126083097254406805 := by
  unfold tailWord_86367
  simp only [CollatzResearch.WordTrace]
  refine ⟨3150063278114584154377355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2100042185409722769584903 3150063278114584154377355)
  ·
    refine ⟨4725094917171876231566033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3150063278114584154377355 4725094917171876231566033)
    ·
      refine ⟨3543821187878907173674525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4725094917171876231566033 3543821187878907173674525)
      ·
        refine ⟨1328932945454590190127947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3543821187878907173674525 1328932945454590190127947)
        ·
          refine ⟨1993399418181885285191921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1328932945454590190127947 1993399418181885285191921)
          ·
            refine ⟨1495049563636413963893941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1993399418181885285191921 1495049563636413963893941)
            ·
              refine ⟨140160896590913809115057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1495049563636413963893941 140160896590913809115057)
              ·
                refine ⟨105120672443185356836293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 140160896590913809115057 105120672443185356836293)
                ·
                  refine ⟨19710126083097254406805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 105120672443185356836293 19710126083097254406805)
                  ·
                    rfl

theorem cell21_86367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 5, 2, 4].length) (baseStart_86367 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_86367 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_86367 prefixEnd_86367 := by exact prefixLift 86367
  have htrace : WordTrace (prefixWord ++ tailWord_86367) baseStart_86367 baseEnd_86367 := by
    simpa [prefixWord, tailWord_86367, baseEnd_86367] using wordTrace_append hprefix tailTrace_86367
  have hstable : (prefixWord ++ tailWord_86367).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86367).length < 2 ^ (prefixWord ++ tailWord_86367).sum := by decide
  have hdescent : baseEnd_86367 < baseStart_86367 := by decide
  rcases family_descends (prefixWord ++ tailWord_86367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86370 : List Nat := [3, 3, 2, 1, 1, 2, 2, 4, 3]
def baseStart_86370 : Nat := 118140960795 + 86370 * 2 ^ 59
def prefixEnd_86370 : Nat := 4983230072969 + 3 ^ 40 * 86370 * 2
def baseEnd_86370 : Nat := 19710810723969915856799

theorem tailTrace_86370 : CollatzResearch.WordTrace tailWord_86370 prefixEnd_86370 19710810723969915856799 := by
  unfold tailWord_86370
  simp only [CollatzResearch.WordTrace]
  refine ⟨787543174275928916684141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2100115131402477111157709 787543174275928916684141)
  ·
    refine ⟨295328690353473343756553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 787543174275928916684141 295328690353473343756553)
    ·
      refine ⟨221496517765105007817415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 295328690353473343756553 221496517765105007817415)
      ·
        refine ⟨332244776647657511726123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221496517765105007817415 332244776647657511726123)
        ·
          refine ⟨498367164971486267589185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 332244776647657511726123 498367164971486267589185)
          ·
            refine ⟨373775373728614700691889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 498367164971486267589185 373775373728614700691889)
            ·
              refine ⟨280331530296461025518917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 373775373728614700691889 280331530296461025518917)
              ·
                refine ⟨52562161930586442284797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 280331530296461025518917 52562161930586442284797)
                ·
                  refine ⟨19710810723969915856799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52562161930586442284797 19710810723969915856799)
                  ·
                    rfl

theorem cell21_86370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 4, 3].length) (baseStart_86370 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_86370 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_86370 prefixEnd_86370 := by exact prefixLift 86370
  have htrace : WordTrace (prefixWord ++ tailWord_86370) baseStart_86370 baseEnd_86370 := by
    simpa [prefixWord, tailWord_86370, baseEnd_86370] using wordTrace_append hprefix tailTrace_86370
  have hstable : (prefixWord ++ tailWord_86370).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86370).length < 2 ^ (prefixWord ++ tailWord_86370).sum := by decide
  have hdescent : baseEnd_86370 < baseStart_86370 := by decide
  rcases family_descends (prefixWord ++ tailWord_86370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86381 : List Nat := [1, 5, 1, 1, 1, 2, 2, 8]
def baseStart_86381 : Nat := 118140960795 + 86381 * 2 ^ 59
def prefixEnd_86381 : Nat := 4983230072969 + 3 ^ 40 * 86381 * 2
def baseEnd_86381 : Nat := 6571107024612113724481

theorem tailTrace_86381 : CollatzResearch.WordTrace tailWord_86381 prefixEnd_86381 6571107024612113724481 := by
  unfold tailWord_86381
  simp only [CollatzResearch.WordTrace]
  refine ⟨3150573900063864545386997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2100382600042576363591331 3150573900063864545386997)
  ·
    refine ⟨295366303130987301130031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3150573900063864545386997 295366303130987301130031)
    ·
      refine ⟨443049454696480951695047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 295366303130987301130031 443049454696480951695047)
      ·
        refine ⟨664574182044721427542571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 443049454696480951695047 664574182044721427542571)
        ·
          refine ⟨996861273067082141313857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 664574182044721427542571 996861273067082141313857)
          ·
            refine ⟨747645954800311605985393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 996861273067082141313857 747645954800311605985393)
            ·
              refine ⟨560734466100233704489045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 747645954800311605985393 560734466100233704489045)
              ·
                refine ⟨6571107024612113724481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 560734466100233704489045 6571107024612113724481)
                ·
                  rfl

theorem cell21_86381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 8].length) (baseStart_86381 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_86381 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_86381 prefixEnd_86381 := by exact prefixLift 86381
  have htrace : WordTrace (prefixWord ++ tailWord_86381) baseStart_86381 baseEnd_86381 := by
    simpa [prefixWord, tailWord_86381, baseEnd_86381] using wordTrace_append hprefix tailTrace_86381
  have hstable : (prefixWord ++ tailWord_86381).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86381).length < 2 ^ (prefixWord ++ tailWord_86381).sum := by decide
  have hdescent : baseEnd_86381 < baseStart_86381 := by decide
  rcases family_descends (prefixWord ++ tailWord_86381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86384 : List Nat := [2, 1, 1, 1, 4, 4, 3, 1, 4]
def baseStart_86384 : Nat := 118140960795 + 86384 * 2 ^ 59
def prefixEnd_86384 : Nat := 4983230072969 + 3 ^ 40 * 86384 * 2
def baseEnd_86384 : Nat := 19714005714709002623437

theorem tailTrace_86384 : CollatzResearch.WordTrace tailWord_86384 prefixEnd_86384 19714005714709002623437 := by
  unfold tailWord_86384
  simp only [CollatzResearch.WordTrace]
  refine ⟨1575341659526498028873103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2100455546035330705164137 1575341659526498028873103)
  ·
    refine ⟨2363012489289747043309655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1575341659526498028873103 2363012489289747043309655)
    ·
      refine ⟨3544518733934620564964483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2363012489289747043309655 3544518733934620564964483)
      ·
        refine ⟨5316778100901930847446725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3544518733934620564964483 5316778100901930847446725)
        ·
          refine ⟨996895893919112033896261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5316778100901930847446725 996895893919112033896261)
          ·
            refine ⟨186917980109833506355549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 996895893919112033896261 186917980109833506355549)
            ·
              refine ⟨70094242541187564883331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 186917980109833506355549 70094242541187564883331)
              ·
                refine ⟨105141363811781347324997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70094242541187564883331 105141363811781347324997)
                ·
                  refine ⟨19714005714709002623437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 105141363811781347324997 19714005714709002623437)
                  ·
                    rfl

theorem cell21_86384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 3, 1, 4].length) (baseStart_86384 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_86384 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_86384 prefixEnd_86384 := by exact prefixLift 86384
  have htrace : WordTrace (prefixWord ++ tailWord_86384) baseStart_86384 baseEnd_86384 := by
    simpa [prefixWord, tailWord_86384, baseEnd_86384] using wordTrace_append hprefix tailTrace_86384
  have hstable : (prefixWord ++ tailWord_86384).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86384).length < 2 ^ (prefixWord ++ tailWord_86384).sum := by decide
  have hdescent : baseEnd_86384 < baseStart_86384 := by decide
  rcases family_descends (prefixWord ++ tailWord_86384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86457 : List Nat := [1, 2, 1, 4, 3, 1, 2, 7]
def baseStart_86457 : Nat := 118140960795 + 86457 * 2 ^ 59
def prefixEnd_86457 : Nat := 4983230072969 + 3 ^ 40 * 86457 * 2
def baseEnd_86457 : Nat := 6576888436425699302207

theorem tailTrace_86457 : CollatzResearch.WordTrace tailWord_86457 prefixEnd_86457 6576888436425699302207 := by
  unfold tailWord_86457
  simp only [CollatzResearch.WordTrace]
  refine ⟨3153345847788529525153625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2102230565192353016769083 3153345847788529525153625)
  ·
    refine ⟨2365009385841397143865219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3153345847788529525153625 2365009385841397143865219)
    ·
      refine ⟨3547514078762095715797829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2365009385841397143865219 3547514078762095715797829)
      ·
        refine ⟨665158889767892946712093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3547514078762095715797829 665158889767892946712093)
        ·
          refine ⟨249434583662959855017035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 665158889767892946712093 249434583662959855017035)
          ·
            refine ⟨374151875494439782525553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 249434583662959855017035 374151875494439782525553)
            ·
              refine ⟨280613906620829836894165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 374151875494439782525553 280613906620829836894165)
              ·
                refine ⟨6576888436425699302207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 280613906620829836894165 6576888436425699302207)
                ·
                  rfl

theorem cell21_86457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 7].length) (baseStart_86457 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_86457 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_86457 prefixEnd_86457 := by exact prefixLift 86457
  have htrace : WordTrace (prefixWord ++ tailWord_86457) baseStart_86457 baseEnd_86457 := by
    simpa [prefixWord, tailWord_86457, baseEnd_86457] using wordTrace_append hprefix tailTrace_86457
  have hstable : (prefixWord ++ tailWord_86457).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86457).length < 2 ^ (prefixWord ++ tailWord_86457).sum := by decide
  have hdescent : baseEnd_86457 < baseStart_86457 := by decide
  rcases family_descends (prefixWord ++ tailWord_86457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86567 : List Nat := [1, 1, 7, 2, 1, 1, 1, 7]
def baseStart_86567 : Nat := 118140960795 + 86567 * 2 ^ 59
def prefixEnd_86567 : Nat := 4983230072969 + 3 ^ 40 * 86567 * 2
def baseEnd_86567 : Nat := 6585256269313783691021

theorem tailTrace_86567 : CollatzResearch.WordTrace tailWord_86567 prefixEnd_86567 6585256269313783691021 := by
  unfold tailWord_86567
  simp only [CollatzResearch.WordTrace]
  refine ⟨3157357877390018311657955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2104905251593345541105303 3157357877390018311657955)
  ·
    refine ⟨4736036816085027467486933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3157357877390018311657955 4736036816085027467486933)
    ·
      refine ⟨111000862876992831269225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 4736036816085027467486933 111000862876992831269225)
      ·
        refine ⟨83250647157744623451919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111000862876992831269225 83250647157744623451919)
        ·
          refine ⟨124875970736616935177879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83250647157744623451919 124875970736616935177879)
          ·
            refine ⟨187313956104925402766819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124875970736616935177879 187313956104925402766819)
            ·
              refine ⟨280970934157388104150229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 187313956104925402766819 280970934157388104150229)
              ·
                refine ⟨6585256269313783691021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 280970934157388104150229 6585256269313783691021)
                ·
                  rfl

theorem cell21_86567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 7].length) (baseStart_86567 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_86567 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_86567 prefixEnd_86567 := by exact prefixLift 86567
  have htrace : WordTrace (prefixWord ++ tailWord_86567) baseStart_86567 baseEnd_86567 := by
    simpa [prefixWord, tailWord_86567, baseEnd_86567] using wordTrace_append hprefix tailTrace_86567
  have hstable : (prefixWord ++ tailWord_86567).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86567).length < 2 ^ (prefixWord ++ tailWord_86567).sum := by decide
  have hdescent : baseEnd_86567 < baseStart_86567 := by decide
  rcases family_descends (prefixWord ++ tailWord_86567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86573 : List Nat := [1, 5, 4, 1, 1, 2, 1, 3, 3]
def baseStart_86573 : Nat := 118140960795 + 86573 * 2 ^ 59
def prefixEnd_86573 : Nat := 4983230072969 + 3 ^ 40 * 86573 * 2
def baseEnd_86573 : Nat := 19757138089686673973051

theorem tailTrace_86573 : CollatzResearch.WordTrace tailWord_86573 prefixEnd_86573 19757138089686673973051 := by
  unfold tailWord_86573
  simp only [CollatzResearch.WordTrace]
  refine ⟨3157576715368281336376373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2105051143578854224250915 3157576715368281336376373)
  ·
    refine ⟨296022817065776375285285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3157576715368281336376373 296022817065776375285285)
    ·
      refine ⟨55504278199833070365991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 296022817065776375285285 55504278199833070365991)
      ·
        refine ⟨83256417299749605548987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55504278199833070365991 83256417299749605548987)
        ·
          refine ⟨124884625949624408323481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83256417299749605548987 124884625949624408323481)
          ·
            refine ⟨93663469462218306242611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124884625949624408323481 93663469462218306242611)
            ·
              refine ⟨140495204193327459363917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93663469462218306242611 140495204193327459363917)
              ·
                refine ⟨52685701572497797261469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 140495204193327459363917 52685701572497797261469)
                ·
                  refine ⟨19757138089686673973051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52685701572497797261469 19757138089686673973051)
                  ·
                    rfl

theorem cell21_86573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 1, 3, 3].length) (baseStart_86573 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_86573 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_86573 prefixEnd_86573 := by exact prefixLift 86573
  have htrace : WordTrace (prefixWord ++ tailWord_86573) baseStart_86573 baseEnd_86573 := by
    simpa [prefixWord, tailWord_86573, baseEnd_86573] using wordTrace_append hprefix tailTrace_86573
  have hstable : (prefixWord ++ tailWord_86573).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86573).length < 2 ^ (prefixWord ++ tailWord_86573).sum := by decide
  have hdescent : baseEnd_86573 < baseStart_86573 := by decide
  rcases family_descends (prefixWord ++ tailWord_86573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86578 : List Nat := [3, 2, 1, 1, 2, 1, 3, 2, 6]
def baseStart_86578 : Nat := 118140960795 + 86578 * 2 ^ 59
def prefixEnd_86578 : Nat := 4983230072969 + 3 ^ 40 * 86578 * 2
def baseEnd_86578 : Nat := 19758279157807776389707

theorem tailTrace_86578 : CollatzResearch.WordTrace tailWord_86578 prefixEnd_86578 19758279157807776389707 := by
  unfold tailWord_86578
  simp only [CollatzResearch.WordTrace]
  refine ⟨789439770087541797577097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2105172720233444793538925 789439770087541797577097)
  ·
    refine ⟨592079827565656348182823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 789439770087541797577097 592079827565656348182823)
    ·
      refine ⟨888119741348484522274235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 592079827565656348182823 888119741348484522274235)
      ·
        refine ⟨1332179612022726783411353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 888119741348484522274235 1332179612022726783411353)
        ·
          refine ⟨999134709017045087558515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1332179612022726783411353 999134709017045087558515)
          ·
            refine ⟨1498702063525567631337773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 999134709017045087558515 1498702063525567631337773)
            ·
              refine ⟨562013273822087861751665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1498702063525567631337773 562013273822087861751665)
              ·
                refine ⟨421509955366565896313749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 562013273822087861751665 421509955366565896313749)
                ·
                  refine ⟨19758279157807776389707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 421509955366565896313749 19758279157807776389707)
                  ·
                    rfl

theorem cell21_86578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 2, 6].length) (baseStart_86578 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_86578 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_86578 prefixEnd_86578 := by exact prefixLift 86578
  have htrace : WordTrace (prefixWord ++ tailWord_86578) baseStart_86578 baseEnd_86578 := by
    simpa [prefixWord, tailWord_86578, baseEnd_86578] using wordTrace_append hprefix tailTrace_86578
  have hstable : (prefixWord ++ tailWord_86578).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86578).length < 2 ^ (prefixWord ++ tailWord_86578).sum := by decide
  have hdescent : baseEnd_86578 < baseStart_86578 := by decide
  rcases family_descends (prefixWord ++ tailWord_86578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86592 : List Nat := [2, 1, 1, 2, 2, 2, 11]
def baseStart_86592 : Nat := 118140960795 + 86592 * 2 ^ 59
def prefixEnd_86592 : Nat := 4983230072969 + 3 ^ 40 * 86592 * 2
def baseEnd_86592 : Nat := 2195719349838540350705

theorem tailTrace_86592 : CollatzResearch.WordTrace tailWord_86592 prefixEnd_86592 2195719349838540350705 := by
  unfold tailWord_86592
  simp only [CollatzResearch.WordTrace]
  refine ⟨1579134851149723790659015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2105513134866298387545353 1579134851149723790659015)
  ·
    refine ⟨2368702276724585685988523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1579134851149723790659015 2368702276724585685988523)
    ·
      refine ⟨3553053415086878528982785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2368702276724585685988523 3553053415086878528982785)
      ·
        refine ⟨2664790061315158896737089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3553053415086878528982785 2664790061315158896737089)
        ·
          refine ⟨1998592545986369172552817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2664790061315158896737089 1998592545986369172552817)
          ·
            refine ⟨1498944409489776879414613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1998592545986369172552817 1498944409489776879414613)
            ·
              refine ⟨2195719349838540350705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 1498944409489776879414613 2195719349838540350705)
              ·
                rfl

theorem cell21_86592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 11].length) (baseStart_86592 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_86592 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_86592 prefixEnd_86592 := by exact prefixLift 86592
  have htrace : WordTrace (prefixWord ++ tailWord_86592) baseStart_86592 baseEnd_86592 := by
    simpa [prefixWord, tailWord_86592, baseEnd_86592] using wordTrace_append hprefix tailTrace_86592
  have hstable : (prefixWord ++ tailWord_86592).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86592).length < 2 ^ (prefixWord ++ tailWord_86592).sum := by decide
  have hdescent : baseEnd_86592 < baseStart_86592 := by decide
  rcases family_descends (prefixWord ++ tailWord_86592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86598 : List Nat := [6, 1, 1, 1, 2, 1, 3, 1, 5]
def baseStart_86598 : Nat := 118140960795 + 86598 * 2 ^ 59
def prefixEnd_86598 : Nat := 4983230072969 + 3 ^ 40 * 86598 * 2
def baseEnd_86598 : Nat := 19762843430292186056333

theorem tailTrace_86598 : CollatzResearch.WordTrace tailWord_86598 prefixEnd_86598 19762843430292186056333 := by
  unfold tailWord_86598
  simp only [CollatzResearch.WordTrace]
  refine ⟨98702766883678456438639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 2105659026851807070690965 98702766883678456438639)
  ·
    refine ⟨148054150325517684657959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98702766883678456438639 148054150325517684657959)
    ·
      refine ⟨222081225488276526986939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148054150325517684657959 222081225488276526986939)
      ·
        refine ⟨333121838232414790480409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222081225488276526986939 333121838232414790480409)
        ·
          refine ⟨249841378674311092860307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 333121838232414790480409 249841378674311092860307)
          ·
            refine ⟨374762068011466639290461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 249841378674311092860307 374762068011466639290461)
            ·
              refine ⟨140535775504299989733923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 374762068011466639290461 140535775504299989733923)
              ·
                refine ⟨210803663256449984600885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 140535775504299989733923 210803663256449984600885)
                ·
                  refine ⟨19762843430292186056333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 210803663256449984600885 19762843430292186056333)
                  ·
                    rfl

theorem cell21_86598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_86598 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_86598 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_86598 prefixEnd_86598 := by exact prefixLift 86598
  have htrace : WordTrace (prefixWord ++ tailWord_86598) baseStart_86598 baseEnd_86598 := by
    simpa [prefixWord, tailWord_86598, baseEnd_86598] using wordTrace_append hprefix tailTrace_86598
  have hstable : (prefixWord ++ tailWord_86598).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86598).length < 2 ^ (prefixWord ++ tailWord_86598).sum := by decide
  have hdescent : baseEnd_86598 < baseStart_86598 := by decide
  rcases family_descends (prefixWord ++ tailWord_86598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86609 : List Nat := [1, 2, 2, 1, 3, 4, 2, 6]
def baseStart_86609 : Nat := 118140960795 + 86609 * 2 ^ 59
def prefixEnd_86609 : Nat := 4983230072969 + 3 ^ 40 * 86609 * 2
def baseEnd_86609 : Nat := 6588451260052870457659

theorem tailTrace_86609 : CollatzResearch.WordTrace tailWord_86609 prefixEnd_86609 6588451260052870457659 := by
  unfold tailWord_86609
  simp only [CollatzResearch.WordTrace]
  refine ⟨3158889743237859484686881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2105926495491906323124587 3158889743237859484686881)
  ·
    refine ⟨2369167307428394613515161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3158889743237859484686881 2369167307428394613515161)
    ·
      refine ⟨1776875480571295960136371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2369167307428394613515161 1776875480571295960136371)
      ·
        refine ⟨2665313220856943940204557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1776875480571295960136371 2665313220856943940204557)
        ·
          refine ⟨999492457821353977576709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2665313220856943940204557 999492457821353977576709)
          ·
            refine ⟨187404835841503870795633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 999492457821353977576709 187404835841503870795633)
            ·
              refine ⟨140553626881127903096725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 187404835841503870795633 140553626881127903096725)
              ·
                refine ⟨6588451260052870457659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 140553626881127903096725 6588451260052870457659)
                ·
                  rfl

theorem cell21_86609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 2, 6].length) (baseStart_86609 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_86609 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_86609 prefixEnd_86609 := by exact prefixLift 86609
  have htrace : WordTrace (prefixWord ++ tailWord_86609) baseStart_86609 baseEnd_86609 := by
    simpa [prefixWord, tailWord_86609, baseEnd_86609] using wordTrace_append hprefix tailTrace_86609
  have hstable : (prefixWord ++ tailWord_86609).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86609).length < 2 ^ (prefixWord ++ tailWord_86609).sum := by decide
  have hdescent : baseEnd_86609 < baseStart_86609 := by decide
  rcases family_descends (prefixWord ++ tailWord_86609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86612 : List Nat := [2, 4, 1, 1, 1, 3, 4, 1, 4]
def baseStart_86612 : Nat := 118140960795 + 86612 * 2 ^ 59
def prefixEnd_86612 : Nat := 4983230072969 + 3 ^ 40 * 86612 * 2
def baseEnd_86612 : Nat := 19766038421031272822971

theorem tailTrace_86612 : CollatzResearch.WordTrace tailWord_86612 prefixEnd_86612 19766038421031272822971 := by
  unfold tailWord_86612
  simp only [CollatzResearch.WordTrace]
  refine ⟨1579499581113495498523045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2105999441484660664697393 1579499581113495498523045)
  ·
    refine ⟨296156171458780405973071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1579499581113495498523045 296156171458780405973071)
    ·
      refine ⟨444234257188170608959607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 296156171458780405973071 444234257188170608959607)
      ·
        refine ⟨666351385782255913439411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 444234257188170608959607 666351385782255913439411)
        ·
          refine ⟨999527078673383870159117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 666351385782255913439411 999527078673383870159117)
          ·
            refine ⟨374822654502518951309669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 999527078673383870159117 374822654502518951309669)
            ·
              refine ⟨70279247719222303370563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 374822654502518951309669 70279247719222303370563)
              ·
                refine ⟨105418871578833455055845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70279247719222303370563 105418871578833455055845)
                ·
                  refine ⟨19766038421031272822971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 105418871578833455055845 19766038421031272822971)
                  ·
                    rfl

theorem cell21_86612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 4, 1, 4].length) (baseStart_86612 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_86612 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_86612 prefixEnd_86612 := by exact prefixLift 86612
  have htrace : WordTrace (prefixWord ++ tailWord_86612) baseStart_86612 baseEnd_86612 := by
    simpa [prefixWord, tailWord_86612, baseEnd_86612] using wordTrace_append hprefix tailTrace_86612
  have hstable : (prefixWord ++ tailWord_86612).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86612).length < 2 ^ (prefixWord ++ tailWord_86612).sum := by decide
  have hdescent : baseEnd_86612 < baseStart_86612 := by decide
  rcases family_descends (prefixWord ++ tailWord_86612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86623 : List Nat := [1, 1, 2, 3, 1, 1, 1, 6, 5]
def baseStart_86623 : Nat := 118140960795 + 86623 * 2 ^ 59
def prefixEnd_86623 : Nat := 4983230072969 + 3 ^ 40 * 86623 * 2
def baseEnd_86623 : Nat := 19768548770897698139615

theorem tailTrace_86623 : CollatzResearch.WordTrace tailWord_86623 prefixEnd_86623 19768548770897698139615 := by
  unfold tailWord_86623
  simp only [CollatzResearch.WordTrace]
  refine ⟨3159400365187139875696523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2106266910124759917131015 3159400365187139875696523)
  ·
    refine ⟨4739100547780709813544785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3159400365187139875696523 4739100547780709813544785)
    ·
      refine ⟨3554325410835532360158589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4739100547780709813544785 3554325410835532360158589)
      ·
        refine ⟨1332872029063324635059471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3554325410835532360158589 1332872029063324635059471)
        ·
          refine ⟨1999308043594986952589207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1332872029063324635059471 1999308043594986952589207)
          ·
            refine ⟨2998962065392480428883811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1999308043594986952589207 2998962065392480428883811)
            ·
              refine ⟨4498443098088720643325717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2998962065392480428883811 4498443098088720643325717)
              ·
                refine ⟨210864520222908780155893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4498443098088720643325717 210864520222908780155893)
                ·
                  refine ⟨19768548770897698139615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 210864520222908780155893 19768548770897698139615)
                  ·
                    rfl

theorem cell21_86623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 6, 5].length) (baseStart_86623 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_86623 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_86623 prefixEnd_86623 := by exact prefixLift 86623
  have htrace : WordTrace (prefixWord ++ tailWord_86623) baseStart_86623 baseEnd_86623 := by
    simpa [prefixWord, tailWord_86623, baseEnd_86623] using wordTrace_append hprefix tailTrace_86623
  have hstable : (prefixWord ++ tailWord_86623).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86623).length < 2 ^ (prefixWord ++ tailWord_86623).sum := by decide
  have hdescent : baseEnd_86623 < baseStart_86623 := by decide
  rcases family_descends (prefixWord ++ tailWord_86623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86657 : List Nat := [1, 2, 4, 2, 1, 1, 3, 4, 3]
def baseStart_86657 : Nat := 118140960795 + 86657 * 2 ^ 59
def prefixEnd_86657 : Nat := 4983230072969 + 3 ^ 40 * 86657 * 2
def baseEnd_86657 : Nat := 19776308034121194572879

theorem tailTrace_86657 : CollatzResearch.WordTrace tailWord_86657 prefixEnd_86657 19776308034121194572879 := by
  unfold tailWord_86657
  simp only [CollatzResearch.WordTrace]
  refine ⟨3160640447063963682434225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2107093631375975788289483 3160640447063963682434225)
  ·
    refine ⟨2370480335297972761825669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3160640447063963682434225 2370480335297972761825669)
    ·
      refine ⟨444465062868369892842313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2370480335297972761825669 444465062868369892842313)
      ·
        refine ⟨333348797151277419631735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 444465062868369892842313 333348797151277419631735)
        ·
          refine ⟨500023195726916129447603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 333348797151277419631735 500023195726916129447603)
          ·
            refine ⟨750034793590374194171405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 500023195726916129447603 750034793590374194171405)
            ·
              refine ⟨281263047596390322814277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 750034793590374194171405 281263047596390322814277)
              ·
                refine ⟨52736821424323185527677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 281263047596390322814277 52736821424323185527677)
                ·
                  refine ⟨19776308034121194572879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52736821424323185527677 19776308034121194572879)
                  ·
                    rfl

theorem cell21_86657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 4, 3].length) (baseStart_86657 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_86657 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_86657 prefixEnd_86657 := by exact prefixLift 86657
  have htrace : WordTrace (prefixWord ++ tailWord_86657) baseStart_86657 baseEnd_86657 := by
    simpa [prefixWord, tailWord_86657, baseEnd_86657] using wordTrace_append hprefix tailTrace_86657
  have hstable : (prefixWord ++ tailWord_86657).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86657).length < 2 ^ (prefixWord ++ tailWord_86657).sum := by decide
  have hdescent : baseEnd_86657 < baseStart_86657 := by decide
  rcases family_descends (prefixWord ++ tailWord_86657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86668 : List Nat := [2, 2, 1, 2, 1, 1, 2, 10]
def baseStart_86668 : Nat := 118140960795 + 86668 * 2 ^ 59
def prefixEnd_86668 : Nat := 4983230072969 + 3 ^ 40 * 86668 * 2
def baseEnd_86668 : Nat := 6592939461329206629841

theorem tailTrace_86668 : CollatzResearch.WordTrace tailWord_86668 prefixEnd_86668 6592939461329206629841 := by
  unfold tailWord_86668
  simp only [CollatzResearch.WordTrace]
  refine ⟨1580520825012056280542329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2107361100016075040723105 1580520825012056280542329)
  ·
    refine ⟨1185390618759042210406747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1580520825012056280542329 1185390618759042210406747)
    ·
      refine ⟨1778085928138563315610121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1185390618759042210406747 1778085928138563315610121)
      ·
        refine ⟨1333564446103922486707591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1778085928138563315610121 1333564446103922486707591)
        ·
          refine ⟨2000346669155883730061387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1333564446103922486707591 2000346669155883730061387)
          ·
            refine ⟨3000520003733825595092081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2000346669155883730061387 3000520003733825595092081)
            ·
              refine ⟨2250390002800369196319061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3000520003733825595092081 2250390002800369196319061)
              ·
                refine ⟨6592939461329206629841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 2250390002800369196319061 6592939461329206629841)
                ·
                  rfl

theorem cell21_86668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 10].length) (baseStart_86668 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_86668 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_86668 prefixEnd_86668 := by exact prefixLift 86668
  have htrace : WordTrace (prefixWord ++ tailWord_86668) baseStart_86668 baseEnd_86668 := by
    simpa [prefixWord, tailWord_86668, baseEnd_86668] using wordTrace_append hprefix tailTrace_86668
  have hstable : (prefixWord ++ tailWord_86668).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86668).length < 2 ^ (prefixWord ++ tailWord_86668).sum := by decide
  have hdescent : baseEnd_86668 < baseStart_86668 := by decide
  rcases family_descends (prefixWord ++ tailWord_86668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86702 : List Nat := [4, 1, 4, 1, 1, 2, 8]
def baseStart_86702 : Nat := 118140960795 + 86702 * 2 ^ 59
def prefixEnd_86702 : Nat := 4983230072969 + 3 ^ 40 * 86702 * 2
def baseEnd_86702 : Nat := 2198508627467901813643

theorem tailTrace_86702 : CollatzResearch.WordTrace tailWord_86702 prefixEnd_86702 2198508627467901813643 := by
  unfold tailWord_86702
  simp only [CollatzResearch.WordTrace]
  refine ⟨395285216487617045977795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2108187821267290911881573 395285216487617045977795)
  ·
    refine ⟨592927824731425568966693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 395285216487617045977795 592927824731425568966693)
    ·
      refine ⟨111173967137142294181255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 592927824731425568966693 111173967137142294181255)
      ·
        refine ⟨166760950705713441271883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111173967137142294181255 166760950705713441271883)
        ·
          refine ⟨250141426058570161907825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166760950705713441271883 250141426058570161907825)
          ·
            refine ⟨187606069543927621430869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 250141426058570161907825 187606069543927621430869)
            ·
              refine ⟨2198508627467901813643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 187606069543927621430869 2198508627467901813643)
              ·
                rfl

theorem cell21_86702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 8].length) (baseStart_86702 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_86702 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_86702 prefixEnd_86702 := by exact prefixLift 86702
  have htrace : WordTrace (prefixWord ++ tailWord_86702) baseStart_86702 baseEnd_86702 := by
    simpa [prefixWord, tailWord_86702, baseEnd_86702] using wordTrace_append hprefix tailTrace_86702
  have hstable : (prefixWord ++ tailWord_86702).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86702).length < 2 ^ (prefixWord ++ tailWord_86702).sum := by decide
  have hdescent : baseEnd_86702 < baseStart_86702 := by decide
  rcases family_descends (prefixWord ++ tailWord_86702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86705 : List Nat := [1, 2, 2, 6, 1, 2, 1, 2, 4]
def baseStart_86705 : Nat := 118140960795 + 86705 * 2 ^ 59
def prefixEnd_86705 : Nat := 4983230072969 + 3 ^ 40 * 86705 * 2
def baseEnd_86705 : Nat := 19787262288083777772781

theorem tailTrace_86705 : CollatzResearch.WordTrace tailWord_86705 prefixEnd_86705 19787262288083777772781 := by
  unfold tailWord_86705
  simp only [CollatzResearch.WordTrace]
  refine ⟨3162391150890067880181569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2108260767260045253454379 3162391150890067880181569)
  ·
    refine ⟨2371793363167550910136177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3162391150890067880181569 2371793363167550910136177)
    ·
      refine ⟨1778845022375663182602133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2371793363167550910136177 1778845022375663182602133)
      ·
        refine ⟨83383360423859211684475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 1778845022375663182602133 83383360423859211684475)
        ·
          refine ⟨125075040635788817526713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83383360423859211684475 125075040635788817526713)
          ·
            refine ⟨93806280476841613145035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125075040635788817526713 93806280476841613145035)
            ·
              refine ⟨140709420715262419717553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93806280476841613145035 140709420715262419717553)
              ·
                refine ⟨105532065536446814788165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 140709420715262419717553 105532065536446814788165)
                ·
                  refine ⟨19787262288083777772781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 105532065536446814788165 19787262288083777772781)
                  ·
                    rfl

theorem cell21_86705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 1, 2, 4].length) (baseStart_86705 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_86705 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_86705 prefixEnd_86705 := by exact prefixLift 86705
  have htrace : WordTrace (prefixWord ++ tailWord_86705) baseStart_86705 baseEnd_86705 := by
    simpa [prefixWord, tailWord_86705, baseEnd_86705] using wordTrace_append hprefix tailTrace_86705
  have hstable : (prefixWord ++ tailWord_86705).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86705).length < 2 ^ (prefixWord ++ tailWord_86705).sum := by decide
  have hdescent : baseEnd_86705 < baseStart_86705 := by decide
  rcases family_descends (prefixWord ++ tailWord_86705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86716 : List Nat := [2, 2, 2, 3, 1, 1, 4, 1, 5]
def baseStart_86716 : Nat := 118140960795 + 86716 * 2 ^ 59
def prefixEnd_86716 : Nat := 4983230072969 + 3 ^ 40 * 86716 * 2
def baseEnd_86716 : Nat := 19789772637950203089425

theorem tailTrace_86716 : CollatzResearch.WordTrace tailWord_86716 prefixEnd_86716 19789772637950203089425 := by
  unfold tailWord_86716
  simp only [CollatzResearch.WordTrace]
  refine ⟨1581396176925108379416001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2108528235900144505888001 1581396176925108379416001)
  ·
    refine ⟨1186047132693831284562001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1581396176925108379416001 1186047132693831284562001)
    ·
      refine ⟨889535349520373463421501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1186047132693831284562001 889535349520373463421501)
      ·
        refine ⟨333575756070140048783063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 889535349520373463421501 333575756070140048783063)
        ·
          refine ⟨500363634105210073174595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 333575756070140048783063 500363634105210073174595)
          ·
            refine ⟨750545451157815109761893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 500363634105210073174595 750545451157815109761893)
            ·
              refine ⟨140727272092090333080355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 750545451157815109761893 140727272092090333080355)
              ·
                refine ⟨211090908138135499620533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 140727272092090333080355 211090908138135499620533)
                ·
                  refine ⟨19789772637950203089425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 211090908138135499620533 19789772637950203089425)
                  ·
                    rfl

theorem cell21_86716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 4, 1, 5].length) (baseStart_86716 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_86716 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_86716 prefixEnd_86716 := by exact prefixLift 86716
  have htrace : WordTrace (prefixWord ++ tailWord_86716) baseStart_86716 baseEnd_86716 := by
    simpa [prefixWord, tailWord_86716, baseEnd_86716] using wordTrace_append hprefix tailTrace_86716
  have hstable : (prefixWord ++ tailWord_86716).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86716).length < 2 ^ (prefixWord ++ tailWord_86716).sum := by decide
  have hdescent : baseEnd_86716 < baseStart_86716 := by decide
  rcases family_descends (prefixWord ++ tailWord_86716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86820 : List Nat := [2, 3, 1, 3, 12]
def baseStart_86820 : Nat := 118140960795 + 86820 * 2 ^ 59
def prefixEnd_86820 : Nat := 4983230072969 + 3 ^ 40 * 86820 * 2
def baseEnd_86820 : Nat := 244611195739125103159

theorem tailTrace_86820 : CollatzResearch.WordTrace tailWord_86820 prefixEnd_86820 244611195739125103159 := by
  unfold tailWord_86820
  simp only [CollatzResearch.WordTrace]
  refine ⟨1583292772736721260308957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2111057030315628347078609 1583292772736721260308957)
  ·
    refine ⟨593734789776270472615859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1583292772736721260308957 593734789776270472615859)
    ·
      refine ⟨890602184664405708923789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 593734789776270472615859 890602184664405708923789)
      ·
        refine ⟨333975819249152140846421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 890602184664405708923789 333975819249152140846421)
        ·
          refine ⟨244611195739125103159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 333975819249152140846421 244611195739125103159)
          ·
            rfl

theorem cell21_86820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 12].length) (baseStart_86820 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_86820 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_86820 prefixEnd_86820 := by exact prefixLift 86820
  have htrace : WordTrace (prefixWord ++ tailWord_86820) baseStart_86820 baseEnd_86820 := by
    simpa [prefixWord, tailWord_86820, baseEnd_86820] using wordTrace_append hprefix tailTrace_86820
  have hstable : (prefixWord ++ tailWord_86820).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86820).length < 2 ^ (prefixWord ++ tailWord_86820).sum := by decide
  have hdescent : baseEnd_86820 < baseStart_86820 := by decide
  rcases family_descends (prefixWord ++ tailWord_86820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86837 : List Nat := [1, 3, 3, 1, 3, 1, 3, 6]
def baseStart_86837 : Nat := 118140960795 + 86837 * 2 ^ 59
def prefixEnd_86837 : Nat := 4983230072969 + 3 ^ 40 * 86837 * 2
def baseEnd_86837 : Nat := 6605795495493627190837

theorem tailTrace_86837 : CollatzResearch.WordTrace tailWord_86837 prefixEnd_86837 6605795495493627190837 := by
  unfold tailWord_86837
  simp only [CollatzResearch.WordTrace]
  refine ⟨3167205586411854423986765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2111470390941236282657843 3167205586411854423986765)
  ·
    refine ⟨1187702094904445408995037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3167205586411854423986765 1187702094904445408995037)
    ·
      refine ⟨445388285589167028373139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1187702094904445408995037 445388285589167028373139)
      ·
        refine ⟨668082428383750542559709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 445388285589167028373139 668082428383750542559709)
        ·
          refine ⟨250530910643906453459891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 668082428383750542559709 250530910643906453459891)
          ·
            refine ⟨375796365965859680189837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 250530910643906453459891 375796365965859680189837)
            ·
              refine ⟨140923637237197380071189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 375796365965859680189837 140923637237197380071189)
              ·
                refine ⟨6605795495493627190837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 140923637237197380071189 6605795495493627190837)
                ·
                  rfl

theorem cell21_86837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 3, 6].length) (baseStart_86837 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_86837 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_86837 prefixEnd_86837 := by exact prefixLift 86837
  have htrace : WordTrace (prefixWord ++ tailWord_86837) baseStart_86837 baseEnd_86837 := by
    simpa [prefixWord, tailWord_86837, baseEnd_86837] using wordTrace_append hprefix tailTrace_86837
  have hstable : (prefixWord ++ tailWord_86837).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86837).length < 2 ^ (prefixWord ++ tailWord_86837).sum := by decide
  have hdescent : baseEnd_86837 < baseStart_86837 := by decide
  rcases family_descends (prefixWord ++ tailWord_86837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86851 : List Nat := [1, 1, 1, 3, 1, 4, 3, 2, 5]
def baseStart_86851 : Nat := 118140960795 + 86851 * 2 ^ 59
def prefixEnd_86851 : Nat := 4983230072969 + 3 ^ 40 * 86851 * 2
def baseEnd_86851 : Nat := 19820581477219968339149

theorem tailTrace_86851 : CollatzResearch.WordTrace tailWord_86851 prefixEnd_86851 19820581477219968339149 := by
  unfold tailWord_86851
  simp only [CollatzResearch.WordTrace]
  refine ⟨3167716208361134814996407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2111810805574089876664271 3167716208361134814996407)
  ·
    refine ⟨4751574312541702222494611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3167716208361134814996407 4751574312541702222494611)
    ·
      refine ⟨7127361468812553333741917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4751574312541702222494611 7127361468812553333741917)
      ·
        refine ⟨2672760550804707500153219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7127361468812553333741917 2672760550804707500153219)
        ·
          refine ⟨4009140826207061250229829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2672760550804707500153219 4009140826207061250229829)
          ·
            refine ⟨751713904913823984418093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4009140826207061250229829 751713904913823984418093)
            ·
              refine ⟨281892714342683994156785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 751713904913823984418093 281892714342683994156785)
              ·
                refine ⟨211419535757012995617589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 281892714342683994156785 211419535757012995617589)
                ·
                  refine ⟨19820581477219968339149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 211419535757012995617589 19820581477219968339149)
                  ·
                    rfl

theorem cell21_86851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 2, 5].length) (baseStart_86851 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_86851 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_86851 prefixEnd_86851 := by exact prefixLift 86851
  have htrace : WordTrace (prefixWord ++ tailWord_86851) baseStart_86851 baseEnd_86851 := by
    simpa [prefixWord, tailWord_86851, baseEnd_86851] using wordTrace_append hprefix tailTrace_86851
  have hstable : (prefixWord ++ tailWord_86851).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86851).length < 2 ^ (prefixWord ++ tailWord_86851).sum := by decide
  have hdescent : baseEnd_86851 < baseStart_86851 := by decide
  rcases family_descends (prefixWord ++ tailWord_86851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86930 : List Nat := [3, 2, 3, 2, 2, 2, 7]
def baseStart_86930 : Nat := 118140960795 + 86930 * 2 ^ 59
def prefixEnd_86930 : Nat := 4983230072969 + 3 ^ 40 * 86930 * 2
def baseEnd_86930 : Nat := 2204290039281487391369

theorem tailTrace_86930 : CollatzResearch.WordTrace tailWord_86930 prefixEnd_86930 2204290039281487391369 := by
  unfold tailWord_86930
  simp only [CollatzResearch.WordTrace]
  refine ⟨792649393768732826780561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2113731716716620871414829 792649393768732826780561)
  ·
    refine ⟨594487045326549620085421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 792649393768732826780561 594487045326549620085421)
    ·
      refine ⟨222932641997456107532033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 594487045326549620085421 222932641997456107532033)
      ·
        refine ⟨167199481498092080649025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 222932641997456107532033 167199481498092080649025)
        ·
          refine ⟨125399611123569060486769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 167199481498092080649025 125399611123569060486769)
          ·
            refine ⟨94049708342676795365077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125399611123569060486769 94049708342676795365077)
            ·
              refine ⟨2204290039281487391369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 94049708342676795365077 2204290039281487391369)
              ·
                rfl

theorem cell21_86930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 7].length) (baseStart_86930 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_86930 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_86930 prefixEnd_86930 := by exact prefixLift 86930
  have htrace : WordTrace (prefixWord ++ tailWord_86930) baseStart_86930 baseEnd_86930 := by
    simpa [prefixWord, tailWord_86930, baseEnd_86930] using wordTrace_append hprefix tailTrace_86930
  have hstable : (prefixWord ++ tailWord_86930).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86930).length < 2 ^ (prefixWord ++ tailWord_86930).sum := by decide
  have hdescent : baseEnd_86930 < baseStart_86930 := by decide
  rcases family_descends (prefixWord ++ tailWord_86930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_86944 : List Nat := [2, 1, 1, 4, 1, 1, 2, 6, 3]
def baseStart_86944 : Nat := 118140960795 + 86944 * 2 ^ 59
def prefixEnd_86944 : Nat := 4983230072969 + 3 ^ 40 * 86944 * 2
def baseEnd_86944 : Nat := 19841805344272473288959

theorem tailTrace_86944 : CollatzResearch.WordTrace tailWord_86944 prefixEnd_86944 19841805344272473288959 := by
  unfold tailWord_86944
  simp only [CollatzResearch.WordTrace]
  refine ⟨1585554098512105849065943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2114072131349474465421257 1585554098512105849065943)
  ·
    refine ⟨2378331147768158773598915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1585554098512105849065943 2378331147768158773598915)
    ·
      refine ⟨3567496721652238160398373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2378331147768158773598915 3567496721652238160398373)
      ·
        refine ⟨668905635309794655074695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3567496721652238160398373 668905635309794655074695)
        ·
          refine ⟨1003358452964691982612043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 668905635309794655074695 1003358452964691982612043)
          ·
            refine ⟨1505037679447037973918065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1003358452964691982612043 1505037679447037973918065)
            ·
              refine ⟨1128778259585278480438549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1505037679447037973918065 1128778259585278480438549)
              ·
                refine ⟨52911480918059928770557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1128778259585278480438549 52911480918059928770557)
                ·
                  refine ⟨19841805344272473288959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52911480918059928770557 19841805344272473288959)
                  ·
                    rfl

theorem cell21_86944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 6, 3].length) (baseStart_86944 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_86944 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_86944 prefixEnd_86944 := by exact prefixLift 86944
  have htrace : WordTrace (prefixWord ++ tailWord_86944) baseStart_86944 baseEnd_86944 := by
    simpa [prefixWord, tailWord_86944, baseEnd_86944] using wordTrace_append hprefix tailTrace_86944
  have hstable : (prefixWord ++ tailWord_86944).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_86944).length < 2 ^ (prefixWord ++ tailWord_86944).sum := by decide
  have hdescent : baseEnd_86944 < baseStart_86944 := by decide
  rcases family_descends (prefixWord ++ tailWord_86944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87048 : List Nat := [2, 1, 3, 2, 1, 4, 8]
def baseStart_87048 : Nat := 118140960795 + 87048 * 2 ^ 59
def prefixEnd_87048 : Nat := 4983230072969 + 3 ^ 40 * 87048 * 2
def baseEnd_87048 : Nat := 2207282173465711506157

theorem tailTrace_87048 : CollatzResearch.WordTrace tailWord_87048 prefixEnd_87048 2207282173465711506157 := by
  unfold tailWord_87048
  simp only [CollatzResearch.WordTrace]
  refine ⟨1587450694323718729958899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2116600925764958306611865 1587450694323718729958899)
  ·
    refine ⟨2381176041485578094938349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1587450694323718729958899 2381176041485578094938349)
    ·
      refine ⟨892941015557091785601881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2381176041485578094938349 892941015557091785601881)
      ·
        refine ⟨669705761667818839201411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 892941015557091785601881 669705761667818839201411)
        ·
          refine ⟨1004558642501728258802117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 669705761667818839201411 1004558642501728258802117)
          ·
            refine ⟨188354745469074048525397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1004558642501728258802117 188354745469074048525397)
            ·
              refine ⟨2207282173465711506157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 188354745469074048525397 2207282173465711506157)
              ·
                rfl

theorem cell21_87048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 8].length) (baseStart_87048 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_87048 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_87048 prefixEnd_87048 := by exact prefixLift 87048
  have htrace : WordTrace (prefixWord ++ tailWord_87048) baseStart_87048 baseEnd_87048 := by
    simpa [prefixWord, tailWord_87048, baseEnd_87048] using wordTrace_append hprefix tailTrace_87048
  have hstable : (prefixWord ++ tailWord_87048).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87048).length < 2 ^ (prefixWord ++ tailWord_87048).sum := by decide
  have hdescent : baseEnd_87048 < baseStart_87048 := by decide
  rcases family_descends (prefixWord ++ tailWord_87048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87051 : List Nat := [1, 1, 1, 1, 6, 4, 1, 2, 4]
def baseStart_87051 : Nat := 118140960795 + 87051 * 2 ^ 59
def prefixEnd_87051 : Nat := 4983230072969 + 3 ^ 40 * 87051 * 2
def baseEnd_87051 : Nat := 19866224202064065005407

theorem tailTrace_87051 : CollatzResearch.WordTrace tailWord_87051 prefixEnd_87051 19866224202064065005407 := by
  unfold tailWord_87051
  simp only [CollatzResearch.WordTrace]
  refine ⟨3175010807636568972277007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2116673871757712648184671 3175010807636568972277007)
  ·
    refine ⟨4762516211454853458415511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3175010807636568972277007 4762516211454853458415511)
    ·
      refine ⟨7143774317182280187623267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4762516211454853458415511 7143774317182280187623267)
      ·
        refine ⟨10715661475773420281434901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7143774317182280187623267 10715661475773420281434901)
        ·
          refine ⟨502296631676879075692261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 10715661475773420281434901 502296631676879075692261)
          ·
            refine ⟨94180618439414826692299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 502296631676879075692261 94180618439414826692299)
            ·
              refine ⟨141270927659122240038449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94180618439414826692299 141270927659122240038449)
              ·
                refine ⟨105953195744341680028837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 141270927659122240038449 105953195744341680028837)
                ·
                  refine ⟨19866224202064065005407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 105953195744341680028837 19866224202064065005407)
                  ·
                    rfl

theorem cell21_87051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 1, 2, 4].length) (baseStart_87051 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_87051 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_87051 prefixEnd_87051 := by exact prefixLift 87051
  have htrace : WordTrace (prefixWord ++ tailWord_87051) baseStart_87051 baseEnd_87051 := by
    simpa [prefixWord, tailWord_87051, baseEnd_87051] using wordTrace_append hprefix tailTrace_87051
  have hstable : (prefixWord ++ tailWord_87051).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87051).length < 2 ^ (prefixWord ++ tailWord_87051).sum := by decide
  have hdescent : baseEnd_87051 < baseStart_87051 := by decide
  rcases family_descends (prefixWord ++ tailWord_87051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87068 : List Nat := [2, 2, 3, 1, 4, 1, 3, 1, 4]
def baseStart_87068 : Nat := 118140960795 + 87068 * 2 ^ 59
def prefixEnd_87068 : Nat := 4983230072969 + 3 ^ 40 * 87068 * 2
def baseEnd_87068 : Nat := 19870103833675813222039

theorem tailTrace_87068 : CollatzResearch.WordTrace tailWord_87068 prefixEnd_87068 19870103833675813222039 := by
  unfold tailWord_87068
  simp only [CollatzResearch.WordTrace]
  refine ⟨1587815424287490437822929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2117087232383320583763905 1587815424287490437822929)
  ·
    refine ⟨1190861568215617828367197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1587815424287490437822929 1190861568215617828367197)
    ·
      refine ⟨446573088080856685637699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1190861568215617828367197 446573088080856685637699)
      ·
        refine ⟨669859632121285028456549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 446573088080856685637699 669859632121285028456549)
        ·
          refine ⟨125598681022740942835603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 669859632121285028456549 125598681022740942835603)
          ·
            refine ⟨188398021534111414253405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125598681022740942835603 188398021534111414253405)
            ·
              refine ⟨70649258075291780345027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 188398021534111414253405 70649258075291780345027)
              ·
                refine ⟨105973887112937670517541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70649258075291780345027 105973887112937670517541)
                ·
                  refine ⟨19870103833675813222039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 105973887112937670517541 19870103833675813222039)
                  ·
                    rfl

theorem cell21_87068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 3, 1, 4].length) (baseStart_87068 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_87068 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_87068 prefixEnd_87068 := by exact prefixLift 87068
  have htrace : WordTrace (prefixWord ++ tailWord_87068) baseStart_87068 baseEnd_87068 := by
    simpa [prefixWord, tailWord_87068, baseEnd_87068] using wordTrace_append hprefix tailTrace_87068
  have hstable : (prefixWord ++ tailWord_87068).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87068).length < 2 ^ (prefixWord ++ tailWord_87068).sum := by decide
  have hdescent : baseEnd_87068 < baseStart_87068 := by decide
  rcases family_descends (prefixWord ++ tailWord_87068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87124 : List Nat := [2, 4, 1, 1, 1, 1, 3, 8]
def baseStart_87124 : Nat := 118140960795 + 87124 * 2 ^ 59
def prefixEnd_87124 : Nat := 4983230072969 + 3 ^ 40 * 87124 * 2
def baseEnd_87124 : Nat := 6627627932210720096197

theorem tailTrace_87124 : CollatzResearch.WordTrace tailWord_87124 prefixEnd_87124 6627627932210720096197 := by
  unfold tailWord_87124
  simp only [CollatzResearch.WordTrace]
  refine ⟨1588836668186051219842213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2118448890914734959789617 1588836668186051219842213)
  ·
    refine ⟨297906875284884603720415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1588836668186051219842213 297906875284884603720415)
    ·
      refine ⟨446860312927326905580623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 297906875284884603720415 446860312927326905580623)
      ·
        refine ⟨670290469390990358370935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 446860312927326905580623 670290469390990358370935)
        ·
          refine ⟨1005435704086485537556403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 670290469390990358370935 1005435704086485537556403)
          ·
            refine ⟨1508153556129728306334605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1005435704086485537556403 1508153556129728306334605)
            ·
              refine ⟨565557583548648114875477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1508153556129728306334605 565557583548648114875477)
              ·
                refine ⟨6627627932210720096197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 565557583548648114875477 6627627932210720096197)
                ·
                  rfl

theorem cell21_87124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 8].length) (baseStart_87124 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_87124 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_87124 prefixEnd_87124 := by exact prefixLift 87124
  have htrace : WordTrace (prefixWord ++ tailWord_87124) baseStart_87124 baseEnd_87124 := by
    simpa [prefixWord, tailWord_87124, baseEnd_87124] using wordTrace_append hprefix tailTrace_87124
  have hstable : (prefixWord ++ tailWord_87124).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87124).length < 2 ^ (prefixWord ++ tailWord_87124).sum := by decide
  have hdescent : baseEnd_87124 < baseStart_87124 := by decide
  rcases family_descends (prefixWord ++ tailWord_87124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87265 : List Nat := [1, 2, 3, 1, 3, 4, 1, 3, 3]
def baseStart_87265 : Nat := 118140960795 + 87265 * 2 ^ 59
def prefixEnd_87265 : Nat := 4983230072969 + 3 ^ 40 * 87265 * 2
def baseEnd_87265 : Nat := 19915061917647248438303

theorem tailTrace_87265 : CollatzResearch.WordTrace tailWord_87265 prefixEnd_87265 19915061917647248438303 := by
  unfold tailWord_87265
  simp only [CollatzResearch.WordTrace]
  refine ⟨3182816028861283520567249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2121877352574189013711499 3182816028861283520567249)
  ·
    refine ⟨2387112021645962640425437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3182816028861283520567249 2387112021645962640425437)
    ·
      refine ⟨895167008117235990159539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2387112021645962640425437 895167008117235990159539)
      ·
        refine ⟨1342750512175853985239309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 895167008117235990159539 1342750512175853985239309)
        ·
          refine ⟨503531442065945244464741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1342750512175853985239309 503531442065945244464741)
          ·
            refine ⟨94412145387364733337139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 503531442065945244464741 94412145387364733337139)
            ·
              refine ⟨141618218081047100005709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94412145387364733337139 141618218081047100005709)
              ·
                refine ⟨53106831780392662502141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 141618218081047100005709 53106831780392662502141)
                ·
                  refine ⟨19915061917647248438303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53106831780392662502141 19915061917647248438303)
                  ·
                    rfl

theorem cell21_87265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 1, 3, 3].length) (baseStart_87265 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_87265 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_87265 prefixEnd_87265 := by exact prefixLift 87265
  have htrace : WordTrace (prefixWord ++ tailWord_87265) baseStart_87265 baseEnd_87265 := by
    simpa [prefixWord, tailWord_87265, baseEnd_87265] using wordTrace_append hprefix tailTrace_87265
  have hstable : (prefixWord ++ tailWord_87265).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87265).length < 2 ^ (prefixWord ++ tailWord_87265).sum := by decide
  have hdescent : baseEnd_87265 < baseStart_87265 := by decide
  rcases family_descends (prefixWord ++ tailWord_87265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87276 : List Nat := [2, 2, 1, 1, 2, 6, 7]
def baseStart_87276 : Nat := 118140960795 + 87276 * 2 ^ 59
def prefixEnd_87276 : Nat := 4983230072969 + 3 ^ 40 * 87276 * 2
def baseEnd_87276 : Nat := 2213063585279297083883

theorem tailTrace_87276 : CollatzResearch.WordTrace tailWord_87276 prefixEnd_87276 2213063585279297083883 := by
  unfold tailWord_87276
  simp only [CollatzResearch.WordTrace]
  refine ⟨1591608615910716199608841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2122144821214288266145121 1591608615910716199608841)
  ·
    refine ⟨1193706461933037149706631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1591608615910716199608841 1193706461933037149706631)
    ·
      refine ⟨1790559692899555724559947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1193706461933037149706631 1790559692899555724559947)
      ·
        refine ⟨2685839539349333586839921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1790559692899555724559947 2685839539349333586839921)
        ·
          refine ⟨2014379654512000190129941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2685839539349333586839921 2014379654512000190129941)
          ·
            refine ⟨94424046305250008912341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 2014379654512000190129941 94424046305250008912341)
            ·
              refine ⟨2213063585279297083883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 94424046305250008912341 2213063585279297083883)
              ·
                rfl

theorem cell21_87276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 7].length) (baseStart_87276 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_87276 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_87276 prefixEnd_87276 := by exact prefixLift 87276
  have htrace : WordTrace (prefixWord ++ tailWord_87276) baseStart_87276 baseEnd_87276 := by
    simpa [prefixWord, tailWord_87276, baseEnd_87276] using wordTrace_append hprefix tailTrace_87276
  have hstable : (prefixWord ++ tailWord_87276).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87276).length < 2 ^ (prefixWord ++ tailWord_87276).sum := by decide
  have hdescent : baseEnd_87276 < baseStart_87276 := by decide
  rcases family_descends (prefixWord ++ tailWord_87276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87282 : List Nat := [3, 2, 1, 3, 3, 1, 3, 2, 3]
def baseStart_87282 : Nat := 118140960795 + 87282 * 2 ^ 59
def prefixEnd_87282 : Nat := 4983230072969 + 3 ^ 40 * 87282 * 2
def baseEnd_87282 : Nat := 19918941549258996654935

theorem tailTrace_87282 : CollatzResearch.WordTrace tailWord_87282 prefixEnd_87282 19918941549258996654935 := by
  unfold tailWord_87282
  simp only [CollatzResearch.WordTrace]
  refine ⟨795859017449923855984025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2122290713199796949290733 795859017449923855984025)
  ·
    refine ⟨596894263087442891988019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 795859017449923855984025 596894263087442891988019)
    ·
      refine ⟨895341394631164337982029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 596894263087442891988019 895341394631164337982029)
      ·
        refine ⟨335753022986686626743261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 895341394631164337982029 335753022986686626743261)
        ·
          refine ⟨125907383620007485028723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 335753022986686626743261 125907383620007485028723)
          ·
            refine ⟨188861075430011227543085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125907383620007485028723 188861075430011227543085)
            ·
              refine ⟨70822903286254210328657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 188861075430011227543085 70822903286254210328657)
              ·
                refine ⟨53117177464690657746493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70822903286254210328657 53117177464690657746493)
                ·
                  refine ⟨19918941549258996654935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53117177464690657746493 19918941549258996654935)
                  ·
                    rfl

theorem cell21_87282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 3, 2, 3].length) (baseStart_87282 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_87282 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_87282 prefixEnd_87282 := by exact prefixLift 87282
  have htrace : WordTrace (prefixWord ++ tailWord_87282) baseStart_87282 baseEnd_87282 := by
    simpa [prefixWord, tailWord_87282, baseEnd_87282] using wordTrace_append hprefix tailTrace_87282
  have hstable : (prefixWord ++ tailWord_87282).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87282).length < 2 ^ (prefixWord ++ tailWord_87282).sum := by decide
  have hdescent : baseEnd_87282 < baseStart_87282 := by decide
  rcases family_descends (prefixWord ++ tailWord_87282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87397 : List Nat := [1, 3, 1, 3, 1, 2, 3, 1, 6]
def baseStart_87397 : Nat := 118140960795 + 87397 * 2 ^ 59
def prefixEnd_87397 : Nat := 4983230072969 + 3 ^ 40 * 87397 * 2
def baseEnd_87397 : Nat := 19945186116044352238033

theorem tailTrace_87397 : CollatzResearch.WordTrace tailWord_87397 prefixEnd_87397 19945186116044352238033 := by
  unfold tailWord_87397
  simp only [CollatzResearch.WordTrace]
  refine ⟨3187630464383070064372445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2125086976255380042914963 3187630464383070064372445)
  ·
    refine ⟨1195361424143651274139667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3187630464383070064372445 1195361424143651274139667)
    ·
      refine ⟨1793042136215476911209501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1195361424143651274139667 1793042136215476911209501)
      ·
        refine ⟨672390801080803841703563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1793042136215476911209501 672390801080803841703563)
        ·
          refine ⟨1008586201621205762555345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 672390801080803841703563 1008586201621205762555345)
          ·
            refine ⟨756439651215904321916509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1008586201621205762555345 756439651215904321916509)
            ·
              refine ⟨283664869205964120718691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 756439651215904321916509 283664869205964120718691)
              ·
                refine ⟨425497303808946181078037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 283664869205964120718691 425497303808946181078037)
                ·
                  refine ⟨19945186116044352238033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 425497303808946181078037 19945186116044352238033)
                  ·
                    rfl

theorem cell21_87397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 1, 6].length) (baseStart_87397 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_87397 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_87397 prefixEnd_87397 := by exact prefixLift 87397
  have htrace : WordTrace (prefixWord ++ tailWord_87397) baseStart_87397 baseEnd_87397 := by
    simpa [prefixWord, tailWord_87397, baseEnd_87397] using wordTrace_append hprefix tailTrace_87397
  have hstable : (prefixWord ++ tailWord_87397).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87397).length < 2 ^ (prefixWord ++ tailWord_87397).sum := by decide
  have hdescent : baseEnd_87397 < baseStart_87397 := by decide
  rcases family_descends (prefixWord ++ tailWord_87397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87400 : List Nat := [2, 1, 4, 2, 3, 1, 2, 1, 5]
def baseStart_87400 : Nat := 118140960795 + 87400 * 2 ^ 59
def prefixEnd_87400 : Nat := 4983230072969 + 3 ^ 40 * 87400 * 2
def baseEnd_87400 : Nat := 19945870756917013688027

theorem tailTrace_87400 : CollatzResearch.WordTrace tailWord_87400 prefixEnd_87400 19945870756917013688027 := by
  unfold tailWord_87400
  simp only [CollatzResearch.WordTrace]
  refine ⟨1593869941686100788365827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2125159922248134384487769 1593869941686100788365827)
  ·
    refine ⟨2390804912529151182548741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1593869941686100788365827 2390804912529151182548741)
    ·
      refine ⟨448275921099215846727889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2390804912529151182548741 448275921099215846727889)
      ·
        refine ⟨336206940824411885045917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 448275921099215846727889 336206940824411885045917)
        ·
          refine ⟨126077602809154456892219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 336206940824411885045917 126077602809154456892219)
          ·
            refine ⟨189116404213731685338329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126077602809154456892219 189116404213731685338329)
            ·
              refine ⟨141837303160298764003747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 189116404213731685338329 141837303160298764003747)
              ·
                refine ⟨212755954740448146005621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 141837303160298764003747 212755954740448146005621)
                ·
                  refine ⟨19945870756917013688027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 212755954740448146005621 19945870756917013688027)
                  ·
                    rfl

theorem cell21_87400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 2, 1, 5].length) (baseStart_87400 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_87400 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_87400 prefixEnd_87400 := by exact prefixLift 87400
  have htrace : WordTrace (prefixWord ++ tailWord_87400) baseStart_87400 baseEnd_87400 := by
    simpa [prefixWord, tailWord_87400, baseEnd_87400] using wordTrace_append hprefix tailTrace_87400
  have hstable : (prefixWord ++ tailWord_87400).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87400).length < 2 ^ (prefixWord ++ tailWord_87400).sum := by decide
  have hdescent : baseEnd_87400 < baseStart_87400 := by decide
  rcases family_descends (prefixWord ++ tailWord_87400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87428 : List Nat := [2, 3, 2, 1, 1, 4, 1, 7]
def baseStart_87428 : Nat := 118140960795 + 87428 * 2 ^ 59
def prefixEnd_87428 : Nat := 4983230072969 + 3 ^ 40 * 87428 * 2
def baseEnd_87428 : Nat := 6650753579465062407101

theorem tailTrace_87428 : CollatzResearch.WordTrace tailWord_87428 prefixEnd_87428 6650753579465062407101 := by
  unfold tailWord_87428
  simp only [CollatzResearch.WordTrace]
  refine ⟨1594380563635381179375469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2125840751513841572500625 1594380563635381179375469)
  ·
    refine ⟨597892711363267942265801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1594380563635381179375469 597892711363267942265801)
    ·
      refine ⟨448419533522450956699351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 597892711363267942265801 448419533522450956699351)
      ·
        refine ⟨672629300283676435049027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 448419533522450956699351 672629300283676435049027)
        ·
          refine ⟨1008943950425514652573541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 672629300283676435049027 1008943950425514652573541)
          ·
            refine ⟨189176990704783997357539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1008943950425514652573541 189176990704783997357539)
            ·
              refine ⟨283765486057175996036309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 189176990704783997357539 283765486057175996036309)
              ·
                refine ⟨6650753579465062407101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 283765486057175996036309 6650753579465062407101)
                ·
                  rfl

theorem cell21_87428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 7].length) (baseStart_87428 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_87428 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_87428 prefixEnd_87428 := by exact prefixLift 87428
  have htrace : WordTrace (prefixWord ++ tailWord_87428) baseStart_87428 baseEnd_87428 := by
    simpa [prefixWord, tailWord_87428, baseEnd_87428] using wordTrace_append hprefix tailTrace_87428
  have hstable : (prefixWord ++ tailWord_87428).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87428).length < 2 ^ (prefixWord ++ tailWord_87428).sum := by decide
  have hdescent : baseEnd_87428 < baseStart_87428 := by decide
  rcases family_descends (prefixWord ++ tailWord_87428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87510 : List Nat := [5, 2, 1, 1, 1, 2, 4, 2, 3]
def baseStart_87510 : Nat := 118140960795 + 87510 * 2 ^ 59
def prefixEnd_87510 : Nat := 4983230072969 + 3 ^ 40 * 87510 * 2
def baseEnd_87510 : Nat := 19970974255581266854469

theorem tailTrace_87510 : CollatzResearch.WordTrace tailWord_87510 prefixEnd_87510 19970974255581266854469 := by
  unfold tailWord_87510
  simp only [CollatzResearch.WordTrace]
  refine ⟨199484494560855647702249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2127834608649126908823989 199484494560855647702249)
  ·
    refine ⟨149613370920641735776687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199484494560855647702249 149613370920641735776687)
    ·
      refine ⟨224420056380962603665031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149613370920641735776687 224420056380962603665031)
      ·
        refine ⟨336630084571443905497547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224420056380962603665031 336630084571443905497547)
        ·
          refine ⟨504945126857165858246321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 336630084571443905497547 504945126857165858246321)
          ·
            refine ⟨378708845142874393684741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 504945126857165858246321 378708845142874393684741)
            ·
              refine ⟨71007908464288948815889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 378708845142874393684741 71007908464288948815889)
              ·
                refine ⟨53255931348216711611917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71007908464288948815889 53255931348216711611917)
                ·
                  refine ⟨19970974255581266854469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53255931348216711611917 19970974255581266854469)
                  ·
                    rfl

theorem cell21_87510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 4, 2, 3].length) (baseStart_87510 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_87510 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_87510 prefixEnd_87510 := by exact prefixLift 87510
  have htrace : WordTrace (prefixWord ++ tailWord_87510) baseStart_87510 baseEnd_87510 := by
    simpa [prefixWord, tailWord_87510, baseEnd_87510] using wordTrace_append hprefix tailTrace_87510
  have hstable : (prefixWord ++ tailWord_87510).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87510).length < 2 ^ (prefixWord ++ tailWord_87510).sum := by decide
  have hdescent : baseEnd_87510 < baseStart_87510 := by decide
  rcases family_descends (prefixWord ++ tailWord_87510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87558 : List Nat := [6, 2, 1, 1, 2, 2, 1, 2, 4]
def baseStart_87558 : Nat := 118140960795 + 87558 * 2 ^ 59
def prefixEnd_87558 : Nat := 4983230072969 + 3 ^ 40 * 87558 * 2
def baseEnd_87558 : Nat := 19981928509543850054371

theorem tailTrace_87558 : CollatzResearch.WordTrace tailWord_87558 prefixEnd_87558 19981928509543850054371 := by
  unfold tailWord_87558
  simp only [CollatzResearch.WordTrace]
  refine ⟨99796956774993580030729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 2129001744533196373988885 99796956774993580030729)
  ·
    refine ⟨74847717581245185023047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99796956774993580030729 74847717581245185023047)
    ·
      refine ⟨112271576371867777534571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74847717581245185023047 112271576371867777534571)
      ·
        refine ⟨168407364557801666301857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112271576371867777534571 168407364557801666301857)
        ·
          refine ⟨126305523418351249726393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168407364557801666301857 126305523418351249726393)
          ·
            refine ⟨94729142563763437294795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126305523418351249726393 94729142563763437294795)
            ·
              refine ⟨142093713845645155942193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94729142563763437294795 142093713845645155942193)
              ·
                refine ⟨106570285384233866956645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 142093713845645155942193 106570285384233866956645)
                ·
                  refine ⟨19981928509543850054371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 106570285384233866956645 19981928509543850054371)
                  ·
                    rfl

theorem cell21_87558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_87558 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_87558 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_87558 prefixEnd_87558 := by exact prefixLift 87558
  have htrace : WordTrace (prefixWord ++ tailWord_87558) baseStart_87558 baseEnd_87558 := by
    simpa [prefixWord, tailWord_87558, baseEnd_87558] using wordTrace_append hprefix tailTrace_87558
  have hstable : (prefixWord ++ tailWord_87558).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87558).length < 2 ^ (prefixWord ++ tailWord_87558).sum := by decide
  have hdescent : baseEnd_87558 < baseStart_87558 := by decide
  rcases family_descends (prefixWord ++ tailWord_87558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87566 : List Nat := [4, 1, 1, 2, 4, 1, 1, 1, 6]
def baseStart_87566 : Nat := 118140960795 + 87566 * 2 ^ 59
def prefixEnd_87566 : Nat := 4983230072969 + 3 ^ 40 * 87566 * 2
def baseEnd_87566 : Nat := 19983754218537613921021

theorem tailTrace_87566 : CollatzResearch.WordTrace tailWord_87566 prefixEnd_87566 19983754218537613921021 := by
  unfold tailWord_87566
  simp only [CollatzResearch.WordTrace]
  refine ⟨399224300096351490909319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2129196267180541284849701 399224300096351490909319)
  ·
    refine ⟨598836450144527236363979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 399224300096351490909319 598836450144527236363979)
    ·
      refine ⟨898254675216790854545969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 598836450144527236363979 898254675216790854545969)
      ·
        refine ⟨673691006412593140909477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 898254675216790854545969 673691006412593140909477)
        ·
          refine ⟨126317063702361213920527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 673691006412593140909477 126317063702361213920527)
          ·
            refine ⟨189475595553541820880791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126317063702361213920527 189475595553541820880791)
            ·
              refine ⟨284213393330312731321187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 189475595553541820880791 284213393330312731321187)
              ·
                refine ⟨426320089995469096981781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 284213393330312731321187 426320089995469096981781)
                ·
                  refine ⟨19983754218537613921021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 426320089995469096981781 19983754218537613921021)
                  ·
                    rfl

theorem cell21_87566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 1, 6].length) (baseStart_87566 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_87566 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_87566 prefixEnd_87566 := by exact prefixLift 87566
  have htrace : WordTrace (prefixWord ++ tailWord_87566) baseStart_87566 baseEnd_87566 := by
    simpa [prefixWord, tailWord_87566, baseEnd_87566] using wordTrace_append hprefix tailTrace_87566
  have hstable : (prefixWord ++ tailWord_87566).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87566).length < 2 ^ (prefixWord ++ tailWord_87566).sum := by decide
  have hdescent : baseEnd_87566 < baseStart_87566 := by decide
  rcases family_descends (prefixWord ++ tailWord_87566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87639 : List Nat := [1, 1, 3, 2, 2, 3, 1, 8]
def baseStart_87639 : Nat := 118140960795 + 87639 * 2 ^ 59
def prefixEnd_87639 : Nat := 4983230072969 + 3 ^ 40 * 87639 * 2
def baseEnd_87639 : Nat := 6666804604368569734735

theorem tailTrace_87639 : CollatzResearch.WordTrace tailWord_87639 prefixEnd_87639 6666804604368569734735 := by
  unfold tailWord_87639
  simp only [CollatzResearch.WordTrace]
  refine ⟨3196456929506345394681971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2130971286337563596454647 3196456929506345394681971)
  ·
    refine ⟨4794685394259518092022957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3196456929506345394681971 4794685394259518092022957)
    ·
      refine ⟨1798007022847319284508609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4794685394259518092022957 1798007022847319284508609)
      ·
        refine ⟨1348505267135489463381457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1798007022847319284508609 1348505267135489463381457)
        ·
          refine ⟨1011378950351617097536093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1348505267135489463381457 1011378950351617097536093)
          ·
            refine ⟨379267106381856411576035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1011378950351617097536093 379267106381856411576035)
            ·
              refine ⟨568900659572784617364053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 379267106381856411576035 568900659572784617364053)
              ·
                refine ⟨6666804604368569734735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 568900659572784617364053 6666804604368569734735)
                ·
                  rfl

theorem cell21_87639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 8].length) (baseStart_87639 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_87639 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_87639 prefixEnd_87639 := by exact prefixLift 87639
  have htrace : WordTrace (prefixWord ++ tailWord_87639) baseStart_87639 baseEnd_87639 := by
    simpa [prefixWord, tailWord_87639, baseEnd_87639] using wordTrace_append hprefix tailTrace_87639
  have hstable : (prefixWord ++ tailWord_87639).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87639).length < 2 ^ (prefixWord ++ tailWord_87639).sum := by decide
  have hdescent : baseEnd_87639 < baseStart_87639 := by decide
  rcases family_descends (prefixWord ++ tailWord_87639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87656 : List Nat := [2, 1, 4, 3, 1, 1, 2, 7]
def baseStart_87656 : Nat := 118140960795 + 87656 * 2 ^ 59
def prefixEnd_87656 : Nat := 4983230072969 + 3 ^ 40 * 87656 * 2
def baseEnd_87656 : Nat := 6668097814905819140279

theorem tailTrace_87656 : CollatzResearch.WordTrace tailWord_87656 prefixEnd_87656 6668097814905819140279 := by
  unfold tailWord_87656
  simp only [CollatzResearch.WordTrace]
  refine ⟨1598538485222378649025411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2131384646963171532033881 1598538485222378649025411)
  ·
    refine ⟨2397807727833567973538117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1598538485222378649025411 2397807727833567973538117)
    ·
      refine ⟨449588948968793995038397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2397807727833567973538117 449588948968793995038397)
      ·
        refine ⟨168595855863297748139399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 449588948968793995038397 168595855863297748139399)
        ·
          refine ⟨252893783794946622209099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168595855863297748139399 252893783794946622209099)
          ·
            refine ⟨379340675692419933313649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 252893783794946622209099 379340675692419933313649)
            ·
              refine ⟨284505506769314949985237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 379340675692419933313649 284505506769314949985237)
              ·
                refine ⟨6668097814905819140279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 284505506769314949985237 6668097814905819140279)
                ·
                  rfl

theorem cell21_87656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 7].length) (baseStart_87656 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_87656 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_87656 prefixEnd_87656 := by exact prefixLift 87656
  have htrace : WordTrace (prefixWord ++ tailWord_87656) baseStart_87656 baseEnd_87656 := by
    simpa [prefixWord, tailWord_87656, baseEnd_87656] using wordTrace_append hprefix tailTrace_87656
  have hstable : (prefixWord ++ tailWord_87656).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87656).length < 2 ^ (prefixWord ++ tailWord_87656).sum := by decide
  have hdescent : baseEnd_87656 < baseStart_87656 := by decide
  rcases family_descends (prefixWord ++ tailWord_87656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87766 : List Nat := [5, 2, 1, 3, 1, 1, 1, 7]
def baseStart_87766 : Nat := 118140960795 + 87766 * 2 ^ 59
def prefixEnd_87766 : Nat := 4983230072969 + 3 ^ 40 * 87766 * 2
def baseEnd_87766 : Nat := 6676465647793903529093

theorem tailTrace_87766 : CollatzResearch.WordTrace tailWord_87766 prefixEnd_87766 6676465647793903529093 := by
  unfold tailWord_87766
  simp only [CollatzResearch.WordTrace]
  refine ⟨200068062502890380284697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2134059333364164056370101 200068062502890380284697)
  ·
    refine ⟨150051046877167785213523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 200068062502890380284697 150051046877167785213523)
    ·
      refine ⟨225076570315751677820285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150051046877167785213523 225076570315751677820285)
      ·
        refine ⟨84403713868406879182607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 225076570315751677820285 84403713868406879182607)
        ·
          refine ⟨126605570802610318773911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84403713868406879182607 126605570802610318773911)
          ·
            refine ⟨189908356203915478160867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126605570802610318773911 189908356203915478160867)
            ·
              refine ⟨284862534305873217241301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 189908356203915478160867 284862534305873217241301)
              ·
                refine ⟨6676465647793903529093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 284862534305873217241301 6676465647793903529093)
                ·
                  rfl

theorem cell21_87766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 7].length) (baseStart_87766 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_87766 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_87766 prefixEnd_87766 := by exact prefixLift 87766
  have htrace : WordTrace (prefixWord ++ tailWord_87766) baseStart_87766 baseEnd_87766 := by
    simpa [prefixWord, tailWord_87766, baseEnd_87766] using wordTrace_append hprefix tailTrace_87766
  have hstable : (prefixWord ++ tailWord_87766).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87766).length < 2 ^ (prefixWord ++ tailWord_87766).sum := by decide
  have hdescent : baseEnd_87766 < baseStart_87766 := by decide
  rcases family_descends (prefixWord ++ tailWord_87766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87822 : List Nat := [4, 1, 1, 2, 1, 1, 2, 4, 5]
def baseStart_87822 : Nat := 118140960795 + 87822 * 2 ^ 59
def prefixEnd_87822 : Nat := 4983230072969 + 3 ^ 40 * 87822 * 2
def baseEnd_87822 : Nat := 20042176906338057653831

theorem tailTrace_87822 : CollatzResearch.WordTrace tailWord_87822 prefixEnd_87822 20042176906338057653831 := by
  unfold tailWord_87822
  simp only [CollatzResearch.WordTrace]
  refine ⟨400391435980420956074215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2135420991895578432395813 400391435980420956074215)
  ·
    refine ⟨600587153970631434111323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 400391435980420956074215 600587153970631434111323)
    ·
      refine ⟨900880730955947151166985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 600587153970631434111323 900880730955947151166985)
      ·
        refine ⟨675660548216960363375239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 900880730955947151166985 675660548216960363375239)
        ·
          refine ⟨1013490822325440545062859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 675660548216960363375239 1013490822325440545062859)
          ·
            refine ⟨1520236233488160817594289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1013490822325440545062859 1520236233488160817594289)
            ·
              refine ⟨1140177175116120613195717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1520236233488160817594289 1140177175116120613195717)
              ·
                refine ⟨213783220334272614974197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1140177175116120613195717 213783220334272614974197)
                ·
                  refine ⟨20042176906338057653831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 213783220334272614974197 20042176906338057653831)
                  ·
                    rfl

theorem cell21_87822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 4, 5].length) (baseStart_87822 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_87822 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_87822 prefixEnd_87822 := by exact prefixLift 87822
  have htrace : WordTrace (prefixWord ++ tailWord_87822) baseStart_87822 baseEnd_87822 := by
    simpa [prefixWord, tailWord_87822, baseEnd_87822] using wordTrace_append hprefix tailTrace_87822
  have hstable : (prefixWord ++ tailWord_87822).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87822).length < 2 ^ (prefixWord ++ tailWord_87822).sum := by decide
  have hdescent : baseEnd_87822 < baseStart_87822 := by decide
  rcases family_descends (prefixWord ++ tailWord_87822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87839 : List Nat := [1, 1, 2, 4, 2, 1, 2, 5, 3]
def baseStart_87839 : Nat := 118140960795 + 87839 * 2 ^ 59
def prefixEnd_87839 : Nat := 4983230072969 + 3 ^ 40 * 87839 * 2
def baseEnd_87839 : Nat := 20046056537949805870463

theorem tailTrace_87839 : CollatzResearch.WordTrace tailWord_87839 prefixEnd_87839 20046056537949805870463 := by
  unfold tailWord_87839
  simp only [CollatzResearch.WordTrace]
  refine ⟨3203751528781779551962571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2135834352521186367975047 3203751528781779551962571)
  ·
    refine ⟨4805627293172669327943857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3203751528781779551962571 4805627293172669327943857)
    ·
      refine ⟨3604220469879501995957893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4805627293172669327943857 3604220469879501995957893)
      ·
        refine ⟨675791338102406624242105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3604220469879501995957893 675791338102406624242105)
        ·
          refine ⟨506843503576804968181579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 675791338102406624242105 506843503576804968181579)
          ·
            refine ⟨760265255365207452272369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 506843503576804968181579 760265255365207452272369)
            ·
              refine ⟨570198941523905589204277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 760265255365207452272369 570198941523905589204277)
              ·
                refine ⟨53456150767866148987901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 570198941523905589204277 53456150767866148987901)
                ·
                  refine ⟨20046056537949805870463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53456150767866148987901 20046056537949805870463)
                  ·
                    rfl

theorem cell21_87839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 5, 3].length) (baseStart_87839 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_87839 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_87839 prefixEnd_87839 := by exact prefixLift 87839
  have htrace : WordTrace (prefixWord ++ tailWord_87839) baseStart_87839 baseEnd_87839 := by
    simpa [prefixWord, tailWord_87839, baseEnd_87839] using wordTrace_append hprefix tailTrace_87839
  have hstable : (prefixWord ++ tailWord_87839).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87839).length < 2 ^ (prefixWord ++ tailWord_87839).sum := by decide
  have hdescent : baseEnd_87839 < baseStart_87839 := by decide
  rcases family_descends (prefixWord ++ tailWord_87839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87870 : List Nat := [4, 2, 1, 2, 2, 1, 2, 3, 4]
def baseStart_87870 : Nat := 118140960795 + 87870 * 2 ^ 59
def prefixEnd_87870 : Nat := 4983230072969 + 3 ^ 40 * 87870 * 2
def baseEnd_87870 : Nat := 20053131160300640853733

theorem tailTrace_87870 : CollatzResearch.WordTrace tailWord_87870 prefixEnd_87870 20053131160300640853733 := by
  unfold tailWord_87870
  simp only [CollatzResearch.WordTrace]
  refine ⟨400610273958683980792633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2136588127779647897560709 400610273958683980792633)
  ·
    refine ⟨300457705469012985594475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 400610273958683980792633 300457705469012985594475)
    ·
      refine ⟨450686558203519478391713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 300457705469012985594475 450686558203519478391713)
      ·
        refine ⟨338014918652639608793785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 450686558203519478391713 338014918652639608793785)
        ·
          refine ⟨253511188989479706595339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 338014918652639608793785 253511188989479706595339)
          ·
            refine ⟨380266783484219559893009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 253511188989479706595339 380266783484219559893009)
            ·
              refine ⟨285200087613164669919757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 380266783484219559893009 285200087613164669919757)
              ·
                refine ⟨106950032854936751219909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 285200087613164669919757 106950032854936751219909)
                ·
                  refine ⟨20053131160300640853733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 106950032854936751219909 20053131160300640853733)
                  ·
                    rfl

theorem cell21_87870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 3, 4].length) (baseStart_87870 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_87870 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_87870 prefixEnd_87870 := by exact prefixLift 87870
  have htrace : WordTrace (prefixWord ++ tailWord_87870) baseStart_87870 baseEnd_87870 := by
    simpa [prefixWord, tailWord_87870, baseEnd_87870] using wordTrace_append hprefix tailTrace_87870
  have hstable : (prefixWord ++ tailWord_87870).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87870).length < 2 ^ (prefixWord ++ tailWord_87870).sum := by decide
  have hdescent : baseEnd_87870 < baseStart_87870 := by decide
  rcases family_descends (prefixWord ++ tailWord_87870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_87966 : List Nat := [4, 3, 1, 3, 2, 1, 1, 1, 5]
def baseStart_87966 : Nat := 118140960795 + 87966 * 2 ^ 59
def prefixEnd_87966 : Nat := 4983230072969 + 3 ^ 40 * 87966 * 2
def baseEnd_87966 : Nat := 20075039668225807253537

theorem tailTrace_87966 : CollatzResearch.WordTrace tailWord_87966 prefixEnd_87966 20075039668225807253537 := by
  unfold tailWord_87966
  simp only [CollatzResearch.WordTrace]
  refine ⟨401047949915210030229469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2138922399547786827890501 401047949915210030229469)
  ·
    refine ⟨150392981218203761336051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 401047949915210030229469 150392981218203761336051)
    ·
      refine ⟨225589471827305642004077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 150392981218203761336051 225589471827305642004077)
      ·
        refine ⟨84596051935239615751529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 225589471827305642004077 84596051935239615751529)
        ·
          refine ⟨63447038951429711813647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84596051935239615751529 63447038951429711813647)
          ·
            refine ⟨95170558427144567720471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63447038951429711813647 95170558427144567720471)
            ·
              refine ⟨142755837640716851580707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95170558427144567720471 142755837640716851580707)
              ·
                refine ⟨214133756461075277371061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 142755837640716851580707 214133756461075277371061)
                ·
                  refine ⟨20075039668225807253537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 214133756461075277371061 20075039668225807253537)
                  ·
                    rfl

theorem cell21_87966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 1, 1, 5].length) (baseStart_87966 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_87966 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_87966 prefixEnd_87966 := by exact prefixLift 87966
  have htrace : WordTrace (prefixWord ++ tailWord_87966) baseStart_87966 baseEnd_87966 := by
    simpa [prefixWord, tailWord_87966, baseEnd_87966] using wordTrace_append hprefix tailTrace_87966
  have hstable : (prefixWord ++ tailWord_87966).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_87966).length < 2 ^ (prefixWord ++ tailWord_87966).sum := by decide
  have hdescent : baseEnd_87966 < baseStart_87966 := by decide
  rcases family_descends (prefixWord ++ tailWord_87966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88025 : List Nat := [1, 2, 1, 2, 6, 2, 2, 2, 3]
def baseStart_88025 : Nat := 118140960795 + 88025 * 2 ^ 59
def prefixEnd_88025 : Nat := 4983230072969 + 3 ^ 40 * 88025 * 2
def baseEnd_88025 : Nat := 20088504272054815770083

theorem tailTrace_88025 : CollatzResearch.WordTrace tailWord_88025 prefixEnd_88025 20088504272054815770083 := by
  unfold tailWord_88025
  simp only [CollatzResearch.WordTrace]
  refine ⟨3210535506107933318233529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2140357004071955545489019 3210535506107933318233529)
  ·
    refine ⟨2407901629580949988675147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3210535506107933318233529 2407901629580949988675147)
    ·
      refine ⟨3611852444371424983012721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2407901629580949988675147 3611852444371424983012721)
      ·
        refine ⟨2708889333278568737259541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3611852444371424983012721 2708889333278568737259541)
        ·
          refine ⟨126979187497432909559041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 2708889333278568737259541 126979187497432909559041)
          ·
            refine ⟨95234390623074682169281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126979187497432909559041 95234390623074682169281)
            ·
              refine ⟨71425792967306011626961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95234390623074682169281 71425792967306011626961)
              ·
                refine ⟨53569344725479508720221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71425792967306011626961 53569344725479508720221)
                ·
                  refine ⟨20088504272054815770083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53569344725479508720221 20088504272054815770083)
                  ·
                    rfl

theorem cell21_88025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 2, 2, 3].length) (baseStart_88025 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_88025 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_88025 prefixEnd_88025 := by exact prefixLift 88025
  have htrace : WordTrace (prefixWord ++ tailWord_88025) baseStart_88025 baseEnd_88025 := by
    simpa [prefixWord, tailWord_88025, baseEnd_88025] using wordTrace_append hprefix tailTrace_88025
  have hstable : (prefixWord ++ tailWord_88025).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88025).length < 2 ^ (prefixWord ++ tailWord_88025).sum := by decide
  have hdescent : baseEnd_88025 < baseStart_88025 := by decide
  rcases family_descends (prefixWord ++ tailWord_88025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88098 : List Nat := [3, 3, 1, 1, 1, 2, 5, 1, 4]
def baseStart_88098 : Nat := 118140960795 + 88098 * 2 ^ 59
def prefixEnd_88098 : Nat := 4983230072969 + 3 ^ 40 * 88098 * 2
def baseEnd_88098 : Nat := 20105163866622911053267

theorem tailTrace_88098 : CollatzResearch.WordTrace tailWord_88098 prefixEnd_88098 20105163866622911053267 := by
  unfold tailWord_88098
  simp only [CollatzResearch.WordTrace]
  refine ⟨803299508710866696410237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2142132023228977857093965 803299508710866696410237)
  ·
    refine ⟨301237315766575011153839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 803299508710866696410237 301237315766575011153839)
    ·
      refine ⟨451855973649862516730759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 301237315766575011153839 451855973649862516730759)
      ·
        refine ⟨677783960474793775096139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 451855973649862516730759 677783960474793775096139)
        ·
          refine ⟨1016675940712190662644209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 677783960474793775096139 1016675940712190662644209)
          ·
            refine ⟨762506955534142996983157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1016675940712190662644209 762506955534142996983157)
            ·
              refine ⟨71485027081325905967171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 762506955534142996983157 71485027081325905967171)
              ·
                refine ⟨107227540621988858950757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71485027081325905967171 107227540621988858950757)
                ·
                  refine ⟨20105163866622911053267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 107227540621988858950757 20105163866622911053267)
                  ·
                    rfl

theorem cell21_88098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 5, 1, 4].length) (baseStart_88098 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_88098 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_88098 prefixEnd_88098 := by exact prefixLift 88098
  have htrace : WordTrace (prefixWord ++ tailWord_88098) baseStart_88098 baseEnd_88098 := by
    simpa [prefixWord, tailWord_88098, baseEnd_88098] using wordTrace_append hprefix tailTrace_88098
  have hstable : (prefixWord ++ tailWord_88098).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88098).length < 2 ^ (prefixWord ++ tailWord_88098).sum := by decide
  have hdescent : baseEnd_88098 < baseStart_88098 := by decide
  rcases family_descends (prefixWord ++ tailWord_88098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88112 : List Nat := [2, 1, 1, 1, 2, 7, 2, 5]
def baseStart_88112 : Nat := 118140960795 + 88112 * 2 ^ 59
def prefixEnd_88112 : Nat := 4983230072969 + 3 ^ 40 * 88112 * 2
def baseEnd_88112 : Nat := 6702786285787332606635

theorem tailTrace_88112 : CollatzResearch.WordTrace tailWord_88112 prefixEnd_88112 6702786285787332606635 := by
  unfold tailWord_88112
  simp only [CollatzResearch.WordTrace]
  refine ⟨1606854328396373588325295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2142472437861831451100393 1606854328396373588325295)
  ·
    refine ⟨2410281492594560382487943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1606854328396373588325295 2410281492594560382487943)
    ·
      refine ⟨3615422238891840573731915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2410281492594560382487943 3615422238891840573731915)
      ·
        refine ⟨5423133358337760860597873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3615422238891840573731915 5423133358337760860597873)
        ·
          refine ⟨4067350018753320645448405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5423133358337760860597873 4067350018753320645448405)
          ·
            refine ⟨95328516064530952627697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 4067350018753320645448405 95328516064530952627697)
            ·
              refine ⟨71496387048398214470773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95328516064530952627697 71496387048398214470773)
              ·
                refine ⟨6702786285787332606635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 71496387048398214470773 6702786285787332606635)
                ·
                  rfl

theorem cell21_88112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 2, 5].length) (baseStart_88112 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_88112 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_88112 prefixEnd_88112 := by exact prefixLift 88112
  have htrace : WordTrace (prefixWord ++ tailWord_88112) baseStart_88112 baseEnd_88112 := by
    simpa [prefixWord, tailWord_88112, baseEnd_88112] using wordTrace_append hprefix tailTrace_88112
  have hstable : (prefixWord ++ tailWord_88112).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88112).length < 2 ^ (prefixWord ++ tailWord_88112).sum := by decide
  have hdescent : baseEnd_88112 < baseStart_88112 := by decide
  rcases family_descends (prefixWord ++ tailWord_88112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88140 : List Nat := [2, 2, 1, 3, 1, 1, 4, 1, 6]
def baseStart_88140 : Nat := 118140960795 + 88140 * 2 ^ 59
def prefixEnd_88140 : Nat := 4983230072969 + 3 ^ 40 * 88140 * 2
def baseEnd_88140 : Nat := 20114748838840171353181

theorem tailTrace_88140 : CollatzResearch.WordTrace tailWord_88140 prefixEnd_88140 20114748838840171353181 := by
  unfold tailWord_88140
  simp only [CollatzResearch.WordTrace]
  refine ⟨1607364950345653979334937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2143153267127538639113249 1607364950345653979334937)
  ·
    refine ⟨1205523712759240484501203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1607364950345653979334937 1205523712759240484501203)
    ·
      refine ⟨1808285569138860726751805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1205523712759240484501203 1808285569138860726751805)
      ·
        refine ⟨678107088427072772531927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1808285569138860726751805 678107088427072772531927)
        ·
          refine ⟨1017160632640609158797891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 678107088427072772531927 1017160632640609158797891)
          ·
            refine ⟨1525740948960913738196837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1017160632640609158797891 1525740948960913738196837)
            ·
              refine ⟨286076427930171325911907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1525740948960913738196837 286076427930171325911907)
              ·
                refine ⟨429114641895256988867861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 286076427930171325911907 429114641895256988867861)
                ·
                  refine ⟨20114748838840171353181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 429114641895256988867861 20114748838840171353181)
                  ·
                    rfl

theorem cell21_88140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 1, 6].length) (baseStart_88140 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_88140 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_88140 prefixEnd_88140 := by exact prefixLift 88140
  have htrace : WordTrace (prefixWord ++ tailWord_88140) baseStart_88140 baseEnd_88140 := by
    simpa [prefixWord, tailWord_88140, baseEnd_88140] using wordTrace_append hprefix tailTrace_88140
  have hstable : (prefixWord ++ tailWord_88140).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88140).length < 2 ^ (prefixWord ++ tailWord_88140).sum := by decide
  have hdescent : baseEnd_88140 < baseStart_88140 := by decide
  rcases family_descends (prefixWord ++ tailWord_88140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88261 : List Nat := [1, 3, 1, 1, 1, 1, 5, 3, 5]
def baseStart_88261 : Nat := 118140960795 + 88261 * 2 ^ 59
def prefixEnd_88261 : Nat := 4983230072969 + 3 ^ 40 * 88261 * 2
def baseEnd_88261 : Nat := 20142362687370849836267

theorem tailTrace_88261 : CollatzResearch.WordTrace tailWord_88261 prefixEnd_88261 20142362687370849836267 := by
  unfold tailWord_88261
  simp only [CollatzResearch.WordTrace]
  refine ⟨3219143133252945623824637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2146095422168630415883091 3219143133252945623824637)
  ·
    refine ⟨1207178674969854608934239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3219143133252945623824637 1207178674969854608934239)
    ·
      refine ⟨1810768012454781913401359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1207178674969854608934239 1810768012454781913401359)
      ·
        refine ⟨2716152018682172870102039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1810768012454781913401359 2716152018682172870102039)
        ·
          refine ⟨4074228028023259305153059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2716152018682172870102039 4074228028023259305153059)
          ·
            refine ⟨6111342042034888957729589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4074228028023259305153059 6111342042034888957729589)
            ·
              refine ⟨572938316440770839787149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6111342042034888957729589 572938316440770839787149)
              ·
                refine ⟨214851868665289064920181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 572938316440770839787149 214851868665289064920181)
                ·
                  refine ⟨20142362687370849836267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 214851868665289064920181 20142362687370849836267)
                  ·
                    rfl

theorem cell21_88261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 3, 5].length) (baseStart_88261 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_88261 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_88261 prefixEnd_88261 := by exact prefixLift 88261
  have htrace : WordTrace (prefixWord ++ tailWord_88261) baseStart_88261 baseEnd_88261 := by
    simpa [prefixWord, tailWord_88261, baseEnd_88261] using wordTrace_append hprefix tailTrace_88261
  have hstable : (prefixWord ++ tailWord_88261).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88261).length < 2 ^ (prefixWord ++ tailWord_88261).sum := by decide
  have hdescent : baseEnd_88261 < baseStart_88261 := by decide
  rcases family_descends (prefixWord ++ tailWord_88261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88275 : List Nat := [1, 1, 1, 2, 1, 1, 1, 3, 10]
def baseStart_88275 : Nat := 118140960795 + 88275 * 2 ^ 59
def prefixEnd_88275 : Nat := 4983230072969 + 3 ^ 40 * 88275 * 2
def baseEnd_88275 : Nat := 20145557678109936602905

theorem tailTrace_88275 : CollatzResearch.WordTrace tailWord_88275 prefixEnd_88275 20145557678109936602905 := by
  unfold tailWord_88275
  simp only [CollatzResearch.WordTrace]
  refine ⟨3219653755202226014834279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2146435836801484009889519 3219653755202226014834279)
  ·
    refine ⟨4829480632803339022251419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3219653755202226014834279 4829480632803339022251419)
    ·
      refine ⟨7244220949205008533377129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4829480632803339022251419 7244220949205008533377129)
      ·
        refine ⟨5433165711903756400032847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7244220949205008533377129 5433165711903756400032847)
        ·
          refine ⟨8149748567855634600049271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5433165711903756400032847 8149748567855634600049271)
          ·
            refine ⟨12224622851783451900073907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8149748567855634600049271 12224622851783451900073907)
            ·
              refine ⟨18336934277675177850110861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12224622851783451900073907 18336934277675177850110861)
              ·
                refine ⟨6876350354128191693791573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18336934277675177850110861 6876350354128191693791573)
                ·
                  refine ⟨20145557678109936602905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 6876350354128191693791573 20145557678109936602905)
                  ·
                    rfl

theorem cell21_88275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 10].length) (baseStart_88275 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_88275 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_88275 prefixEnd_88275 := by exact prefixLift 88275
  have htrace : WordTrace (prefixWord ++ tailWord_88275) baseStart_88275 baseEnd_88275 := by
    simpa [prefixWord, tailWord_88275, baseEnd_88275] using wordTrace_append hprefix tailTrace_88275
  have hstable : (prefixWord ++ tailWord_88275).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88275).length < 2 ^ (prefixWord ++ tailWord_88275).sum := by decide
  have hdescent : baseEnd_88275 < baseStart_88275 := by decide
  rcases family_descends (prefixWord ++ tailWord_88275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88427 : List Nat := [1, 1, 1, 1, 2, 2, 2, 5, 6]
def baseStart_88427 : Nat := 118140960795 + 88427 * 2 ^ 59
def prefixEnd_88427 : Nat := 4983230072969 + 3 ^ 40 * 88427 * 2
def baseEnd_88427 : Nat := 20180246148991450069261

theorem tailTrace_88427 : CollatzResearch.WordTrace tailWord_88427 prefixEnd_88427 20180246148991450069261 := by
  unfold tailWord_88427
  simp only [CollatzResearch.WordTrace]
  refine ⟨3225197650651555974367535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2150131767101037316245023 3225197650651555974367535)
  ·
    refine ⟨4837796475977333961551303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3225197650651555974367535 4837796475977333961551303)
    ·
      refine ⟨7256694713966000942326955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4837796475977333961551303 7256694713966000942326955)
      ·
        refine ⟨10885042070949001413490433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7256694713966000942326955 10885042070949001413490433)
        ·
          refine ⟨8163781553211751060117825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10885042070949001413490433 8163781553211751060117825)
          ·
            refine ⟨6122836164908813295088369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8163781553211751060117825 6122836164908813295088369)
            ·
              refine ⟨4592127123681609971316277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6122836164908813295088369 4592127123681609971316277)
              ·
                refine ⟨430511917845150934810901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4592127123681609971316277 430511917845150934810901)
                ·
                  refine ⟨20180246148991450069261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 430511917845150934810901 20180246148991450069261)
                  ·
                    rfl

theorem cell21_88427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 5, 6].length) (baseStart_88427 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_88427 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_88427 prefixEnd_88427 := by exact prefixLift 88427
  have htrace : WordTrace (prefixWord ++ tailWord_88427) baseStart_88427 baseEnd_88427 := by
    simpa [prefixWord, tailWord_88427, baseEnd_88427] using wordTrace_append hprefix tailTrace_88427
  have hstable : (prefixWord ++ tailWord_88427).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88427).length < 2 ^ (prefixWord ++ tailWord_88427).sum := by decide
  have hdescent : baseEnd_88427 < baseStart_88427 := by decide
  rcases family_descends (prefixWord ++ tailWord_88427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88450 : List Nat := [3, 4, 2, 1, 2, 2, 2, 5]
def baseStart_88450 : Nat := 118140960795 + 88450 * 2 ^ 59
def prefixEnd_88450 : Nat := 4983230072969 + 3 ^ 40 * 88450 * 2
def baseEnd_88450 : Nat := 6728498354116173728627

theorem tailTrace_88450 : CollatzResearch.WordTrace tailWord_88450 prefixEnd_88450 6728498354116173728627 := by
  unfold tailWord_88450
  simp only [CollatzResearch.WordTrace]
  refine ⟨806509132392057725613701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2150691019712153934969869 806509132392057725613701)
  ·
    refine ⟨151220462323510823552569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 806509132392057725613701 151220462323510823552569)
    ·
      refine ⟨113415346742633117664427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151220462323510823552569 113415346742633117664427)
      ·
        refine ⟨170123020113949676496641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113415346742633117664427 170123020113949676496641)
        ·
          refine ⟨127592265085462257372481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170123020113949676496641 127592265085462257372481)
          ·
            refine ⟨95694198814096693029361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127592265085462257372481 95694198814096693029361)
            ·
              refine ⟨71770649110572519772021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 95694198814096693029361 71770649110572519772021)
              ·
                refine ⟨6728498354116173728627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 71770649110572519772021 6728498354116173728627)
                ·
                  rfl

theorem cell21_88450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 2, 5].length) (baseStart_88450 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_88450 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_88450 prefixEnd_88450 := by exact prefixLift 88450
  have htrace : WordTrace (prefixWord ++ tailWord_88450) baseStart_88450 baseEnd_88450 := by
    simpa [prefixWord, tailWord_88450, baseEnd_88450] using wordTrace_append hprefix tailTrace_88450
  have hstable : (prefixWord ++ tailWord_88450).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88450).length < 2 ^ (prefixWord ++ tailWord_88450).sum := by decide
  have hdescent : baseEnd_88450 < baseStart_88450 := by decide
  rcases family_descends (prefixWord ++ tailWord_88450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88481 : List Nat := [1, 2, 3, 5, 1, 1, 3, 2, 3]
def baseStart_88481 : Nat := 118140960795 + 88481 * 2 ^ 59
def prefixEnd_88481 : Nat := 4983230072969 + 3 ^ 40 * 88481 * 2
def baseEnd_88481 : Nat := 20192569684699356169151

theorem tailTrace_88481 : CollatzResearch.WordTrace tailWord_88481 prefixEnd_88481 20192569684699356169151 := by
  unfold tailWord_88481
  simp only [CollatzResearch.WordTrace]
  refine ⟨3227167192455923196833297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2151444794970615464555531 3227167192455923196833297)
  ·
    refine ⟨2420375394341942397624973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3227167192455923196833297 2420375394341942397624973)
    ·
      refine ⟨907640772878228399109365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2420375394341942397624973 907640772878228399109365)
      ·
        refine ⟨85091322457333912416503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 907640772878228399109365 85091322457333912416503)
        ·
          refine ⟨127636983686000868624755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85091322457333912416503 127636983686000868624755)
          ·
            refine ⟨191455475529001302937133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127636983686000868624755 191455475529001302937133)
            ·
              refine ⟨71795803323375488601425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 191455475529001302937133 71795803323375488601425)
              ·
                refine ⟨53846852492531616451069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71795803323375488601425 53846852492531616451069)
                ·
                  refine ⟨20192569684699356169151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53846852492531616451069 20192569684699356169151)
                  ·
                    rfl

theorem cell21_88481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 3, 2, 3].length) (baseStart_88481 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_88481 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_88481 prefixEnd_88481 := by exact prefixLift 88481
  have htrace : WordTrace (prefixWord ++ tailWord_88481) baseStart_88481 baseEnd_88481 := by
    simpa [prefixWord, tailWord_88481, baseEnd_88481] using wordTrace_append hprefix tailTrace_88481
  have hstable : (prefixWord ++ tailWord_88481).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88481).length < 2 ^ (prefixWord ++ tailWord_88481).sum := by decide
  have hdescent : baseEnd_88481 < baseStart_88481 := by decide
  rcases family_descends (prefixWord ++ tailWord_88481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88579 : List Nat := [1, 1, 1, 3, 2, 1, 4, 2, 6]
def baseStart_88579 : Nat := 118140960795 + 88579 * 2 ^ 59
def prefixEnd_88579 : Nat := 4983230072969 + 3 ^ 40 * 88579 * 2
def baseEnd_88579 : Nat := 20214934619872963535617

theorem tailTrace_88579 : CollatzResearch.WordTrace tailWord_88579 prefixEnd_88579 20214934619872963535617 := by
  unfold tailWord_88579
  simp only [CollatzResearch.WordTrace]
  refine ⟨3230741546100885933900791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2153827697400590622600527 3230741546100885933900791)
  ·
    refine ⟨4846112319151328900851187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3230741546100885933900791 4846112319151328900851187)
    ·
      refine ⟨7269168478726993351276781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4846112319151328900851187 7269168478726993351276781)
      ·
        refine ⟨2725938179522622506728793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7269168478726993351276781 2725938179522622506728793)
        ·
          refine ⟨2044453634641966880046595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2725938179522622506728793 2044453634641966880046595)
          ·
            refine ⟨3066680451962950320069893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2044453634641966880046595 3066680451962950320069893)
            ·
              refine ⟨575002584743053185013105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3066680451962950320069893 575002584743053185013105)
              ·
                refine ⟨431251938557289888759829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 575002584743053185013105 431251938557289888759829)
                ·
                  refine ⟨20214934619872963535617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 431251938557289888759829 20214934619872963535617)
                  ·
                    rfl

theorem cell21_88579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 2, 6].length) (baseStart_88579 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_88579 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_88579 prefixEnd_88579 := by exact prefixLift 88579
  have htrace : WordTrace (prefixWord ++ tailWord_88579) baseStart_88579 baseEnd_88579 := by
    simpa [prefixWord, tailWord_88579, baseEnd_88579] using wordTrace_append hprefix tailTrace_88579
  have hstable : (prefixWord ++ tailWord_88579).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88579).length < 2 ^ (prefixWord ++ tailWord_88579).sum := by decide
  have hdescent : baseEnd_88579 < baseStart_88579 := by decide
  rcases family_descends (prefixWord ++ tailWord_88579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88599 : List Nat := [1, 1, 3, 6, 1, 1, 2, 1, 5]
def baseStart_88599 : Nat := 118140960795 + 88599 * 2 ^ 59
def prefixEnd_88599 : Nat := 4983230072969 + 3 ^ 40 * 88599 * 2
def baseEnd_88599 : Nat := 20219498892357373202243

theorem tailTrace_88599 : CollatzResearch.WordTrace tailWord_88599 prefixEnd_88599 20219498892357373202243 := by
  unfold tailWord_88599
  simp only [CollatzResearch.WordTrace]
  refine ⟨3231471006028429349628851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2154314004018952899752567 3231471006028429349628851)
  ·
    refine ⟨4847206509042644024443277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3231471006028429349628851 4847206509042644024443277)
    ·
      refine ⟨1817702440890991509166229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4847206509042644024443277 1817702440890991509166229)
      ·
        refine ⟨85204801916765226992167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 1817702440890991509166229 85204801916765226992167)
        ·
          refine ⟨127807202875147840488251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85204801916765226992167 127807202875147840488251)
          ·
            refine ⟨191710804312721760732377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127807202875147840488251 191710804312721760732377)
            ·
              refine ⟨143783103234541320549283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 191710804312721760732377 143783103234541320549283)
              ·
                refine ⟨215674654851811980823925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 143783103234541320549283 215674654851811980823925)
                ·
                  refine ⟨20219498892357373202243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 215674654851811980823925 20219498892357373202243)
                  ·
                    rfl

theorem cell21_88599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 2, 1, 5].length) (baseStart_88599 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_88599 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_88599 prefixEnd_88599 := by exact prefixLift 88599
  have htrace : WordTrace (prefixWord ++ tailWord_88599) baseStart_88599 baseEnd_88599 := by
    simpa [prefixWord, tailWord_88599, baseEnd_88599] using wordTrace_append hprefix tailTrace_88599
  have hstable : (prefixWord ++ tailWord_88599).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88599).length < 2 ^ (prefixWord ++ tailWord_88599).sum := by decide
  have hdescent : baseEnd_88599 < baseStart_88599 := by decide
  rcases family_descends (prefixWord ++ tailWord_88599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88610 : List Nat := [3, 3, 1, 1, 1, 1, 1, 10]
def baseStart_88610 : Nat := 118140960795 + 88610 * 2 ^ 59
def prefixEnd_88610 : Nat := 4983230072969 + 3 ^ 40 * 88610 * 2
def baseEnd_88610 : Nat := 6740669747407932839629

theorem tailTrace_88610 : CollatzResearch.WordTrace tailWord_88610 prefixEnd_88610 6740669747407932839629 := by
  unfold tailWord_88610
  simp only [CollatzResearch.WordTrace]
  refine ⟨807968052247144557069821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2154581472659052152186189 807968052247144557069821)
  ·
    refine ⟨302988019592679208901183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 807968052247144557069821 302988019592679208901183)
    ·
      refine ⟨454482029389018813351775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 302988019592679208901183 454482029389018813351775)
      ·
        refine ⟨681723044083528220027663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 454482029389018813351775 681723044083528220027663)
        ·
          refine ⟨1022584566125292330041495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 681723044083528220027663 1022584566125292330041495)
          ·
            refine ⟨1533876849187938495062243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1022584566125292330041495 1533876849187938495062243)
            ·
              refine ⟨2300815273781907742593365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1533876849187938495062243 2300815273781907742593365)
              ·
                refine ⟨6740669747407932839629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 2300815273781907742593365 6740669747407932839629)
                ·
                  rfl

theorem cell21_88610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 10].length) (baseStart_88610 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_88610 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_88610 prefixEnd_88610 := by exact prefixLift 88610
  have htrace : WordTrace (prefixWord ++ tailWord_88610) baseStart_88610 baseEnd_88610 := by
    simpa [prefixWord, tailWord_88610, baseEnd_88610] using wordTrace_append hprefix tailTrace_88610
  have hstable : (prefixWord ++ tailWord_88610).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88610).length < 2 ^ (prefixWord ++ tailWord_88610).sum := by decide
  have hdescent : baseEnd_88610 < baseStart_88610 := by decide
  rcases family_descends (prefixWord ++ tailWord_88610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88655 : List Nat := [1, 1, 2, 1, 1, 2, 6, 1, 6]
def baseStart_88655 : Nat := 118140960795 + 88655 * 2 ^ 59
def prefixEnd_88655 : Nat := 4983230072969 + 3 ^ 40 * 88655 * 2
def baseEnd_88655 : Nat := 20232278855313720268795

theorem tailTrace_88655 : CollatzResearch.WordTrace tailWord_88655 prefixEnd_88655 20232278855313720268795 := by
  unfold tailWord_88655
  simp only [CollatzResearch.WordTrace]
  refine ⟨3233513493825550913667419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2155675662550367275778279 3233513493825550913667419)
  ·
    refine ⟨4850270240738326370501129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3233513493825550913667419 4850270240738326370501129)
    ·
      refine ⟨3637702680553744777875847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4850270240738326370501129 3637702680553744777875847)
      ·
        refine ⟨5456554020830617166813771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3637702680553744777875847 5456554020830617166813771)
        ·
          refine ⟨8184831031245925750220657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5456554020830617166813771 8184831031245925750220657)
          ·
            refine ⟨6138623273434444312665493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8184831031245925750220657 6138623273434444312665493)
            ·
              refine ⟨287747965942239577156195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 6138623273434444312665493 287747965942239577156195)
              ·
                refine ⟨431621948913359365734293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 287747965942239577156195 431621948913359365734293)
                ·
                  refine ⟨20232278855313720268795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 431621948913359365734293 20232278855313720268795)
                  ·
                    rfl

theorem cell21_88655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 1, 6].length) (baseStart_88655 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_88655 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_88655 prefixEnd_88655 := by exact prefixLift 88655
  have htrace : WordTrace (prefixWord ++ tailWord_88655) baseStart_88655 baseEnd_88655 := by
    simpa [prefixWord, tailWord_88655, baseEnd_88655] using wordTrace_append hprefix tailTrace_88655
  have hstable : (prefixWord ++ tailWord_88655).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88655).length < 2 ^ (prefixWord ++ tailWord_88655).sum := by decide
  have hdescent : baseEnd_88655 < baseStart_88655 := by decide
  rcases family_descends (prefixWord ++ tailWord_88655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88734 : List Nat := [4, 3, 1, 1, 1, 1, 3, 2, 5]
def baseStart_88734 : Nat := 118140960795 + 88734 * 2 ^ 59
def prefixEnd_88734 : Nat := 4983230072969 + 3 ^ 40 * 88734 * 2
def baseEnd_88734 : Nat := 20250307731627138451967

theorem tailTrace_88734 : CollatzResearch.WordTrace tailWord_88734 prefixEnd_88734 20250307731627138451967 := by
  unfold tailWord_88734
  simp only [CollatzResearch.WordTrace]
  refine ⟨404549357567418425724157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2157596573692898270528837 404549357567418425724157)
  ·
    refine ⟨151706009087781909646559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 404549357567418425724157 151706009087781909646559)
    ·
      refine ⟨227559013631672864469839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151706009087781909646559 227559013631672864469839)
      ·
        refine ⟨341338520447509296704759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227559013631672864469839 341338520447509296704759)
        ·
          refine ⟨512007780671263945057139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 341338520447509296704759 512007780671263945057139)
          ·
            refine ⟨768011671006895917585709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 512007780671263945057139 768011671006895917585709)
            ·
              refine ⟨288004376627585969094641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 768011671006895917585709 288004376627585969094641)
              ·
                refine ⟨216003282470689476820981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 288004376627585969094641 216003282470689476820981)
                ·
                  refine ⟨20250307731627138451967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 216003282470689476820981 20250307731627138451967)
                  ·
                    rfl

theorem cell21_88734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_88734 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_88734 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_88734 prefixEnd_88734 := by exact prefixLift 88734
  have htrace : WordTrace (prefixWord ++ tailWord_88734) baseStart_88734 baseEnd_88734 := by
    simpa [prefixWord, tailWord_88734, baseEnd_88734] using wordTrace_append hprefix tailTrace_88734
  have hstable : (prefixWord ++ tailWord_88734).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88734).length < 2 ^ (prefixWord ++ tailWord_88734).sum := by decide
  have hdescent : baseEnd_88734 < baseStart_88734 := by decide
  rcases family_descends (prefixWord ++ tailWord_88734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88765 : List Nat := [1, 4, 1, 2, 1, 5, 1, 2, 4]
def baseStart_88765 : Nat := 118140960795 + 88765 * 2 ^ 59
def prefixEnd_88765 : Nat := 4983230072969 + 3 ^ 40 * 88765 * 2
def baseEnd_88765 : Nat := 20257382353977973435237

theorem tailTrace_88765 : CollatzResearch.WordTrace tailWord_88765 prefixEnd_88765 20257382353977973435237 := by
  unfold tailWord_88765
  simp only [CollatzResearch.WordTrace]
  refine ⟨3237525523427039700171749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2158350348951359800114499 3237525523427039700171749)
  ·
    refine ⟨607036035642569943782203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3237525523427039700171749 607036035642569943782203)
    ·
      refine ⟨910554053463854915673305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 607036035642569943782203 910554053463854915673305)
      ·
        refine ⟨682915540097891186754979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 910554053463854915673305 682915540097891186754979)
        ·
          refine ⟨1024373310146836780132469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 682915540097891186754979 1024373310146836780132469)
          ·
            refine ⟨96034997826265948137419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1024373310146836780132469 96034997826265948137419)
            ·
              refine ⟨144052496739398922206129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96034997826265948137419 144052496739398922206129)
              ·
                refine ⟨108039372554549191654597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 144052496739398922206129 108039372554549191654597)
                ·
                  refine ⟨20257382353977973435237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 108039372554549191654597 20257382353977973435237)
                  ·
                    rfl

theorem cell21_88765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 1, 2, 4].length) (baseStart_88765 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_88765 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_88765 prefixEnd_88765 := by exact prefixLift 88765
  have htrace : WordTrace (prefixWord ++ tailWord_88765) baseStart_88765 baseEnd_88765 := by
    simpa [prefixWord, tailWord_88765, baseEnd_88765] using wordTrace_append hprefix tailTrace_88765
  have hstable : (prefixWord ++ tailWord_88765).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88765).length < 2 ^ (prefixWord ++ tailWord_88765).sum := by decide
  have hdescent : baseEnd_88765 < baseStart_88765 := by decide
  rcases family_descends (prefixWord ++ tailWord_88765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88796 : List Nat := [2, 2, 5, 1, 1, 1, 4, 5]
def baseStart_88796 : Nat := 118140960795 + 88796 * 2 ^ 59
def prefixEnd_88796 : Nat := 4983230072969 + 3 ^ 40 * 88796 * 2
def baseEnd_88796 : Nat := 6754818992109602806169

theorem tailTrace_88796 : CollatzResearch.WordTrace tailWord_88796 prefixEnd_88796 6754818992109602806169 := by
  unfold tailWord_88796
  simp only [CollatzResearch.WordTrace]
  refine ⟨1619328093157365997275121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2159104124209821329700161 1619328093157365997275121)
  ·
    refine ⟨1214496069868024497956341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1619328093157365997275121 1214496069868024497956341)
    ·
      refine ⟨113859006550127296683407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1214496069868024497956341 113859006550127296683407)
      ·
        refine ⟨170788509825190945025111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113859006550127296683407 170788509825190945025111)
        ·
          refine ⟨256182764737786417537667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170788509825190945025111 256182764737786417537667)
          ·
            refine ⟨384274147106679626306501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 256182764737786417537667 384274147106679626306501)
            ·
              refine ⟨72051402582502429932469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 384274147106679626306501 72051402582502429932469)
              ·
                refine ⟨6754818992109602806169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 72051402582502429932469 6754818992109602806169)
                ·
                  rfl

theorem cell21_88796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 4, 5].length) (baseStart_88796 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_88796 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_88796 prefixEnd_88796 := by exact prefixLift 88796
  have htrace : WordTrace (prefixWord ++ tailWord_88796) baseStart_88796 baseEnd_88796 := by
    simpa [prefixWord, tailWord_88796, baseEnd_88796] using wordTrace_append hprefix tailTrace_88796
  have hstable : (prefixWord ++ tailWord_88796).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88796).length < 2 ^ (prefixWord ++ tailWord_88796).sum := by decide
  have hdescent : baseEnd_88796 < baseStart_88796 := by decide
  rcases family_descends (prefixWord ++ tailWord_88796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88928 : List Nat := [2, 1, 1, 3, 3, 1, 1, 2, 7]
def baseStart_88928 : Nat := 118140960795 + 88928 * 2 ^ 59
def prefixEnd_88928 : Nat := 4983230072969 + 3 ^ 40 * 88928 * 2
def baseEnd_88928 : Nat := 20294581174725912218237

theorem tailTrace_88928 : CollatzResearch.WordTrace tailWord_88928 prefixEnd_88928 20294581174725912218237 := by
  unfold tailWord_88928
  simp only [CollatzResearch.WordTrace]
  refine ⟨1621735310918259269177719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2162313747891012358903625 1621735310918259269177719)
  ·
    refine ⟨2432602966377388903766579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1621735310918259269177719 2432602966377388903766579)
    ·
      refine ⟨3648904449566083355649869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2432602966377388903766579 3648904449566083355649869)
      ·
        refine ⟨1368339168587281258368701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3648904449566083355649869 1368339168587281258368701)
        ·
          refine ⟨513127188220230471888263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1368339168587281258368701 513127188220230471888263)
          ·
            refine ⟨769690782330345707832395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 513127188220230471888263 769690782330345707832395)
            ·
              refine ⟨1154536173495518561748593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 769690782330345707832395 1154536173495518561748593)
              ·
                refine ⟨865902130121638921311445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1154536173495518561748593 865902130121638921311445)
                ·
                  refine ⟨20294581174725912218237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 865902130121638921311445 20294581174725912218237)
                  ·
                    rfl

theorem cell21_88928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 2, 7].length) (baseStart_88928 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_88928 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_88928 prefixEnd_88928 := by exact prefixLift 88928
  have htrace : WordTrace (prefixWord ++ tailWord_88928) baseStart_88928 baseEnd_88928 := by
    simpa [prefixWord, tailWord_88928, baseEnd_88928] using wordTrace_append hprefix tailTrace_88928
  have hstable : (prefixWord ++ tailWord_88928).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88928).length < 2 ^ (prefixWord ++ tailWord_88928).sum := by decide
  have hdescent : baseEnd_88928 < baseStart_88928 := by decide
  rcases family_descends (prefixWord ++ tailWord_88928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88945 : List Nat := [1, 2, 2, 2, 1, 5, 2, 1, 5]
def baseStart_88945 : Nat := 118140960795 + 88945 * 2 ^ 59
def prefixEnd_88945 : Nat := 4983230072969 + 3 ^ 40 * 88945 * 2
def baseEnd_88945 : Nat := 20298460806337660434869

theorem tailTrace_88945 : CollatzResearch.WordTrace tailWord_88945 prefixEnd_88945 20298460806337660434869 := by
  unfold tailWord_88945
  simp only [CollatzResearch.WordTrace]
  refine ⟨3244090662774930441724289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2162727108516620294482859 3244090662774930441724289)
  ·
    refine ⟨2433067997081197831293217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3244090662774930441724289 2433067997081197831293217)
    ·
      refine ⟨1824800997810898373469913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2433067997081197831293217 1824800997810898373469913)
      ·
        refine ⟨1368600748358173780102435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1824800997810898373469913 1368600748358173780102435)
        ·
          refine ⟨2052901122537260670153653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1368600748358173780102435 2052901122537260670153653)
          ·
            refine ⟨192459480237868187826905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2052901122537260670153653 192459480237868187826905)
            ·
              refine ⟨144344610178401140870179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 192459480237868187826905 144344610178401140870179)
              ·
                refine ⟨216516915267601711305269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 144344610178401140870179 216516915267601711305269)
                ·
                  refine ⟨20298460806337660434869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 216516915267601711305269 20298460806337660434869)
                  ·
                    rfl

theorem cell21_88945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 2, 1, 5].length) (baseStart_88945 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_88945 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_88945 prefixEnd_88945 := by exact prefixLift 88945
  have htrace : WordTrace (prefixWord ++ tailWord_88945) baseStart_88945 baseEnd_88945 := by
    simpa [prefixWord, tailWord_88945, baseEnd_88945] using wordTrace_append hprefix tailTrace_88945
  have hstable : (prefixWord ++ tailWord_88945).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88945).length < 2 ^ (prefixWord ++ tailWord_88945).sum := by decide
  have hdescent : baseEnd_88945 < baseStart_88945 := by decide
  rcases family_descends (prefixWord ++ tailWord_88945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_88959 : List Nat := [1, 1, 2, 2, 1, 1, 4, 5, 4]
def baseStart_88959 : Nat := 118140960795 + 88959 * 2 ^ 59
def prefixEnd_88959 : Nat := 4983230072969 + 3 ^ 40 * 88959 * 2
def baseEnd_88959 : Nat := 20301655797076747201507

theorem tailTrace_88959 : CollatzResearch.WordTrace tailWord_88959 prefixEnd_88959 20301655797076747201507 := by
  unfold tailWord_88959
  simp only [CollatzResearch.WordTrace]
  refine ⟨3244601284724210832733931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2163067523149473888489287 3244601284724210832733931)
  ·
    refine ⟨4866901927086316249100897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3244601284724210832733931 4866901927086316249100897)
    ·
      refine ⟨3650176445314737186825673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4866901927086316249100897 3650176445314737186825673)
      ·
        refine ⟨2737632333986052890119255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3650176445314737186825673 2737632333986052890119255)
        ·
          refine ⟨4106448500979079335178883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2737632333986052890119255 4106448500979079335178883)
          ·
            refine ⟨6159672751468619002768325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4106448500979079335178883 6159672751468619002768325)
            ·
              refine ⟨1154938640900366063019061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6159672751468619002768325 1154938640900366063019061)
              ·
                refine ⟨108275497584409318408037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1154938640900366063019061 108275497584409318408037)
                ·
                  refine ⟨20301655797076747201507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 108275497584409318408037 20301655797076747201507)
                  ·
                    rfl

theorem cell21_88959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 5, 4].length) (baseStart_88959 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_88959 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_88959 prefixEnd_88959 := by exact prefixLift 88959
  have htrace : WordTrace (prefixWord ++ tailWord_88959) baseStart_88959 baseEnd_88959 := by
    simpa [prefixWord, tailWord_88959, baseEnd_88959] using wordTrace_append hprefix tailTrace_88959
  have hstable : (prefixWord ++ tailWord_88959).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_88959).length < 2 ^ (prefixWord ++ tailWord_88959).sum := by decide
  have hdescent : baseEnd_88959 < baseStart_88959 := by decide
  rcases family_descends (prefixWord ++ tailWord_88959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89049 : List Nat := [1, 2, 1, 2, 5, 10]
def baseStart_89049 : Nat := 118140960795 + 89049 * 2 ^ 59
def prefixEnd_89049 : Nat := 4983230072969 + 3 ^ 40 * 89049 * 2
def baseEnd_89049 : Nat := 752673889750244100049

theorem tailTrace_89049 : CollatzResearch.WordTrace tailWord_89049 prefixEnd_89049 752673889750244100049 := by
  unfold tailWord_89049
  simp only [CollatzResearch.WordTrace]
  refine ⟨3247883854398156203510201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2165255902932104135673467 3247883854398156203510201)
  ·
    refine ⟨2435912890798617152632651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3247883854398156203510201 2435912890798617152632651)
    ·
      refine ⟨3653869336197925728948977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2435912890798617152632651 3653869336197925728948977)
      ·
        refine ⟨2740402002148444296711733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3653869336197925728948977 2740402002148444296711733)
        ·
          refine ⟨256912687701416652816725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2740402002148444296711733 256912687701416652816725)
          ·
            refine ⟨752673889750244100049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 256912687701416652816725 752673889750244100049)
            ·
              rfl

theorem cell21_89049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 10].length) (baseStart_89049 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_89049 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_89049 prefixEnd_89049 := by exact prefixLift 89049
  have htrace : WordTrace (prefixWord ++ tailWord_89049) baseStart_89049 baseEnd_89049 := by
    simpa [prefixWord, tailWord_89049, baseEnd_89049] using wordTrace_append hprefix tailTrace_89049
  have hstable : (prefixWord ++ tailWord_89049).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89049).length < 2 ^ (prefixWord ++ tailWord_89049).sum := by decide
  have hdescent : baseEnd_89049 < baseStart_89049 := by decide
  rcases family_descends (prefixWord ++ tailWord_89049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89066 : List Nat := [3, 1, 3, 1, 2, 2, 3, 6]
def baseStart_89066 : Nat := 118140960795 + 89066 * 2 ^ 59
def prefixEnd_89066 : Nat := 4983230072969 + 3 ^ 40 * 89066 * 2
def baseEnd_89066 : Nat := 6775358218289446305985

theorem tailTrace_89066 : CollatzResearch.WordTrace tailWord_89066 prefixEnd_89066 6775358218289446305985 := by
  unfold tailWord_89066
  simp only [CollatzResearch.WordTrace]
  refine ⟨812125973834142026719763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2165669263557712071252701 812125973834142026719763)
  ·
    refine ⟨1218188960751213040079645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 812125973834142026719763 1218188960751213040079645)
    ·
      refine ⟨456820860281704890029867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1218188960751213040079645 456820860281704890029867)
      ·
        refine ⟨685231290422557335044801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 456820860281704890029867 685231290422557335044801)
        ·
          refine ⟨513923467816918001283601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 685231290422557335044801 513923467816918001283601)
          ·
            refine ⟨385442600862688500962701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 513923467816918001283601 385442600862688500962701)
            ·
              refine ⟨144540975323508187861013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 385442600862688500962701 144540975323508187861013)
              ·
                refine ⟨6775358218289446305985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 144540975323508187861013 6775358218289446305985)
                ·
                  rfl

theorem cell21_89066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 3, 6].length) (baseStart_89066 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_89066 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_89066 prefixEnd_89066 := by exact prefixLift 89066
  have htrace : WordTrace (prefixWord ++ tailWord_89066) baseStart_89066 baseEnd_89066 := by
    simpa [prefixWord, tailWord_89066, baseEnd_89066] using wordTrace_append hprefix tailTrace_89066
  have hstable : (prefixWord ++ tailWord_89066).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89066).length < 2 ^ (prefixWord ++ tailWord_89066).sum := by decide
  have hdescent : baseEnd_89066 < baseStart_89066 := by decide
  rcases family_descends (prefixWord ++ tailWord_89066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89125 : List Nat := [1, 3, 1, 2, 2, 2, 2, 8]
def baseStart_89125 : Nat := 118140960795 + 89125 * 2 ^ 59
def prefixEnd_89125 : Nat := 4983230072969 + 3 ^ 40 * 89125 * 2
def baseEnd_89125 : Nat := 6779846419565782478167

theorem tailTrace_89125 : CollatzResearch.WordTrace tailWord_89125 prefixEnd_89125 6779846419565782478167 := by
  unfold tailWord_89125
  simp only [CollatzResearch.WordTrace]
  refine ⟨3250655802122821183276829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2167103868081880788851219 3250655802122821183276829)
  ·
    refine ⟨1218995925796057943728811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3250655802122821183276829 1218995925796057943728811)
    ·
      refine ⟨1828493888694086915593217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1218995925796057943728811 1828493888694086915593217)
      ·
        refine ⟨1371370416520565186694913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1828493888694086915593217 1371370416520565186694913)
        ·
          refine ⟨1028527812390423890021185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1371370416520565186694913 1028527812390423890021185)
          ·
            refine ⟨771395859292817917515889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1028527812390423890021185 771395859292817917515889)
            ·
              refine ⟨578546894469613438136917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 771395859292817917515889 578546894469613438136917)
              ·
                refine ⟨6779846419565782478167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 578546894469613438136917 6779846419565782478167)
                ·
                  rfl

theorem cell21_89125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 8].length) (baseStart_89125 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_89125 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_89125 prefixEnd_89125 := by exact prefixLift 89125
  have htrace : WordTrace (prefixWord ++ tailWord_89125) baseStart_89125 baseEnd_89125 := by
    simpa [prefixWord, tailWord_89125, baseEnd_89125] using wordTrace_append hprefix tailTrace_89125
  have hstable : (prefixWord ++ tailWord_89125).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89125).length < 2 ^ (prefixWord ++ tailWord_89125).sum := by decide
  have hdescent : baseEnd_89125 < baseStart_89125 := by decide
  rcases family_descends (prefixWord ++ tailWord_89125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89224 : List Nat := [2, 1, 3, 4, 2, 2, 2, 2, 3]
def baseStart_89224 : Nat := 118140960795 + 89224 * 2 ^ 59
def prefixEnd_89224 : Nat := 4983230072969 + 3 ^ 40 * 89224 * 2
def baseEnd_89224 : Nat := 20362132407495175284299

theorem tailTrace_89224 : CollatzResearch.WordTrace tailWord_89224 prefixEnd_89224 20362132407495175284299 := by
  unfold tailWord_89224
  simp only [CollatzResearch.WordTrace]
  refine ⟨1627133314382080545565363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2169511085842774060753817 1627133314382080545565363)
  ·
    refine ⟨2440699971573120818348045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1627133314382080545565363 2440699971573120818348045)
    ·
      refine ⟨915262489339920306880517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2440699971573120818348045 915262489339920306880517)
      ·
        refine ⟨171611716751235057540097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 915262489339920306880517 171611716751235057540097)
        ·
          refine ⟨128708787563426293155073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171611716751235057540097 128708787563426293155073)
          ·
            refine ⟨96531590672569719866305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128708787563426293155073 96531590672569719866305)
            ·
              refine ⟨72398693004427289899729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96531590672569719866305 72398693004427289899729)
              ·
                refine ⟨54299019753320467424797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72398693004427289899729 54299019753320467424797)
                ·
                  refine ⟨20362132407495175284299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54299019753320467424797 20362132407495175284299)
                  ·
                    rfl

theorem cell21_89224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 2, 2, 3].length) (baseStart_89224 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_89224 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_89224 prefixEnd_89224 := by exact prefixLift 89224
  have htrace : WordTrace (prefixWord ++ tailWord_89224) baseStart_89224 baseEnd_89224 := by
    simpa [prefixWord, tailWord_89224, baseEnd_89224] using wordTrace_append hprefix tailTrace_89224
  have hstable : (prefixWord ++ tailWord_89224).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89224).length < 2 ^ (prefixWord ++ tailWord_89224).sum := by decide
  have hdescent : baseEnd_89224 < baseStart_89224 := by decide
  rcases family_descends (prefixWord ++ tailWord_89224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89266 : List Nat := [3, 2, 1, 1, 1, 5, 2, 3, 3]
def baseStart_89266 : Nat := 118140960795 + 89266 * 2 ^ 59
def prefixEnd_89266 : Nat := 4983230072969 + 3 ^ 40 * 89266 * 2
def baseEnd_89266 : Nat := 20371717379712435584213

theorem tailTrace_89266 : CollatzResearch.WordTrace tailWord_89266 prefixEnd_89266 20371717379712435584213 := by
  unfold tailWord_89266
  simp only [CollatzResearch.WordTrace]
  refine ⟨813949623653000566039913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2170532329741334842773101 813949623653000566039913)
  ·
    refine ⟨610462217739750424529935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 813949623653000566039913 610462217739750424529935)
    ·
      refine ⟨915693326609625636794903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 610462217739750424529935 915693326609625636794903)
      ·
        refine ⟨1373539989914438455192355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 915693326609625636794903 1373539989914438455192355)
        ·
          refine ⟨2060309984871657682788533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1373539989914438455192355 2060309984871657682788533)
          ·
            refine ⟨193154061081717907761425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2060309984871657682788533 193154061081717907761425)
            ·
              refine ⟨144865545811288430821069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 193154061081717907761425 144865545811288430821069)
              ·
                refine ⟨54324579679233161557901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 144865545811288430821069 54324579679233161557901)
                ·
                  refine ⟨20371717379712435584213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54324579679233161557901 20371717379712435584213)
                  ·
                    rfl

theorem cell21_89266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 2, 3, 3].length) (baseStart_89266 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_89266 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_89266 prefixEnd_89266 := by exact prefixLift 89266
  have htrace : WordTrace (prefixWord ++ tailWord_89266) baseStart_89266 baseEnd_89266 := by
    simpa [prefixWord, tailWord_89266, baseEnd_89266] using wordTrace_append hprefix tailTrace_89266
  have hstable : (prefixWord ++ tailWord_89266).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89266).length < 2 ^ (prefixWord ++ tailWord_89266).sum := by decide
  have hdescent : baseEnd_89266 < baseStart_89266 := by decide
  rcases family_descends (prefixWord ++ tailWord_89266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89342 : List Nat := [4, 2, 2, 1, 1, 4, 1, 1, 5]
def baseStart_89342 : Nat := 118140960795 + 89342 * 2 ^ 59
def prefixEnd_89342 : Nat := 4983230072969 + 3 ^ 40 * 89342 * 2
def baseEnd_89342 : Nat := 20389061615153192317391

theorem tailTrace_89342 : CollatzResearch.WordTrace tailWord_89342 prefixEnd_89342 20389061615153192317391 := by
  unfold tailWord_89342
  simp only [CollatzResearch.WordTrace]
  refine ⟨407321305292083405490785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2172380294891111495950853 407321305292083405490785)
  ·
    refine ⟨305490978969062554118089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 407321305292083405490785 305490978969062554118089)
    ·
      refine ⟨229118234226796915588567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 305490978969062554118089 229118234226796915588567)
      ·
        refine ⟨343677351340195373382851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229118234226796915588567 343677351340195373382851)
        ·
          refine ⟨515516027010293060074277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 343677351340195373382851 515516027010293060074277)
          ·
            refine ⟨96659255064429948763927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 515516027010293060074277 96659255064429948763927)
            ·
              refine ⟨144988882596644923145891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96659255064429948763927 144988882596644923145891)
              ·
                refine ⟨217483323894967384718837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 144988882596644923145891 217483323894967384718837)
                ·
                  refine ⟨20389061615153192317391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 217483323894967384718837 20389061615153192317391)
                  ·
                    rfl

theorem cell21_89342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 1, 1, 5].length) (baseStart_89342 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_89342 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_89342 prefixEnd_89342 := by exact prefixLift 89342
  have htrace : WordTrace (prefixWord ++ tailWord_89342) baseStart_89342 baseEnd_89342 := by
    simpa [prefixWord, tailWord_89342, baseEnd_89342] using wordTrace_append hprefix tailTrace_89342
  have hstable : (prefixWord ++ tailWord_89342).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89342).length < 2 ^ (prefixWord ++ tailWord_89342).sum := by decide
  have hdescent : baseEnd_89342 < baseStart_89342 := by decide
  rcases family_descends (prefixWord ++ tailWord_89342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89353 : List Nat := [1, 2, 1, 1, 3, 3, 4, 6]
def baseStart_89353 : Nat := 118140960795 + 89353 * 2 ^ 59
def prefixEnd_89353 : Nat := 4983230072969 + 3 ^ 40 * 89353 * 2
def baseEnd_89353 : Nat := 6797190655006539211345

theorem tailTrace_89353 : CollatzResearch.WordTrace tailWord_89353 prefixEnd_89353 6797190655006539211345 := by
  unfold tailWord_89353
  simp only [CollatzResearch.WordTrace]
  refine ⟨3258971645296816122576713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2172647763531210748384475 3258971645296816122576713)
  ·
    refine ⟨2444228733972612091932535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3258971645296816122576713 2444228733972612091932535)
    ·
      refine ⟨3666343100958918137898803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2444228733972612091932535 3666343100958918137898803)
      ·
        refine ⟨5499514651438377206848205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3666343100958918137898803 5499514651438377206848205)
        ·
          refine ⟨2062317994289391452568077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5499514651438377206848205 2062317994289391452568077)
          ·
            refine ⟨773369247858521794713029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2062317994289391452568077 773369247858521794713029)
            ·
              refine ⟨145006733973472836508693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 773369247858521794713029 145006733973472836508693)
              ·
                refine ⟨6797190655006539211345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 145006733973472836508693 6797190655006539211345)
                ·
                  rfl

theorem cell21_89353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 4, 6].length) (baseStart_89353 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_89353 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_89353 prefixEnd_89353 := by exact prefixLift 89353
  have htrace : WordTrace (prefixWord ++ tailWord_89353) baseStart_89353 baseEnd_89353 := by
    simpa [prefixWord, tailWord_89353, baseEnd_89353] using wordTrace_append hprefix tailTrace_89353
  have hstable : (prefixWord ++ tailWord_89353).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89353).length < 2 ^ (prefixWord ++ tailWord_89353).sum := by decide
  have hdescent : baseEnd_89353 < baseStart_89353 := by decide
  rcases family_descends (prefixWord ++ tailWord_89353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89356 : List Nat := [2, 2, 1, 2, 2, 3, 4, 1, 4]
def baseStart_89356 : Nat := 118140960795 + 89356 * 2 ^ 59
def prefixEnd_89356 : Nat := 4983230072969 + 3 ^ 40 * 89356 * 2
def baseEnd_89356 : Nat := 20392256605892279084029

theorem tailTrace_89356 : CollatzResearch.WordTrace tailWord_89356 prefixEnd_89356 20392256605892279084029 := by
  unfold tailWord_89356
  simp only [CollatzResearch.WordTrace]
  refine ⟨1629540532142973817467961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2172720709523965089957281 1629540532142973817467961)
  ·
    refine ⟨1222155399107230363100971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1629540532142973817467961 1222155399107230363100971)
    ·
      refine ⟨1833233098660845544651457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1222155399107230363100971 1833233098660845544651457)
      ·
        refine ⟨1374924823995634158488593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1833233098660845544651457 1374924823995634158488593)
        ·
          refine ⟨1031193617996725618866445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1374924823995634158488593 1031193617996725618866445)
          ·
            refine ⟨386697606748772107074917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1031193617996725618866445 386697606748772107074917)
            ·
              refine ⟨72505801265394770076547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 386697606748772107074917 72505801265394770076547)
              ·
                refine ⟨108758701898092155114821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72505801265394770076547 108758701898092155114821)
                ·
                  refine ⟨20392256605892279084029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 108758701898092155114821 20392256605892279084029)
                  ·
                    rfl

theorem cell21_89356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 4, 1, 4].length) (baseStart_89356 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_89356 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_89356 prefixEnd_89356 := by exact prefixLift 89356
  have htrace : WordTrace (prefixWord ++ tailWord_89356) baseStart_89356 baseEnd_89356 := by
    simpa [prefixWord, tailWord_89356, baseEnd_89356] using wordTrace_append hprefix tailTrace_89356
  have hstable : (prefixWord ++ tailWord_89356).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89356).length < 2 ^ (prefixWord ++ tailWord_89356).sum := by decide
  have hdescent : baseEnd_89356 < baseStart_89356 := by decide
  rcases family_descends (prefixWord ++ tailWord_89356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89415 : List Nat := [1, 1, 4, 1, 2, 3, 2, 3, 4]
def baseStart_89415 : Nat := 118140960795 + 89415 * 2 ^ 59
def prefixEnd_89415 : Nat := 4983230072969 + 3 ^ 40 * 89415 * 2
def baseEnd_89415 : Nat := 20405721209721287600575

theorem tailTrace_89415 : CollatzResearch.WordTrace tailWord_89415 prefixEnd_89415 20405721209721287600575 := by
  unfold tailWord_89415
  simp only [CollatzResearch.WordTrace]
  refine ⟨3261232971072200711333699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2174155314048133807555799 3261232971072200711333699)
  ·
    refine ⟨4891849456608301067000549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3261232971072200711333699 4891849456608301067000549)
    ·
      refine ⟨917221773114056450062603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4891849456608301067000549 917221773114056450062603)
      ·
        refine ⟨1375832659671084675093905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 917221773114056450062603 1375832659671084675093905)
        ·
          refine ⟨1031874494753313506320429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1375832659671084675093905 1031874494753313506320429)
          ·
            refine ⟨386952935532492564870161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1031874494753313506320429 386952935532492564870161)
            ·
              refine ⟨290214701649369423652621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 386952935532492564870161 290214701649369423652621)
              ·
                refine ⟨108830513118513533869733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 290214701649369423652621 108830513118513533869733)
                ·
                  refine ⟨20405721209721287600575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 108830513118513533869733 20405721209721287600575)
                  ·
                    rfl

theorem cell21_89415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 3, 4].length) (baseStart_89415 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_89415 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_89415 prefixEnd_89415 := by exact prefixLift 89415
  have htrace : WordTrace (prefixWord ++ tailWord_89415) baseStart_89415 baseEnd_89415 := by
    simpa [prefixWord, tailWord_89415, baseEnd_89415] using wordTrace_append hprefix tailTrace_89415
  have hstable : (prefixWord ++ tailWord_89415).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89415).length < 2 ^ (prefixWord ++ tailWord_89415).sum := by decide
  have hdescent : baseEnd_89415 < baseStart_89415 := by decide
  rcases family_descends (prefixWord ++ tailWord_89415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89525 : List Nat := [1, 3, 3, 2, 2, 3, 2, 1, 4]
def baseStart_89525 : Nat := 118140960795 + 89525 * 2 ^ 59
def prefixEnd_89525 : Nat := 4983230072969 + 3 ^ 40 * 89525 * 2
def baseEnd_89525 : Nat := 20430824708385540767017

theorem tailTrace_89525 : CollatzResearch.WordTrace tailWord_89525 prefixEnd_89525 20430824708385540767017 := by
  unfold tailWord_89525
  simp only [CollatzResearch.WordTrace]
  refine ⟨3265245000673689497838029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2176830000449126331892019 3265245000673689497838029)
  ·
    refine ⟨1224466875252633561689261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3265245000673689497838029 1224466875252633561689261)
    ·
      refine ⟨459175078219737585633473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1224466875252633561689261 459175078219737585633473)
      ·
        refine ⟨344381308664803189225105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 459175078219737585633473 344381308664803189225105)
        ·
          refine ⟨258285981498602391918829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 344381308664803189225105 258285981498602391918829)
          ·
            refine ⟨96857243061975896969561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 258285981498602391918829 96857243061975896969561)
            ·
              refine ⟨72642932296481922727171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96857243061975896969561 72642932296481922727171)
              ·
                refine ⟨108964398444722884090757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72642932296481922727171 108964398444722884090757)
                ·
                  refine ⟨20430824708385540767017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 108964398444722884090757 20430824708385540767017)
                  ·
                    rfl

theorem cell21_89525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 2, 1, 4].length) (baseStart_89525 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_89525 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_89525 prefixEnd_89525 := by exact prefixLift 89525
  have htrace : WordTrace (prefixWord ++ tailWord_89525) baseStart_89525 baseEnd_89525 := by
    simpa [prefixWord, tailWord_89525, baseEnd_89525] using wordTrace_append hprefix tailTrace_89525
  have hstable : (prefixWord ++ tailWord_89525).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89525).length < 2 ^ (prefixWord ++ tailWord_89525).sum := by decide
  have hdescent : baseEnd_89525 < baseStart_89525 := by decide
  rcases family_descends (prefixWord ++ tailWord_89525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89550 : List Nat := [4, 1, 1, 1, 2, 1, 2, 1, 8]
def baseStart_89550 : Nat := 118140960795 + 89550 * 2 ^ 59
def prefixEnd_89550 : Nat := 4983230072969 + 3 ^ 40 * 89550 * 2
def baseEnd_89550 : Nat := 20436530048991052850299

theorem tailTrace_89550 : CollatzResearch.WordTrace tailWord_89550 prefixEnd_89550 20436530048991052850299 := by
  unfold tailWord_89550
  simp only [CollatzResearch.WordTrace]
  refine ⟨408269603197889845937263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2177437883722079178332069 408269603197889845937263)
  ·
    refine ⟨612404404796834768905895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 408269603197889845937263 612404404796834768905895)
    ·
      refine ⟨918606607195252153358843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 612404404796834768905895 918606607195252153358843)
      ·
        refine ⟨1377909910792878230038265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 918606607195252153358843 1377909910792878230038265)
        ·
          refine ⟨1033432433094658672528699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1377909910792878230038265 1033432433094658672528699)
          ·
            refine ⟨1550148649641988008793049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1033432433094658672528699 1550148649641988008793049)
            ·
              refine ⟨1162611487231491006594787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1550148649641988008793049 1162611487231491006594787)
              ·
                refine ⟨1743917230847236509892181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1162611487231491006594787 1743917230847236509892181)
                ·
                  refine ⟨20436530048991052850299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1743917230847236509892181 20436530048991052850299)
                  ·
                    rfl

theorem cell21_89550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 8].length) (baseStart_89550 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_89550 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_89550 prefixEnd_89550 := by exact prefixLift 89550
  have htrace : WordTrace (prefixWord ++ tailWord_89550) baseStart_89550 baseEnd_89550 := by
    simpa [prefixWord, tailWord_89550, baseEnd_89550] using wordTrace_append hprefix tailTrace_89550
  have hstable : (prefixWord ++ tailWord_89550).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89550).length < 2 ^ (prefixWord ++ tailWord_89550).sum := by decide
  have hdescent : baseEnd_89550 < baseStart_89550 := by decide
  rcases family_descends (prefixWord ++ tailWord_89550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89564 : List Nat := [2, 2, 17]
def baseStart_89564 : Nat := 118140960795 + 89564 * 2 ^ 59
def prefixEnd_89564 : Nat := 4983230072969 + 3 ^ 40 * 89564 * 2
def baseEnd_89564 : Nat := 28038031604568092753

theorem tailTrace_89564 : CollatzResearch.WordTrace tailWord_89564 prefixEnd_89564 28038031604568092753 := by
  unfold tailWord_89564
  simp only [CollatzResearch.WordTrace]
  refine ⟨1633333723766199579253873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2177778298354932772338497 1633333723766199579253873)
  ·
    refine ⟨1225000292824649684440405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1633333723766199579253873 1225000292824649684440405)
    ·
      refine ⟨28038031604568092753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 17 1225000292824649684440405 28038031604568092753)
      ·
        rfl

theorem cell21_89564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 17].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 17].length) (baseStart_89564 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_89564 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_89564 prefixEnd_89564 := by exact prefixLift 89564
  have htrace : WordTrace (prefixWord ++ tailWord_89564) baseStart_89564 baseEnd_89564 := by
    simpa [prefixWord, tailWord_89564, baseEnd_89564] using wordTrace_append hprefix tailTrace_89564
  have hstable : (prefixWord ++ tailWord_89564).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89564).length < 2 ^ (prefixWord ++ tailWord_89564).sum := by decide
  have hdescent : baseEnd_89564 < baseStart_89564 := by decide
  rcases family_descends (prefixWord ++ tailWord_89564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89567 : List Nat := [1, 1, 2, 3, 3, 1, 4, 2, 4]
def baseStart_89567 : Nat := 118140960795 + 89567 * 2 ^ 59
def prefixEnd_89567 : Nat := 4983230072969 + 3 ^ 40 * 89567 * 2
def baseEnd_89567 : Nat := 20440409680602801066931

theorem tailTrace_89567 : CollatzResearch.WordTrace tailWord_89567 prefixEnd_89567 20440409680602801066931 := by
  unfold tailWord_89567
  simp only [CollatzResearch.WordTrace]
  refine ⟨3266776866521530670866955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2177851244347687113911303 3266776866521530670866955)
  ·
    refine ⟨4900165299782296006300433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3266776866521530670866955 4900165299782296006300433)
    ·
      refine ⟨3675123974836722004725325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4900165299782296006300433 3675123974836722004725325)
      ·
        refine ⟨1378171490563770751771997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3675123974836722004725325 1378171490563770751771997)
        ·
          refine ⟨516814308961414031914499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1378171490563770751771997 516814308961414031914499)
          ·
            refine ⟨775221463442121047871749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 516814308961414031914499 775221463442121047871749)
            ·
              refine ⟨145354024395397696475953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 775221463442121047871749 145354024395397696475953)
              ·
                refine ⟨109015518296548272356965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 145354024395397696475953 109015518296548272356965)
                ·
                  refine ⟨20440409680602801066931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 109015518296548272356965 20440409680602801066931)
                  ·
                    rfl

theorem cell21_89567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 4, 2, 4].length) (baseStart_89567 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_89567 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_89567 prefixEnd_89567 := by exact prefixLift 89567
  have htrace : WordTrace (prefixWord ++ tailWord_89567) baseStart_89567 baseEnd_89567 := by
    simpa [prefixWord, tailWord_89567, baseEnd_89567] using wordTrace_append hprefix tailTrace_89567
  have hstable : (prefixWord ++ tailWord_89567).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89567).length < 2 ^ (prefixWord ++ tailWord_89567).sum := by decide
  have hdescent : baseEnd_89567 < baseStart_89567 := by decide
  rcases family_descends (prefixWord ++ tailWord_89567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89595 : List Nat := [1, 1, 1, 1, 1, 3, 2, 6, 5]
def baseStart_89595 : Nat := 118140960795 + 89595 * 2 ^ 59
def prefixEnd_89595 : Nat := 4983230072969 + 3 ^ 40 * 89595 * 2
def baseEnd_89595 : Nat := 20446799662080974600207

theorem tailTrace_89595 : CollatzResearch.WordTrace tailWord_89595 prefixEnd_89595 20446799662080974600207 := by
  unfold tailWord_89595
  simp only [CollatzResearch.WordTrace]
  refine ⟨3267798110420091452886239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2178532073613394301924159 3267798110420091452886239)
  ·
    refine ⟨4901697165630137179329359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3267798110420091452886239 4901697165630137179329359)
    ·
      refine ⟨7352545748445205768994039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4901697165630137179329359 7352545748445205768994039)
      ·
        refine ⟨11028818622667808653491059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7352545748445205768994039 11028818622667808653491059)
        ·
          refine ⟨16543227934001712980236589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11028818622667808653491059 16543227934001712980236589)
          ·
            refine ⟨6203710475250642367588721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16543227934001712980236589 6203710475250642367588721)
            ·
              refine ⟨4652782856437981775691541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6203710475250642367588721 4652782856437981775691541)
              ·
                refine ⟨218099196395530395735541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4652782856437981775691541 218099196395530395735541)
                ·
                  refine ⟨20446799662080974600207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 218099196395530395735541 20446799662080974600207)
                  ·
                    rfl

theorem cell21_89595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 6, 5].length) (baseStart_89595 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_89595 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_89595 prefixEnd_89595 := by exact prefixLift 89595
  have htrace : WordTrace (prefixWord ++ tailWord_89595) baseStart_89595 baseEnd_89595 := by
    simpa [prefixWord, tailWord_89595, baseEnd_89595] using wordTrace_append hprefix tailTrace_89595
  have hstable : (prefixWord ++ tailWord_89595).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89595).length < 2 ^ (prefixWord ++ tailWord_89595).sum := by decide
  have hdescent : baseEnd_89595 < baseStart_89595 := by decide
  rcases family_descends (prefixWord ++ tailWord_89595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89629 : List Nat := [1, 4, 2, 2, 1, 1, 1, 6, 3]
def baseStart_89629 : Nat := 118140960795 + 89629 * 2 ^ 59
def prefixEnd_89629 : Nat := 4983230072969 + 3 ^ 40 * 89629 * 2
def baseEnd_89629 : Nat := 20454558925304471033471

theorem tailTrace_89629 : CollatzResearch.WordTrace tailWord_89629 prefixEnd_89629 20454558925304471033471 := by
  unfold tailWord_89629
  simp only [CollatzResearch.WordTrace]
  refine ⟨3269038192296915259623941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2179358794864610173082627 3269038192296915259623941)
  ·
    refine ⟨612944661055671611179489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3269038192296915259623941 612944661055671611179489)
    ·
      refine ⟨459708495791753708384617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 612944661055671611179489 459708495791753708384617)
      ·
        refine ⟨344781371843815281288463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 459708495791753708384617 344781371843815281288463)
        ·
          refine ⟨517172057765722921932695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 344781371843815281288463 517172057765722921932695)
          ·
            refine ⟨775758086648584382899043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 517172057765722921932695 775758086648584382899043)
            ·
              refine ⟨1163637129972876574348565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 775758086648584382899043 1163637129972876574348565)
              ·
                refine ⟨54545490467478589422589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1163637129972876574348565 54545490467478589422589)
                ·
                  refine ⟨20454558925304471033471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54545490467478589422589 20454558925304471033471)
                  ·
                    rfl

theorem cell21_89629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 6, 3].length) (baseStart_89629 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_89629 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_89629 prefixEnd_89629 := by exact prefixLift 89629
  have htrace : WordTrace (prefixWord ++ tailWord_89629) baseStart_89629 baseEnd_89629 := by
    simpa [prefixWord, tailWord_89629, baseEnd_89629] using wordTrace_append hprefix tailTrace_89629
  have hstable : (prefixWord ++ tailWord_89629).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89629).length < 2 ^ (prefixWord ++ tailWord_89629).sum := by decide
  have hdescent : baseEnd_89629 < baseStart_89629 := by decide
  rcases family_descends (prefixWord ++ tailWord_89629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89657 : List Nat := [1, 2, 1, 5, 1, 3, 1, 7]
def baseStart_89657 : Nat := 118140960795 + 89657 * 2 ^ 59
def prefixEnd_89657 : Nat := 4983230072969 + 3 ^ 40 * 89657 * 2
def baseEnd_89657 : Nat := 6820316302260881522249

theorem tailTrace_89657 : CollatzResearch.WordTrace tailWord_89657 prefixEnd_89657 6820316302260881522249 := by
  unfold tailWord_89657
  simp only [CollatzResearch.WordTrace]
  refine ⟨3270059436195476041643225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2180039624130317361095483 3270059436195476041643225)
  ·
    refine ⟨2452544577146607031232419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3270059436195476041643225 2452544577146607031232419)
    ·
      refine ⟨3678816865719910546848629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2452544577146607031232419 3678816865719910546848629)
      ·
        refine ⟨344889081161241613767059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3678816865719910546848629 344889081161241613767059)
        ·
          refine ⟨517333621741862420650589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 344889081161241613767059 517333621741862420650589)
          ·
            refine ⟨194000108153198407743971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 517333621741862420650589 194000108153198407743971)
            ·
              refine ⟨291000162229797611615957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 194000108153198407743971 291000162229797611615957)
              ·
                refine ⟨6820316302260881522249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 291000162229797611615957 6820316302260881522249)
                ·
                  rfl

theorem cell21_89657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 7].length) (baseStart_89657 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_89657 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_89657 prefixEnd_89657 := by exact prefixLift 89657
  have htrace : WordTrace (prefixWord ++ tailWord_89657) baseStart_89657 baseEnd_89657 := by
    simpa [prefixWord, tailWord_89657, baseEnd_89657] using wordTrace_append hprefix tailTrace_89657
  have hstable : (prefixWord ++ tailWord_89657).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89657).length < 2 ^ (prefixWord ++ tailWord_89657).sum := by decide
  have hdescent : baseEnd_89657 < baseStart_89657 := by decide
  rcases family_descends (prefixWord ++ tailWord_89657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89764 : List Nat := [2, 3, 1, 2, 2, 3, 1, 2, 5]
def baseStart_89764 : Nat := 118140960795 + 89764 * 2 ^ 59
def prefixEnd_89764 : Nat := 4983230072969 + 3 ^ 40 * 89764 * 2
def baseEnd_89764 : Nat := 20485367764574236283195

theorem tailTrace_89764 : CollatzResearch.WordTrace tailWord_89764 prefixEnd_89764 20485367764574236283195 := by
  unfold tailWord_89764
  simp only [CollatzResearch.WordTrace]
  refine ⟨1636981023403916657894173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2182641364538555543858897 1636981023403916657894173)
  ·
    refine ⟨613867883776468746710315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1636981023403916657894173 613867883776468746710315)
    ·
      refine ⟨920801825664703120065473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 613867883776468746710315 920801825664703120065473)
      ·
        refine ⟨690601369248527340049105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 920801825664703120065473 690601369248527340049105)
        ·
          refine ⟨517951026936395505036829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 690601369248527340049105 517951026936395505036829)
          ·
            refine ⟨194231635101148314388811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 517951026936395505036829 194231635101148314388811)
            ·
              refine ⟨291347452651722471583217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 194231635101148314388811 291347452651722471583217)
              ·
                refine ⟨218510589488791853687413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 291347452651722471583217 218510589488791853687413)
                ·
                  refine ⟨20485367764574236283195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 218510589488791853687413 20485367764574236283195)
                  ·
                    rfl

theorem cell21_89764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 2, 5].length) (baseStart_89764 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_89764 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_89764 prefixEnd_89764 := by exact prefixLift 89764
  have htrace : WordTrace (prefixWord ++ tailWord_89764) baseStart_89764 baseEnd_89764 := by
    simpa [prefixWord, tailWord_89764, baseEnd_89764] using wordTrace_append hprefix tailTrace_89764
  have hstable : (prefixWord ++ tailWord_89764).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89764).length < 2 ^ (prefixWord ++ tailWord_89764).sum := by decide
  have hdescent : baseEnd_89764 < baseStart_89764 := by decide
  rcases family_descends (prefixWord ++ tailWord_89764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89792 : List Nat := [2, 1, 1, 2, 4, 1, 10]
def baseStart_89792 : Nat := 118140960795 + 89792 * 2 ^ 59
def prefixEnd_89792 : Nat := 4983230072969 + 3 ^ 40 * 89792 * 2
def baseEnd_89792 : Nat := 2276861971783601090719

theorem tailTrace_89792 : CollatzResearch.WordTrace tailWord_89792 prefixEnd_89792 2276861971783601090719 := by
  unfold tailWord_89792
  simp only [CollatzResearch.WordTrace]
  refine ⟨1637491645353197048903815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2183322193804262731871753 1637491645353197048903815)
  ·
    refine ⟨2456237468029795573355723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1637491645353197048903815 2456237468029795573355723)
    ·
      refine ⟨3684356202044693360033585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2456237468029795573355723 3684356202044693360033585)
      ·
        refine ⟨2763267151533520020025189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3684356202044693360033585 2763267151533520020025189)
        ·
          refine ⟨518112590912535003754723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2763267151533520020025189 518112590912535003754723)
          ·
            refine ⟨777168886368802505632085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 518112590912535003754723 777168886368802505632085)
            ·
              refine ⟨2276861971783601090719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 777168886368802505632085 2276861971783601090719)
              ·
                rfl

theorem cell21_89792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 10].length) (baseStart_89792 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_89792 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_89792 prefixEnd_89792 := by exact prefixLift 89792
  have htrace : WordTrace (prefixWord ++ tailWord_89792) baseStart_89792 baseEnd_89792 := by
    simpa [prefixWord, tailWord_89792, baseEnd_89792] using wordTrace_append hprefix tailTrace_89792
  have hstable : (prefixWord ++ tailWord_89792).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89792).length < 2 ^ (prefixWord ++ tailWord_89792).sum := by decide
  have hdescent : baseEnd_89792 < baseStart_89792 := by decide
  rcases family_descends (prefixWord ++ tailWord_89792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89798 : List Nat := [6, 1, 2, 1, 1, 1, 1, 3, 5]
def baseStart_89798 : Nat := 118140960795 + 89798 * 2 ^ 59
def prefixEnd_89798 : Nat := 4983230072969 + 3 ^ 40 * 89798 * 2
def baseEnd_89798 : Nat := 20493127027797732716459

theorem tailTrace_89798 : CollatzResearch.WordTrace tailWord_89798 prefixEnd_89798 20493127027797732716459 := by
  unfold tailWord_89798
  simp only [CollatzResearch.WordTrace]
  refine ⟨102350066521395535078939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 2183468085789771415017365 102350066521395535078939)
  ·
    refine ⟨153525099782093302618409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102350066521395535078939 153525099782093302618409)
    ·
      refine ⟨115143824836569976963807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153525099782093302618409 115143824836569976963807)
      ·
        refine ⟨172715737254854965445711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115143824836569976963807 172715737254854965445711)
        ·
          refine ⟨259073605882282448168567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172715737254854965445711 259073605882282448168567)
          ·
            refine ⟨388610408823423672252851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 259073605882282448168567 388610408823423672252851)
            ·
              refine ⟨582915613235135508379277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 388610408823423672252851 582915613235135508379277)
              ·
                refine ⟨218593354963175815642229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 582915613235135508379277 218593354963175815642229)
                ·
                  refine ⟨20493127027797732716459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 218593354963175815642229 20493127027797732716459)
                  ·
                    rfl

theorem cell21_89798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_89798 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_89798 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_89798 prefixEnd_89798 := by exact prefixLift 89798
  have htrace : WordTrace (prefixWord ++ tailWord_89798) baseStart_89798 baseEnd_89798 := by
    simpa [prefixWord, tailWord_89798, baseEnd_89798] using wordTrace_append hprefix tailTrace_89798
  have hstable : (prefixWord ++ tailWord_89798).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89798).length < 2 ^ (prefixWord ++ tailWord_89798).sum := by decide
  have hdescent : baseEnd_89798 < baseStart_89798 := by decide
  rcases family_descends (prefixWord ++ tailWord_89798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89823 : List Nat := [1, 1, 2, 3, 2, 2, 1, 4, 5]
def baseStart_89823 : Nat := 118140960795 + 89823 * 2 ^ 59
def prefixEnd_89823 : Nat := 4983230072969 + 3 ^ 40 * 89823 * 2
def baseEnd_89823 : Nat := 20498832368403244799741

theorem tailTrace_89823 : CollatzResearch.WordTrace tailWord_89823 prefixEnd_89823 20498832368403244799741 := by
  unfold tailWord_89823
  simp only [CollatzResearch.WordTrace]
  refine ⟨3276113953594086392186123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2184075969062724261457415 3276113953594086392186123)
  ·
    refine ⟨4914170930391129588279185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3276113953594086392186123 4914170930391129588279185)
    ·
      refine ⟨3685628197793347191209389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4914170930391129588279185 3685628197793347191209389)
      ·
        refine ⟨1382110574172505196703521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3685628197793347191209389 1382110574172505196703521)
        ·
          refine ⟨1036582930629378897527641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1382110574172505196703521 1036582930629378897527641)
          ·
            refine ⟨777437197972034173145731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1036582930629378897527641 777437197972034173145731)
            ·
              refine ⟨1166155796958051259718597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 777437197972034173145731 1166155796958051259718597)
              ·
                refine ⟨218654211929634611197237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1166155796958051259718597 218654211929634611197237)
                ·
                  refine ⟨20498832368403244799741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 218654211929634611197237 20498832368403244799741)
                  ·
                    rfl

theorem cell21_89823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 4, 5].length) (baseStart_89823 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_89823 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_89823 prefixEnd_89823 := by exact prefixLift 89823
  have htrace : WordTrace (prefixWord ++ tailWord_89823) baseStart_89823 baseEnd_89823 := by
    simpa [prefixWord, tailWord_89823, baseEnd_89823] using wordTrace_append hprefix tailTrace_89823
  have hstable : (prefixWord ++ tailWord_89823).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89823).length < 2 ^ (prefixWord ++ tailWord_89823).sum := by decide
  have hdescent : baseEnd_89823 < baseStart_89823 := by decide
  rcases family_descends (prefixWord ++ tailWord_89823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89840 : List Nat := [2, 1, 1, 1, 3, 1, 2, 7, 3]
def baseStart_89840 : Nat := 118140960795 + 89840 * 2 ^ 59
def prefixEnd_89840 : Nat := 4983230072969 + 3 ^ 40 * 89840 * 2
def baseEnd_89840 : Nat := 20502712000014993016373

theorem tailTrace_89840 : CollatzResearch.WordTrace tailWord_89840 prefixEnd_89840 20502712000014993016373 := by
  unfold tailWord_89840
  simp only [CollatzResearch.WordTrace]
  refine ⟨1638366997266249147777487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2184489329688332197036649 1638366997266249147777487)
  ·
    refine ⟨2457550495899373721666231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1638366997266249147777487 2457550495899373721666231)
    ·
      refine ⟨3686325743849060582499347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2457550495899373721666231 3686325743849060582499347)
      ·
        refine ⟨5529488615773590873749021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3686325743849060582499347 5529488615773590873749021)
        ·
          refine ⟨2073558230915096577655883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5529488615773590873749021 2073558230915096577655883)
          ·
            refine ⟨3110337346372644866483825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2073558230915096577655883 3110337346372644866483825)
            ·
              refine ⟨2332753009779483649862869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3110337346372644866483825 2332753009779483649862869)
              ·
                refine ⟨54673898666706648043661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2332753009779483649862869 54673898666706648043661)
                ·
                  refine ⟨20502712000014993016373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54673898666706648043661 20502712000014993016373)
                  ·
                    rfl

theorem cell21_89840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 7, 3].length) (baseStart_89840 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_89840 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_89840 prefixEnd_89840 := by exact prefixLift 89840
  have htrace : WordTrace (prefixWord ++ tailWord_89840) baseStart_89840 baseEnd_89840 := by
    simpa [prefixWord, tailWord_89840, baseEnd_89840] using wordTrace_append hprefix tailTrace_89840
  have hstable : (prefixWord ++ tailWord_89840).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89840).length < 2 ^ (prefixWord ++ tailWord_89840).sum := by decide
  have hdescent : baseEnd_89840 < baseStart_89840 := by decide
  rcases family_descends (prefixWord ++ tailWord_89840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89868 : List Nat := [2, 2, 1, 2, 2, 1, 3, 8]
def baseStart_89868 : Nat := 118140960795 + 89868 * 2 ^ 59
def prefixEnd_89868 : Nat := 4983230072969 + 3 ^ 40 * 89868 * 2
def baseEnd_89868 : Nat := 6836367327164388849883

theorem tailTrace_89868 : CollatzResearch.WordTrace tailWord_89868 prefixEnd_89868 6836367327164388849883 := by
  unfold tailWord_89868
  simp only [CollatzResearch.WordTrace]
  refine ⟨1638877619215529538787129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2185170158954039385049505 1638877619215529538787129)
  ·
    refine ⟨1229158214411647154090347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1638877619215529538787129 1229158214411647154090347)
    ·
      refine ⟨1843737321617470731135521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1229158214411647154090347 1843737321617470731135521)
      ·
        refine ⟨1382802991213103048351641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1843737321617470731135521 1382802991213103048351641)
        ·
          refine ⟨1037102243409827286263731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1382802991213103048351641 1037102243409827286263731)
          ·
            refine ⟨1555653365114740929395597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1037102243409827286263731 1555653365114740929395597)
            ·
              refine ⟨583370011918027848523349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1555653365114740929395597 583370011918027848523349)
              ·
                refine ⟨6836367327164388849883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 583370011918027848523349 6836367327164388849883)
                ·
                  rfl

theorem cell21_89868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 8].length) (baseStart_89868 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_89868 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_89868 prefixEnd_89868 := by exact prefixLift 89868
  have htrace : WordTrace (prefixWord ++ tailWord_89868) baseStart_89868 baseEnd_89868 := by
    simpa [prefixWord, tailWord_89868, baseEnd_89868] using wordTrace_append hprefix tailTrace_89868
  have hstable : (prefixWord ++ tailWord_89868).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89868).length < 2 ^ (prefixWord ++ tailWord_89868).sum := by decide
  have hdescent : baseEnd_89868 < baseStart_89868 := by decide
  rcases family_descends (prefixWord ++ tailWord_89868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89902 : List Nat := [4, 1, 3, 2, 3, 8]
def baseStart_89902 : Nat := 118140960795 + 89902 * 2 ^ 59
def prefixEnd_89902 : Nat := 4983230072969 + 3 ^ 40 * 89902 * 2
def baseEnd_89902 : Nat := 759883749804320851219

theorem tailTrace_89902 : CollatzResearch.WordTrace tailWord_89902 prefixEnd_89902 759883749804320851219 := by
  unfold tailWord_89902
  simp only [CollatzResearch.WordTrace]
  refine ⟨409874415038485360538995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2185996880205255256207973 409874415038485360538995)
  ·
    refine ⟨614811622557728040808493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 409874415038485360538995 614811622557728040808493)
    ·
      refine ⟨230554358459148015303185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 614811622557728040808493 230554358459148015303185)
      ·
        refine ⟨172915768844361011477389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 230554358459148015303185 172915768844361011477389)
        ·
          refine ⟨64843413316635379304021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 172915768844361011477389 64843413316635379304021)
          ·
            refine ⟨759883749804320851219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 64843413316635379304021 759883749804320851219)
            ·
              rfl

theorem cell21_89902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 8].length) (baseStart_89902 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_89902 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_89902 prefixEnd_89902 := by exact prefixLift 89902
  have htrace : WordTrace (prefixWord ++ tailWord_89902) baseStart_89902 baseEnd_89902 := by
    simpa [prefixWord, tailWord_89902, baseEnd_89902] using wordTrace_append hprefix tailTrace_89902
  have hstable : (prefixWord ++ tailWord_89902).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89902).length < 2 ^ (prefixWord ++ tailWord_89902).sum := by decide
  have hdescent : baseEnd_89902 < baseStart_89902 := by decide
  rcases family_descends (prefixWord ++ tailWord_89902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89930 : List Nat := [3, 1, 2, 1, 1, 1, 3, 5, 4]
def baseStart_89930 : Nat := 118140960795 + 89930 * 2 ^ 59
def prefixEnd_89930 : Nat := 4983230072969 + 3 ^ 40 * 89930 * 2
def baseEnd_89930 : Nat := 20523251226194836516189

theorem tailTrace_89930 : CollatzResearch.WordTrace tailWord_89930 prefixEnd_89930 20523251226194836516189 := by
  unfold tailWord_89930
  simp only [CollatzResearch.WordTrace]
  refine ⟨820004141051610916582811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2186677709470962444220829 820004141051610916582811)
  ·
    refine ⟨1230006211577416374874217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 820004141051610916582811 1230006211577416374874217)
    ·
      refine ⟨922504658683062281155663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1230006211577416374874217 922504658683062281155663)
      ·
        refine ⟨1383756988024593421733495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 922504658683062281155663 1383756988024593421733495)
        ·
          refine ⟨2075635482036890132600243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1383756988024593421733495 2075635482036890132600243)
          ·
            refine ⟨3113453223055335198900365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2075635482036890132600243 3113453223055335198900365)
            ·
              refine ⟨1167544958645750699587637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3113453223055335198900365 1167544958645750699587637)
              ·
                refine ⟨109457339873039128086341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1167544958645750699587637 109457339873039128086341)
                ·
                  refine ⟨20523251226194836516189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 109457339873039128086341 20523251226194836516189)
                  ·
                    rfl

theorem cell21_89930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 5, 4].length) (baseStart_89930 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_89930 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_89930 prefixEnd_89930 := by exact prefixLift 89930
  have htrace : WordTrace (prefixWord ++ tailWord_89930) baseStart_89930 baseEnd_89930 := by
    simpa [prefixWord, tailWord_89930, baseEnd_89930] using wordTrace_append hprefix tailTrace_89930
  have hstable : (prefixWord ++ tailWord_89930).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89930).length < 2 ^ (prefixWord ++ tailWord_89930).sum := by decide
  have hdescent : baseEnd_89930 < baseStart_89930 := by decide
  rcases family_descends (prefixWord ++ tailWord_89930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_89933 : List Nat := [1, 6, 1, 2, 1, 2, 1, 2, 5]
def baseStart_89933 : Nat := 118140960795 + 89933 * 2 ^ 59
def prefixEnd_89933 : Nat := 4983230072969 + 3 ^ 40 * 89933 * 2
def baseEnd_89933 : Nat := 20523935867067497966183

theorem tailTrace_89933 : CollatzResearch.WordTrace tailWord_89933 prefixEnd_89933 20523935867067497966183 := by
  unfold tailWord_89933
  simp only [CollatzResearch.WordTrace]
  refine ⟨3280125983195575178690453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2186750655463716785793635 3280125983195575178690453)
  ·
    refine ⟨153755905462292586501115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 3280125983195575178690453 153755905462292586501115)
    ·
      refine ⟨230633858193438879751673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153755905462292586501115 230633858193438879751673)
      ·
        refine ⟨172975393645079159813755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 230633858193438879751673 172975393645079159813755)
        ·
          refine ⟨259463090467618739720633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172975393645079159813755 259463090467618739720633)
          ·
            refine ⟨194597317850714054790475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 259463090467618739720633 194597317850714054790475)
            ·
              refine ⟨291895976776071082185713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 194597317850714054790475 291895976776071082185713)
              ·
                refine ⟨218921982582053311639285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 291895976776071082185713 218921982582053311639285)
                ·
                  refine ⟨20523935867067497966183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 218921982582053311639285 20523935867067497966183)
                  ·
                    rfl

theorem cell21_89933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_89933 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_89933 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_89933 prefixEnd_89933 := by exact prefixLift 89933
  have htrace : WordTrace (prefixWord ++ tailWord_89933) baseStart_89933 baseEnd_89933 := by
    simpa [prefixWord, tailWord_89933, baseEnd_89933] using wordTrace_append hprefix tailTrace_89933
  have hstable : (prefixWord ++ tailWord_89933).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_89933).length < 2 ^ (prefixWord ++ tailWord_89933).sum := by decide
  have hdescent : baseEnd_89933 < baseStart_89933 := by decide
  rcases family_descends (prefixWord ++ tailWord_89933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90020 : List Nat := [2, 3, 1, 2, 1, 3, 9]
def baseStart_90020 : Nat := 118140960795 + 90020 * 2 ^ 59
def prefixEnd_90020 : Nat := 4983230072969 + 3 ^ 40 * 90020 * 2
def baseEnd_90020 : Nat := 2282643383597186668445

theorem tailTrace_90020 : CollatzResearch.WordTrace tailWord_90020 prefixEnd_90020 2282643383597186668445 := by
  unfold tailWord_90020
  simp only [CollatzResearch.WordTrace]
  refine ⟨1641649566940194518553757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2188866089253592691405009 1641649566940194518553757)
  ·
    refine ⟨615618587602572944457659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1641649566940194518553757 615618587602572944457659)
    ·
      refine ⟨923427881403859416686489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 615618587602572944457659 923427881403859416686489)
      ·
        refine ⟨692570911052894562514867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 923427881403859416686489 692570911052894562514867)
        ·
          refine ⟨1038856366579341843772301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 692570911052894562514867 1038856366579341843772301)
          ·
            refine ⟨389571137467253191414613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1038856366579341843772301 389571137467253191414613)
            ·
              refine ⟨2282643383597186668445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 389571137467253191414613 2282643383597186668445)
              ·
                rfl

theorem cell21_90020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 9].length) (baseStart_90020 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_90020 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_90020 prefixEnd_90020 := by exact prefixLift 90020
  have htrace : WordTrace (prefixWord ++ tailWord_90020) baseStart_90020 baseEnd_90020 := by
    simpa [prefixWord, tailWord_90020, baseEnd_90020] using wordTrace_append hprefix tailTrace_90020
  have hstable : (prefixWord ++ tailWord_90020).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90020).length < 2 ^ (prefixWord ++ tailWord_90020).sum := by decide
  have hdescent : baseEnd_90020 < baseStart_90020 := by decide
  rcases family_descends (prefixWord ++ tailWord_90020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90037 : List Nat := [1, 3, 3, 2, 1, 3, 2, 6]
def baseStart_90037 : Nat := 118140960795 + 90037 * 2 ^ 59
def prefixEnd_90037 : Nat := 4983230072969 + 3 ^ 40 * 90037 * 2
def baseEnd_90037 : Nat := 6849223361328809410879

theorem tailTrace_90037 : CollatzResearch.WordTrace tailWord_90037 prefixEnd_90037 6849223361328809410879 := by
  unfold tailWord_90037
  simp only [CollatzResearch.WordTrace]
  refine ⟨3283919174818800940476365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2189279449879200626984243 3283919174818800940476365)
  ·
    refine ⟨1231469690557050352678637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3283919174818800940476365 1231469690557050352678637)
    ·
      refine ⟨461801133958893882254489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1231469690557050352678637 461801133958893882254489)
      ·
        refine ⟨346350850469170411690867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 461801133958893882254489 346350850469170411690867)
        ·
          refine ⟨519526275703755617536301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 346350850469170411690867 519526275703755617536301)
          ·
            refine ⟨194822353388908356576113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 519526275703755617536301 194822353388908356576113)
            ·
              refine ⟨146116765041681267432085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 194822353388908356576113 146116765041681267432085)
              ·
                refine ⟨6849223361328809410879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 146116765041681267432085 6849223361328809410879)
                ·
                  rfl

theorem cell21_90037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 2, 6].length) (baseStart_90037 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_90037 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_90037 prefixEnd_90037 := by exact prefixLift 90037
  have htrace : WordTrace (prefixWord ++ tailWord_90037) baseStart_90037 baseEnd_90037 := by
    simpa [prefixWord, tailWord_90037, baseEnd_90037] using wordTrace_append hprefix tailTrace_90037
  have hstable : (prefixWord ++ tailWord_90037).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90037).length < 2 ^ (prefixWord ++ tailWord_90037).sum := by decide
  have hdescent : baseEnd_90037 < baseStart_90037 := by decide
  rcases family_descends (prefixWord ++ tailWord_90037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90065 : List Nat := [1, 2, 2, 1, 2, 1, 2, 4, 6]
def baseStart_90065 : Nat := 118140960795 + 90065 * 2 ^ 59
def prefixEnd_90065 : Nat := 4983230072969 + 3 ^ 40 * 90065 * 2
def baseEnd_90065 : Nat := 20554060065464601765913

theorem tailTrace_90065 : CollatzResearch.WordTrace tailWord_90065 prefixEnd_90065 20554060065464601765913 := by
  unfold tailWord_90065
  simp only [CollatzResearch.WordTrace]
  refine ⟨3284940418717361722495649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2189960279144907814997099 3284940418717361722495649)
  ·
    refine ⟨2463705314038021291871737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3284940418717361722495649 2463705314038021291871737)
    ·
      refine ⟨1847778985528515968903803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2463705314038021291871737 1847778985528515968903803)
      ·
        refine ⟨2771668478292773953355705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1847778985528515968903803 2771668478292773953355705)
        ·
          refine ⟨2078751358719580465016779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2771668478292773953355705 2078751358719580465016779)
          ·
            refine ⟨3118127038079370697525169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2078751358719580465016779 3118127038079370697525169)
            ·
              refine ⟨2338595278559528023143877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3118127038079370697525169 2338595278559528023143877)
              ·
                refine ⟨438486614729911504339477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2338595278559528023143877 438486614729911504339477)
                ·
                  refine ⟨20554060065464601765913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 438486614729911504339477 20554060065464601765913)
                  ·
                    rfl

theorem cell21_90065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 4, 6].length) (baseStart_90065 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_90065 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_90065 prefixEnd_90065 := by exact prefixLift 90065
  have htrace : WordTrace (prefixWord ++ tailWord_90065) baseStart_90065 baseEnd_90065 := by
    simpa [prefixWord, tailWord_90065, baseEnd_90065] using wordTrace_append hprefix tailTrace_90065
  have hstable : (prefixWord ++ tailWord_90065).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90065).length < 2 ^ (prefixWord ++ tailWord_90065).sum := by decide
  have hdescent : baseEnd_90065 < baseStart_90065 := by decide
  rcases family_descends (prefixWord ++ tailWord_90065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90096 : List Nat := [2, 1, 1, 1, 3, 2, 5, 6]
def baseStart_90096 : Nat := 118140960795 + 90096 * 2 ^ 59
def prefixEnd_90096 : Nat := 4983230072969 + 3 ^ 40 * 90096 * 2
def baseEnd_90096 : Nat := 6853711562605145583061

theorem tailTrace_90096 : CollatzResearch.WordTrace tailWord_90096 prefixEnd_90096 6853711562605145583061 := by
  unfold tailWord_90096
  simp only [CollatzResearch.WordTrace]
  refine ⟨1643035540802527008437071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2190714054403369344582761 1643035540802527008437071)
  ·
    refine ⟨2464553311203790512655607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1643035540802527008437071 2464553311203790512655607)
    ·
      refine ⟨3696829966805685768983411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2464553311203790512655607 3696829966805685768983411)
      ·
        refine ⟨5545244950208528653475117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3696829966805685768983411 5545244950208528653475117)
        ·
          refine ⟨2079466856328198245053169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5545244950208528653475117 2079466856328198245053169)
          ·
            refine ⟨1559600142246148683789877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2079466856328198245053169 1559600142246148683789877)
            ·
              refine ⟨146212513335576439105301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1559600142246148683789877 146212513335576439105301)
              ·
                refine ⟨6853711562605145583061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 146212513335576439105301 6853711562605145583061)
                ·
                  rfl

theorem cell21_90096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 5, 6].length) (baseStart_90096 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_90096 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_90096 prefixEnd_90096 := by exact prefixLift 90096
  have htrace : WordTrace (prefixWord ++ tailWord_90096) baseStart_90096 baseEnd_90096 := by
    simpa [prefixWord, tailWord_90096, baseEnd_90096] using wordTrace_append hprefix tailTrace_90096
  have hstable : (prefixWord ++ tailWord_90096).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90096).length < 2 ^ (prefixWord ++ tailWord_90096).sum := by decide
  have hdescent : baseEnd_90096 < baseStart_90096 := by decide
  rcases family_descends (prefixWord ++ tailWord_90096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90113 : List Nat := [1, 2, 4, 1, 2, 1, 5, 5]
def baseStart_90113 : Nat := 118140960795 + 90113 * 2 ^ 59
def prefixEnd_90113 : Nat := 4983230072969 + 3 ^ 40 * 90113 * 2
def baseEnd_90113 : Nat := 6855004773142394988605

theorem tailTrace_90113 : CollatzResearch.WordTrace tailWord_90113 prefixEnd_90113 6855004773142394988605 := by
  unfold tailWord_90113
  simp only [CollatzResearch.WordTrace]
  refine ⟨3286691122543465920242993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2191127415028977280161995 3286691122543465920242993)
  ·
    refine ⟨2465018341907599440182245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3286691122543465920242993 2465018341907599440182245)
    ·
      refine ⟨462190939107674895034171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2465018341907599440182245 462190939107674895034171)
      ·
        refine ⟨693286408661512342551257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 462190939107674895034171 693286408661512342551257)
        ·
          refine ⟨519964806496134256913443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 693286408661512342551257 519964806496134256913443)
          ·
            refine ⟨779947209744201385370165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 519964806496134256913443 779947209744201385370165)
            ·
              refine ⟨73120050913518879878453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 779947209744201385370165 73120050913518879878453)
              ·
                refine ⟨6855004773142394988605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 73120050913518879878453 6855004773142394988605)
                ·
                  rfl

theorem cell21_90113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 5, 5].length) (baseStart_90113 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_90113 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_90113 prefixEnd_90113 := by exact prefixLift 90113
  have htrace : WordTrace (prefixWord ++ tailWord_90113) baseStart_90113 baseEnd_90113 := by
    simpa [prefixWord, tailWord_90113, baseEnd_90113] using wordTrace_append hprefix tailTrace_90113
  have hstable : (prefixWord ++ tailWord_90113).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90113).length < 2 ^ (prefixWord ++ tailWord_90113).sum := by decide
  have hdescent : baseEnd_90113 < baseStart_90113 := by decide
  rcases family_descends (prefixWord ++ tailWord_90113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90164 : List Nat := [2, 5, 1, 2, 3, 1, 2, 5]
def baseStart_90164 : Nat := 118140960795 + 90164 * 2 ^ 59
def prefixEnd_90164 : Nat := 4983230072969 + 3 ^ 40 * 90164 * 2
def baseEnd_90164 : Nat := 6858884404754143205237

theorem tailTrace_90164 : CollatzResearch.WordTrace tailWord_90164 prefixEnd_90164 6858884404754143205237 := by
  unfold tailWord_90164
  simp only [CollatzResearch.WordTrace]
  refine ⟨1644275622679350815174773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2192367496905801086899697 1644275622679350815174773)
  ·
    refine ⟨154150839626189138922635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1644275622679350815174773 154150839626189138922635)
    ·
      refine ⟨231226259439283708383953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 154150839626189138922635 231226259439283708383953)
      ·
        refine ⟨173419694579462781287965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 231226259439283708383953 173419694579462781287965)
        ·
          refine ⟨65032385467298542982987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 173419694579462781287965 65032385467298542982987)
          ·
            refine ⟨97548578200947814474481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65032385467298542982987 97548578200947814474481)
            ·
              refine ⟨73161433650710860855861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97548578200947814474481 73161433650710860855861)
              ·
                refine ⟨6858884404754143205237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 73161433650710860855861 6858884404754143205237)
                ·
                  rfl

theorem cell21_90164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 2, 5].length) (baseStart_90164 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_90164 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_90164 prefixEnd_90164 := by exact prefixLift 90164
  have htrace : WordTrace (prefixWord ++ tailWord_90164) baseStart_90164 baseEnd_90164 := by
    simpa [prefixWord, tailWord_90164, baseEnd_90164] using wordTrace_append hprefix tailTrace_90164
  have hstable : (prefixWord ++ tailWord_90164).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90164).length < 2 ^ (prefixWord ++ tailWord_90164).sum := by decide
  have hdescent : baseEnd_90164 < baseStart_90164 := by decide
  rcases family_descends (prefixWord ++ tailWord_90164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90172 : List Nat := [2, 2, 2, 2, 2, 1, 3, 7]
def baseStart_90172 : Nat := 118140960795 + 90172 * 2 ^ 59
def prefixEnd_90172 : Nat := 4983230072969 + 3 ^ 40 * 90172 * 2
def baseEnd_90172 : Nat := 6859492974418731160787

theorem tailTrace_90172 : CollatzResearch.WordTrace tailWord_90172 prefixEnd_90172 6859492974418731160787 := by
  unfold tailWord_90172
  simp only [CollatzResearch.WordTrace]
  refine ⟨1644421514664859498320385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2192562019553145997760513 1644421514664859498320385)
  ·
    refine ⟨1233316135998644623740289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1644421514664859498320385 1233316135998644623740289)
    ·
      refine ⟨924987101998983467805217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1233316135998644623740289 924987101998983467805217)
      ·
        refine ⟨693740326499237600853913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 924987101998983467805217 693740326499237600853913)
        ·
          refine ⟨520305244874428200640435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 693740326499237600853913 520305244874428200640435)
          ·
            refine ⟨780457867311642300960653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 520305244874428200640435 780457867311642300960653)
            ·
              refine ⟨292671700241865862860245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 780457867311642300960653 292671700241865862860245)
              ·
                refine ⟨6859492974418731160787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 292671700241865862860245 6859492974418731160787)
                ·
                  rfl

theorem cell21_90172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 7].length) (baseStart_90172 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_90172 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_90172 prefixEnd_90172 := by exact prefixLift 90172
  have htrace : WordTrace (prefixWord ++ tailWord_90172) baseStart_90172 baseEnd_90172 := by
    simpa [prefixWord, tailWord_90172, baseEnd_90172] using wordTrace_append hprefix tailTrace_90172
  have hstable : (prefixWord ++ tailWord_90172).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90172).length < 2 ^ (prefixWord ++ tailWord_90172).sum := by decide
  have hdescent : baseEnd_90172 < baseStart_90172 := by decide
  rcases family_descends (prefixWord ++ tailWord_90172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90248 : List Nat := [2, 1, 3, 4, 1, 10]
def baseStart_90248 : Nat := 118140960795 + 90248 * 2 ^ 59
def prefixEnd_90248 : Nat := 4983230072969 + 3 ^ 40 * 90248 * 2
def baseEnd_90248 : Nat := 762808265136924082057

theorem tailTrace_90248 : CollatzResearch.WordTrace tailWord_90248 prefixEnd_90248 762808265136924082057 := by
  unfold tailWord_90248
  simp only [CollatzResearch.WordTrace]
  refine ⟨1645807488527191988203699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2194409984702922650938265 1645807488527191988203699)
  ·
    refine ⟨2468711232790787982305549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1645807488527191988203699 2468711232790787982305549)
    ·
      refine ⟨925766712296545493364581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2468711232790787982305549 925766712296545493364581)
      ·
        refine ⟨173581258555602280005859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 925766712296545493364581 173581258555602280005859)
        ·
          refine ⟨260371887833403420008789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 173581258555602280005859 260371887833403420008789)
          ·
            refine ⟨762808265136924082057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 260371887833403420008789 762808265136924082057)
            ·
              rfl

theorem cell21_90248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 10].length) (baseStart_90248 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_90248 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_90248 prefixEnd_90248 := by exact prefixLift 90248
  have htrace : WordTrace (prefixWord ++ tailWord_90248) baseStart_90248 baseEnd_90248 := by
    simpa [prefixWord, tailWord_90248, baseEnd_90248] using wordTrace_append hprefix tailTrace_90248
  have hstable : (prefixWord ++ tailWord_90248).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90248).length < 2 ^ (prefixWord ++ tailWord_90248).sum := by decide
  have hdescent : baseEnd_90248 < baseStart_90248 := by decide
  rcases family_descends (prefixWord ++ tailWord_90248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90296 : List Nat := [2, 1, 2, 1, 2, 1, 6, 3, 3]
def baseStart_90296 : Nat := 118140960795 + 90296 * 2 ^ 59
def prefixEnd_90296 : Nat := 4983230072969 + 3 ^ 40 * 90296 * 2
def baseEnd_90296 : Nat := 20606777412659533415441

theorem tailTrace_90296 : CollatzResearch.WordTrace tailWord_90296 prefixEnd_90296 20606777412659533415441 := by
  unfold tailWord_90296
  simp only [CollatzResearch.WordTrace]
  refine ⟨1646682840440244087077371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2195577120586992116103161 1646682840440244087077371)
  ·
    refine ⟨2470024260660366130616057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1646682840440244087077371 2470024260660366130616057)
    ·
      refine ⟨1852518195495274597962043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2470024260660366130616057 1852518195495274597962043)
      ·
        refine ⟨2778777293242911896943065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1852518195495274597962043 2778777293242911896943065)
        ·
          refine ⟨2084082969932183922707299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2778777293242911896943065 2084082969932183922707299)
          ·
            refine ⟨3126124454898275884060949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2084082969932183922707299 3126124454898275884060949)
            ·
              refine ⟨146537083823356682065357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 3126124454898275884060949 146537083823356682065357)
              ·
                refine ⟨54951406433758755774509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 146537083823356682065357 54951406433758755774509)
                ·
                  refine ⟨20606777412659533415441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54951406433758755774509 20606777412659533415441)
                  ·
                    rfl

theorem cell21_90296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 6, 3, 3].length) (baseStart_90296 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_90296 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_90296 prefixEnd_90296 := by exact prefixLift 90296
  have htrace : WordTrace (prefixWord ++ tailWord_90296) baseStart_90296 baseEnd_90296 := by
    simpa [prefixWord, tailWord_90296, baseEnd_90296] using wordTrace_append hprefix tailTrace_90296
  have hstable : (prefixWord ++ tailWord_90296).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90296).length < 2 ^ (prefixWord ++ tailWord_90296).sum := by decide
  have hdescent : baseEnd_90296 < baseStart_90296 := by decide
  rcases family_descends (prefixWord ++ tailWord_90296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90341 : List Nat := [1, 3, 1, 4, 2, 1, 4, 5]
def baseStart_90341 : Nat := 118140960795 + 90341 * 2 ^ 59
def prefixEnd_90341 : Nat := 4983230072969 + 3 ^ 40 * 90341 * 2
def baseEnd_90341 : Nat := 6872349008583151721783

theorem tailTrace_90341 : CollatzResearch.WordTrace tailWord_90341 prefixEnd_90341 6872349008583151721783 := by
  unfold tailWord_90341
  simp only [CollatzResearch.WordTrace]
  refine ⟨3295006965717460859542877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2196671310478307239695251 3295006965717460859542877)
  ·
    refine ⟨1235627612144047822328579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3295006965717460859542877 1235627612144047822328579)
    ·
      refine ⟨1853441418216071733492869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1235627612144047822328579 1853441418216071733492869)
      ·
        refine ⟨347520265915513450029913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1853441418216071733492869 347520265915513450029913)
        ·
          refine ⟨260640199436635087522435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 347520265915513450029913 260640199436635087522435)
          ·
            refine ⟨390960299154952631283653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 260640199436635087522435 390960299154952631283653)
            ·
              refine ⟨73305056091553618365685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 390960299154952631283653 73305056091553618365685)
              ·
                refine ⟨6872349008583151721783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 73305056091553618365685 6872349008583151721783)
                ·
                  rfl

theorem cell21_90341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 4, 5].length) (baseStart_90341 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_90341 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_90341 prefixEnd_90341 := by exact prefixLift 90341
  have htrace : WordTrace (prefixWord ++ tailWord_90341) baseStart_90341 baseEnd_90341 := by
    simpa [prefixWord, tailWord_90341, baseEnd_90341] using wordTrace_append hprefix tailTrace_90341
  have hstable : (prefixWord ++ tailWord_90341).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90341).length < 2 ^ (prefixWord ++ tailWord_90341).sum := by decide
  have hdescent : baseEnd_90341 < baseStart_90341 := by decide
  rcases family_descends (prefixWord ++ tailWord_90341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90369 : List Nat := [1, 2, 4, 1, 1, 2, 1, 3, 6]
def baseStart_90369 : Nat := 118140960795 + 90369 * 2 ^ 59
def prefixEnd_90369 : Nat := 4983230072969 + 3 ^ 40 * 90369 * 2
def baseEnd_90369 : Nat := 20623437007227628698625

theorem tailTrace_90369 : CollatzResearch.WordTrace tailWord_90369 prefixEnd_90369 20623437007227628698625 := by
  unfold tailWord_90369
  simp only [CollatzResearch.WordTrace]
  refine ⟨3296028209616021641562161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2197352139744014427708107 3296028209616021641562161)
  ·
    refine ⟨2472021157212016231171621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3296028209616021641562161 2472021157212016231171621)
    ·
      refine ⟨463503966977253043344679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2472021157212016231171621 463503966977253043344679)
      ·
        refine ⟨695255950465879565017019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 463503966977253043344679 695255950465879565017019)
        ·
          refine ⟨1042883925698819347525529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 695255950465879565017019 1042883925698819347525529)
          ·
            refine ⟨782162944274114510644147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1042883925698819347525529 782162944274114510644147)
            ·
              refine ⟨1173244416411171765966221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 782162944274114510644147 1173244416411171765966221)
              ·
                refine ⟨439966656154189412237333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1173244416411171765966221 439966656154189412237333)
                ·
                  refine ⟨20623437007227628698625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 439966656154189412237333 20623437007227628698625)
                  ·
                    rfl

theorem cell21_90369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 3, 6].length) (baseStart_90369 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_90369 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_90369 prefixEnd_90369 := by exact prefixLift 90369
  have htrace : WordTrace (prefixWord ++ tailWord_90369) baseStart_90369 baseEnd_90369 := by
    simpa [prefixWord, tailWord_90369, baseEnd_90369] using wordTrace_append hprefix tailTrace_90369
  have hstable : (prefixWord ++ tailWord_90369).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90369).length < 2 ^ (prefixWord ++ tailWord_90369).sum := by decide
  have hdescent : baseEnd_90369 < baseStart_90369 := by decide
  rcases family_descends (prefixWord ++ tailWord_90369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90400 : List Nat := [2, 1, 1, 5, 2, 1, 2, 7]
def baseStart_90400 : Nat := 118140960795 + 90400 * 2 ^ 59
def prefixEnd_90400 : Nat := 4983230072969 + 3 ^ 40 * 90400 * 2
def baseEnd_90400 : Nat := 6876837209859487893965

theorem tailTrace_90400 : CollatzResearch.WordTrace tailWord_90400 prefixEnd_90400 6876837209859487893965 := by
  unfold tailWord_90400
  simp only [CollatzResearch.WordTrace]
  refine ⟨1648579436251856967970327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2198105915002475957293769 1648579436251856967970327)
  ·
    refine ⟨2472869154377785451955491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1648579436251856967970327 2472869154377785451955491)
    ·
      refine ⟨3709303731566678177933237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2472869154377785451955491 3709303731566678177933237)
      ·
        refine ⟨347747224834376079181241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3709303731566678177933237 347747224834376079181241)
        ·
          refine ⟨260810418625782059385931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 347747224834376079181241 260810418625782059385931)
          ·
            refine ⟨391215627938673089078897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 260810418625782059385931 391215627938673089078897)
            ·
              refine ⟨293411720954004816809173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 391215627938673089078897 293411720954004816809173)
              ·
                refine ⟨6876837209859487893965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 293411720954004816809173 6876837209859487893965)
                ·
                  rfl

theorem cell21_90400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 7].length) (baseStart_90400 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_90400 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_90400 prefixEnd_90400 := by exact prefixLift 90400
  have htrace : WordTrace (prefixWord ++ tailWord_90400) baseStart_90400 baseEnd_90400 := by
    simpa [prefixWord, tailWord_90400, baseEnd_90400] using wordTrace_append hprefix tailTrace_90400
  have hstable : (prefixWord ++ tailWord_90400).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90400).length < 2 ^ (prefixWord ++ tailWord_90400).sum := by decide
  have hdescent : baseEnd_90400 < baseStart_90400 := by decide
  rcases family_descends (prefixWord ++ tailWord_90400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90476 : List Nat := [2, 2, 1, 1, 6, 1, 8]
def baseStart_90476 : Nat := 118140960795 + 90476 * 2 ^ 59
def prefixEnd_90476 : Nat := 4983230072969 + 3 ^ 40 * 90476 * 2
def baseEnd_90476 : Nat := 2294206207224357823897

theorem tailTrace_90476 : CollatzResearch.WordTrace tailWord_90476 prefixEnd_90476 2294206207224357823897 := by
  unfold tailWord_90476
  simp only [CollatzResearch.WordTrace]
  refine ⟨1649965410114189457853641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2199953880152252610471521 1649965410114189457853641)
  ·
    refine ⟨1237474057585642093390231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1649965410114189457853641 1237474057585642093390231)
    ·
      refine ⟨1856211086378463140085347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1237474057585642093390231 1856211086378463140085347)
      ·
        refine ⟨2784316629567694710128021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1856211086378463140085347 2784316629567694710128021)
        ·
          refine ⟨130514842010985689537251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 2784316629567694710128021 130514842010985689537251)
          ·
            refine ⟨195772263016478534305877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 130514842010985689537251 195772263016478534305877)
            ·
              refine ⟨2294206207224357823897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 195772263016478534305877 2294206207224357823897)
              ·
                rfl

theorem cell21_90476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 8].length) (baseStart_90476 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_90476 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_90476 prefixEnd_90476 := by exact prefixLift 90476
  have htrace : WordTrace (prefixWord ++ tailWord_90476) baseStart_90476 baseEnd_90476 := by
    simpa [prefixWord, tailWord_90476, baseEnd_90476] using wordTrace_append hprefix tailTrace_90476
  have hstable : (prefixWord ++ tailWord_90476).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90476).length < 2 ^ (prefixWord ++ tailWord_90476).sum := by decide
  have hdescent : baseEnd_90476 < baseStart_90476 := by decide
  rcases family_descends (prefixWord ++ tailWord_90476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90510 : List Nat := [4, 1, 1, 4, 1, 3, 2, 5]
def baseStart_90510 : Nat := 118140960795 + 90510 * 2 ^ 59
def prefixEnd_90510 : Nat := 4983230072969 + 3 ^ 40 * 90510 * 2
def baseEnd_90510 : Nat := 6885205042747572282779

theorem tailTrace_90510 : CollatzResearch.WordTrace tailWord_90510 prefixEnd_90510 6885205042747572282779 := by
  unfold tailWord_90510
  simp only [CollatzResearch.WordTrace]
  refine ⟨412646362763150340305623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2200780601403468481629989 412646362763150340305623)
  ·
    refine ⟨618969544144725510458435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 412646362763150340305623 618969544144725510458435)
    ·
      refine ⟨928454316217088265687653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 618969544144725510458435 928454316217088265687653)
      ·
        refine ⟨174085184290704049816435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 928454316217088265687653 174085184290704049816435)
        ·
          refine ⟨261127776436056074724653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174085184290704049816435 261127776436056074724653)
          ·
            refine ⟨97922916163521028021745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 261127776436056074724653 97922916163521028021745)
            ·
              refine ⟨73442187122640771016309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97922916163521028021745 73442187122640771016309)
              ·
                refine ⟨6885205042747572282779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 73442187122640771016309 6885205042747572282779)
                ·
                  rfl

theorem cell21_90510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 2, 5].length) (baseStart_90510 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_90510 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_90510 prefixEnd_90510 := by exact prefixLift 90510
  have htrace : WordTrace (prefixWord ++ tailWord_90510) baseStart_90510 baseEnd_90510 := by
    simpa [prefixWord, tailWord_90510, baseEnd_90510] using wordTrace_append hprefix tailTrace_90510
  have hstable : (prefixWord ++ tailWord_90510).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90510).length < 2 ^ (prefixWord ++ tailWord_90510).sum := by decide
  have hdescent : baseEnd_90510 < baseStart_90510 := by decide
  rcases family_descends (prefixWord ++ tailWord_90510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90541 : List Nat := [1, 5, 2, 2, 2, 2, 1, 1, 5]
def baseStart_90541 : Nat := 118140960795 + 90541 * 2 ^ 59
def prefixEnd_90541 : Nat := 4983230072969 + 3 ^ 40 * 90541 * 2
def baseEnd_90541 : Nat := 20662689750593551831607

theorem tailTrace_90541 : CollatzResearch.WordTrace tailWord_90541 prefixEnd_90541 20662689750593551831607 := by
  unfold tailWord_90541
  simp only [CollatzResearch.WordTrace]
  refine ⟨3302301564992895016823477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2201534376661930011215651 3302301564992895016823477)
  ·
    refine ⟨309590771718083907827201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3302301564992895016823477 309590771718083907827201)
    ·
      refine ⟨232193078788562930870401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 309590771718083907827201 232193078788562930870401)
      ·
        refine ⟨174144809091422198152801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 232193078788562930870401 174144809091422198152801)
        ·
          refine ⟨130608606818566648614601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174144809091422198152801 130608606818566648614601)
          ·
            refine ⟨97956455113924986460951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 130608606818566648614601 97956455113924986460951)
            ·
              refine ⟨146934682670887479691427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97956455113924986460951 146934682670887479691427)
              ·
                refine ⟨220402024006331219537141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 146934682670887479691427 220402024006331219537141)
                ·
                  refine ⟨20662689750593551831607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 220402024006331219537141 20662689750593551831607)
                  ·
                    rfl

theorem cell21_90541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 1, 1, 5].length) (baseStart_90541 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_90541 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_90541 prefixEnd_90541 := by exact prefixLift 90541
  have htrace : WordTrace (prefixWord ++ tailWord_90541) baseStart_90541 baseEnd_90541 := by
    simpa [prefixWord, tailWord_90541, baseEnd_90541] using wordTrace_append hprefix tailTrace_90541
  have hstable : (prefixWord ++ tailWord_90541).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90541).length < 2 ^ (prefixWord ++ tailWord_90541).sum := by decide
  have hdescent : baseEnd_90541 < baseStart_90541 := by decide
  rcases family_descends (prefixWord ++ tailWord_90541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90600 : List Nat := [2, 1, 4, 1, 1, 4, 1, 4, 3]
def baseStart_90600 : Nat := 118140960795 + 90600 * 2 ^ 59
def prefixEnd_90600 : Nat := 4983230072969 + 3 ^ 40 * 90600 * 2
def baseEnd_90600 : Nat := 20676154354422560348153

theorem tailTrace_90600 : CollatzResearch.WordTrace tailWord_90600 prefixEnd_90600 20676154354422560348153 := by
  unfold tailWord_90600
  simp only [CollatzResearch.WordTrace]
  refine ⟨1652226735889574046610627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2202968981186098728814169 1652226735889574046610627)
  ·
    refine ⟨2478340103834361069915941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1652226735889574046610627 2478340103834361069915941)
    ·
      refine ⟨464688769468942700609239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2478340103834361069915941 464688769468942700609239)
      ·
        refine ⟨697033154203414050913859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 464688769468942700609239 697033154203414050913859)
        ·
          refine ⟨1045549731305121076370789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 697033154203414050913859 1045549731305121076370789)
          ·
            refine ⟨196040574619710201819523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1045549731305121076370789 196040574619710201819523)
            ·
              refine ⟨294060861929565302729285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 196040574619710201819523 294060861929565302729285)
              ·
                refine ⟨55136411611793494261741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 294060861929565302729285 55136411611793494261741)
                ·
                  refine ⟨20676154354422560348153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55136411611793494261741 20676154354422560348153)
                  ·
                    rfl

theorem cell21_90600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 4, 3].length) (baseStart_90600 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_90600 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_90600 prefixEnd_90600 := by exact prefixLift 90600
  have htrace : WordTrace (prefixWord ++ tailWord_90600) baseStart_90600 baseEnd_90600 := by
    simpa [prefixWord, tailWord_90600, baseEnd_90600] using wordTrace_append hprefix tailTrace_90600
  have hstable : (prefixWord ++ tailWord_90600).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90600).length < 2 ^ (prefixWord ++ tailWord_90600).sum := by decide
  have hdescent : baseEnd_90600 < baseStart_90600 := by decide
  rcases family_descends (prefixWord ++ tailWord_90600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90614 : List Nat := [5, 1, 1, 1, 2, 1, 1, 5, 4]
def baseStart_90614 : Nat := 118140960795 + 90614 * 2 ^ 59
def prefixEnd_90614 : Nat := 4983230072969 + 3 ^ 40 * 90614 * 2
def baseEnd_90614 : Nat := 20679349345161647114791

theorem tailTrace_90614 : CollatzResearch.WordTrace tailWord_90614 prefixEnd_90614 20679349345161647114791 := by
  unfold tailWord_90614
  simp only [CollatzResearch.WordTrace]
  refine ⟨206560255858026780264431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2203309395818952322820597 206560255858026780264431)
  ·
    refine ⟨309840383787040170396647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 206560255858026780264431 309840383787040170396647)
    ·
      refine ⟨464760575680560255594971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 309840383787040170396647 464760575680560255594971)
      ·
        refine ⟨697140863520840383392457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 464760575680560255594971 697140863520840383392457)
        ·
          refine ⟨522855647640630287544343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 697140863520840383392457 522855647640630287544343)
          ·
            refine ⟨784283471460945431316515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 522855647640630287544343 784283471460945431316515)
            ·
              refine ⟨1176425207191418146974773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 784283471460945431316515 1176425207191418146974773)
              ·
                refine ⟨110289863174195451278885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1176425207191418146974773 110289863174195451278885)
                ·
                  refine ⟨20679349345161647114791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 110289863174195451278885 20679349345161647114791)
                  ·
                    rfl

theorem cell21_90614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 5, 4].length) (baseStart_90614 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_90614 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_90614 prefixEnd_90614 := by exact prefixLift 90614
  have htrace : WordTrace (prefixWord ++ tailWord_90614) baseStart_90614 baseEnd_90614 := by
    simpa [prefixWord, tailWord_90614, baseEnd_90614] using wordTrace_append hprefix tailTrace_90614
  have hstable : (prefixWord ++ tailWord_90614).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90614).length < 2 ^ (prefixWord ++ tailWord_90614).sum := by decide
  have hdescent : baseEnd_90614 < baseStart_90614 := by decide
  rcases family_descends (prefixWord ++ tailWord_90614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90659 : List Nat := [1, 1, 1, 4, 4, 2, 2, 1, 5]
def baseStart_90659 : Nat := 118140960795 + 90659 * 2 ^ 59
def prefixEnd_90659 : Nat := 4983230072969 + 3 ^ 40 * 90659 * 2
def baseEnd_90659 : Nat := 20689618958251568864699

theorem tailTrace_90659 : CollatzResearch.WordTrace tailWord_90659 prefixEnd_90659 20689618958251568864699 := by
  unfold tailWord_90659
  simp only [CollatzResearch.WordTrace]
  refine ⟨3306605378565401169619031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2204403585710267446412687 3306605378565401169619031)
  ·
    refine ⟨4959908067848101754428547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3306605378565401169619031 4959908067848101754428547)
    ·
      refine ⟨7439862101772152631642821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4959908067848101754428547 7439862101772152631642821)
      ·
        refine ⟨1394974144082278618433029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7439862101772152631642821 1394974144082278618433029)
        ·
          refine ⟨261557652015427240956193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1394974144082278618433029 261557652015427240956193)
          ·
            refine ⟨196168239011570430717145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 261557652015427240956193 196168239011570430717145)
            ·
              refine ⟨147126179258677823037859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 196168239011570430717145 147126179258677823037859)
              ·
                refine ⟨220689268888016734556789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 147126179258677823037859 220689268888016734556789)
                ·
                  refine ⟨20689618958251568864699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 220689268888016734556789 20689618958251568864699)
                  ·
                    rfl

theorem cell21_90659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 2, 1, 5].length) (baseStart_90659 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_90659 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_90659 prefixEnd_90659 := by exact prefixLift 90659
  have htrace : WordTrace (prefixWord ++ tailWord_90659) baseStart_90659 baseEnd_90659 := by
    simpa [prefixWord, tailWord_90659, baseEnd_90659] using wordTrace_append hprefix tailTrace_90659
  have hstable : (prefixWord ++ tailWord_90659).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90659).length < 2 ^ (prefixWord ++ tailWord_90659).sum := by decide
  have hdescent : baseEnd_90659 < baseStart_90659 := by decide
  rcases family_descends (prefixWord ++ tailWord_90659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90673 : List Nat := [1, 2, 2, 3, 1, 1, 2, 5, 4]
def baseStart_90673 : Nat := 118140960795 + 90673 * 2 ^ 59
def prefixEnd_90673 : Nat := 4983230072969 + 3 ^ 40 * 90673 * 2
def baseEnd_90673 : Nat := 20692813948990655631337

theorem tailTrace_90673 : CollatzResearch.WordTrace tailWord_90673 prefixEnd_90673 20692813948990655631337 := by
  unfold tailWord_90673
  simp only [CollatzResearch.WordTrace]
  refine ⟨3307116000514681560628673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2204744000343121040419115 3307116000514681560628673)
  ·
    refine ⟨2480337000386011170471505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3307116000514681560628673 2480337000386011170471505)
    ·
      refine ⟨1860252750289508377853629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2480337000386011170471505 1860252750289508377853629)
      ·
        refine ⟨697594781358565641695111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1860252750289508377853629 697594781358565641695111)
        ·
          refine ⟨1046392172037848462542667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 697594781358565641695111 1046392172037848462542667)
          ·
            refine ⟨1569588258056772693814001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1046392172037848462542667 1569588258056772693814001)
            ·
              refine ⟨1177191193542579520360501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1569588258056772693814001 1177191193542579520360501)
              ·
                refine ⟨110361674394616830033797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1177191193542579520360501 110361674394616830033797)
                ·
                  refine ⟨20692813948990655631337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 110361674394616830033797 20692813948990655631337)
                  ·
                    rfl

theorem cell21_90673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 5, 4].length) (baseStart_90673 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_90673 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_90673 prefixEnd_90673 := by exact prefixLift 90673
  have htrace : WordTrace (prefixWord ++ tailWord_90673) baseStart_90673 baseEnd_90673 := by
    simpa [prefixWord, tailWord_90673, baseEnd_90673] using wordTrace_append hprefix tailTrace_90673
  have hstable : (prefixWord ++ tailWord_90673).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90673).length < 2 ^ (prefixWord ++ tailWord_90673).sum := by decide
  have hdescent : baseEnd_90673 < baseStart_90673 := by decide
  rcases family_descends (prefixWord ++ tailWord_90673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90687 : List Nat := [1, 1, 2, 2, 3, 2, 3, 7]
def baseStart_90687 : Nat := 118140960795 + 90687 * 2 ^ 59
def prefixEnd_90687 : Nat := 4983230072969 + 3 ^ 40 * 90687 * 2
def baseEnd_90687 : Nat := 6898669646576580799325

theorem tailTrace_90687 : CollatzResearch.WordTrace tailWord_90687 prefixEnd_90687 6898669646576580799325 := by
  unfold tailWord_90687
  simp only [CollatzResearch.WordTrace]
  refine ⟨3307626622463961951638315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2205084414975974634425543 3307626622463961951638315)
  ·
    refine ⟨4961439933695942927457473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3307626622463961951638315 4961439933695942927457473)
    ·
      refine ⟨3721079950271957195593105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4961439933695942927457473 3721079950271957195593105)
      ·
        refine ⟨2790809962703967896694829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3721079950271957195593105 2790809962703967896694829)
        ·
          refine ⟨1046553736013987961260561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2790809962703967896694829 1046553736013987961260561)
          ·
            refine ⟨784915302010490970945421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1046553736013987961260561 784915302010490970945421)
            ·
              refine ⟨294343238253934114104533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 784915302010490970945421 294343238253934114104533)
              ·
                refine ⟨6898669646576580799325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 294343238253934114104533 6898669646576580799325)
                ·
                  rfl

theorem cell21_90687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 7].length) (baseStart_90687 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_90687 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_90687 prefixEnd_90687 := by exact prefixLift 90687
  have htrace : WordTrace (prefixWord ++ tailWord_90687) baseStart_90687 baseEnd_90687 := by
    simpa [prefixWord, tailWord_90687, baseEnd_90687] using wordTrace_append hprefix tailTrace_90687
  have hstable : (prefixWord ++ tailWord_90687).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90687).length < 2 ^ (prefixWord ++ tailWord_90687).sum := by decide
  have hdescent : baseEnd_90687 < baseStart_90687 := by decide
  rcases family_descends (prefixWord ++ tailWord_90687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90766 : List Nat := [4, 1, 1, 3, 1, 1, 4, 2, 4]
def baseStart_90766 : Nat := 118140960795 + 90766 * 2 ^ 59
def prefixEnd_90766 : Nat := 4983230072969 + 3 ^ 40 * 90766 * 2
def baseEnd_90766 : Nat := 20714037816043160581147

theorem tailTrace_90766 : CollatzResearch.WordTrace tailWord_90766 prefixEnd_90766 20714037816043160581147 := by
  unfold tailWord_90766
  simp only [CollatzResearch.WordTrace]
  refine ⟨413813498647219805470519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2207005326118505629176101 413813498647219805470519)
  ·
    refine ⟨620720247970829708205779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 413813498647219805470519 620720247970829708205779)
    ·
      refine ⟨931080371956244562308669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 620720247970829708205779 931080371956244562308669)
      ·
        refine ⟨349155139483591710865751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 931080371956244562308669 349155139483591710865751)
        ·
          refine ⟨523732709225387566298627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 349155139483591710865751 523732709225387566298627)
          ·
            refine ⟨785599063838081349447941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 523732709225387566298627 785599063838081349447941)
            ·
              refine ⟨147299824469640253021489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 785599063838081349447941 147299824469640253021489)
              ·
                refine ⟨110474868352230189766117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 147299824469640253021489 110474868352230189766117)
                ·
                  refine ⟨20714037816043160581147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 110474868352230189766117 20714037816043160581147)
                  ·
                    rfl

theorem cell21_90766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 4, 2, 4].length) (baseStart_90766 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_90766 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_90766 prefixEnd_90766 := by exact prefixLift 90766
  have htrace : WordTrace (prefixWord ++ tailWord_90766) baseStart_90766 baseEnd_90766 := by
    simpa [prefixWord, tailWord_90766, baseEnd_90766] using wordTrace_append hprefix tailTrace_90766
  have hstable : (prefixWord ++ tailWord_90766).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90766).length < 2 ^ (prefixWord ++ tailWord_90766).sum := by decide
  have hdescent : baseEnd_90766 < baseStart_90766 := by decide
  rcases family_descends (prefixWord ++ tailWord_90766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90780 : List Nat := [2, 2, 3, 2, 2, 1, 3, 6]
def baseStart_90780 : Nat := 118140960795 + 90780 * 2 ^ 59
def prefixEnd_90780 : Nat := 4983230072969 + 3 ^ 40 * 90780 * 2
def baseEnd_90780 : Nat := 6905744268927415782595

theorem tailTrace_90780 : CollatzResearch.WordTrace tailWord_90780 prefixEnd_90780 6905744268927415782595 := by
  unfold tailWord_90780
  simp only [CollatzResearch.WordTrace]
  refine ⟨1655509305563519417386897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2207345740751359223182529 1655509305563519417386897)
  ·
    refine ⟨1241631979172639563040173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1655509305563519417386897 1241631979172639563040173)
    ·
      refine ⟨465611992189739836140065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1241631979172639563040173 465611992189739836140065)
      ·
        refine ⟨349208994142304877105049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 465611992189739836140065 349208994142304877105049)
        ·
          refine ⟨261906745606728657828787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 349208994142304877105049 261906745606728657828787)
          ·
            refine ⟨392860118410092986743181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 261906745606728657828787 392860118410092986743181)
            ·
              refine ⟨147322544403784870028693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 392860118410092986743181 147322544403784870028693)
              ·
                refine ⟨6905744268927415782595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 147322544403784870028693 6905744268927415782595)
                ·
                  rfl

theorem cell21_90780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 3, 6].length) (baseStart_90780 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_90780 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_90780 prefixEnd_90780 := by exact prefixLift 90780
  have htrace : WordTrace (prefixWord ++ tailWord_90780) baseStart_90780 baseEnd_90780 := by
    simpa [prefixWord, tailWord_90780, baseEnd_90780] using wordTrace_append hprefix tailTrace_90780
  have hstable : (prefixWord ++ tailWord_90780).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90780).length < 2 ^ (prefixWord ++ tailWord_90780).sum := by decide
  have hdescent : baseEnd_90780 < baseStart_90780 := by decide
  rcases family_descends (prefixWord ++ tailWord_90780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90797 : List Nat := [1, 5, 2, 1, 1, 3, 3, 5]
def baseStart_90797 : Nat := 118140960795 + 90797 * 2 ^ 59
def prefixEnd_90797 : Nat := 4983230072969 + 3 ^ 40 * 90797 * 2
def baseEnd_90797 : Nat := 6907037479464665188139

theorem tailTrace_90797 : CollatzResearch.WordTrace tailWord_90797 prefixEnd_90797 6907037479464665188139 := by
  unfold tailWord_90797
  simp only [CollatzResearch.WordTrace]
  refine ⟨3311638652065450738142645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2207759101376967158761763 3311638652065450738142645)
  ·
    refine ⟨310466123631136006700873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3311638652065450738142645 310466123631136006700873)
    ·
      refine ⟨232849592723352005025655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 310466123631136006700873 232849592723352005025655)
      ·
        refine ⟨349274389085028007538483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232849592723352005025655 349274389085028007538483)
        ·
          refine ⟨523911583627542011307725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 349274389085028007538483 523911583627542011307725)
          ·
            refine ⟨196466843860328254240397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 523911583627542011307725 196466843860328254240397)
            ·
              refine ⟨73675066447623095340149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 196466843860328254240397 73675066447623095340149)
              ·
                refine ⟨6907037479464665188139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 73675066447623095340149 6907037479464665188139)
                ·
                  rfl

theorem cell21_90797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 3, 5].length) (baseStart_90797 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_90797 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_90797 prefixEnd_90797 := by exact prefixLift 90797
  have htrace : WordTrace (prefixWord ++ tailWord_90797) baseStart_90797 baseEnd_90797 := by
    simpa [prefixWord, tailWord_90797, baseEnd_90797] using wordTrace_append hprefix tailTrace_90797
  have hstable : (prefixWord ++ tailWord_90797).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90797).length < 2 ^ (prefixWord ++ tailWord_90797).sum := by decide
  have hdescent : baseEnd_90797 < baseStart_90797 := by decide
  rcases family_descends (prefixWord ++ tailWord_90797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90817 : List Nat := [1, 2, 6, 2, 2, 1, 1, 2, 4]
def baseStart_90817 : Nat := 118140960795 + 90817 * 2 ^ 59
def prefixEnd_90817 : Nat := 4983230072969 + 3 ^ 40 * 90817 * 2
def baseEnd_90817 : Nat := 20725676710878405231043

theorem tailTrace_90817 : CollatzResearch.WordTrace tailWord_90817 prefixEnd_90817 20725676710878405231043 := by
  unfold tailWord_90817
  simp only [CollatzResearch.WordTrace]
  refine ⟨3312368111992994153870705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2208245407995329435913803 3312368111992994153870705)
  ·
    refine ⟨2484276083994745615403029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3312368111992994153870705 2484276083994745615403029)
    ·
      refine ⟨116450441437253700722017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 2484276083994745615403029 116450441437253700722017)
      ·
        refine ⟨87337831077940275541513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116450441437253700722017 87337831077940275541513)
        ·
          refine ⟨65503373308455206656135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87337831077940275541513 65503373308455206656135)
          ·
            refine ⟨98255059962682809984203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65503373308455206656135 98255059962682809984203)
            ·
              refine ⟨147382589944024214976305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98255059962682809984203 147382589944024214976305)
              ·
                refine ⟨110536942458018161232229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 147382589944024214976305 110536942458018161232229)
                ·
                  refine ⟨20725676710878405231043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 110536942458018161232229 20725676710878405231043)
                  ·
                    rfl

theorem cell21_90817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 1, 2, 4].length) (baseStart_90817 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_90817 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_90817 prefixEnd_90817 := by exact prefixLift 90817
  have htrace : WordTrace (prefixWord ++ tailWord_90817) baseStart_90817 baseEnd_90817 := by
    simpa [prefixWord, tailWord_90817, baseEnd_90817] using wordTrace_append hprefix tailTrace_90817
  have hstable : (prefixWord ++ tailWord_90817).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90817).length < 2 ^ (prefixWord ++ tailWord_90817).sum := by decide
  have hdescent : baseEnd_90817 < baseStart_90817 := by decide
  rcases family_descends (prefixWord ++ tailWord_90817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90828 : List Nat := [2, 2, 1, 5, 1, 1, 2, 4, 3]
def baseStart_90828 : Nat := 118140960795 + 90828 * 2 ^ 59
def prefixEnd_90828 : Nat := 4983230072969 + 3 ^ 40 * 90828 * 2
def baseEnd_90828 : Nat := 20728187060744830547687

theorem tailTrace_90828 : CollatzResearch.WordTrace tailWord_90828 prefixEnd_90828 20728187060744830547687 := by
  unfold tailWord_90828
  simp only [CollatzResearch.WordTrace]
  refine ⟨1656384657476571516260569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2208512876635428688347425 1656384657476571516260569)
  ·
    refine ⟨1242288493107428637195427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1656384657476571516260569 1242288493107428637195427)
    ·
      refine ⟨1863432739661142955793141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1242288493107428637195427 1863432739661142955793141)
      ·
        refine ⟨174696819343232152105607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1863432739661142955793141 174696819343232152105607)
        ·
          refine ⟨262045229014848228158411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174696819343232152105607 262045229014848228158411)
          ·
            refine ⟨393067843522272342237617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 262045229014848228158411 393067843522272342237617)
            ·
              refine ⟨294800882641704256678213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 393067843522272342237617 294800882641704256678213)
              ·
                refine ⟨55275165495319548127165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 294800882641704256678213 55275165495319548127165)
                ·
                  refine ⟨20728187060744830547687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55275165495319548127165 20728187060744830547687)
                  ·
                    rfl

theorem cell21_90828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 4, 3].length) (baseStart_90828 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_90828 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_90828 prefixEnd_90828 := by exact prefixLift 90828
  have htrace : WordTrace (prefixWord ++ tailWord_90828) baseStart_90828 baseEnd_90828 := by
    simpa [prefixWord, tailWord_90828, baseEnd_90828] using wordTrace_append hprefix tailTrace_90828
  have hstable : (prefixWord ++ tailWord_90828).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90828).length < 2 ^ (prefixWord ++ tailWord_90828).sum := by decide
  have hdescent : baseEnd_90828 < baseStart_90828 := by decide
  rcases family_descends (prefixWord ++ tailWord_90828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90842 : List Nat := [3, 1, 1, 2, 2, 2, 5, 1, 4]
def baseStart_90842 : Nat := 118140960795 + 90842 * 2 ^ 59
def prefixEnd_90842 : Nat := 4983230072969 + 3 ^ 40 * 90842 * 2
def baseEnd_90842 : Nat := 20731382051483917314325

theorem tailTrace_90842 : CollatzResearch.WordTrace tailWord_90842 prefixEnd_90842 20731382051483917314325 := by
  unfold tailWord_90842
  simp only [CollatzResearch.WordTrace]
  refine ⟨828319984225605855882695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2208853291268282282353853 828319984225605855882695)
  ·
    refine ⟨1242479976338408783824043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 828319984225605855882695 1242479976338408783824043)
    ·
      refine ⟨1863719964507613175736065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1242479976338408783824043 1863719964507613175736065)
      ·
        refine ⟨1397789973380709881802049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1863719964507613175736065 1397789973380709881802049)
        ·
          refine ⟨1048342480035532411351537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1397789973380709881802049 1048342480035532411351537)
          ·
            refine ⟨786256860026649308513653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1048342480035532411351537 786256860026649308513653)
            ·
              refine ⟨73711580627498372673155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 786256860026649308513653 73711580627498372673155)
              ·
                refine ⟨110567370941247559009733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73711580627498372673155 110567370941247559009733)
                ·
                  refine ⟨20731382051483917314325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 110567370941247559009733 20731382051483917314325)
                  ·
                    rfl

theorem cell21_90842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 5, 1, 4].length) (baseStart_90842 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_90842 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_90842 prefixEnd_90842 := by exact prefixLift 90842
  have htrace : WordTrace (prefixWord ++ tailWord_90842) baseStart_90842 baseEnd_90842 := by
    simpa [prefixWord, tailWord_90842, baseEnd_90842] using wordTrace_append hprefix tailTrace_90842
  have hstable : (prefixWord ++ tailWord_90842).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90842).length < 2 ^ (prefixWord ++ tailWord_90842).sum := by decide
  have hdescent : baseEnd_90842 < baseStart_90842 := by decide
  rcases family_descends (prefixWord ++ tailWord_90842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90856 : List Nat := [2, 1, 4, 1, 4, 1, 1, 7]
def baseStart_90856 : Nat := 118140960795 + 90856 * 2 ^ 59
def prefixEnd_90856 : Nat := 4983230072969 + 3 ^ 40 * 90856 * 2
def baseEnd_90856 : Nat := 6911525680741001360321

theorem tailTrace_90856 : CollatzResearch.WordTrace tailWord_90856 prefixEnd_90856 6911525680741001360321 := by
  unfold tailWord_90856
  simp only [CollatzResearch.WordTrace]
  refine ⟨1656895279425851907270211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2209193705901135876360281 1656895279425851907270211)
  ·
    refine ⟨2485342919138777860905317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1656895279425851907270211 2485342919138777860905317)
    ·
      refine ⟨466001797338520848919747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2485342919138777860905317 466001797338520848919747)
      ·
        refine ⟨699002696007781273379621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 466001797338520848919747 699002696007781273379621)
        ·
          refine ⟨131063005501458988758679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 699002696007781273379621 131063005501458988758679)
          ·
            refine ⟨196594508252188483138019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131063005501458988758679 196594508252188483138019)
            ·
              refine ⟨294891762378282724707029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 196594508252188483138019 294891762378282724707029)
              ·
                refine ⟨6911525680741001360321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 294891762378282724707029 6911525680741001360321)
                ·
                  rfl

theorem cell21_90856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 7].length) (baseStart_90856 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_90856 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_90856 prefixEnd_90856 := by exact prefixLift 90856
  have htrace : WordTrace (prefixWord ++ tailWord_90856) baseStart_90856 baseEnd_90856 := by
    simpa [prefixWord, tailWord_90856, baseEnd_90856] using wordTrace_append hprefix tailTrace_90856
  have hstable : (prefixWord ++ tailWord_90856).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90856).length < 2 ^ (prefixWord ++ tailWord_90856).sum := by decide
  have hdescent : baseEnd_90856 < baseStart_90856 := by decide
  rcases family_descends (prefixWord ++ tailWord_90856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90887 : List Nat := [1, 1, 4, 4, 1, 1, 3, 1, 5]
def baseStart_90887 : Nat := 118140960795 + 90887 * 2 ^ 59
def prefixEnd_90887 : Nat := 4983230072969 + 3 ^ 40 * 90887 * 2
def baseEnd_90887 : Nat := 20741651664573839064233

theorem tailTrace_90887 : CollatzResearch.WordTrace tailWord_90887 prefixEnd_90887 20741651664573839064233 := by
  unfold tailWord_90887
  simp only [CollatzResearch.WordTrace]
  refine ⟨3314921221739396108918915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2209947481159597405945943 3314921221739396108918915)
  ·
    refine ⟨4972381832609094163378373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3314921221739396108918915 4972381832609094163378373)
    ·
      refine ⟨932321593614205155633445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4972381832609094163378373 932321593614205155633445)
      ·
        refine ⟨174810298802663466681271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 932321593614205155633445 174810298802663466681271)
        ·
          refine ⟨262215448203995200021907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174810298802663466681271 262215448203995200021907)
          ·
            refine ⟨393323172305992800032861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 262215448203995200021907 393323172305992800032861)
            ·
              refine ⟨147496189614747300012323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 393323172305992800032861 147496189614747300012323)
              ·
                refine ⟨221244284422120950018485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 147496189614747300012323 221244284422120950018485)
                ·
                  refine ⟨20741651664573839064233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 221244284422120950018485 20741651664573839064233)
                  ·
                    rfl

theorem cell21_90887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 3, 1, 5].length) (baseStart_90887 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_90887 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_90887 prefixEnd_90887 := by exact prefixLift 90887
  have htrace : WordTrace (prefixWord ++ tailWord_90887) baseStart_90887 baseEnd_90887 := by
    simpa [prefixWord, tailWord_90887, baseEnd_90887] using wordTrace_append hprefix tailTrace_90887
  have hstable : (prefixWord ++ tailWord_90887).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90887).length < 2 ^ (prefixWord ++ tailWord_90887).sum := by decide
  have hdescent : baseEnd_90887 < baseStart_90887 := by decide
  rcases family_descends (prefixWord ++ tailWord_90887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90901 : List Nat := [1, 3, 2, 1, 2, 2, 3, 3, 4]
def baseStart_90901 : Nat := 118140960795 + 90901 * 2 ^ 59
def prefixEnd_90901 : Nat := 4983230072969 + 3 ^ 40 * 90901 * 2
def baseEnd_90901 : Nat := 20744846655312925830871

theorem tailTrace_90901 : CollatzResearch.WordTrace tailWord_90901 prefixEnd_90901 20744846655312925830871 := by
  unfold tailWord_90901
  simp only [CollatzResearch.WordTrace]
  refine ⟨3315431843688676499928557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2210287895792450999952371 3315431843688676499928557)
  ·
    refine ⟨1243286941383253687473209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3315431843688676499928557 1243286941383253687473209)
    ·
      refine ⟨932465206037440265604907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1243286941383253687473209 932465206037440265604907)
      ·
        refine ⟨1398697809056160398407361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 932465206037440265604907 1398697809056160398407361)
        ·
          refine ⟨1049023356792120298805521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1398697809056160398407361 1049023356792120298805521)
          ·
            refine ⟨786767517594090224104141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1049023356792120298805521 786767517594090224104141)
            ·
              refine ⟨295037819097783834039053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 786767517594090224104141 295037819097783834039053)
              ·
                refine ⟨110639182161668937764645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 295037819097783834039053 110639182161668937764645)
                ·
                  refine ⟨20744846655312925830871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 110639182161668937764645 20744846655312925830871)
                  ·
                    rfl

theorem cell21_90901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 3, 4].length) (baseStart_90901 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_90901 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_90901 prefixEnd_90901 := by exact prefixLift 90901
  have htrace : WordTrace (prefixWord ++ tailWord_90901) baseStart_90901 baseEnd_90901 := by
    simpa [prefixWord, tailWord_90901, baseEnd_90901] using wordTrace_append hprefix tailTrace_90901
  have hstable : (prefixWord ++ tailWord_90901).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90901).length < 2 ^ (prefixWord ++ tailWord_90901).sum := by decide
  have hdescent : baseEnd_90901 < baseStart_90901 := by decide
  rcases family_descends (prefixWord ++ tailWord_90901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90932 : List Nat := [2, 5, 1, 1, 3, 9]
def baseStart_90932 : Nat := 118140960795 + 90932 * 2 ^ 59
def prefixEnd_90932 : Nat := 4983230072969 + 3 ^ 40 * 90932 * 2
def baseEnd_90932 : Nat := 768589676950509659783

theorem tailTrace_90932 : CollatzResearch.WordTrace tailWord_90932 prefixEnd_90932 768589676950509659783 := by
  unfold tailWord_90932
  simp only [CollatzResearch.WordTrace]
  refine ⟨1658281253288184397153525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2211041671050912529538033 1658281253288184397153525)
  ·
    refine ⟨155463867495767287233143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1658281253288184397153525 155463867495767287233143)
    ·
      refine ⟨233195801243650930849715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155463867495767287233143 233195801243650930849715)
      ·
        refine ⟨349793701865476396274573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233195801243650930849715 349793701865476396274573)
        ·
          refine ⟨131172638199553648602965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 349793701865476396274573 131172638199553648602965)
          ·
            refine ⟨768589676950509659783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 131172638199553648602965 768589676950509659783)
            ·
              rfl

theorem cell21_90932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 9].length) (baseStart_90932 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_90932 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_90932 prefixEnd_90932 := by exact prefixLift 90932
  have htrace : WordTrace (prefixWord ++ tailWord_90932) baseStart_90932 baseEnd_90932 := by
    simpa [prefixWord, tailWord_90932, baseEnd_90932] using wordTrace_append hprefix tailTrace_90932
  have hstable : (prefixWord ++ tailWord_90932).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90932).length < 2 ^ (prefixWord ++ tailWord_90932).sum := by decide
  have hdescent : baseEnd_90932 < baseStart_90932 := by decide
  rcases family_descends (prefixWord ++ tailWord_90932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90938 : List Nat := [3, 1, 1, 1, 7, 1, 2, 2, 3]
def baseStart_90938 : Nat := 118140960795 + 90938 * 2 ^ 59
def prefixEnd_90938 : Nat := 4983230072969 + 3 ^ 40 * 90938 * 2
def baseEnd_90938 : Nat := 20753290559409083714129

theorem tailTrace_90938 : CollatzResearch.WordTrace tailWord_90938 prefixEnd_90938 20753290559409083714129 := by
  unfold tailWord_90938
  simp only [CollatzResearch.WordTrace]
  refine ⟨829195336138657954756367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2211187563036421212683645 829195336138657954756367)
  ·
    refine ⟨1243793004207986932134551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 829195336138657954756367 1243793004207986932134551)
    ·
      refine ⟨1865689506311980398201827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1243793004207986932134551 1865689506311980398201827)
      ·
        refine ⟨2798534259467970597302741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1865689506311980398201827 2798534259467970597302741)
        ·
          refine ⟨65590646706280560874283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 2798534259467970597302741 65590646706280560874283)
          ·
            refine ⟨98385970059420841311425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65590646706280560874283 98385970059420841311425)
            ·
              refine ⟨73789477544565630983569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98385970059420841311425 73789477544565630983569)
              ·
                refine ⟨55342108158424223237677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73789477544565630983569 55342108158424223237677)
                ·
                  refine ⟨20753290559409083714129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55342108158424223237677 20753290559409083714129)
                  ·
                    rfl

theorem cell21_90938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 2, 2, 3].length) (baseStart_90938 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_90938 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_90938 prefixEnd_90938 := by exact prefixLift 90938
  have htrace : WordTrace (prefixWord ++ tailWord_90938) baseStart_90938 baseEnd_90938 := by
    simpa [prefixWord, tailWord_90938, baseEnd_90938] using wordTrace_append hprefix tailTrace_90938
  have hstable : (prefixWord ++ tailWord_90938).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90938).length < 2 ^ (prefixWord ++ tailWord_90938).sum := by decide
  have hdescent : baseEnd_90938 < baseStart_90938 := by decide
  rcases family_descends (prefixWord ++ tailWord_90938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_90980 : List Nat := [2, 3, 1, 1, 4, 2, 2, 3, 3]
def baseStart_90980 : Nat := 118140960795 + 90980 * 2 ^ 59
def prefixEnd_90980 : Nat := 4983230072969 + 3 ^ 40 * 90980 * 2
def baseEnd_90980 : Nat := 20762875531626344014043

theorem tailTrace_90980 : CollatzResearch.WordTrace tailWord_90980 prefixEnd_90980 20762875531626344014043 := by
  unfold tailWord_90980
  simp only [CollatzResearch.WordTrace]
  refine ⟨1659156605201236496027197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2212208806934981994702929 1659156605201236496027197)
  ·
    refine ⟨622183726950463686010199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1659156605201236496027197 622183726950463686010199)
    ·
      refine ⟨933275590425695529015299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 622183726950463686010199 933275590425695529015299)
      ·
        refine ⟨1399913385638543293522949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 933275590425695529015299 1399913385638543293522949)
        ·
          refine ⟨262483759807226867535553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1399913385638543293522949 262483759807226867535553)
          ·
            refine ⟨196862819855420150651665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 262483759807226867535553 196862819855420150651665)
            ·
              refine ⟨147647114891565112988749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 196862819855420150651665 147647114891565112988749)
              ·
                refine ⟨55367668084336917370781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 147647114891565112988749 55367668084336917370781)
                ·
                  refine ⟨20762875531626344014043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55367668084336917370781 20762875531626344014043)
                  ·
                    rfl

theorem cell21_90980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 2, 3, 3].length) (baseStart_90980 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_90980 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_90980 prefixEnd_90980 := by exact prefixLift 90980
  have htrace : WordTrace (prefixWord ++ tailWord_90980) baseStart_90980 baseEnd_90980 := by
    simpa [prefixWord, tailWord_90980, baseEnd_90980] using wordTrace_append hprefix tailTrace_90980
  have hstable : (prefixWord ++ tailWord_90980).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_90980).length < 2 ^ (prefixWord ++ tailWord_90980).sum := by decide
  have hdescent : baseEnd_90980 < baseStart_90980 := by decide
  rcases family_descends (prefixWord ++ tailWord_90980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91062 : List Nat := [5, 1, 4, 1, 1, 2, 2, 1, 4]
def baseStart_91062 : Nat := 118140960795 + 91062 * 2 ^ 59
def prefixEnd_91062 : Nat := 4983230072969 + 3 ^ 40 * 91062 * 2
def baseEnd_91062 : Nat := 20781589048812423647209

theorem tailTrace_91062 : CollatzResearch.WordTrace tailWord_91062 prefixEnd_91062 20781589048812423647209 := by
  unfold tailWord_91062
  simp only [CollatzResearch.WordTrace]
  refine ⟨207581499756587562283715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2214202664070267331026293 207581499756587562283715)
  ·
    refine ⟨311372249634881343425573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207581499756587562283715 311372249634881343425573)
    ·
      refine ⟨58382296806540251892295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 311372249634881343425573 58382296806540251892295)
      ·
        refine ⟨87573445209810377838443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58382296806540251892295 87573445209810377838443)
        ·
          refine ⟨131360167814715566757665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87573445209810377838443 131360167814715566757665)
          ·
            refine ⟨98520125861036675068249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131360167814715566757665 98520125861036675068249)
            ·
              refine ⟨73890094395777506301187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98520125861036675068249 73890094395777506301187)
              ·
                refine ⟨110835141593666259451781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73890094395777506301187 110835141593666259451781)
                ·
                  refine ⟨20781589048812423647209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 110835141593666259451781 20781589048812423647209)
                  ·
                    rfl

theorem cell21_91062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 2, 1, 4].length) (baseStart_91062 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_91062 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_91062 prefixEnd_91062 := by exact prefixLift 91062
  have htrace : WordTrace (prefixWord ++ tailWord_91062) baseStart_91062 baseEnd_91062 := by
    simpa [prefixWord, tailWord_91062, baseEnd_91062] using wordTrace_append hprefix tailTrace_91062
  have hstable : (prefixWord ++ tailWord_91062).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91062).length < 2 ^ (prefixWord ++ tailWord_91062).sum := by decide
  have hdescent : baseEnd_91062 < baseStart_91062 := by decide
  rcases family_descends (prefixWord ++ tailWord_91062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91112 : List Nat := [2, 1, 4, 1, 1, 1, 2, 3, 6]
def baseStart_91112 : Nat := 118140960795 + 91112 * 2 ^ 59
def prefixEnd_91112 : Nat := 4983230072969 + 3 ^ 40 * 91112 * 2
def baseEnd_91112 : Nat := 20792999730023447813773

theorem tailTrace_91112 : CollatzResearch.WordTrace tailWord_91112 prefixEnd_91112 20792999730023447813773 := by
  unfold tailWord_91112
  simp only [CollatzResearch.WordTrace]
  refine ⟨1661563822962129767929795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2215418430616173023906393 1661563822962129767929795)
  ·
    refine ⟨2492345734443194651894693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1661563822962129767929795 2492345734443194651894693)
    ·
      refine ⟨467314825208098997230255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2492345734443194651894693 467314825208098997230255)
      ·
        refine ⟨700972237812148495845383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 467314825208098997230255 700972237812148495845383)
        ·
          refine ⟨1051458356718222743768075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 700972237812148495845383 1051458356718222743768075)
          ·
            refine ⟨1577187535077334115652113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1051458356718222743768075 1577187535077334115652113)
            ·
              refine ⟨1182890651308000586739085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1577187535077334115652113 1182890651308000586739085)
              ·
                refine ⟨443583994240500220027157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1182890651308000586739085 443583994240500220027157)
                ·
                  refine ⟨20792999730023447813773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 443583994240500220027157 20792999730023447813773)
                  ·
                    rfl

theorem cell21_91112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 3, 6].length) (baseStart_91112 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_91112 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_91112 prefixEnd_91112 := by exact prefixLift 91112
  have htrace : WordTrace (prefixWord ++ tailWord_91112) baseStart_91112 baseEnd_91112 := by
    simpa [prefixWord, tailWord_91112, baseEnd_91112] using wordTrace_append hprefix tailTrace_91112
  have hstable : (prefixWord ++ tailWord_91112).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91112).length < 2 ^ (prefixWord ++ tailWord_91112).sum := by decide
  have hdescent : baseEnd_91112 < baseStart_91112 := by decide
  rcases family_descends (prefixWord ++ tailWord_91112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91318 : List Nat := [5, 1, 3, 2, 1, 1, 2, 3, 3]
def baseStart_91318 : Nat := 118140960795 + 91318 * 2 ^ 59
def prefixEnd_91318 : Nat := 4983230072969 + 3 ^ 40 * 91318 * 2
def baseEnd_91318 : Nat := 20840011736612867380019

theorem tailTrace_91318 : CollatzResearch.WordTrace tailWord_91318 prefixEnd_91318 20840011736612867380019 := by
  unfold tailWord_91318
  simp only [CollatzResearch.WordTrace]
  refine ⟨208165067698622294866163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2220427388785304478572405 208165067698622294866163)
  ·
    refine ⟨312247601547933442299245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 208165067698622294866163 312247601547933442299245)
    ·
      refine ⟨117092850580475040862217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 312247601547933442299245 117092850580475040862217)
      ·
        refine ⟨87819637935356280646663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117092850580475040862217 87819637935356280646663)
        ·
          refine ⟨131729456903034420969995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87819637935356280646663 131729456903034420969995)
          ·
            refine ⟨197594185354551631454993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131729456903034420969995 197594185354551631454993)
            ·
              refine ⟨148195639015913723591245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 197594185354551631454993 148195639015913723591245)
              ·
                refine ⟨55573364630967646346717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 148195639015913723591245 55573364630967646346717)
                ·
                  refine ⟨20840011736612867380019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55573364630967646346717 20840011736612867380019)
                  ·
                    rfl

theorem cell21_91318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 2, 3, 3].length) (baseStart_91318 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_91318 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_91318 prefixEnd_91318 := by exact prefixLift 91318
  have htrace : WordTrace (prefixWord ++ tailWord_91318) baseStart_91318 baseEnd_91318 := by
    simpa [prefixWord, tailWord_91318, baseEnd_91318] using wordTrace_append hprefix tailTrace_91318
  have hstable : (prefixWord ++ tailWord_91318).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91318).length < 2 ^ (prefixWord ++ tailWord_91318).sum := by decide
  have hdescent : baseEnd_91318 < baseStart_91318 := by decide
  rcases family_descends (prefixWord ++ tailWord_91318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91354 : List Nat := [3, 1, 1, 2, 2, 1, 1, 10]
def baseStart_91354 : Nat := 118140960795 + 91354 * 2 ^ 59
def prefixEnd_91354 : Nat := 4983230072969 + 3 ^ 40 * 91354 * 2
def baseEnd_91354 : Nat := 6949409142361601593315

theorem tailTrace_91354 : CollatzResearch.WordTrace tailWord_91354 prefixEnd_91354 6949409142361601593315 := by
  unfold tailWord_91354
  simp only [CollatzResearch.WordTrace]
  refine ⟨832988527761883716542279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2221302740698356577446077 832988527761883716542279)
  ·
    refine ⟨1249482791642825574813419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 832988527761883716542279 1249482791642825574813419)
    ·
      refine ⟨1874224187464238362220129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1249482791642825574813419 1874224187464238362220129)
      ·
        refine ⟨1405668140598178771665097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1874224187464238362220129 1405668140598178771665097)
        ·
          refine ⟨1054251105448634078748823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1405668140598178771665097 1054251105448634078748823)
          ·
            refine ⟨1581376658172951118123235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1054251105448634078748823 1581376658172951118123235)
            ·
              refine ⟨2372064987259426677184853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1581376658172951118123235 2372064987259426677184853)
              ·
                refine ⟨6949409142361601593315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 2372064987259426677184853 6949409142361601593315)
                ·
                  rfl

theorem cell21_91354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 10].length) (baseStart_91354 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_91354 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_91354 prefixEnd_91354 := by exact prefixLift 91354
  have htrace : WordTrace (prefixWord ++ tailWord_91354) baseStart_91354 baseEnd_91354 := by
    simpa [prefixWord, tailWord_91354, baseEnd_91354] using wordTrace_append hprefix tailTrace_91354
  have hstable : (prefixWord ++ tailWord_91354).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91354).length < 2 ^ (prefixWord ++ tailWord_91354).sum := by decide
  have hdescent : baseEnd_91354 < baseStart_91354 := by decide
  rcases family_descends (prefixWord ++ tailWord_91354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91371 : List Nat := [1, 1, 1, 1, 2, 6, 4, 5]
def baseStart_91371 : Nat := 118140960795 + 91371 * 2 ^ 59
def prefixEnd_91371 : Nat := 4983230072969 + 3 ^ 40 * 91371 * 2
def baseEnd_91371 : Nat := 6950702352898850998859

theorem tailTrace_91371 : CollatzResearch.WordTrace tailWord_91371 prefixEnd_91371 6950702352898850998859 := by
  unfold tailWord_91371
  simp only [CollatzResearch.WordTrace]
  refine ⟨3332574151985946769537967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2221716101323964513025311 3332574151985946769537967)
  ·
    refine ⟨4998861227978920154306951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3332574151985946769537967 4998861227978920154306951)
    ·
      refine ⟨7498291841968380231460427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4998861227978920154306951 7498291841968380231460427)
      ·
        refine ⟨11247437762952570347190641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7498291841968380231460427 11247437762952570347190641)
        ·
          refine ⟨8435578322214427760392981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11247437762952570347190641 8435578322214427760392981)
          ·
            refine ⟨395417733853801301268421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 8435578322214427760392981 395417733853801301268421)
            ·
              refine ⟨74140825097587743987829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 395417733853801301268421 74140825097587743987829)
              ·
                refine ⟨6950702352898850998859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 74140825097587743987829 6950702352898850998859)
                ·
                  rfl

theorem cell21_91371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 4, 5].length) (baseStart_91371 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_91371 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_91371 prefixEnd_91371 := by exact prefixLift 91371
  have htrace : WordTrace (prefixWord ++ tailWord_91371) baseStart_91371 baseEnd_91371 := by
    simpa [prefixWord, tailWord_91371, baseEnd_91371] using wordTrace_append hprefix tailTrace_91371
  have hstable : (prefixWord ++ tailWord_91371).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91371).length < 2 ^ (prefixWord ++ tailWord_91371).sum := by decide
  have hdescent : baseEnd_91371 < baseStart_91371 := by decide
  rcases family_descends (prefixWord ++ tailWord_91371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91388 : List Nat := [2, 2, 2, 1, 6, 1, 7]
def baseStart_91388 : Nat := 118140960795 + 91388 * 2 ^ 59
def prefixEnd_91388 : Nat := 4983230072969 + 3 ^ 40 * 91388 * 2
def baseEnd_91388 : Nat := 2317331854478700134801

theorem tailTrace_91388 : CollatzResearch.WordTrace tailWord_91388 prefixEnd_91388 2317331854478700134801 := by
  unfold tailWord_91388
  simp only [CollatzResearch.WordTrace]
  refine ⟨1666597096462179336453409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2222129461949572448604545 1666597096462179336453409)
  ·
    refine ⟨1249947822346634502340057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1666597096462179336453409 1249947822346634502340057)
    ·
      refine ⟨937460866759975876755043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1249947822346634502340057 937460866759975876755043)
      ·
        refine ⟨1406191300139963815132565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 937460866759975876755043 1406191300139963815132565)
        ·
          refine ⟨65915217194060803834339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 1406191300139963815132565 65915217194060803834339)
          ·
            refine ⟨98872825791091205751509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65915217194060803834339 98872825791091205751509)
            ·
              refine ⟨2317331854478700134801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 98872825791091205751509 2317331854478700134801)
              ·
                rfl

theorem cell21_91388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 7].length) (baseStart_91388 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_91388 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_91388 prefixEnd_91388 := by exact prefixLift 91388
  have htrace : WordTrace (prefixWord ++ tailWord_91388) baseStart_91388 baseEnd_91388 := by
    simpa [prefixWord, tailWord_91388, baseEnd_91388] using wordTrace_append hprefix tailTrace_91388
  have hstable : (prefixWord ++ tailWord_91388).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91388).length < 2 ^ (prefixWord ++ tailWord_91388).sum := by decide
  have hdescent : baseEnd_91388 < baseStart_91388 := by decide
  rcases family_descends (prefixWord ++ tailWord_91388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91506 : List Nat := [3, 2, 1, 2, 1, 2, 10]
def baseStart_91506 : Nat := 118140960795 + 91506 * 2 ^ 59
def prefixEnd_91506 : Nat := 4983230072969 + 3 ^ 40 * 91506 * 2
def baseEnd_91506 : Nat := 2320323988662924249589

theorem tailTrace_91506 : CollatzResearch.WordTrace tailWord_91506 prefixEnd_91506 2320323988662924249589 := by
  unfold tailWord_91506
  simp only [CollatzResearch.WordTrace]
  refine ⟨834374501624216206425593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2224998670997909883801581 834374501624216206425593)
  ·
    refine ⟨625780876218162154819195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 834374501624216206425593 625780876218162154819195)
    ·
      refine ⟨938671314327243232228793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 625780876218162154819195 938671314327243232228793)
      ·
        refine ⟨704003485745432424171595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 938671314327243232228793 704003485745432424171595)
        ·
          refine ⟨1056005228618148636257393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 704003485745432424171595 1056005228618148636257393)
          ·
            refine ⟨792003921463611477193045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1056005228618148636257393 792003921463611477193045)
            ·
              refine ⟨2320323988662924249589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 792003921463611477193045 2320323988662924249589)
              ·
                rfl

theorem cell21_91506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 10].length) (baseStart_91506 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_91506 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_91506 prefixEnd_91506 := by exact prefixLift 91506
  have htrace : WordTrace (prefixWord ++ tailWord_91506) baseStart_91506 baseEnd_91506 := by
    simpa [prefixWord, tailWord_91506, baseEnd_91506] using wordTrace_append hprefix tailTrace_91506
  have hstable : (prefixWord ++ tailWord_91506).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91506).length < 2 ^ (prefixWord ++ tailWord_91506).sum := by decide
  have hdescent : baseEnd_91506 < baseStart_91506 := by decide
  rcases family_descends (prefixWord ++ tailWord_91506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91509 : List Nat := [1, 3, 4, 1, 3, 1, 1, 1, 6]
def baseStart_91509 : Nat := 118140960795 + 91509 * 2 ^ 59
def prefixEnd_91509 : Nat := 4983230072969 + 3 ^ 40 * 91509 * 2
def baseEnd_91509 : Nat := 20883600538838979696295

theorem tailTrace_91509 : CollatzResearch.WordTrace tailWord_91509 prefixEnd_91509 20883600538838979696295 := by
  unfold tailWord_91509
  simp only [CollatzResearch.WordTrace]
  refine ⟨3337607425485996338061581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2225071616990664225374387 3337607425485996338061581)
  ·
    refine ⟨1251602784557248626773093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3337607425485996338061581 1251602784557248626773093)
    ·
      refine ⟨234675522104484117519955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1251602784557248626773093 234675522104484117519955)
      ·
        refine ⟨352013283156726176279933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234675522104484117519955 352013283156726176279933)
        ·
          refine ⟨132004981183772316104975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 352013283156726176279933 132004981183772316104975)
          ·
            refine ⟨198007471775658474157463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132004981183772316104975 198007471775658474157463)
            ·
              refine ⟨297011207663487711236195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 198007471775658474157463 297011207663487711236195)
              ·
                refine ⟨445516811495231566854293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 297011207663487711236195 445516811495231566854293)
                ·
                  refine ⟨20883600538838979696295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 445516811495231566854293 20883600538838979696295)
                  ·
                    rfl

theorem cell21_91509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 1, 6].length) (baseStart_91509 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_91509 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_91509 prefixEnd_91509 := by exact prefixLift 91509
  have htrace : WordTrace (prefixWord ++ tailWord_91509) baseStart_91509 baseEnd_91509 := by
    simpa [prefixWord, tailWord_91509, baseEnd_91509] using wordTrace_append hprefix tailTrace_91509
  have hstable : (prefixWord ++ tailWord_91509).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91509).length < 2 ^ (prefixWord ++ tailWord_91509).sum := by decide
  have hdescent : baseEnd_91509 < baseStart_91509 := by decide
  rcases family_descends (prefixWord ++ tailWord_91509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91540 : List Nat := [2, 4, 2, 1, 2, 1, 4, 5]
def baseStart_91540 : Nat := 118140960795 + 91540 * 2 ^ 59
def prefixEnd_91540 : Nat := 4983230072969 + 3 ^ 40 * 91540 * 2
def baseEnd_91540 : Nat := 6963558387063271559855

theorem tailTrace_91540 : CollatzResearch.WordTrace tailWord_91540 prefixEnd_91540 6963558387063271559855 := by
  unfold tailWord_91540
  simp only [CollatzResearch.WordTrace]
  refine ⟨1669369044186844316220037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2225825392249125754960049 1669369044186844316220037)
  ·
    refine ⟨313006695785033309291257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1669369044186844316220037 313006695785033309291257)
    ·
      refine ⟨234755021838774981968443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 313006695785033309291257 234755021838774981968443)
      ·
        refine ⟨352132532758162472952665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234755021838774981968443 352132532758162472952665)
        ·
          refine ⟨264099399568621854714499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 352132532758162472952665 264099399568621854714499)
          ·
            refine ⟨396149099352932782071749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 264099399568621854714499 396149099352932782071749)
            ·
              refine ⟨74277956128674896638453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 396149099352932782071749 74277956128674896638453)
              ·
                refine ⟨6963558387063271559855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 74277956128674896638453 6963558387063271559855)
                ·
                  rfl

theorem cell21_91540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 4, 5].length) (baseStart_91540 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_91540 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_91540 prefixEnd_91540 := by exact prefixLift 91540
  have htrace : WordTrace (prefixWord ++ tailWord_91540) baseStart_91540 baseEnd_91540 := by
    simpa [prefixWord, tailWord_91540, baseEnd_91540] using wordTrace_append hprefix tailTrace_91540
  have hstable : (prefixWord ++ tailWord_91540).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91540).length < 2 ^ (prefixWord ++ tailWord_91540).sum := by decide
  have hdescent : baseEnd_91540 < baseStart_91540 := by decide
  rcases family_descends (prefixWord ++ tailWord_91540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91644 : List Nat := [2, 2, 2, 1, 2, 1, 4, 3, 4]
def baseStart_91644 : Nat := 118140960795 + 91644 * 2 ^ 59
def prefixEnd_91644 : Nat := 4983230072969 + 3 ^ 40 * 91644 * 2
def baseEnd_91644 : Nat := 20914409378108744946019

theorem tailTrace_91644 : CollatzResearch.WordTrace tailWord_91644 prefixEnd_91644 20914409378108744946019 := by
  unfold tailWord_91644
  simp only [CollatzResearch.WordTrace]
  refine ⟨1671265639998457197112993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2228354186664609596150657 1671265639998457197112993)
  ·
    refine ⟨1253449229998842897834745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1671265639998457197112993 1253449229998842897834745)
    ·
      refine ⟨940086922499132173376059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1253449229998842897834745 940086922499132173376059)
      ·
        refine ⟨1410130383748698260064089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 940086922499132173376059 1410130383748698260064089)
        ·
          refine ⟨1057597787811523695048067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1410130383748698260064089 1057597787811523695048067)
          ·
            refine ⟨1586396681717285542572101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1057597787811523695048067 1586396681717285542572101)
            ·
              refine ⟨297449377821991039232269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1586396681717285542572101 297449377821991039232269)
              ·
                refine ⟨111543516683246639712101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 297449377821991039232269 111543516683246639712101)
                ·
                  refine ⟨20914409378108744946019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 111543516683246639712101 20914409378108744946019)
                  ·
                    rfl

theorem cell21_91644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 3, 4].length) (baseStart_91644 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_91644 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_91644 prefixEnd_91644 := by exact prefixLift 91644
  have htrace : WordTrace (prefixWord ++ tailWord_91644) baseStart_91644 baseEnd_91644 := by
    simpa [prefixWord, tailWord_91644, baseEnd_91644] using wordTrace_append hprefix tailTrace_91644
  have hstable : (prefixWord ++ tailWord_91644).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91644).length < 2 ^ (prefixWord ++ tailWord_91644).sum := by decide
  have hdescent : baseEnd_91644 < baseStart_91644 := by decide
  rcases family_descends (prefixWord ++ tailWord_91644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91709 : List Nat := [1, 4, 1, 3, 4, 1, 2, 5]
def baseStart_91709 : Nat := 118140960795 + 91709 * 2 ^ 59
def prefixEnd_91709 : Nat := 4983230072969 + 3 ^ 40 * 91709 * 2
def baseEnd_91709 : Nat := 6976414421227692120851

theorem tailTrace_91709 : CollatzResearch.WordTrace tailWord_91709 prefixEnd_91709 6976414421227692120851 := by
  unfold tailWord_91709
  simp only [CollatzResearch.WordTrace]
  refine ⟨3344902024761430495342181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2229934683174286996894787 3344902024761430495342181)
  ·
    refine ⟨627169129642768217876659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3344902024761430495342181 627169129642768217876659)
    ·
      refine ⟨940753694464152326814989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 627169129642768217876659 940753694464152326814989)
      ·
        refine ⟨352782635424057122555621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 940753694464152326814989 352782635424057122555621)
        ·
          refine ⟨66146744142010710479179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 352782635424057122555621 66146744142010710479179)
          ·
            refine ⟨99220116213016065718769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66146744142010710479179 99220116213016065718769)
            ·
              refine ⟨74415087159762049289077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99220116213016065718769 74415087159762049289077)
              ·
                refine ⟨6976414421227692120851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 74415087159762049289077 6976414421227692120851)
                ·
                  rfl

theorem cell21_91709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 2, 5].length) (baseStart_91709 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_91709 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_91709 prefixEnd_91709 := by exact prefixLift 91709
  have htrace : WordTrace (prefixWord ++ tailWord_91709) baseStart_91709 baseEnd_91709 := by
    simpa [prefixWord, tailWord_91709, baseEnd_91709] using wordTrace_append hprefix tailTrace_91709
  have hstable : (prefixWord ++ tailWord_91709).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91709).length < 2 ^ (prefixWord ++ tailWord_91709).sum := by decide
  have hdescent : baseEnd_91709 < baseStart_91709 := by decide
  rcases family_descends (prefixWord ++ tailWord_91709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91740 : List Nat := [2, 2, 4, 1, 2, 2, 3, 2, 3]
def baseStart_91740 : Nat := 118140960795 + 91740 * 2 ^ 59
def prefixEnd_91740 : Nat := 4983230072969 + 3 ^ 40 * 91740 * 2
def baseEnd_91740 : Nat := 20936317886033911345823

theorem tailTrace_91740 : CollatzResearch.WordTrace tailWord_91740 prefixEnd_91740 20936317886033911345823 := by
  unfold tailWord_91740
  simp only [CollatzResearch.WordTrace]
  refine ⟨1673016343824561394860337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2230688458432748526480449 1673016343824561394860337)
  ·
    refine ⟨1254762257868421046145253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1673016343824561394860337 1254762257868421046145253)
    ·
      refine ⟨235267923350328946152235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1254762257868421046145253 235267923350328946152235)
      ·
        refine ⟨352901885025493419228353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235267923350328946152235 352901885025493419228353)
        ·
          refine ⟨264676413769120064421265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 352901885025493419228353 264676413769120064421265)
          ·
            refine ⟨198507310326840048315949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 264676413769120064421265 198507310326840048315949)
            ·
              refine ⟨74440241372565018118481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 198507310326840048315949 74440241372565018118481)
              ·
                refine ⟨55830181029423763588861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74440241372565018118481 55830181029423763588861)
                ·
                  refine ⟨20936317886033911345823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55830181029423763588861 20936317886033911345823)
                  ·
                    rfl

theorem cell21_91740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 3, 2, 3].length) (baseStart_91740 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_91740 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_91740 prefixEnd_91740 := by exact prefixLift 91740
  have htrace : WordTrace (prefixWord ++ tailWord_91740) baseStart_91740 baseEnd_91740 := by
    simpa [prefixWord, tailWord_91740, baseEnd_91740] using wordTrace_append hprefix tailTrace_91740
  have hstable : (prefixWord ++ tailWord_91740).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91740).length < 2 ^ (prefixWord ++ tailWord_91740).sum := by decide
  have hdescent : baseEnd_91740 < baseStart_91740 := by decide
  rcases family_descends (prefixWord ++ tailWord_91740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91754 : List Nat := [3, 1, 3, 2, 1, 4, 2, 1, 4]
def baseStart_91754 : Nat := 118140960795 + 91754 * 2 ^ 59
def prefixEnd_91754 : Nat := 4983230072969 + 3 ^ 40 * 91754 * 2
def baseEnd_91754 : Nat := 20939512876772998112461

theorem tailTrace_91754 : CollatzResearch.WordTrace tailWord_91754 prefixEnd_91754 20939512876772998112461 := by
  unfold tailWord_91754
  simp only [CollatzResearch.WordTrace]
  refine ⟨836635827399600795182579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2231028873065602120486877 836635827399600795182579)
  ·
    refine ⟨1254953741099401192773869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 836635827399600795182579 1254953741099401192773869)
    ·
      refine ⟨470607652912275447290201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1254953741099401192773869 470607652912275447290201)
      ·
        refine ⟨352955739684206585467651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 470607652912275447290201 352955739684206585467651)
        ·
          refine ⟨529433609526309878201477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 352955739684206585467651 529433609526309878201477)
          ·
            refine ⟨99268801786183102162777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 529433609526309878201477 99268801786183102162777)
            ·
              refine ⟨74451601339637326622083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99268801786183102162777 74451601339637326622083)
              ·
                refine ⟨111677402009455989933125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74451601339637326622083 111677402009455989933125)
                ·
                  refine ⟨20939512876772998112461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 111677402009455989933125 20939512876772998112461)
                  ·
                    rfl

theorem cell21_91754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 2, 1, 4].length) (baseStart_91754 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_91754 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_91754 prefixEnd_91754 := by exact prefixLift 91754
  have htrace : WordTrace (prefixWord ++ tailWord_91754) baseStart_91754 baseEnd_91754 := by
    simpa [prefixWord, tailWord_91754, baseEnd_91754] using wordTrace_append hprefix tailTrace_91754
  have hstable : (prefixWord ++ tailWord_91754).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91754).length < 2 ^ (prefixWord ++ tailWord_91754).sum := by decide
  have hdescent : baseEnd_91754 < baseStart_91754 := by decide
  rcases family_descends (prefixWord ++ tailWord_91754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91799 : List Nat := [1, 1, 3, 3, 2, 2, 4, 2, 3]
def baseStart_91799 : Nat := 118140960795 + 91799 * 2 ^ 59
def prefixEnd_91799 : Nat := 4983230072969 + 3 ^ 40 * 91799 * 2
def baseEnd_91799 : Nat := 20949782489862919862369

theorem tailTrace_91799 : CollatzResearch.WordTrace tailWord_91799 prefixEnd_91799 20949782489862919862369 := by
  unfold tailWord_91799
  simp only [CollatzResearch.WordTrace]
  refine ⟨3348184594435375866118451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2232123062956917244078967 3348184594435375866118451)
  ·
    refine ⟨5022276891653063799177677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3348184594435375866118451 5022276891653063799177677)
    ·
      refine ⟨1883353834369898924691629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5022276891653063799177677 1883353834369898924691629)
      ·
        refine ⟨706257687888712096759361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1883353834369898924691629 706257687888712096759361)
        ·
          refine ⟨529693265916534072569521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 706257687888712096759361 529693265916534072569521)
          ·
            refine ⟨397269949437400554427141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 529693265916534072569521 397269949437400554427141)
            ·
              refine ⟨74488115519512603955089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 397269949437400554427141 74488115519512603955089)
              ·
                refine ⟨55866086639634452966317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74488115519512603955089 55866086639634452966317)
                ·
                  refine ⟨20949782489862919862369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55866086639634452966317 20949782489862919862369)
                  ·
                    rfl

theorem cell21_91799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 4, 2, 3].length) (baseStart_91799 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_91799 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_91799 prefixEnd_91799 := by exact prefixLift 91799
  have htrace : WordTrace (prefixWord ++ tailWord_91799) baseStart_91799 baseEnd_91799 := by
    simpa [prefixWord, tailWord_91799, baseEnd_91799] using wordTrace_append hprefix tailTrace_91799
  have hstable : (prefixWord ++ tailWord_91799).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91799).length < 2 ^ (prefixWord ++ tailWord_91799).sum := by decide
  have hdescent : baseEnd_91799 < baseStart_91799 := by decide
  rcases family_descends (prefixWord ++ tailWord_91799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91816 : List Nat := [2, 1, 7, 1, 1, 1, 1, 2, 5]
def baseStart_91816 : Nat := 118140960795 + 91816 * 2 ^ 59
def prefixEnd_91816 : Nat := 4983230072969 + 3 ^ 40 * 91816 * 2
def baseEnd_91816 : Nat := 20953662121474668079001

theorem tailTrace_91816 : CollatzResearch.WordTrace tailWord_91816 prefixEnd_91816 20953662121474668079001 := by
  unfold tailWord_91816
  simp only [CollatzResearch.WordTrace]
  refine ⟨1674402317686893884743651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2232536423582525179658201 1674402317686893884743651)
  ·
    refine ⟨2511603476530340827115477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1674402317686893884743651 2511603476530340827115477)
    ·
      refine ⟨58865706481179863135519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 2511603476530340827115477 58865706481179863135519)
      ·
        refine ⟨88298559721769794703279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58865706481179863135519 88298559721769794703279)
        ·
          refine ⟨132447839582654692054919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88298559721769794703279 132447839582654692054919)
          ·
            refine ⟨198671759373982038082379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132447839582654692054919 198671759373982038082379)
            ·
              refine ⟨298007639060973057123569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 198671759373982038082379 298007639060973057123569)
              ·
                refine ⟨223505729295729792842677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 298007639060973057123569 223505729295729792842677)
                ·
                  refine ⟨20953662121474668079001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 223505729295729792842677 20953662121474668079001)
                  ·
                    rfl

theorem cell21_91816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 2, 5].length) (baseStart_91816 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_91816 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_91816 prefixEnd_91816 := by exact prefixLift 91816
  have htrace : WordTrace (prefixWord ++ tailWord_91816) baseStart_91816 baseEnd_91816 := by
    simpa [prefixWord, tailWord_91816, baseEnd_91816] using wordTrace_append hprefix tailTrace_91816
  have hstable : (prefixWord ++ tailWord_91816).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91816).length < 2 ^ (prefixWord ++ tailWord_91816).sum := by decide
  have hdescent : baseEnd_91816 < baseStart_91816 := by decide
  rcases family_descends (prefixWord ++ tailWord_91816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91824 : List Nat := [2, 1, 1, 1, 2, 1, 5, 1, 7]
def baseStart_91824 : Nat := 118140960795 + 91824 * 2 ^ 59
def prefixEnd_91824 : Nat := 4983230072969 + 3 ^ 40 * 91824 * 2
def baseEnd_91824 : Nat := 20955487830468431945651

theorem tailTrace_91824 : CollatzResearch.WordTrace tailWord_91824 prefixEnd_91824 20955487830468431945651 := by
  unfold tailWord_91824
  simp only [CollatzResearch.WordTrace]
  refine ⟨1674548209672402567889263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2232730946229870090519017 1674548209672402567889263)
  ·
    refine ⟨2511822314508603851833895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1674548209672402567889263 2511822314508603851833895)
    ·
      refine ⟨3767733471762905777750843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2511822314508603851833895 3767733471762905777750843)
      ·
        refine ⟨5651600207644358666626265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3767733471762905777750843 5651600207644358666626265)
        ·
          refine ⟨4238700155733268999969699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5651600207644358666626265 4238700155733268999969699)
          ·
            refine ⟨6358050233599903499954549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4238700155733268999969699 6358050233599903499954549)
            ·
              refine ⟨596067209399990953120739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6358050233599903499954549 596067209399990953120739)
              ·
                refine ⟨894100814099986429681109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 596067209399990953120739 894100814099986429681109)
                ·
                  refine ⟨20955487830468431945651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 894100814099986429681109 20955487830468431945651)
                  ·
                    rfl

theorem cell21_91824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 1, 7].length) (baseStart_91824 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_91824 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_91824 prefixEnd_91824 := by exact prefixLift 91824
  have htrace : WordTrace (prefixWord ++ tailWord_91824) baseStart_91824 baseEnd_91824 := by
    simpa [prefixWord, tailWord_91824, baseEnd_91824] using wordTrace_append hprefix tailTrace_91824
  have hstable : (prefixWord ++ tailWord_91824).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91824).length < 2 ^ (prefixWord ++ tailWord_91824).sum := by decide
  have hdescent : baseEnd_91824 < baseStart_91824 := by decide
  rcases family_descends (prefixWord ++ tailWord_91824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91858 : List Nat := [3, 2, 2, 2, 2, 2, 2, 1, 5]
def baseStart_91858 : Nat := 118140960795 + 91858 * 2 ^ 59
def prefixEnd_91858 : Nat := 4983230072969 + 3 ^ 40 * 91858 * 2
def baseEnd_91858 : Nat := 20963247093691928378915

theorem tailTrace_91858 : CollatzResearch.WordTrace tailWord_91858 prefixEnd_91858 20963247093691928378915 := by
  unfold tailWord_91858
  simp only [CollatzResearch.WordTrace]
  refine ⟨837584125305407235629057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2233557667481085961677485 837584125305407235629057)
  ·
    refine ⟨628188093979055426721793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 837584125305407235629057 628188093979055426721793)
    ·
      refine ⟨471141070484291570041345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 628188093979055426721793 471141070484291570041345)
      ·
        refine ⟨353355802863218677531009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 471141070484291570041345 353355802863218677531009)
        ·
          refine ⟨265016852147414008148257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 353355802863218677531009 265016852147414008148257)
          ·
            refine ⟨198762639110560506111193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 265016852147414008148257 198762639110560506111193)
            ·
              refine ⟨149071979332920379583395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 198762639110560506111193 149071979332920379583395)
              ·
                refine ⟨223607968999380569375093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 149071979332920379583395 223607968999380569375093)
                ·
                  refine ⟨20963247093691928378915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 223607968999380569375093 20963247093691928378915)
                  ·
                    rfl

theorem cell21_91858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 2, 1, 5].length) (baseStart_91858 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_91858 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_91858 prefixEnd_91858 := by exact prefixLift 91858
  have htrace : WordTrace (prefixWord ++ tailWord_91858) baseStart_91858 baseEnd_91858 := by
    simpa [prefixWord, tailWord_91858, baseEnd_91858] using wordTrace_append hprefix tailTrace_91858
  have hstable : (prefixWord ++ tailWord_91858).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91858).length < 2 ^ (prefixWord ++ tailWord_91858).sum := by decide
  have hdescent : baseEnd_91858 < baseStart_91858 := by decide
  rcases family_descends (prefixWord ++ tailWord_91858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91886 : List Nat := [4, 1, 2, 1, 1, 2, 3, 7]
def baseStart_91886 : Nat := 118140960795 + 91886 * 2 ^ 59
def prefixEnd_91886 : Nat := 4983230072969 + 3 ^ 40 * 91886 * 2
def baseEnd_91886 : Nat := 6989879025056700637397

theorem tailTrace_91886 : CollatzResearch.WordTrace tailWord_91886 prefixEnd_91886 6989879025056700637397 := by
  unfold tailWord_91886
  simp only [CollatzResearch.WordTrace]
  refine ⟨418919718140023715566939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2234238496746793149690341 418919718140023715566939)
  ·
    refine ⟨628379577210035573350409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 418919718140023715566939 628379577210035573350409)
    ·
      refine ⟨471284682907526680012807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 628379577210035573350409 471284682907526680012807)
      ·
        refine ⟨706927024361290020019211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 471284682907526680012807 706927024361290020019211)
        ·
          refine ⟨1060390536541935030028817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 706927024361290020019211 1060390536541935030028817)
          ·
            refine ⟨795292902406451272521613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1060390536541935030028817 795292902406451272521613)
            ·
              refine ⟨298234838402419227195605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 795292902406451272521613 298234838402419227195605)
              ·
                refine ⟨6989879025056700637397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 298234838402419227195605 6989879025056700637397)
                ·
                  rfl

theorem cell21_91886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 7].length) (baseStart_91886 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_91886 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_91886 prefixEnd_91886 := by exact prefixLift 91886
  have htrace : WordTrace (prefixWord ++ tailWord_91886) baseStart_91886 baseEnd_91886 := by
    simpa [prefixWord, tailWord_91886, baseEnd_91886] using wordTrace_append hprefix tailTrace_91886
  have hstable : (prefixWord ++ tailWord_91886).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91886).length < 2 ^ (prefixWord ++ tailWord_91886).sum := by decide
  have hdescent : baseEnd_91886 < baseStart_91886 := by decide
  rcases family_descends (prefixWord ++ tailWord_91886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91931 : List Nat := [1, 1, 1, 1, 1, 1, 4, 7, 4]
def baseStart_91931 : Nat := 118140960795 + 91931 * 2 ^ 59
def prefixEnd_91931 : Nat := 4983230072969 + 3 ^ 40 * 91931 * 2
def baseEnd_91931 : Nat := 20979906688260023662099

theorem tailTrace_91931 : CollatzResearch.WordTrace tailWord_91931 prefixEnd_91931 20979906688260023662099 := by
  unfold tailWord_91931
  simp only [CollatzResearch.WordTrace]
  refine ⟨3352999029957162409923647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2235332686638108273282431 3352999029957162409923647)
  ·
    refine ⟨5029498544935743614885471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3352999029957162409923647 5029498544935743614885471)
    ·
      refine ⟨7544247817403615422328207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5029498544935743614885471 7544247817403615422328207)
      ·
        refine ⟨11316371726105423133492311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7544247817403615422328207 11316371726105423133492311)
        ·
          refine ⟨16974557589158134700238467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11316371726105423133492311 16974557589158134700238467)
          ·
            refine ⟨25461836383737202050357701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16974557589158134700238467 25461836383737202050357701)
            ·
              refine ⟨4774094321950725384442069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25461836383737202050357701 4774094321950725384442069)
              ·
                refine ⟨111892835670720126197861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4774094321950725384442069 111892835670720126197861)
                ·
                  refine ⟨20979906688260023662099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 111892835670720126197861 20979906688260023662099)
                  ·
                    rfl

theorem cell21_91931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 7, 4].length) (baseStart_91931 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_91931 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_91931 prefixEnd_91931 := by exact prefixLift 91931
  have htrace : WordTrace (prefixWord ++ tailWord_91931) baseStart_91931 baseEnd_91931 := by
    simpa [prefixWord, tailWord_91931, baseEnd_91931] using wordTrace_append hprefix tailTrace_91931
  have hstable : (prefixWord ++ tailWord_91931).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91931).length < 2 ^ (prefixWord ++ tailWord_91931).sum := by decide
  have hdescent : baseEnd_91931 < baseStart_91931 := by decide
  rcases family_descends (prefixWord ++ tailWord_91931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91965 : List Nat := [1, 4, 1, 4, 1, 2, 2, 2, 4]
def baseStart_91965 : Nat := 118140960795 + 91965 * 2 ^ 59
def prefixEnd_91965 : Nat := 4983230072969 + 3 ^ 40 * 91965 * 2
def baseEnd_91965 : Nat := 20987665951483520095363

theorem tailTrace_91965 : CollatzResearch.WordTrace tailWord_91965 prefixEnd_91965 20987665951483520095363 := by
  unfold tailWord_91965
  simp only [CollatzResearch.WordTrace]
  refine ⟨3354239111833986216661349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2236159407889324144440899 3354239111833986216661349)
  ·
    refine ⟨628919833468872415624003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3354239111833986216661349 628919833468872415624003)
    ·
      refine ⟨943379750203308623436005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 628919833468872415624003 943379750203308623436005)
      ·
        refine ⟨176883703163120366894251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 943379750203308623436005 176883703163120366894251)
        ·
          refine ⟨265325554744680550341377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 176883703163120366894251 265325554744680550341377)
          ·
            refine ⟨198994166058510412756033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 265325554744680550341377 198994166058510412756033)
            ·
              refine ⟨149245624543882809567025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 198994166058510412756033 149245624543882809567025)
              ·
                refine ⟨111934218407912107175269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 149245624543882809567025 111934218407912107175269)
                ·
                  refine ⟨20987665951483520095363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 111934218407912107175269 20987665951483520095363)
                  ·
                    rfl

theorem cell21_91965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 2, 2, 4].length) (baseStart_91965 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_91965 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_91965 prefixEnd_91965 := by exact prefixLift 91965
  have htrace : WordTrace (prefixWord ++ tailWord_91965) baseStart_91965 baseEnd_91965 := by
    simpa [prefixWord, tailWord_91965, baseEnd_91965] using wordTrace_append hprefix tailTrace_91965
  have hstable : (prefixWord ++ tailWord_91965).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91965).length < 2 ^ (prefixWord ++ tailWord_91965).sum := by decide
  have hdescent : baseEnd_91965 < baseStart_91965 := by decide
  rcases family_descends (prefixWord ++ tailWord_91965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_91996 : List Nat := [2, 2, 4, 2, 2, 1, 3, 5]
def baseStart_91996 : Nat := 118140960795 + 91996 * 2 ^ 59
def prefixEnd_91996 : Nat := 4983230072969 + 3 ^ 40 * 91996 * 2
def baseEnd_91996 : Nat := 6998246857944785026211

theorem tailTrace_91996 : CollatzResearch.WordTrace tailWord_91996 prefixEnd_91996 6998246857944785026211 := by
  unfold tailWord_91996
  simp only [CollatzResearch.WordTrace]
  refine ⟨1677684887360839255519921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2236913183147785674026561 1677684887360839255519921)
  ·
    refine ⟨1258263665520629441639941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1677684887360839255519921 1258263665520629441639941)
    ·
      refine ⟨235924437285118020307489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1258263665520629441639941 235924437285118020307489)
      ·
        refine ⟨176943327963838515230617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 235924437285118020307489 176943327963838515230617)
        ·
          refine ⟨132707495972878886422963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 176943327963838515230617 132707495972878886422963)
          ·
            refine ⟨199061243959318329634445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132707495972878886422963 199061243959318329634445)
            ·
              refine ⟨74647966484744373612917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 199061243959318329634445 74647966484744373612917)
              ·
                refine ⟨6998246857944785026211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 74647966484744373612917 6998246857944785026211)
                ·
                  rfl

theorem cell21_91996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 3, 5].length) (baseStart_91996 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_91996 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_91996 prefixEnd_91996 := by exact prefixLift 91996
  have htrace : WordTrace (prefixWord ++ tailWord_91996) baseStart_91996 baseEnd_91996 := by
    simpa [prefixWord, tailWord_91996, baseEnd_91996] using wordTrace_append hprefix tailTrace_91996
  have hstable : (prefixWord ++ tailWord_91996).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_91996).length < 2 ^ (prefixWord ++ tailWord_91996).sum := by decide
  have hdescent : baseEnd_91996 < baseStart_91996 := by decide
  rcases family_descends (prefixWord ++ tailWord_91996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92007 : List Nat := [1, 1, 5, 1, 2, 1, 2, 2, 6]
def baseStart_92007 : Nat := 118140960795 + 92007 * 2 ^ 59
def prefixEnd_92007 : Nat := 4983230072969 + 3 ^ 40 * 92007 * 2
def baseEnd_92007 : Nat := 20997250923700780395277

theorem tailTrace_92007 : CollatzResearch.WordTrace tailWord_92007 prefixEnd_92007 20997250923700780395277 := by
  unfold tailWord_92007
  simp only [CollatzResearch.WordTrace]
  refine ⟨3355770977681827389690275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2237180651787884926460183 3355770977681827389690275)
  ·
    refine ⟨5033656466522741084535413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3355770977681827389690275 5033656466522741084535413)
    ·
      refine ⟨471905293736506976675195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5033656466522741084535413 471905293736506976675195)
      ·
        refine ⟨707857940604760465012793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 471905293736506976675195 707857940604760465012793)
        ·
          refine ⟨530893455453570348759595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 707857940604760465012793 530893455453570348759595)
          ·
            refine ⟨796340183180355523139393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 530893455453570348759595 796340183180355523139393)
            ·
              refine ⟨597255137385266642354545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 796340183180355523139393 597255137385266642354545)
              ·
                refine ⟨447941353038949981765909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 597255137385266642354545 447941353038949981765909)
                ·
                  refine ⟨20997250923700780395277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 447941353038949981765909 20997250923700780395277)
                  ·
                    rfl

theorem cell21_92007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 2, 6].length) (baseStart_92007 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_92007 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_92007 prefixEnd_92007 := by exact prefixLift 92007
  have htrace : WordTrace (prefixWord ++ tailWord_92007) baseStart_92007 baseEnd_92007 := by
    simpa [prefixWord, tailWord_92007, baseEnd_92007] using wordTrace_append hprefix tailTrace_92007
  have hstable : (prefixWord ++ tailWord_92007).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92007).length < 2 ^ (prefixWord ++ tailWord_92007).sum := by decide
  have hdescent : baseEnd_92007 < baseStart_92007 := by decide
  rcases family_descends (prefixWord ++ tailWord_92007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92055 : List Nat := [1, 1, 3, 3, 1, 5, 2, 5]
def baseStart_92055 : Nat := 118140960795 + 92055 * 2 ^ 59
def prefixEnd_92055 : Nat := 4983230072969 + 3 ^ 40 * 92055 * 2
def baseEnd_92055 : Nat := 7002735059221121198393

theorem tailTrace_92055 : CollatzResearch.WordTrace tailWord_92055 prefixEnd_92055 7002735059221121198393 := by
  unfold tailWord_92055
  simp only [CollatzResearch.WordTrace]
  refine ⟨3357521681507931587437619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2238347787671954391625079 3357521681507931587437619)
  ·
    refine ⟨5036282522261897381156429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3357521681507931587437619 5036282522261897381156429)
    ·
      refine ⟨1888605945848211517933661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5036282522261897381156429 1888605945848211517933661)
      ·
        refine ⟨708227229693079319225123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1888605945848211517933661 708227229693079319225123)
        ·
          refine ⟨1062340844539618978837685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 708227229693079319225123 1062340844539618978837685)
          ·
            refine ⟨99594454175589279266033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1062340844539618978837685 99594454175589279266033)
            ·
              refine ⟨74695840631691959449525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99594454175589279266033 74695840631691959449525)
              ·
                refine ⟨7002735059221121198393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 74695840631691959449525 7002735059221121198393)
                ·
                  rfl

theorem cell21_92055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 2, 5].length) (baseStart_92055 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_92055 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_92055 prefixEnd_92055 := by exact prefixLift 92055
  have htrace : WordTrace (prefixWord ++ tailWord_92055) baseStart_92055 baseEnd_92055 := by
    simpa [prefixWord, tailWord_92055, baseEnd_92055] using wordTrace_append hprefix tailTrace_92055
  have hstable : (prefixWord ++ tailWord_92055).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92055).length < 2 ^ (prefixWord ++ tailWord_92055).sum := by decide
  have hdescent : baseEnd_92055 < baseStart_92055 := by decide
  rcases family_descends (prefixWord ++ tailWord_92055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92072 : List Nat := [2, 1, 6, 2, 1, 2, 7]
def baseStart_92072 : Nat := 118140960795 + 92072 * 2 ^ 59
def prefixEnd_92072 : Nat := 4983230072969 + 3 ^ 40 * 92072 * 2
def baseEnd_92072 : Nat := 2334676089919456867979

theorem tailTrace_92072 : CollatzResearch.WordTrace tailWord_92072 prefixEnd_92072 2334676089919456867979 := by
  unfold tailWord_92072
  simp only [CollatzResearch.WordTrace]
  refine ⟨1679070861223171745403235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2238761148297562327204313 1679070861223171745403235)
  ·
    refine ⟨2518606291834757618104853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1679070861223171745403235 2518606291834757618104853)
    ·
      refine ⟨118059669929754263348665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 2518606291834757618104853 118059669929754263348665)
      ·
        refine ⟨88544752447315697511499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118059669929754263348665 88544752447315697511499)
        ·
          refine ⟨132817128670973546267249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88544752447315697511499 132817128670973546267249)
          ·
            refine ⟨99612846503230159700437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132817128670973546267249 99612846503230159700437)
            ·
              refine ⟨2334676089919456867979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 99612846503230159700437 2334676089919456867979)
              ·
                rfl

theorem cell21_92072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 7].length) (baseStart_92072 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_92072 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_92072 prefixEnd_92072 := by exact prefixLift 92072
  have htrace : WordTrace (prefixWord ++ tailWord_92072) baseStart_92072 baseEnd_92072 := by
    simpa [prefixWord, tailWord_92072, baseEnd_92072] using wordTrace_append hprefix tailTrace_92072
  have hstable : (prefixWord ++ tailWord_92072).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92072).length < 2 ^ (prefixWord ++ tailWord_92072).sum := by decide
  have hdescent : baseEnd_92072 < baseStart_92072 := by decide
  rcases family_descends (prefixWord ++ tailWord_92072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92078 : List Nat := [4, 1, 5, 1, 1, 1, 3, 2, 3]
def baseStart_92078 : Nat := 118140960795 + 92078 * 2 ^ 59
def prefixEnd_92078 : Nat := 4983230072969 + 3 ^ 40 * 92078 * 2
def baseEnd_92078 : Nat := 21013454091020434711799

theorem tailTrace_92078 : CollatzResearch.WordTrace tailWord_92078 prefixEnd_92078 21013454091020434711799 := by
  unfold tailWord_92078
  simp only [CollatzResearch.WordTrace]
  refine ⟨419795070053075814440611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2238907040283071010349925 419795070053075814440611)
  ·
    refine ⟨629692605079613721660917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 419795070053075814440611 629692605079613721660917)
    ·
      refine ⟨59033681726213786405711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 629692605079613721660917 59033681726213786405711)
      ·
        refine ⟨88550522589320679608567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59033681726213786405711 88550522589320679608567)
        ·
          refine ⟨132825783883981019412851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88550522589320679608567 132825783883981019412851)
          ·
            refine ⟨199238675825971529119277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 132825783883981019412851 199238675825971529119277)
            ·
              refine ⟨74714503434739323419729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 199238675825971529119277 74714503434739323419729)
              ·
                refine ⟨56035877576054492564797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74714503434739323419729 56035877576054492564797)
                ·
                  refine ⟨21013454091020434711799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56035877576054492564797 21013454091020434711799)
                  ·
                    rfl

theorem cell21_92078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 3, 2, 3].length) (baseStart_92078 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_92078 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_92078 prefixEnd_92078 := by exact prefixLift 92078
  have htrace : WordTrace (prefixWord ++ tailWord_92078) baseStart_92078 baseEnd_92078 := by
    simpa [prefixWord, tailWord_92078, baseEnd_92078] using wordTrace_append hprefix tailTrace_92078
  have hstable : (prefixWord ++ tailWord_92078).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92078).length < 2 ^ (prefixWord ++ tailWord_92078).sum := by decide
  have hdescent : baseEnd_92078 < baseStart_92078 := by decide
  rcases family_descends (prefixWord ++ tailWord_92078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92083 : List Nat := [1, 1, 1, 2, 3, 1, 4, 4, 4]
def baseStart_92083 : Nat := 118140960795 + 92083 * 2 ^ 59
def prefixEnd_92083 : Nat := 4983230072969 + 3 ^ 40 * 92083 * 2
def baseEnd_92083 : Nat := 21014595159141537128455

theorem tailTrace_92083 : CollatzResearch.WordTrace tailWord_92083 prefixEnd_92083 21014595159141537128455 := by
  unfold tailWord_92083
  simp only [CollatzResearch.WordTrace]
  refine ⟨3358542925406492369456903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2239028616937661579637935 3358542925406492369456903)
  ·
    refine ⟨5037814388109738554185355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3358542925406492369456903 5037814388109738554185355)
    ·
      refine ⟨7556721582164607831278033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5037814388109738554185355 7556721582164607831278033)
      ·
        refine ⟨5667541186623455873458525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7556721582164607831278033 5667541186623455873458525)
        ·
          refine ⟨2125327944983795952546947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5667541186623455873458525 2125327944983795952546947)
          ·
            refine ⟨3187991917475693928820421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2125327944983795952546947 3187991917475693928820421)
            ·
              refine ⟨597748484526692611653829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3187991917475693928820421 597748484526692611653829)
              ·
                refine ⟨112077840848754864685093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 597748484526692611653829 112077840848754864685093)
                ·
                  refine ⟨21014595159141537128455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 112077840848754864685093 21014595159141537128455)
                  ·
                    rfl

theorem cell21_92083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 4, 4].length) (baseStart_92083 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_92083 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_92083 prefixEnd_92083 := by exact prefixLift 92083
  have htrace : WordTrace (prefixWord ++ tailWord_92083) baseStart_92083 baseEnd_92083 := by
    simpa [prefixWord, tailWord_92083, baseEnd_92083] using wordTrace_append hprefix tailTrace_92083
  have hstable : (prefixWord ++ tailWord_92083).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92083).length < 2 ^ (prefixWord ++ tailWord_92083).sum := by decide
  have hdescent : baseEnd_92083 < baseStart_92083 := by decide
  rcases family_descends (prefixWord ++ tailWord_92083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92193 : List Nat := [1, 2, 3, 2, 4, 2, 1, 2, 4]
def baseStart_92193 : Nat := 118140960795 + 92193 * 2 ^ 59
def prefixEnd_92193 : Nat := 4983230072969 + 3 ^ 40 * 92193 * 2
def baseEnd_92193 : Nat := 21039698657805790294897

theorem tailTrace_92193 : CollatzResearch.WordTrace tailWord_92193 prefixEnd_92193 21039698657805790294897 := by
  unfold tailWord_92193
  simp only [CollatzResearch.WordTrace]
  refine ⟨3362554955007981155961233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2241703303338654103974155 3362554955007981155961233)
  ·
    refine ⟨2521916216255985866970925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3362554955007981155961233 2521916216255985866970925)
    ·
      refine ⟨945718581095994700114097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2521916216255985866970925 945718581095994700114097)
      ·
        refine ⟨709288935821996025085573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 945718581095994700114097 709288935821996025085573)
        ·
          refine ⟨132991675466624254703545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 709288935821996025085573 132991675466624254703545)
          ·
            refine ⟨99743756599968191027659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 132991675466624254703545 99743756599968191027659)
            ·
              refine ⟨149615634899952286541489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99743756599968191027659 149615634899952286541489)
              ·
                refine ⟨112211726174964214906117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 149615634899952286541489 112211726174964214906117)
                ·
                  refine ⟨21039698657805790294897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 112211726174964214906117 21039698657805790294897)
                  ·
                    rfl

theorem cell21_92193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 1, 2, 4].length) (baseStart_92193 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_92193 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_92193 prefixEnd_92193 := by exact prefixLift 92193
  have htrace : WordTrace (prefixWord ++ tailWord_92193) baseStart_92193 baseEnd_92193 := by
    simpa [prefixWord, tailWord_92193, baseEnd_92193] using wordTrace_append hprefix tailTrace_92193
  have hstable : (prefixWord ++ tailWord_92193).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92193).length < 2 ^ (prefixWord ++ tailWord_92193).sum := by decide
  have hdescent : baseEnd_92193 < baseStart_92193 := by decide
  rcases family_descends (prefixWord ++ tailWord_92193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92238 : List Nat := [4, 1, 1, 1, 1, 4, 3, 3, 3]
def baseStart_92238 : Nat := 118140960795 + 92238 * 2 ^ 59
def prefixEnd_92238 : Nat := 4983230072969 + 3 ^ 40 * 92238 * 2
def baseEnd_92238 : Nat := 21049968270895712044805

theorem tailTrace_92238 : CollatzResearch.WordTrace tailWord_92238 prefixEnd_92238 21049968270895712044805 := by
  unfold tailWord_92238
  simp only [CollatzResearch.WordTrace]
  refine ⟨420524529980619230168671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2242797493229969227566245 420524529980619230168671)
  ·
    refine ⟨630786794970928845253007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 420524529980619230168671 630786794970928845253007)
    ·
      refine ⟨946180192456393267879511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 630786794970928845253007 946180192456393267879511)
      ·
        refine ⟨1419270288684589901819267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 946180192456393267879511 1419270288684589901819267)
        ·
          refine ⟨2128905433026884852728901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1419270288684589901819267 2128905433026884852728901)
          ·
            refine ⟨399169768692540909886669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2128905433026884852728901 399169768692540909886669)
            ·
              refine ⟨149688663259702841207501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 399169768692540909886669 149688663259702841207501)
              ·
                refine ⟨56133248722388565452813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 149688663259702841207501 56133248722388565452813)
                ·
                  refine ⟨21049968270895712044805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56133248722388565452813 21049968270895712044805)
                  ·
                    rfl

theorem cell21_92238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 3, 3, 3].length) (baseStart_92238 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_92238 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_92238 prefixEnd_92238 := by exact prefixLift 92238
  have htrace : WordTrace (prefixWord ++ tailWord_92238) baseStart_92238 baseEnd_92238 := by
    simpa [prefixWord, tailWord_92238, baseEnd_92238] using wordTrace_append hprefix tailTrace_92238
  have hstable : (prefixWord ++ tailWord_92238).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92238).length < 2 ^ (prefixWord ++ tailWord_92238).sum := by decide
  have hdescent : baseEnd_92238 < baseStart_92238 := by decide
  rcases family_descends (prefixWord ++ tailWord_92238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92297 : List Nat := [1, 2, 1, 1, 4, 2, 2, 5, 3]
def baseStart_92297 : Nat := 118140960795 + 92297 * 2 ^ 59
def prefixEnd_92297 : Nat := 4983230072969 + 3 ^ 40 * 92297 * 2
def baseEnd_92297 : Nat := 21063432874724720561351

theorem tailTrace_92297 : CollatzResearch.WordTrace tailWord_92297 prefixEnd_92297 21063432874724720561351 := by
  unfold tailWord_92297
  simp only [CollatzResearch.WordTrace]
  refine ⟨3366348146631206917747145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2244232097754137945164763 3366348146631206917747145)
  ·
    refine ⟨2524761109973405188310359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3366348146631206917747145 2524761109973405188310359)
    ·
      refine ⟨3787141664960107782465539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2524761109973405188310359 3787141664960107782465539)
      ·
        refine ⟨5680712497440161673698309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3787141664960107782465539 5680712497440161673698309)
        ·
          refine ⟨1065133593270030313818433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5680712497440161673698309 1065133593270030313818433)
          ·
            refine ⟨798850194952522735363825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1065133593270030313818433 798850194952522735363825)
            ·
              refine ⟨599137646214392051522869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 798850194952522735363825 599137646214392051522869)
              ·
                refine ⟨56169154332599254830269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 599137646214392051522869 56169154332599254830269)
                ·
                  refine ⟨21063432874724720561351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56169154332599254830269 21063432874724720561351)
                  ·
                    rfl

theorem cell21_92297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 5, 3].length) (baseStart_92297 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_92297 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_92297 prefixEnd_92297 := by exact prefixLift 92297
  have htrace : WordTrace (prefixWord ++ tailWord_92297) baseStart_92297 baseEnd_92297 := by
    simpa [prefixWord, tailWord_92297, baseEnd_92297] using wordTrace_append hprefix tailTrace_92297
  have hstable : (prefixWord ++ tailWord_92297).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92297).length < 2 ^ (prefixWord ++ tailWord_92297).sum := by decide
  have hdescent : baseEnd_92297 < baseStart_92297 := by decide
  rcases family_descends (prefixWord ++ tailWord_92297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92418 : List Nat := [3, 4, 1, 1, 2, 1, 9]
def baseStart_92418 : Nat := 118140960795 + 92418 * 2 ^ 59
def prefixEnd_92418 : Nat := 4983230072969 + 3 ^ 40 * 92418 * 2
def baseEnd_92418 : Nat := 2343449635917266560493

theorem tailTrace_92418 : CollatzResearch.WordTrace tailWord_92418 prefixEnd_92418 2343449635917266560493 := by
  unfold tailWord_92418
  simp only [CollatzResearch.WordTrace]
  refine ⟨842690344798211145725477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2247174252795229721934605 842690344798211145725477)
  ·
    refine ⟨158004439649664589823527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 842690344798211145725477 158004439649664589823527)
    ·
      refine ⟨237006659474496884735291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158004439649664589823527 237006659474496884735291)
      ·
        refine ⟨355509989211745327102937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237006659474496884735291 355509989211745327102937)
        ·
          refine ⟨266632491908808995327203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 355509989211745327102937 266632491908808995327203)
          ·
            refine ⟨399948737863213492990805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 266632491908808995327203 399948737863213492990805)
            ·
              refine ⟨2343449635917266560493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 399948737863213492990805 2343449635917266560493)
              ·
                rfl

theorem cell21_92418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 9].length) (baseStart_92418 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_92418 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_92418 prefixEnd_92418 := by exact prefixLift 92418
  have htrace : WordTrace (prefixWord ++ tailWord_92418) baseStart_92418 baseEnd_92418 := by
    simpa [prefixWord, tailWord_92418, baseEnd_92418] using wordTrace_append hprefix tailTrace_92418
  have hstable : (prefixWord ++ tailWord_92418).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92418).length < 2 ^ (prefixWord ++ tailWord_92418).sum := by decide
  have hdescent : baseEnd_92418 < baseStart_92418 := by decide
  rcases family_descends (prefixWord ++ tailWord_92418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92539 : List Nat := [1, 1, 1, 1, 1, 7, 3, 2, 4]
def baseStart_92539 : Nat := 118140960795 + 92539 * 2 ^ 59
def prefixEnd_92539 : Nat := 4983230072969 + 3 ^ 40 * 92539 * 2
def baseEnd_92539 : Nat := 21118660571786077527523

theorem tailTrace_92539 : CollatzResearch.WordTrace tailWord_92539 prefixEnd_92539 21118660571786077527523 := by
  unfold tailWord_92539
  simp only [CollatzResearch.WordTrace]
  refine ⟨3375174611754482248056671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2250116407836321498704447 3375174611754482248056671)
  ·
    refine ⟨5062761917631723372085007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3375174611754482248056671 5062761917631723372085007)
    ·
      refine ⟨7594142876447585058127511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5062761917631723372085007 7594142876447585058127511)
      ·
        refine ⟨11391214314671377587191267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7594142876447585058127511 11391214314671377587191267)
        ·
          refine ⟨17086821472007066380786901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11391214314671377587191267 17086821472007066380786901)
          ·
            refine ⟨400472378250165618299693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 17086821472007066380786901 400472378250165618299693)
            ·
              refine ⟨150177141843812106862385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 400472378250165618299693 150177141843812106862385)
              ·
                refine ⟨112632856382859080146789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 150177141843812106862385 112632856382859080146789)
                ·
                  refine ⟨21118660571786077527523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 112632856382859080146789 21118660571786077527523)
                  ·
                    rfl

theorem cell21_92539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 3, 2, 4].length) (baseStart_92539 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_92539 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_92539 prefixEnd_92539 := by exact prefixLift 92539
  have htrace : WordTrace (prefixWord ++ tailWord_92539) baseStart_92539 baseEnd_92539 := by
    simpa [prefixWord, tailWord_92539, baseEnd_92539] using wordTrace_append hprefix tailTrace_92539
  have hstable : (prefixWord ++ tailWord_92539).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92539).length < 2 ^ (prefixWord ++ tailWord_92539).sum := by decide
  have hdescent : baseEnd_92539 < baseStart_92539 := by decide
  rcases family_descends (prefixWord ++ tailWord_92539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92556 : List Nat := [2, 2, 1, 2, 1, 5, 3, 1, 4]
def baseStart_92556 : Nat := 118140960795 + 92556 * 2 ^ 59
def prefixEnd_92556 : Nat := 4983230072969 + 3 ^ 40 * 92556 * 2
def baseEnd_92556 : Nat := 21122540203397825744155

theorem tailTrace_92556 : CollatzResearch.WordTrace tailWord_92556 prefixEnd_92556 21122540203397825744155 := by
  unfold tailWord_92556
  simp only [CollatzResearch.WordTrace]
  refine ⟨1687897326346447075712761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2250529768461929434283681 1687897326346447075712761)
  ·
    refine ⟨1265922994759835306784571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1687897326346447075712761 1265922994759835306784571)
    ·
      refine ⟨1898884492139752960176857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1265922994759835306784571 1898884492139752960176857)
      ·
        refine ⟨1424163369104814720132643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1898884492139752960176857 1424163369104814720132643)
        ·
          refine ⟨2136245053657222080198965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1424163369104814720132643 2136245053657222080198965)
          ·
            refine ⟨200272973780364570018653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2136245053657222080198965 200272973780364570018653)
            ·
              refine ⟨75102365167636713756995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 200272973780364570018653 75102365167636713756995)
              ·
                refine ⟨112653547751455070635493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75102365167636713756995 112653547751455070635493)
                ·
                  refine ⟨21122540203397825744155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 112653547751455070635493 21122540203397825744155)
                  ·
                    rfl

theorem cell21_92556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 3, 1, 4].length) (baseStart_92556 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_92556 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_92556 prefixEnd_92556 := by exact prefixLift 92556
  have htrace : WordTrace (prefixWord ++ tailWord_92556) baseStart_92556 baseEnd_92556 := by
    simpa [prefixWord, tailWord_92556, baseEnd_92556] using wordTrace_append hprefix tailTrace_92556
  have hstable : (prefixWord ++ tailWord_92556).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92556).length < 2 ^ (prefixWord ++ tailWord_92556).sum := by decide
  have hdescent : baseEnd_92556 < baseStart_92556 := by decide
  rcases family_descends (prefixWord ++ tailWord_92556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92570 : List Nat := [3, 1, 1, 4, 1, 2, 4, 5]
def baseStart_92570 : Nat := 118140960795 + 92570 * 2 ^ 59
def prefixEnd_92570 : Nat := 4983230072969 + 3 ^ 40 * 92570 * 2
def baseEnd_92570 : Nat := 7041911731378970836931

theorem tailTrace_92570 : CollatzResearch.WordTrace tailWord_92570 prefixEnd_92570 7041911731378970836931 := by
  unfold tailWord_92570
  simp only [CollatzResearch.WordTrace]
  refine ⟨844076318660543635608791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2250870183094783028290109 844076318660543635608791)
  ·
    refine ⟨1266114477990815453413187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 844076318660543635608791 1266114477990815453413187)
    ·
      refine ⟨1899171716986223180119781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1266114477990815453413187 1899171716986223180119781)
      ·
        refine ⟨356094696934916846272459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1899171716986223180119781 356094696934916846272459)
        ·
          refine ⟨534142045402375269408689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 356094696934916846272459 534142045402375269408689)
          ·
            refine ⟨400606534051781452056517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 534142045402375269408689 400606534051781452056517)
            ·
              refine ⟨75113725134709022260597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 400606534051781452056517 75113725134709022260597)
              ·
                refine ⟨7041911731378970836931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 75113725134709022260597 7041911731378970836931)
                ·
                  rfl

theorem cell21_92570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 4, 5].length) (baseStart_92570 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_92570 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_92570 prefixEnd_92570 := by exact prefixLift 92570
  have htrace : WordTrace (prefixWord ++ tailWord_92570) baseStart_92570 baseEnd_92570 := by
    simpa [prefixWord, tailWord_92570, baseEnd_92570] using wordTrace_append hprefix tailTrace_92570
  have hstable : (prefixWord ++ tailWord_92570).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92570).length < 2 ^ (prefixWord ++ tailWord_92570).sum := by decide
  have hdescent : baseEnd_92570 < baseStart_92570 := by decide
  rcases family_descends (prefixWord ++ tailWord_92570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92601 : List Nat := [1, 2, 1, 4, 3, 3, 1, 1, 5]
def baseStart_92601 : Nat := 118140960795 + 92601 * 2 ^ 59
def prefixEnd_92601 : Nat := 4983230072969 + 3 ^ 40 * 92601 * 2
def baseEnd_92601 : Nat := 21132809816487747494063

theorem tailTrace_92601 : CollatzResearch.WordTrace tailWord_92601 prefixEnd_92601 21132809816487747494063 := by
  unfold tailWord_92601
  simp only [CollatzResearch.WordTrace]
  refine ⟨3377435937529866836813657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2251623958353244557875771 3377435937529866836813657)
  ·
    refine ⟨2533076953147400127610243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3377435937529866836813657 2533076953147400127610243)
    ·
      refine ⟨3799615429721100191415365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2533076953147400127610243 3799615429721100191415365)
      ·
        refine ⟨712427893072706285890381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3799615429721100191415365 712427893072706285890381)
        ·
          refine ⟨267160459902264857208893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 712427893072706285890381 267160459902264857208893)
          ·
            refine ⟨100185172463349321453335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 267160459902264857208893 100185172463349321453335)
            ·
              refine ⟨150277758695023982180003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100185172463349321453335 150277758695023982180003)
              ·
                refine ⟨225416638042535973270005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 150277758695023982180003 225416638042535973270005)
                ·
                  refine ⟨21132809816487747494063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 225416638042535973270005 21132809816487747494063)
                  ·
                    rfl

theorem cell21_92601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 1, 1, 5].length) (baseStart_92601 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_92601 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_92601 prefixEnd_92601 := by exact prefixLift 92601
  have htrace : WordTrace (prefixWord ++ tailWord_92601) baseStart_92601 baseEnd_92601 := by
    simpa [prefixWord, tailWord_92601, baseEnd_92601] using wordTrace_append hprefix tailTrace_92601
  have hstable : (prefixWord ++ tailWord_92601).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92601).length < 2 ^ (prefixWord ++ tailWord_92601).sum := by decide
  have hdescent : baseEnd_92601 < baseStart_92601 := by decide
  rcases family_descends (prefixWord ++ tailWord_92601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92615 : List Nat := [1, 1, 4, 1, 1, 5, 1, 3, 4]
def baseStart_92615 : Nat := 118140960795 + 92615 * 2 ^ 59
def prefixEnd_92615 : Nat := 4983230072969 + 3 ^ 40 * 92615 * 2
def baseEnd_92615 : Nat := 21136004807226834260701

theorem tailTrace_92615 : CollatzResearch.WordTrace tailWord_92615 prefixEnd_92615 21136004807226834260701 := by
  unfold tailWord_92615
  simp only [CollatzResearch.WordTrace]
  refine ⟨3377946559479147227823299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2251964372986098151882199 3377946559479147227823299)
  ·
    refine ⟨5066919839218720841734949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3377946559479147227823299 5066919839218720841734949)
    ·
      refine ⟨950047469853510157825303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5066919839218720841734949 950047469853510157825303)
      ·
        refine ⟨1425071204780265236737955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 950047469853510157825303 1425071204780265236737955)
        ·
          refine ⟨2137606807170397855106933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1425071204780265236737955 2137606807170397855106933)
          ·
            refine ⟨200400638172224798916275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2137606807170397855106933 200400638172224798916275)
            ·
              refine ⟨300600957258337198374413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 200400638172224798916275 300600957258337198374413)
              ·
                refine ⟨112725358971876449390405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 300600957258337198374413 112725358971876449390405)
                ·
                  refine ⟨21136004807226834260701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 112725358971876449390405 21136004807226834260701)
                  ·
                    rfl

theorem cell21_92615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 3, 4].length) (baseStart_92615 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_92615 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_92615 prefixEnd_92615 := by exact prefixLift 92615
  have htrace : WordTrace (prefixWord ++ tailWord_92615) baseStart_92615 baseEnd_92615 := by
    simpa [prefixWord, tailWord_92615, baseEnd_92615] using wordTrace_append hprefix tailTrace_92615
  have hstable : (prefixWord ++ tailWord_92615).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92615).length < 2 ^ (prefixWord ++ tailWord_92615).sum := by decide
  have hdescent : baseEnd_92615 < baseStart_92615 := by decide
  rcases family_descends (prefixWord ++ tailWord_92615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92629 : List Nat := [1, 3, 2, 3, 1, 2, 2, 7]
def baseStart_92629 : Nat := 118140960795 + 92629 * 2 ^ 59
def prefixEnd_92629 : Nat := 4983230072969 + 3 ^ 40 * 92629 * 2
def baseEnd_92629 : Nat := 7046399932655307009113

theorem tailTrace_92629 : CollatzResearch.WordTrace tailWord_92629 prefixEnd_92629 7046399932655307009113 := by
  unfold tailWord_92629
  simp only [CollatzResearch.WordTrace]
  refine ⟨3378457181428427618832941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2252304787618951745888627 3378457181428427618832941)
  ·
    refine ⟨1266921443035660357062353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3378457181428427618832941 1266921443035660357062353)
    ·
      refine ⟨950191082276745267796765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1266921443035660357062353 950191082276745267796765)
      ·
        refine ⟨356321655853779475423787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 950191082276745267796765 356321655853779475423787)
        ·
          refine ⟨534482483780669213135681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 356321655853779475423787 534482483780669213135681)
          ·
            refine ⟨400861862835501909851761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 534482483780669213135681 400861862835501909851761)
            ·
              refine ⟨300646397126626432388821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 400861862835501909851761 300646397126626432388821)
              ·
                refine ⟨7046399932655307009113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 300646397126626432388821 7046399932655307009113)
                ·
                  rfl

theorem cell21_92629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 7].length) (baseStart_92629 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_92629 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_92629 prefixEnd_92629 := by exact prefixLift 92629
  have htrace : WordTrace (prefixWord ++ tailWord_92629) baseStart_92629 baseEnd_92629 := by
    simpa [prefixWord, tailWord_92629, baseEnd_92629] using wordTrace_append hprefix tailTrace_92629
  have hstable : (prefixWord ++ tailWord_92629).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92629).length < 2 ^ (prefixWord ++ tailWord_92629).sum := by decide
  have hdescent : baseEnd_92629 < baseStart_92629 := by decide
  rcases family_descends (prefixWord ++ tailWord_92629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92708 : List Nat := [2, 3, 1, 5, 1, 1, 1, 1, 6]
def baseStart_92708 : Nat := 118140960795 + 92708 * 2 ^ 59
def prefixEnd_92708 : Nat := 4983230072969 + 3 ^ 40 * 92708 * 2
def baseEnd_92708 : Nat := 21157228674279339210511

theorem tailTrace_92708 : CollatzResearch.WordTrace tailWord_92708 prefixEnd_92708 21157228674279339210511 := by
  unfold tailWord_92708
  simp only [CollatzResearch.WordTrace]
  refine ⟨1690669274071112055479389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2254225698761482740639185 1690669274071112055479389)
  ·
    refine ⟨634000977776667020804771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1690669274071112055479389 634000977776667020804771)
    ·
      refine ⟨951001466665000531207157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 634000977776667020804771 951001466665000531207157)
      ·
        refine ⟨89156387499843799800671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 951001466665000531207157 89156387499843799800671)
        ·
          refine ⟨133734581249765699701007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89156387499843799800671 133734581249765699701007)
          ·
            refine ⟨200601871874648549551511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133734581249765699701007 200601871874648549551511)
            ·
              refine ⟨300902807811972824327267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 200601871874648549551511 300902807811972824327267)
              ·
                refine ⟨451354211717959236490901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 300902807811972824327267 451354211717959236490901)
                ·
                  refine ⟨21157228674279339210511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 451354211717959236490901 21157228674279339210511)
                  ·
                    rfl

theorem cell21_92708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 1, 6].length) (baseStart_92708 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_92708 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_92708 prefixEnd_92708 := by exact prefixLift 92708
  have htrace : WordTrace (prefixWord ++ tailWord_92708) baseStart_92708 baseEnd_92708 := by
    simpa [prefixWord, tailWord_92708, baseEnd_92708] using wordTrace_append hprefix tailTrace_92708
  have hstable : (prefixWord ++ tailWord_92708).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92708).length < 2 ^ (prefixWord ++ tailWord_92708).sum := by decide
  have hdescent : baseEnd_92708 < baseStart_92708 := by decide
  rcases family_descends (prefixWord ++ tailWord_92708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92750 : List Nat := [4, 1, 1, 1, 1, 2, 3, 2, 6]
def baseStart_92750 : Nat := 118140960795 + 92750 * 2 ^ 59
def prefixEnd_92750 : Nat := 4983230072969 + 3 ^ 40 * 92750 * 2
def baseEnd_92750 : Nat := 21166813646496599510425

theorem tailTrace_92750 : CollatzResearch.WordTrace tailWord_92750 prefixEnd_92750 21166813646496599510425 := by
  unfold tailWord_92750
  simp only [CollatzResearch.WordTrace]
  refine ⟨422858801748758160498463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2255246942660043522658469 422858801748758160498463)
  ·
    refine ⟨634288202623137240747695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 422858801748758160498463 634288202623137240747695)
    ·
      refine ⟨951432303934705861121543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 634288202623137240747695 951432303934705861121543)
      ·
        refine ⟨1427148455902058791682315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 951432303934705861121543 1427148455902058791682315)
        ·
          refine ⟨2140722683853088187523473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1427148455902058791682315 2140722683853088187523473)
          ·
            refine ⟨1605542012889816140642605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2140722683853088187523473 1605542012889816140642605)
            ·
              refine ⟨602078254833681052740977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1605542012889816140642605 602078254833681052740977)
              ·
                refine ⟨451558691125260789555733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 602078254833681052740977 451558691125260789555733)
                ·
                  refine ⟨21166813646496599510425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 451558691125260789555733 21166813646496599510425)
                  ·
                    rfl

theorem cell21_92750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 2, 6].length) (baseStart_92750 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_92750 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_92750 prefixEnd_92750 := by exact prefixLift 92750
  have htrace : WordTrace (prefixWord ++ tailWord_92750) baseStart_92750 baseEnd_92750 := by
    simpa [prefixWord, tailWord_92750, baseEnd_92750] using wordTrace_append hprefix tailTrace_92750
  have hstable : (prefixWord ++ tailWord_92750).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92750).length < 2 ^ (prefixWord ++ tailWord_92750).sum := by decide
  have hdescent : baseEnd_92750 < baseStart_92750 := by decide
  rcases family_descends (prefixWord ++ tailWord_92750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92753 : List Nat := [1, 2, 2, 1, 3, 3, 3, 3, 3]
def baseStart_92753 : Nat := 118140960795 + 92753 * 2 ^ 59
def prefixEnd_92753 : Nat := 4983230072969 + 3 ^ 40 * 92753 * 2
def baseEnd_92753 : Nat := 21167498287369260960419

theorem tailTrace_92753 : CollatzResearch.WordTrace tailWord_92753 prefixEnd_92753 21167498287369260960419 := by
  unfold tailWord_92753
  simp only [CollatzResearch.WordTrace]
  refine ⟨3382979832979196796346913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2255319888652797864231275 3382979832979196796346913)
  ·
    refine ⟨2537234874734397597260185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3382979832979196796346913 2537234874734397597260185)
    ·
      refine ⟨1902926156050798197945139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2537234874734397597260185 1902926156050798197945139)
      ·
        refine ⟨2854389234076197296917709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1902926156050798197945139 2854389234076197296917709)
        ·
          refine ⟨1070395962778573986344141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2854389234076197296917709 1070395962778573986344141)
          ·
            refine ⟨401398486041965244879053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1070395962778573986344141 401398486041965244879053)
            ·
              refine ⟨150524432265736966829645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 401398486041965244879053 150524432265736966829645)
              ·
                refine ⟨56446662099651362561117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 150524432265736966829645 56446662099651362561117)
                ·
                  refine ⟨21167498287369260960419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56446662099651362561117 21167498287369260960419)
                  ·
                    rfl

theorem cell21_92753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 3, 3, 3].length) (baseStart_92753 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_92753 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_92753 prefixEnd_92753 := by exact prefixLift 92753
  have htrace : WordTrace (prefixWord ++ tailWord_92753) baseStart_92753 baseEnd_92753 := by
    simpa [prefixWord, tailWord_92753, baseEnd_92753] using wordTrace_append hprefix tailTrace_92753
  have hstable : (prefixWord ++ tailWord_92753).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92753).length < 2 ^ (prefixWord ++ tailWord_92753).sum := by decide
  have hdescent : baseEnd_92753 < baseStart_92753 := by decide
  rcases family_descends (prefixWord ++ tailWord_92753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92781 : List Nat := [1, 5, 1, 1, 3, 1, 1, 8]
def baseStart_92781 : Nat := 118140960795 + 92781 * 2 ^ 59
def prefixEnd_92781 : Nat := 4983230072969 + 3 ^ 40 * 92781 * 2
def baseEnd_92781 : Nat := 7057962756282478164565

theorem tailTrace_92781 : CollatzResearch.WordTrace tailWord_92781 prefixEnd_92781 7057962756282478164565 := by
  unfold tailWord_92781
  simp only [CollatzResearch.WordTrace]
  refine ⟨3384001076877757578366197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2256000717918505052244131 3384001076877757578366197)
  ·
    refine ⟨317250100957289772971831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3384001076877757578366197 317250100957289772971831)
    ·
      refine ⟨475875151435934659457747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 317250100957289772971831 475875151435934659457747)
      ·
        refine ⟨713812727153901989186621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 475875151435934659457747 713812727153901989186621)
        ·
          refine ⟨267679772682713245944983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 713812727153901989186621 267679772682713245944983)
          ·
            refine ⟨401519659024069868917475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 267679772682713245944983 401519659024069868917475)
            ·
              refine ⟨602279488536104803376213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 401519659024069868917475 602279488536104803376213)
              ·
                refine ⟨7057962756282478164565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 602279488536104803376213 7057962756282478164565)
                ·
                  rfl

theorem cell21_92781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 8].length) (baseStart_92781 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_92781 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_92781 prefixEnd_92781 := by exact prefixLift 92781
  have htrace : WordTrace (prefixWord ++ tailWord_92781) baseStart_92781 baseEnd_92781 := by
    simpa [prefixWord, tailWord_92781, baseEnd_92781] using wordTrace_append hprefix tailTrace_92781
  have hstable : (prefixWord ++ tailWord_92781).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92781).length < 2 ^ (prefixWord ++ tailWord_92781).sum := by decide
  have hdescent : baseEnd_92781 < baseStart_92781 := by decide
  rcases family_descends (prefixWord ++ tailWord_92781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_92888 : List Nat := [2, 1, 2, 2, 3, 3, 2, 1, 5]
def baseStart_92888 : Nat := 118140960795 + 92888 * 2 ^ 59
def prefixEnd_92888 : Nat := 4983230072969 + 3 ^ 40 * 92888 * 2
def baseEnd_92888 : Nat := 21198307126639026210143

theorem tailTrace_92888 : CollatzResearch.WordTrace tailWord_92888 prefixEnd_92888 21198307126639026210143 := by
  unfold tailWord_92888
  simp only [CollatzResearch.WordTrace]
  refine ⟨1693951843745057426255659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2258602458326743235007545 1693951843745057426255659)
  ·
    refine ⟨2540927765617586139383489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1693951843745057426255659 2540927765617586139383489)
    ·
      refine ⟨1905695824213189604537617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2540927765617586139383489 1905695824213189604537617)
      ·
        refine ⟨1429271868159892203403213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1905695824213189604537617 1429271868159892203403213)
        ·
          refine ⟨535976950559959576276205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1429271868159892203403213 535976950559959576276205)
          ·
            refine ⟨200991356459984841103577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 535976950559959576276205 200991356459984841103577)
            ·
              refine ⟨150743517344988630827683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 200991356459984841103577 150743517344988630827683)
              ·
                refine ⟨226115276017482946241525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 150743517344988630827683 226115276017482946241525)
                ·
                  refine ⟨21198307126639026210143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 226115276017482946241525 21198307126639026210143)
                  ·
                    rfl

theorem cell21_92888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 2, 1, 5].length) (baseStart_92888 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_92888 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_92888 prefixEnd_92888 := by exact prefixLift 92888
  have htrace : WordTrace (prefixWord ++ tailWord_92888) baseStart_92888 baseEnd_92888 := by
    simpa [prefixWord, tailWord_92888, baseEnd_92888] using wordTrace_append hprefix tailTrace_92888
  have hstable : (prefixWord ++ tailWord_92888).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_92888).length < 2 ^ (prefixWord ++ tailWord_92888).sum := by decide
  have hdescent : baseEnd_92888 < baseStart_92888 := by decide
  rcases family_descends (prefixWord ++ tailWord_92888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93023 : List Nat := [1, 1, 2, 3, 1, 3, 3, 2, 5]
def baseStart_93023 : Nat := 118140960795 + 93023 * 2 ^ 59
def prefixEnd_93023 : Nat := 4983230072969 + 3 ^ 40 * 93023 * 2
def baseEnd_93023 : Nat := 21229115965908791459867

theorem tailTrace_93023 : CollatzResearch.WordTrace tailWord_93023 prefixEnd_93023 21229115965908791459867 := by
  unfold tailWord_93023
  simp only [CollatzResearch.WordTrace]
  refine ⟨3392827542001032908675723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2261885028000688605783815 3392827542001032908675723)
  ·
    refine ⟨5089241313001549363013585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3392827542001032908675723 5089241313001549363013585)
    ·
      refine ⟨3816930984751162022260189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5089241313001549363013585 3816930984751162022260189)
      ·
        refine ⟨1431349119281685758347571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3816930984751162022260189 1431349119281685758347571)
        ·
          refine ⟨2147023678922528637521357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1431349119281685758347571 2147023678922528637521357)
          ·
            refine ⟨805133879595948239070509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2147023678922528637521357 805133879595948239070509)
            ·
              refine ⟨301925204848480589651441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 805133879595948239070509 301925204848480589651441)
              ·
                refine ⟨226443903636360442238581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 301925204848480589651441 226443903636360442238581)
                ·
                  refine ⟨21229115965908791459867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 226443903636360442238581 21229115965908791459867)
                  ·
                    rfl

theorem cell21_93023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 3, 2, 5].length) (baseStart_93023 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_93023 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_93023 prefixEnd_93023 := by exact prefixLift 93023
  have htrace : WordTrace (prefixWord ++ tailWord_93023) baseStart_93023 baseEnd_93023 := by
    simpa [prefixWord, tailWord_93023, baseEnd_93023] using wordTrace_append hprefix tailTrace_93023
  have hstable : (prefixWord ++ tailWord_93023).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93023).length < 2 ^ (prefixWord ++ tailWord_93023).sum := by decide
  have hdescent : baseEnd_93023 < baseStart_93023 := by decide
  rcases family_descends (prefixWord ++ tailWord_93023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93040 : List Nat := [2, 1, 1, 1, 4, 1, 3, 5, 3]
def baseStart_93040 : Nat := 118140960795 + 93040 * 2 ^ 59
def prefixEnd_93040 : Nat := 4983230072969 + 3 ^ 40 * 93040 * 2
def baseEnd_93040 : Nat := 21232995597520539676499

theorem tailTrace_93040 : CollatzResearch.WordTrace tailWord_93040 prefixEnd_93040 21232995597520539676499 := by
  unfold tailWord_93040
  simp only [CollatzResearch.WordTrace]
  refine ⟨1696723791469722406022287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2262298388626296541363049 1696723791469722406022287)
  ·
    refine ⟨2545085687204583609033431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1696723791469722406022287 2545085687204583609033431)
    ·
      refine ⟨3817628530806875413550147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2545085687204583609033431 3817628530806875413550147)
      ·
        refine ⟨5726442796210313120325221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3817628530806875413550147 5726442796210313120325221)
        ·
          refine ⟨1073708024289433710060979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5726442796210313120325221 1073708024289433710060979)
          ·
            refine ⟨1610562036434150565091469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1073708024289433710060979 1610562036434150565091469)
            ·
              refine ⟨603960763662806461909301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1610562036434150565091469 603960763662806461909301)
              ·
                refine ⟨56621321593388105803997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 603960763662806461909301 56621321593388105803997)
                ·
                  refine ⟨21232995597520539676499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56621321593388105803997 21232995597520539676499)
                  ·
                    rfl

theorem cell21_93040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 5, 3].length) (baseStart_93040 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_93040 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_93040 prefixEnd_93040 := by exact prefixLift 93040
  have htrace : WordTrace (prefixWord ++ tailWord_93040) baseStart_93040 baseEnd_93040 := by
    simpa [prefixWord, tailWord_93040, baseEnd_93040] using wordTrace_append hprefix tailTrace_93040
  have hstable : (prefixWord ++ tailWord_93040).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93040).length < 2 ^ (prefixWord ++ tailWord_93040).sum := by decide
  have hdescent : baseEnd_93040 < baseStart_93040 := by decide
  rcases family_descends (prefixWord ++ tailWord_93040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93144 : List Nat := [2, 1, 2, 2, 2, 3, 2, 7]
def baseStart_93144 : Nat := 118140960795 + 93144 * 2 ^ 59
def prefixEnd_93144 : Nat := 4983230072969 + 3 ^ 40 * 93144 * 2
def baseEnd_93144 : Nat := 7085576604813156647651

theorem tailTrace_93144 : CollatzResearch.WordTrace tailWord_93144 prefixEnd_93144 7085576604813156647651 := by
  unfold tailWord_93144
  simp only [CollatzResearch.WordTrace]
  refine ⟨1698620387281335286915243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2264827183041780382553657 1698620387281335286915243)
  ·
    refine ⟨2547930580922002930372865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1698620387281335286915243 2547930580922002930372865)
    ·
      refine ⟨1910947935691502197779649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2547930580922002930372865 1910947935691502197779649)
      ·
        refine ⟨1433210951768626648334737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1910947935691502197779649 1433210951768626648334737)
        ·
          refine ⟨1074908213826469986251053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1433210951768626648334737 1074908213826469986251053)
          ·
            refine ⟨403090580184926244844145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1074908213826469986251053 403090580184926244844145)
            ·
              refine ⟨302317935138694683633109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 403090580184926244844145 302317935138694683633109)
              ·
                refine ⟨7085576604813156647651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 302317935138694683633109 7085576604813156647651)
                ·
                  rfl

theorem cell21_93144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 7].length) (baseStart_93144 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_93144 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_93144 prefixEnd_93144 := by exact prefixLift 93144
  have htrace : WordTrace (prefixWord ++ tailWord_93144) baseStart_93144 baseEnd_93144 := by
    simpa [prefixWord, tailWord_93144, baseEnd_93144] using wordTrace_append hprefix tailTrace_93144
  have hstable : (prefixWord ++ tailWord_93144).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93144).length < 2 ^ (prefixWord ++ tailWord_93144).sum := by decide
  have hdescent : baseEnd_93144 < baseStart_93144 := by decide
  rcases family_descends (prefixWord ++ tailWord_93144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93223 : List Nat := [1, 1, 7, 1, 1, 2, 1, 1, 6]
def baseStart_93223 : Nat := 118140960795 + 93223 * 2 ^ 59
def prefixEnd_93223 : Nat := 4983230072969 + 3 ^ 40 * 93223 * 2
def baseEnd_93223 : Nat := 21274758690752888126125

theorem tailTrace_93223 : CollatzResearch.WordTrace tailWord_93223 prefixEnd_93223 21274758690752888126125 := by
  unfold tailWord_93223
  simp only [CollatzResearch.WordTrace]
  refine ⟨3400122141276467065956323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2266748094184311377304215 3400122141276467065956323)
  ·
    refine ⟨5100183211914700598934485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3400122141276467065956323 5100183211914700598934485)
    ·
      refine ⟨119535544029250795287527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 5100183211914700598934485 119535544029250795287527)
      ·
        refine ⟨179303316043876192931291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119535544029250795287527 179303316043876192931291)
        ·
          refine ⟨268954974065814289396937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179303316043876192931291 268954974065814289396937)
          ·
            refine ⟨201716230549360717047703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 268954974065814289396937 201716230549360717047703)
            ·
              refine ⟨302574345824041075571555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 201716230549360717047703 302574345824041075571555)
              ·
                refine ⟨453861518736061613357333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 302574345824041075571555 453861518736061613357333)
                ·
                  refine ⟨21274758690752888126125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 453861518736061613357333 21274758690752888126125)
                  ·
                    rfl

theorem cell21_93223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 1, 6].length) (baseStart_93223 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_93223 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_93223 prefixEnd_93223 := by exact prefixLift 93223
  have htrace : WordTrace (prefixWord ++ tailWord_93223) baseStart_93223 baseEnd_93223 := by
    simpa [prefixWord, tailWord_93223, baseEnd_93223] using wordTrace_append hprefix tailTrace_93223
  have hstable : (prefixWord ++ tailWord_93223).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93223).length < 2 ^ (prefixWord ++ tailWord_93223).sum := by decide
  have hdescent : baseEnd_93223 < baseStart_93223 := by decide
  rcases family_descends (prefixWord ++ tailWord_93223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93254 : List Nat := [6, 1, 1, 1, 1, 3, 1, 7]
def baseStart_93254 : Nat := 118140960795 + 93254 * 2 ^ 59
def prefixEnd_93254 : Nat := 4983230072969 + 3 ^ 40 * 93254 * 2
def baseEnd_93254 : Nat := 7093944437701241036465

theorem tailTrace_93254 : CollatzResearch.WordTrace tailWord_93254 prefixEnd_93254 7093944437701241036465 := by
  unfold tailWord_93254
  simp only [CollatzResearch.WordTrace]
  refine ⟨106289150130129980010463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 2267501869442772906889877 106289150130129980010463)
  ·
    refine ⟨159433725195194970015695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106289150130129980010463 159433725195194970015695)
    ·
      refine ⟨239150587792792455023543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 159433725195194970015695 239150587792792455023543)
      ·
        refine ⟨358725881689188682535315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 239150587792792455023543 358725881689188682535315)
        ·
          refine ⟨538088822533783023802973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 358725881689188682535315 538088822533783023802973)
          ·
            refine ⟨201783308450168633926115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 538088822533783023802973 201783308450168633926115)
            ·
              refine ⟨302674962675252950889173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 201783308450168633926115 302674962675252950889173)
              ·
                refine ⟨7093944437701241036465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 302674962675252950889173 7093944437701241036465)
                ·
                  rfl

theorem cell21_93254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 7].length) (baseStart_93254 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_93254 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_93254 prefixEnd_93254 := by exact prefixLift 93254
  have htrace : WordTrace (prefixWord ++ tailWord_93254) baseStart_93254 baseEnd_93254 := by
    simpa [prefixWord, tailWord_93254, baseEnd_93254] using wordTrace_append hprefix tailTrace_93254
  have hstable : (prefixWord ++ tailWord_93254).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93254).length < 2 ^ (prefixWord ++ tailWord_93254).sum := by decide
  have hdescent : baseEnd_93254 < baseStart_93254 := by decide
  rcases family_descends (prefixWord ++ tailWord_93254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93265 : List Nat := [1, 2, 2, 1, 3, 1, 3, 2, 6]
def baseStart_93265 : Nat := 118140960795 + 93265 * 2 ^ 59
def prefixEnd_93265 : Nat := 4983230072969 + 3 ^ 40 * 93265 * 2
def baseEnd_93265 : Nat := 21284343662970148426039

theorem tailTrace_93265 : CollatzResearch.WordTrace tailWord_93265 prefixEnd_93265 21284343662970148426039 := by
  unfold tailWord_93265
  simp only [CollatzResearch.WordTrace]
  refine ⟨3401654007124308238985249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2267769338082872159323499 3401654007124308238985249)
  ·
    refine ⟨2551240505343231179238937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3401654007124308238985249 2551240505343231179238937)
    ·
      refine ⟨1913430379007423384429203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2551240505343231179238937 1913430379007423384429203)
      ·
        refine ⟨2870145568511135076643805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1913430379007423384429203 2870145568511135076643805)
        ·
          refine ⟨1076304588191675653741427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2870145568511135076643805 1076304588191675653741427)
          ·
            refine ⟨1614456882287513480612141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1076304588191675653741427 1614456882287513480612141)
            ·
              refine ⟨605421330857817555229553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1614456882287513480612141 605421330857817555229553)
              ·
                refine ⟨454065998143363166422165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 605421330857817555229553 454065998143363166422165)
                ·
                  refine ⟨21284343662970148426039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 454065998143363166422165 21284343662970148426039)
                  ·
                    rfl

theorem cell21_93265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 2, 6].length) (baseStart_93265 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_93265 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_93265 prefixEnd_93265 := by exact prefixLift 93265
  have htrace : WordTrace (prefixWord ++ tailWord_93265) baseStart_93265 baseEnd_93265 := by
    simpa [prefixWord, tailWord_93265, baseEnd_93265] using wordTrace_append hprefix tailTrace_93265
  have hstable : (prefixWord ++ tailWord_93265).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93265).length < 2 ^ (prefixWord ++ tailWord_93265).sum := by decide
  have hdescent : baseEnd_93265 < baseStart_93265 := by decide
  rcases family_descends (prefixWord ++ tailWord_93265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93285 : List Nat := [1, 3, 1, 3, 2, 1, 5, 2, 3]
def baseStart_93285 : Nat := 118140960795 + 93285 * 2 ^ 59
def prefixEnd_93285 : Nat := 4983230072969 + 3 ^ 40 * 93285 * 2
def baseEnd_93285 : Nat := 21288907935454558092665

theorem tailTrace_93285 : CollatzResearch.WordTrace tailWord_93285 prefixEnd_93285 21288907935454558092665 := by
  unfold tailWord_93285
  simp only [CollatzResearch.WordTrace]
  refine ⟨3402383467051851654713309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2268255644701234436475539 3402383467051851654713309)
  ·
    refine ⟨1275893800144444370517491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3402383467051851654713309 1275893800144444370517491)
    ·
      refine ⟨1913840700216666555776237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1275893800144444370517491 1913840700216666555776237)
      ·
        refine ⟨717690262581249958416089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1913840700216666555776237 717690262581249958416089)
        ·
          refine ⟨538267696935937468812067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 717690262581249958416089 538267696935937468812067)
          ·
            refine ⟨807401545403906203218101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 538267696935937468812067 807401545403906203218101)
            ·
              refine ⟨75693894881616206551697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 807401545403906203218101 75693894881616206551697)
              ·
                refine ⟨56770421161212154913773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75693894881616206551697 56770421161212154913773)
                ·
                  refine ⟨21288907935454558092665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56770421161212154913773 21288907935454558092665)
                  ·
                    rfl

theorem cell21_93285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 5, 2, 3].length) (baseStart_93285 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_93285 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_93285 prefixEnd_93285 := by exact prefixLift 93285
  have htrace : WordTrace (prefixWord ++ tailWord_93285) baseStart_93285 baseEnd_93285 := by
    simpa [prefixWord, tailWord_93285, baseEnd_93285] using wordTrace_append hprefix tailTrace_93285
  have hstable : (prefixWord ++ tailWord_93285).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93285).length < 2 ^ (prefixWord ++ tailWord_93285).sum := by decide
  have hdescent : baseEnd_93285 < baseStart_93285 := by decide
  rcases family_descends (prefixWord ++ tailWord_93285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93296 : List Nat := [2, 1, 1, 1, 5, 1, 4, 6]
def baseStart_93296 : Nat := 118140960795 + 93296 * 2 ^ 59
def prefixEnd_93296 : Nat := 4983230072969 + 3 ^ 40 * 93296 * 2
def baseEnd_93296 : Nat := 7097139428440327803103

theorem tailTrace_93296 : CollatzResearch.WordTrace tailWord_93296 prefixEnd_93296 7097139428440327803103 := by
  unfold tailWord_93296
  simp only [CollatzResearch.WordTrace]
  refine ⟨1701392335006000266681871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2268523113341333688909161 1701392335006000266681871)
  ·
    refine ⟨2552088502509000400022807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1701392335006000266681871 2552088502509000400022807)
    ·
      refine ⟨3828132753763500600034211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2552088502509000400022807 3828132753763500600034211)
      ·
        refine ⟨5742199130645250900051317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3828132753763500600034211 5742199130645250900051317)
        ·
          refine ⟨538331168497992271879811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5742199130645250900051317 538331168497992271879811)
          ·
            refine ⟨807496752746988407819717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 538331168497992271879811 807496752746988407819717)
            ·
              refine ⟨151405641140060326466197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 807496752746988407819717 151405641140060326466197)
              ·
                refine ⟨7097139428440327803103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 151405641140060326466197 7097139428440327803103)
                ·
                  rfl

theorem cell21_93296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 4, 6].length) (baseStart_93296 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_93296 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_93296 prefixEnd_93296 := by exact prefixLift 93296
  have htrace : WordTrace (prefixWord ++ tailWord_93296) baseStart_93296 baseEnd_93296 := by
    simpa [prefixWord, tailWord_93296, baseEnd_93296] using wordTrace_append hprefix tailTrace_93296
  have hstable : (prefixWord ++ tailWord_93296).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93296).length < 2 ^ (prefixWord ++ tailWord_93296).sum := by decide
  have hdescent : baseEnd_93296 < baseStart_93296 := by decide
  rcases family_descends (prefixWord ++ tailWord_93296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93344 : List Nat := [2, 1, 1, 4, 2, 1, 3, 4, 3]
def baseStart_93344 : Nat := 118140960795 + 93344 * 2 ^ 59
def prefixEnd_93344 : Nat := 4983230072969 + 3 ^ 40 * 93344 * 2
def baseEnd_93344 : Nat := 21302372539283566609211

theorem tailTrace_93344 : CollatzResearch.WordTrace tailWord_93344 prefixEnd_93344 21302372539283566609211 := by
  unfold tailWord_93344
  simp only [CollatzResearch.WordTrace]
  refine ⟨1702267686919052365555543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2269690249225403154074057 1702267686919052365555543)
  ·
    refine ⟨2553401530378578548333315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1702267686919052365555543 2553401530378578548333315)
    ·
      refine ⟨3830102295567867822499973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2553401530378578548333315 3830102295567867822499973)
      ·
        refine ⟨718144180418975216718745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3830102295567867822499973 718144180418975216718745)
        ·
          refine ⟨538608135314231412539059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 718144180418975216718745 538608135314231412539059)
          ·
            refine ⟨807912202971347118808589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 538608135314231412539059 807912202971347118808589)
            ·
              refine ⟨302967076114255169553221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 807912202971347118808589 302967076114255169553221)
              ·
                refine ⟨56806326771422844291229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 302967076114255169553221 56806326771422844291229)
                ·
                  refine ⟨21302372539283566609211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56806326771422844291229 21302372539283566609211)
                  ·
                    rfl

theorem cell21_93344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 4, 3].length) (baseStart_93344 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_93344 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_93344 prefixEnd_93344 := by exact prefixLift 93344
  have htrace : WordTrace (prefixWord ++ tailWord_93344) baseStart_93344 baseEnd_93344 := by
    simpa [prefixWord, tailWord_93344, baseEnd_93344] using wordTrace_append hprefix tailTrace_93344
  have hstable : (prefixWord ++ tailWord_93344).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93344).length < 2 ^ (prefixWord ++ tailWord_93344).sum := by decide
  have hdescent : baseEnd_93344 < baseStart_93344 := by decide
  rcases family_descends (prefixWord ++ tailWord_93344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93431 : List Nat := [1, 1, 3, 1, 1, 1, 2, 11]
def baseStart_93431 : Nat := 118140960795 + 93431 * 2 ^ 59
def prefixEnd_93431 : Nat := 4983230072969 + 3 ^ 40 * 93431 * 2
def baseEnd_93431 : Nat := 7107409041530249553011

theorem tailTrace_93431 : CollatzResearch.WordTrace tailWord_93431 prefixEnd_93431 7107409041530249553011 := by
  unfold tailWord_93431
  simp only [CollatzResearch.WordTrace]
  refine ⟨3407708524522918589528147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2271805683015279059685431 3407708524522918589528147)
  ·
    refine ⟨5111562786784377884292221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3407708524522918589528147 5111562786784377884292221)
    ·
      refine ⟨1916836045044141706609583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5111562786784377884292221 1916836045044141706609583)
      ·
        refine ⟨2875254067566212559914375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1916836045044141706609583 2875254067566212559914375)
        ·
          refine ⟨4312881101349318839871563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2875254067566212559914375 4312881101349318839871563)
          ·
            refine ⟨6469321652023978259807345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4312881101349318839871563 6469321652023978259807345)
            ·
              refine ⟨4851991239017983694855509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6469321652023978259807345 4851991239017983694855509)
              ·
                refine ⟨7107409041530249553011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 4851991239017983694855509 7107409041530249553011)
                ·
                  rfl

theorem cell21_93431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 11].length) (baseStart_93431 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_93431 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_93431 prefixEnd_93431 := by exact prefixLift 93431
  have htrace : WordTrace (prefixWord ++ tailWord_93431) baseStart_93431 baseEnd_93431 := by
    simpa [prefixWord, tailWord_93431, baseEnd_93431] using wordTrace_append hprefix tailTrace_93431
  have hstable : (prefixWord ++ tailWord_93431).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93431).length < 2 ^ (prefixWord ++ tailWord_93431).sum := by decide
  have hdescent : baseEnd_93431 < baseStart_93431 := by decide
  rcases family_descends (prefixWord ++ tailWord_93431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93572 : List Nat := [2, 3, 2, 1, 1, 3, 2, 4, 3]
def baseStart_93572 : Nat := 118140960795 + 93572 * 2 ^ 59
def prefixEnd_93572 : Nat := 4983230072969 + 3 ^ 40 * 93572 * 2
def baseEnd_93572 : Nat := 21354405245605836808745

theorem tailTrace_93572 : CollatzResearch.WordTrace tailWord_93572 prefixEnd_93572 21354405245605836808745 := by
  unfold tailWord_93572
  simp only [CollatzResearch.WordTrace]
  refine ⟨1706425608506049835205485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2275234144674733113607313 1706425608506049835205485)
  ·
    refine ⟨639909603189768688202057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1706425608506049835205485 639909603189768688202057)
    ·
      refine ⟨479932202392326516151543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 639909603189768688202057 479932202392326516151543)
      ·
        refine ⟨719898303588489774227315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 479932202392326516151543 719898303588489774227315)
        ·
          refine ⟨1079847455382734661340973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 719898303588489774227315 1079847455382734661340973)
          ·
            refine ⟨404942795768525498002865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1079847455382734661340973 404942795768525498002865)
            ·
              refine ⟨303707096826394123502149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 404942795768525498002865 303707096826394123502149)
              ·
                refine ⟨56945080654948898156653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 303707096826394123502149 56945080654948898156653)
                ·
                  refine ⟨21354405245605836808745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56945080654948898156653 21354405245605836808745)
                  ·
                    rfl

theorem cell21_93572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 2, 4, 3].length) (baseStart_93572 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_93572 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_93572 prefixEnd_93572 := by exact prefixLift 93572
  have htrace : WordTrace (prefixWord ++ tailWord_93572) baseStart_93572 baseEnd_93572 := by
    simpa [prefixWord, tailWord_93572, baseEnd_93572] using wordTrace_append hprefix tailTrace_93572
  have hstable : (prefixWord ++ tailWord_93572).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93572).length < 2 ^ (prefixWord ++ tailWord_93572).sum := by decide
  have hdescent : baseEnd_93572 < baseStart_93572 := by decide
  rcases family_descends (prefixWord ++ tailWord_93572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93631 : List Nat := [1, 1, 2, 2, 2, 1, 1, 8, 3]
def baseStart_93631 : Nat := 118140960795 + 93631 * 2 ^ 59
def prefixEnd_93631 : Nat := 4983230072969 + 3 ^ 40 * 93631 * 2
def baseEnd_93631 : Nat := 21367869849434845325291

theorem tailTrace_93631 : CollatzResearch.WordTrace tailWord_93631 prefixEnd_93631 21367869849434845325291 := by
  unfold tailWord_93631
  simp only [CollatzResearch.WordTrace]
  refine ⟨3415003123798352746808747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2276668749198901831205831 3415003123798352746808747)
  ·
    refine ⟨5122504685697529120213121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3415003123798352746808747 5122504685697529120213121)
    ·
      refine ⟨3841878514273146840159841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5122504685697529120213121 3841878514273146840159841)
      ·
        refine ⟨2881408885704860130119881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3841878514273146840159841 2881408885704860130119881)
        ·
          refine ⟨2161056664278645097589911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2881408885704860130119881 2161056664278645097589911)
          ·
            refine ⟨3241584996417967646384867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2161056664278645097589911 3241584996417967646384867)
            ·
              refine ⟨4862377494626951469577301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3241584996417967646384867 4862377494626951469577301)
              ·
                refine ⟨56980986265159587534109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4862377494626951469577301 56980986265159587534109)
                ·
                  refine ⟨21367869849434845325291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56980986265159587534109 21367869849434845325291)
                  ·
                    rfl

theorem cell21_93631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 8, 3].length) (baseStart_93631 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_93631 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_93631 prefixEnd_93631 := by exact prefixLift 93631
  have htrace : WordTrace (prefixWord ++ tailWord_93631) baseStart_93631 baseEnd_93631 := by
    simpa [prefixWord, tailWord_93631, baseEnd_93631] using wordTrace_append hprefix tailTrace_93631
  have hstable : (prefixWord ++ tailWord_93631).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93631).length < 2 ^ (prefixWord ++ tailWord_93631).sum := by decide
  have hdescent : baseEnd_93631 < baseStart_93631 := by decide
  rcases family_descends (prefixWord ++ tailWord_93631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93682 : List Nat := [3, 2, 1, 4, 1, 3, 2, 2, 3]
def baseStart_93682 : Nat := 118140960795 + 93682 * 2 ^ 59
def prefixEnd_93682 : Nat := 4983230072969 + 3 ^ 40 * 93682 * 2
def baseEnd_93682 : Nat := 21379508744270089975187

theorem tailTrace_93682 : CollatzResearch.WordTrace tailWord_93682 prefixEnd_93682 21379508744270089975187 := by
  unfold tailWord_93682
  simp only [CollatzResearch.WordTrace]
  refine ⟨854215811653397114228825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2277908831075725637943533 854215811653397114228825)
  ·
    refine ⟨640661858740047835671619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 854215811653397114228825 640661858740047835671619)
    ·
      refine ⟨960992788110071753507429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 640661858740047835671619 960992788110071753507429)
      ·
        refine ⟨180186147770638453782643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 960992788110071753507429 180186147770638453782643)
        ·
          refine ⟨270279221655957680673965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180186147770638453782643 270279221655957680673965)
          ·
            refine ⟨101354708120984130252737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 270279221655957680673965 101354708120984130252737)
            ·
              refine ⟨76016031090738097689553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101354708120984130252737 76016031090738097689553)
              ·
                refine ⟨57012023318053573267165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76016031090738097689553 57012023318053573267165)
                ·
                  refine ⟨21379508744270089975187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57012023318053573267165 21379508744270089975187)
                  ·
                    rfl

theorem cell21_93682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 2, 2, 3].length) (baseStart_93682 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_93682 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_93682 prefixEnd_93682 := by exact prefixLift 93682
  have htrace : WordTrace (prefixWord ++ tailWord_93682) baseStart_93682 baseEnd_93682 := by
    simpa [prefixWord, tailWord_93682, baseEnd_93682] using wordTrace_append hprefix tailTrace_93682
  have hstable : (prefixWord ++ tailWord_93682).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93682).length < 2 ^ (prefixWord ++ tailWord_93682).sum := by decide
  have hdescent : baseEnd_93682 < baseStart_93682 := by decide
  rcases family_descends (prefixWord ++ tailWord_93682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93690 : List Nat := [3, 1, 1, 1, 1, 2, 4, 3, 5]
def baseStart_93690 : Nat := 118140960795 + 93690 * 2 ^ 59
def prefixEnd_93690 : Nat := 4983230072969 + 3 ^ 40 * 93690 * 2
def baseEnd_93690 : Nat := 21381334453263853841837

theorem tailTrace_93690 : CollatzResearch.WordTrace tailWord_93690 prefixEnd_93690 21381334453263853841837 := by
  unfold tailWord_93690
  simp only [CollatzResearch.WordTrace]
  refine ⟨854288757646151455801631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2278103353723070548804349 854288757646151455801631)
  ·
    refine ⟨1281433136469227183702447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 854288757646151455801631 1281433136469227183702447)
    ·
      refine ⟨1922149704703840775553671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1281433136469227183702447 1922149704703840775553671)
      ·
        refine ⟨2883224557055761163330507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1922149704703840775553671 2883224557055761163330507)
        ·
          refine ⟨4324836835583641744995761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2883224557055761163330507 4324836835583641744995761)
          ·
            refine ⟨3243627626687731308746821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4324836835583641744995761 3243627626687731308746821)
            ·
              refine ⟨608180180003949620390029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3243627626687731308746821 608180180003949620390029)
              ·
                refine ⟨228067567501481107646261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 608180180003949620390029 228067567501481107646261)
                ·
                  refine ⟨21381334453263853841837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 228067567501481107646261 21381334453263853841837)
                  ·
                    rfl

theorem cell21_93690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 3, 5].length) (baseStart_93690 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_93690 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_93690 prefixEnd_93690 := by exact prefixLift 93690
  have htrace : WordTrace (prefixWord ++ tailWord_93690) baseStart_93690 baseEnd_93690 := by
    simpa [prefixWord, tailWord_93690, baseEnd_93690] using wordTrace_append hprefix tailTrace_93690
  have hstable : (prefixWord ++ tailWord_93690).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93690).length < 2 ^ (prefixWord ++ tailWord_93690).sum := by decide
  have hdescent : baseEnd_93690 < baseStart_93690 := by decide
  rcases family_descends (prefixWord ++ tailWord_93690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93707 : List Nat := [1, 1, 1, 1, 8, 1, 1, 2, 5]
def baseStart_93707 : Nat := 118140960795 + 93707 * 2 ^ 59
def prefixEnd_93707 : Nat := 4983230072969 + 3 ^ 40 * 93707 * 2
def baseEnd_93707 : Nat := 21385214084875602058469

theorem tailTrace_93707 : CollatzResearch.WordTrace tailWord_93707 prefixEnd_93707 21385214084875602058469 := by
  unfold tailWord_93707
  simp only [CollatzResearch.WordTrace]
  refine ⟨3417775071523017726575375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2278516714348678484383583 3417775071523017726575375)
  ·
    refine ⟨5126662607284526589863063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3417775071523017726575375 5126662607284526589863063)
    ·
      refine ⟨7689993910926789884794595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5126662607284526589863063 7689993910926789884794595)
      ·
        refine ⟨11534990866390184827191893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7689993910926789884794595 11534990866390184827191893)
        ·
          refine ⟨135175674215509978443655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 11534990866390184827191893 135175674215509978443655)
          ·
            refine ⟨202763511323264967665483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135175674215509978443655 202763511323264967665483)
            ·
              refine ⟨304145266984897451498225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 202763511323264967665483 304145266984897451498225)
              ·
                refine ⟨228108950238673088623669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 304145266984897451498225 228108950238673088623669)
                ·
                  refine ⟨21385214084875602058469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 228108950238673088623669 21385214084875602058469)
                  ·
                    rfl

theorem cell21_93707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 2, 5].length) (baseStart_93707 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_93707 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_93707 prefixEnd_93707 := by exact prefixLift 93707
  have htrace : WordTrace (prefixWord ++ tailWord_93707) baseStart_93707 baseEnd_93707 := by
    simpa [prefixWord, tailWord_93707, baseEnd_93707] using wordTrace_append hprefix tailTrace_93707
  have hstable : (prefixWord ++ tailWord_93707).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93707).length < 2 ^ (prefixWord ++ tailWord_93707).sum := by decide
  have hdescent : baseEnd_93707 < baseStart_93707 := by decide
  rcases family_descends (prefixWord ++ tailWord_93707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93724 : List Nat := [2, 2, 3, 1, 2, 1, 4, 3, 3]
def baseStart_93724 : Nat := 118140960795 + 93724 * 2 ^ 59
def prefixEnd_93724 : Nat := 4983230072969 + 3 ^ 40 * 93724 * 2
def baseEnd_93724 : Nat := 21389093716487350275101

theorem tailTrace_93724 : CollatzResearch.WordTrace tailWord_93724 prefixEnd_93724 21389093716487350275101 := by
  unfold tailWord_93724
  simp only [CollatzResearch.WordTrace]
  refine ⟨1709197556230714814972113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2278930074974286419962817 1709197556230714814972113)
  ·
    refine ⟨1281898167173036111229085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1709197556230714814972113 1281898167173036111229085)
    ·
      refine ⟨480711812689888541710907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1281898167173036111229085 480711812689888541710907)
      ·
        refine ⟨721067719034832812566361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 480711812689888541710907 721067719034832812566361)
        ·
          refine ⟨540800789276124609424771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 721067719034832812566361 540800789276124609424771)
          ·
            refine ⟨811201183914186914137157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 540800789276124609424771 811201183914186914137157)
            ·
              refine ⟨152100221983910046400717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 811201183914186914137157 152100221983910046400717)
              ·
                refine ⟨57037583243966267400269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 152100221983910046400717 57037583243966267400269)
                ·
                  refine ⟨21389093716487350275101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57037583243966267400269 21389093716487350275101)
                  ·
                    rfl

theorem cell21_93724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 4, 3, 3].length) (baseStart_93724 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_93724 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_93724 prefixEnd_93724 := by exact prefixLift 93724
  have htrace : WordTrace (prefixWord ++ tailWord_93724) baseStart_93724 baseEnd_93724 := by
    simpa [prefixWord, tailWord_93724, baseEnd_93724] using wordTrace_append hprefix tailTrace_93724
  have hstable : (prefixWord ++ tailWord_93724).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93724).length < 2 ^ (prefixWord ++ tailWord_93724).sum := by decide
  have hdescent : baseEnd_93724 < baseStart_93724 := by decide
  rcases family_descends (prefixWord ++ tailWord_93724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93797 : List Nat := [1, 3, 1, 3, 3, 1, 2, 1, 6]
def baseStart_93797 : Nat := 118140960795 + 93797 * 2 ^ 59
def prefixEnd_93797 : Nat := 4983230072969 + 3 ^ 40 * 93797 * 2
def baseEnd_93797 : Nat := 21405753311055445558285

theorem tailTrace_93797 : CollatzResearch.WordTrace tailWord_93797 prefixEnd_93797 21405753311055445558285 := by
  unfold tailWord_93797
  simp only [CollatzResearch.WordTrace]
  refine ⟨3421057641196963097351645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2280705094131308731567763 3421057641196963097351645)
  ·
    refine ⟨1282896615448861161506867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3421057641196963097351645 1282896615448861161506867)
    ·
      refine ⟨1924344923173291742260301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1282896615448861161506867 1924344923173291742260301)
      ·
        refine ⟨721629346189984403347613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1924344923173291742260301 721629346189984403347613)
        ·
          refine ⟨270611004821244151255355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 721629346189984403347613 270611004821244151255355)
          ·
            refine ⟨405916507231866226883033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 270611004821244151255355 405916507231866226883033)
            ·
              refine ⟨304437380423899670162275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 405916507231866226883033 304437380423899670162275)
              ·
                refine ⟨456656070635849505243413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 304437380423899670162275 456656070635849505243413)
                ·
                  refine ⟨21405753311055445558285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 456656070635849505243413 21405753311055445558285)
                  ·
                    rfl

theorem cell21_93797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 1, 6].length) (baseStart_93797 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_93797 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_93797 prefixEnd_93797 := by exact prefixLift 93797
  have htrace : WordTrace (prefixWord ++ tailWord_93797) baseStart_93797 baseEnd_93797 := by
    simpa [prefixWord, tailWord_93797, baseEnd_93797] using wordTrace_append hprefix tailTrace_93797
  have hstable : (prefixWord ++ tailWord_93797).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93797).length < 2 ^ (prefixWord ++ tailWord_93797).sum := by decide
  have hdescent : baseEnd_93797 < baseStart_93797 := by decide
  rcases family_descends (prefixWord ++ tailWord_93797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93800 : List Nat := [2, 1, 4, 3, 1, 3, 1, 1, 5]
def baseStart_93800 : Nat := 118140960795 + 93800 * 2 ^ 59
def prefixEnd_93800 : Nat := 4983230072969 + 3 ^ 40 * 93800 * 2
def baseEnd_93800 : Nat := 21406437951928107008279

theorem tailTrace_93800 : CollatzResearch.WordTrace tailWord_93800 prefixEnd_93800 21406437951928107008279 := by
  unfold tailWord_93800
  simp only [CollatzResearch.WordTrace]
  refine ⟨1710583530093047304855427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2280778040124063073140569 1710583530093047304855427)
  ·
    refine ⟨2565875295139570957283141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1710583530093047304855427 2565875295139570957283141)
    ·
      refine ⟨481101617838669554490589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2565875295139570957283141 481101617838669554490589)
      ·
        refine ⟨180413106689501082933971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 481101617838669554490589 180413106689501082933971)
        ·
          refine ⟨270619660034251624400957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180413106689501082933971 270619660034251624400957)
          ·
            refine ⟨101482372512844359150359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 270619660034251624400957 101482372512844359150359)
            ·
              refine ⟨152223558769266538725539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101482372512844359150359 152223558769266538725539)
              ·
                refine ⟨228335338153899808088309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 152223558769266538725539 228335338153899808088309)
                ·
                  refine ⟨21406437951928107008279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 228335338153899808088309 21406437951928107008279)
                  ·
                    rfl

theorem cell21_93800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 1, 1, 5].length) (baseStart_93800 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_93800 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_93800 prefixEnd_93800 := by exact prefixLift 93800
  have htrace : WordTrace (prefixWord ++ tailWord_93800) baseStart_93800 baseEnd_93800 := by
    simpa [prefixWord, tailWord_93800, baseEnd_93800] using wordTrace_append hprefix tailTrace_93800
  have hstable : (prefixWord ++ tailWord_93800).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93800).length < 2 ^ (prefixWord ++ tailWord_93800).sum := by decide
  have hdescent : baseEnd_93800 < baseStart_93800 := by decide
  rcases family_descends (prefixWord ++ tailWord_93800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_93859 : List Nat := [1, 1, 1, 4, 1, 1, 5, 4, 3]
def baseStart_93859 : Nat := 118140960795 + 93859 * 2 ^ 59
def prefixEnd_93859 : Nat := 4983230072969 + 3 ^ 40 * 93859 * 2
def baseEnd_93859 : Nat := 21419902555757115524825

theorem tailTrace_93859 : CollatzResearch.WordTrace tailWord_93859 prefixEnd_93859 21419902555757115524825 := by
  unfold tailWord_93859
  simp only [CollatzResearch.WordTrace]
  refine ⟨3423318966972347686108631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2282212644648231790739087 3423318966972347686108631)
  ·
    refine ⟨5134978450458521529162947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3423318966972347686108631 5134978450458521529162947)
    ·
      refine ⟨7702467675687782293744421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5134978450458521529162947 7702467675687782293744421)
      ·
        refine ⟨1444212689191459180077079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7702467675687782293744421 1444212689191459180077079)
        ·
          refine ⟨2166319033787188770115619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1444212689191459180077079 2166319033787188770115619)
          ·
            refine ⟨3249478550680783155173429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2166319033787188770115619 3249478550680783155173429)
            ·
              refine ⟨304638614126323420797509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3249478550680783155173429 304638614126323420797509)
              ·
                refine ⟨57119740148685641399533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 304638614126323420797509 57119740148685641399533)
                ·
                  refine ⟨21419902555757115524825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57119740148685641399533 21419902555757115524825)
                  ·
                    rfl

theorem cell21_93859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 5, 4, 3].length) (baseStart_93859 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_93859 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_93859 prefixEnd_93859 := by exact prefixLift 93859
  have htrace : WordTrace (prefixWord ++ tailWord_93859) baseStart_93859 baseEnd_93859 := by
    simpa [prefixWord, tailWord_93859, baseEnd_93859] using wordTrace_append hprefix tailTrace_93859
  have hstable : (prefixWord ++ tailWord_93859).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_93859).length < 2 ^ (prefixWord ++ tailWord_93859).sum := by decide
  have hdescent : baseEnd_93859 < baseStart_93859 := by decide
  rcases family_descends (prefixWord ++ tailWord_93859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94025 : List Nat := [1, 2, 1, 1, 2, 4, 4, 2, 4]
def baseStart_94025 : Nat := 118140960795 + 94025 * 2 ^ 59
def prefixEnd_94025 : Nat := 4983230072969 + 3 ^ 40 * 94025 * 2
def baseEnd_94025 : Nat := 21457786017377715757819

theorem tailTrace_94025 : CollatzResearch.WordTrace tailWord_94025 prefixEnd_94025 21457786017377715757819 := by
  unfold tailWord_94025
  simp only [CollatzResearch.WordTrace]
  refine ⟨3429373484370958036651529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2286248989580638691101019 3429373484370958036651529)
  ·
    refine ⟨2572030113278218527488647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3429373484370958036651529 2572030113278218527488647)
    ·
      refine ⟨3858045169917327791232971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2572030113278218527488647 3858045169917327791232971)
      ·
        refine ⟨5787067754875991686849457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3858045169917327791232971 5787067754875991686849457)
        ·
          refine ⟨4340300816156993765137093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5787067754875991686849457 4340300816156993765137093)
          ·
            refine ⟨813806403029436330963205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4340300816156993765137093 813806403029436330963205)
            ·
              refine ⟨152588700568019312055601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 813806403029436330963205 152588700568019312055601)
              ·
                refine ⟨114441525426014484041701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 152588700568019312055601 114441525426014484041701)
                ·
                  refine ⟨21457786017377715757819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 114441525426014484041701 21457786017377715757819)
                  ·
                    rfl

theorem cell21_94025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 4, 2, 4].length) (baseStart_94025 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_94025 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_94025 prefixEnd_94025 := by exact prefixLift 94025
  have htrace : WordTrace (prefixWord ++ tailWord_94025) baseStart_94025 baseEnd_94025 := by
    simpa [prefixWord, tailWord_94025, baseEnd_94025] using wordTrace_append hprefix tailTrace_94025
  have hstable : (prefixWord ++ tailWord_94025).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94025).length < 2 ^ (prefixWord ++ tailWord_94025).sum := by decide
  have hdescent : baseEnd_94025 < baseStart_94025 := by decide
  rcases family_descends (prefixWord ++ tailWord_94025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94028 : List Nat := [2, 2, 1, 3, 4, 1, 1, 4, 3]
def baseStart_94028 : Nat := 118140960795 + 94028 * 2 ^ 59
def prefixEnd_94028 : Nat := 4983230072969 + 3 ^ 40 * 94028 * 2
def baseEnd_94028 : Nat := 21458470658250377207813

theorem tailTrace_94028 : CollatzResearch.WordTrace tailWord_94028 prefixEnd_94028 21458470658250377207813 := by
  unfold tailWord_94028
  simp only [CollatzResearch.WordTrace]
  refine ⟨1714741451680044774505369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2286321935573393032673825 1714741451680044774505369)
  ·
    refine ⟨1286056088760033580879027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1714741451680044774505369 1286056088760033580879027)
    ·
      refine ⟨1929084133140050371318541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1286056088760033580879027 1929084133140050371318541)
      ·
        refine ⟨723406549927518889244453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1929084133140050371318541 723406549927518889244453)
        ·
          refine ⟨135638728111409791733335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 723406549927518889244453 135638728111409791733335)
          ·
            refine ⟨203458092167114687600003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135638728111409791733335 203458092167114687600003)
            ·
              refine ⟨305187138250672031400005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 203458092167114687600003 305187138250672031400005)
              ·
                refine ⟨57222588422001005887501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 305187138250672031400005 57222588422001005887501)
                ·
                  refine ⟨21458470658250377207813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57222588422001005887501 21458470658250377207813)
                  ·
                    rfl

theorem cell21_94028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 4, 3].length) (baseStart_94028 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_94028 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_94028 prefixEnd_94028 := by exact prefixLift 94028
  have htrace : WordTrace (prefixWord ++ tailWord_94028) baseStart_94028 baseEnd_94028 := by
    simpa [prefixWord, tailWord_94028, baseEnd_94028] using wordTrace_append hprefix tailTrace_94028
  have hstable : (prefixWord ++ tailWord_94028).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94028).length < 2 ^ (prefixWord ++ tailWord_94028).sum := by decide
  have hdescent : baseEnd_94028 < baseStart_94028 := by decide
  rcases family_descends (prefixWord ++ tailWord_94028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94056 : List Nat := [2, 1, 4, 2, 1, 1, 5, 5]
def baseStart_94056 : Nat := 118140960795 + 94056 * 2 ^ 59
def prefixEnd_94056 : Nat := 4983230072969 + 3 ^ 40 * 94056 * 2
def baseEnd_94056 : Nat := 7154953546576183580363

theorem tailTrace_94056 : CollatzResearch.WordTrace tailWord_94056 prefixEnd_94056 7154953546576183580363 := by
  unfold tailWord_94056
  simp only [CollatzResearch.WordTrace]
  refine ⟨1715252073629325165515011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2287002764839100220686681 1715252073629325165515011)
  ·
    refine ⟨2572878110443987748272517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1715252073629325165515011 2572878110443987748272517)
    ·
      refine ⟨482414645708247702801097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2572878110443987748272517 482414645708247702801097)
      ·
        refine ⟨361810984281185777100823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 482414645708247702801097 361810984281185777100823)
        ·
          refine ⟨542716476421778665651235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 361810984281185777100823 542716476421778665651235)
          ·
            refine ⟨814074714632667998476853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 542716476421778665651235 814074714632667998476853)
            ·
              refine ⟨76319504496812624857205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 814074714632667998476853 76319504496812624857205)
              ·
                refine ⟨7154953546576183580363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 76319504496812624857205 7154953546576183580363)
                ·
                  rfl

theorem cell21_94056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 5, 5].length) (baseStart_94056 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_94056 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_94056 prefixEnd_94056 := by exact prefixLift 94056
  have htrace : WordTrace (prefixWord ++ tailWord_94056) baseStart_94056 baseEnd_94056 := by
    simpa [prefixWord, tailWord_94056, baseEnd_94056] using wordTrace_append hprefix tailTrace_94056
  have hstable : (prefixWord ++ tailWord_94056).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94056).length < 2 ^ (prefixWord ++ tailWord_94056).sum := by decide
  have hdescent : baseEnd_94056 < baseStart_94056 := by decide
  rcases family_descends (prefixWord ++ tailWord_94056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94087 : List Nat := [1, 1, 4, 2, 4, 1, 2, 1, 5]
def baseStart_94087 : Nat := 118140960795 + 94087 * 2 ^ 59
def prefixEnd_94087 : Nat := 4983230072969 + 3 ^ 40 * 94087 * 2
def baseEnd_94087 : Nat := 21471935262079385724359

theorem tailTrace_94087 : CollatzResearch.WordTrace tailWord_94087 prefixEnd_94087 21471935262079385724359 := by
  unfold tailWord_94087
  simp only [CollatzResearch.WordTrace]
  refine ⟨3431634810146342625408515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2287756540097561750272343 3431634810146342625408515)
  ·
    refine ⟨5147452215219513938112773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3431634810146342625408515 5147452215219513938112773)
    ·
      refine ⟨965147290353658863396145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5147452215219513938112773 965147290353658863396145)
      ·
        refine ⟨723860467765244147547109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 965147290353658863396145 723860467765244147547109)
        ·
          refine ⟨135723837705983277665083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 723860467765244147547109 135723837705983277665083)
          ·
            refine ⟨203585756558974916497625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135723837705983277665083 203585756558974916497625)
            ·
              refine ⟨152689317419231187373219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 203585756558974916497625 152689317419231187373219)
              ·
                refine ⟨229033976128846781059829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 152689317419231187373219 229033976128846781059829)
                ·
                  refine ⟨21471935262079385724359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 229033976128846781059829 21471935262079385724359)
                  ·
                    rfl

theorem cell21_94087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 2, 1, 5].length) (baseStart_94087 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_94087 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_94087 prefixEnd_94087 := by exact prefixLift 94087
  have htrace : WordTrace (prefixWord ++ tailWord_94087) baseStart_94087 baseEnd_94087 := by
    simpa [prefixWord, tailWord_94087, baseEnd_94087] using wordTrace_append hprefix tailTrace_94087
  have hstable : (prefixWord ++ tailWord_94087).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94087).length < 2 ^ (prefixWord ++ tailWord_94087).sum := by decide
  have hdescent : baseEnd_94087 < baseStart_94087 := by decide
  rcases family_descends (prefixWord ++ tailWord_94087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94214 : List Nat := [6, 2, 1, 2, 1, 1, 1, 2, 5]
def baseStart_94214 : Nat := 118140960795 + 94214 * 2 ^ 59
def prefixEnd_94214 : Nat := 4983230072969 + 3 ^ 40 * 94214 * 2
def baseEnd_94214 : Nat := 21500918392355387107433

theorem tailTrace_94214 : CollatzResearch.WordTrace tailWord_94214 prefixEnd_94214 21500918392355387107433 := by
  unfold tailWord_94214
  simp only [CollatzResearch.WordTrace]
  refine ⟨107383340021445103602553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 2290844587124162210187797 107383340021445103602553)
  ·
    refine ⟨80537505016083827701915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 107383340021445103602553 80537505016083827701915)
    ·
      refine ⟨120806257524125741552873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80537505016083827701915 120806257524125741552873)
      ·
        refine ⟨90604693143094306164655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120806257524125741552873 90604693143094306164655)
        ·
          refine ⟨135907039714641459246983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90604693143094306164655 135907039714641459246983)
          ·
            refine ⟨203860559571962188870475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135907039714641459246983 203860559571962188870475)
            ·
              refine ⟨305790839357943283305713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 203860559571962188870475 305790839357943283305713)
              ·
                refine ⟨229343129518457462479285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 305790839357943283305713 229343129518457462479285)
                ·
                  refine ⟨21500918392355387107433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 229343129518457462479285 21500918392355387107433)
                  ·
                    rfl

theorem cell21_94214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_94214 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_94214 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_94214 prefixEnd_94214 := by exact prefixLift 94214
  have htrace : WordTrace (prefixWord ++ tailWord_94214) baseStart_94214 baseEnd_94214 := by
    simpa [prefixWord, tailWord_94214, baseEnd_94214] using wordTrace_append hprefix tailTrace_94214
  have hstable : (prefixWord ++ tailWord_94214).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94214).length < 2 ^ (prefixWord ++ tailWord_94214).sum := by decide
  have hdescent : baseEnd_94214 < baseStart_94214 := by decide
  rcases family_descends (prefixWord ++ tailWord_94214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94222 : List Nat := [4, 1, 1, 2, 2, 1, 3, 2, 5]
def baseStart_94222 : Nat := 118140960795 + 94222 * 2 ^ 59
def prefixEnd_94222 : Nat := 4983230072969 + 3 ^ 40 * 94222 * 2
def baseEnd_94222 : Nat := 21502744101349150974083

theorem tailTrace_94222 : CollatzResearch.WordTrace tailWord_94222 prefixEnd_94222 21502744101349150974083 := by
  unfold tailWord_94222
  simp only [CollatzResearch.WordTrace]
  refine ⟨429569833082157585196615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2291039109771507121048613 429569833082157585196615)
  ·
    refine ⟨644354749623236377794923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 429569833082157585196615 644354749623236377794923)
    ·
      refine ⟨966532124434854566692385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 644354749623236377794923 966532124434854566692385)
      ·
        refine ⟨724899093326140925019289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 966532124434854566692385 724899093326140925019289)
        ·
          refine ⟨543674319994605693764467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 724899093326140925019289 543674319994605693764467)
          ·
            refine ⟨815511479991908540646701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 543674319994605693764467 815511479991908540646701)
            ·
              refine ⟨305816804996965702742513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 815511479991908540646701 305816804996965702742513)
              ·
                refine ⟨229362603747724277056885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 305816804996965702742513 229362603747724277056885)
                ·
                  refine ⟨21502744101349150974083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 229362603747724277056885 21502744101349150974083)
                  ·
                    rfl

theorem cell21_94222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 2, 5].length) (baseStart_94222 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_94222 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_94222 prefixEnd_94222 := by exact prefixLift 94222
  have htrace : WordTrace (prefixWord ++ tailWord_94222) baseStart_94222 baseEnd_94222 := by
    simpa [prefixWord, tailWord_94222, baseEnd_94222] using wordTrace_append hprefix tailTrace_94222
  have hstable : (prefixWord ++ tailWord_94222).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94222).length < 2 ^ (prefixWord ++ tailWord_94222).sum := by decide
  have hdescent : baseEnd_94222 < baseStart_94222 := by decide
  rcases family_descends (prefixWord ++ tailWord_94222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94239 : List Nat := [1, 1, 2, 4, 1, 2, 4, 3, 3]
def baseStart_94239 : Nat := 118140960795 + 94239 * 2 ^ 59
def prefixEnd_94239 : Nat := 4983230072969 + 3 ^ 40 * 94239 * 2
def baseEnd_94239 : Nat := 21506623732960899190715

theorem tailTrace_94239 : CollatzResearch.WordTrace tailWord_94239 prefixEnd_94239 21506623732960899190715 := by
  unfold tailWord_94239
  simp only [CollatzResearch.WordTrace]
  refine ⟨3437178705595672584941771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2291452470397115056627847 3437178705595672584941771)
  ·
    refine ⟨5155768058393508877412657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3437178705595672584941771 5155768058393508877412657)
    ·
      refine ⟨3866826043795131658059493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5155768058393508877412657 3866826043795131658059493)
      ·
        refine ⟨725029883211587185886155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3866826043795131658059493 725029883211587185886155)
        ·
          refine ⟨1087544824817380778829233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 725029883211587185886155 1087544824817380778829233)
          ·
            refine ⟨815658618613035584121925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1087544824817380778829233 815658618613035584121925)
            ·
              refine ⟨152935990989944172022861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 815658618613035584121925 152935990989944172022861)
              ·
                refine ⟨57350996621229064508573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 152935990989944172022861 57350996621229064508573)
                ·
                  refine ⟨21506623732960899190715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57350996621229064508573 21506623732960899190715)
                  ·
                    rfl

theorem cell21_94239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 4, 3, 3].length) (baseStart_94239 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_94239 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_94239 prefixEnd_94239 := by exact prefixLift 94239
  have htrace : WordTrace (prefixWord ++ tailWord_94239) baseStart_94239 baseEnd_94239 := by
    simpa [prefixWord, tailWord_94239, baseEnd_94239] using wordTrace_append hprefix tailTrace_94239
  have hstable : (prefixWord ++ tailWord_94239).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94239).length < 2 ^ (prefixWord ++ tailWord_94239).sum := by decide
  have hdescent : baseEnd_94239 < baseStart_94239 := by decide
  rcases family_descends (prefixWord ++ tailWord_94239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94281 : List Nat := [1, 2, 1, 1, 2, 2, 3, 4, 5]
def baseStart_94281 : Nat := 118140960795 + 94281 * 2 ^ 59
def prefixEnd_94281 : Nat := 4983230072969 + 3 ^ 40 * 94281 * 2
def baseEnd_94281 : Nat := 21516208705178159490629

theorem tailTrace_94281 : CollatzResearch.WordTrace tailWord_94281 prefixEnd_94281 21516208705178159490629 := by
  unfold tailWord_94281
  simp only [CollatzResearch.WordTrace]
  refine ⟨3438710571443513757970697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2292473714295675838647131 3438710571443513757970697)
  ·
    refine ⟨2579032928582635318478023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3438710571443513757970697 2579032928582635318478023)
    ·
      refine ⟨3868549392873952977717035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2579032928582635318478023 3868549392873952977717035)
      ·
        refine ⟨5802824089310929466575553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3868549392873952977717035 5802824089310929466575553)
        ·
          refine ⟨4352118066983197099931665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5802824089310929466575553 4352118066983197099931665)
          ·
            refine ⟨3264088550237397824948749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4352118066983197099931665 3264088550237397824948749)
            ·
              refine ⟨1224033206339024184355781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3264088550237397824948749 1224033206339024184355781)
              ·
                refine ⟨229506226188567034566709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1224033206339024184355781 229506226188567034566709)
                ·
                  refine ⟨21516208705178159490629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 229506226188567034566709 21516208705178159490629)
                  ·
                    rfl

theorem cell21_94281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 4, 5].length) (baseStart_94281 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_94281 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_94281 prefixEnd_94281 := by exact prefixLift 94281
  have htrace : WordTrace (prefixWord ++ tailWord_94281) baseStart_94281 baseEnd_94281 := by
    simpa [prefixWord, tailWord_94281, baseEnd_94281] using wordTrace_append hprefix tailTrace_94281
  have hstable : (prefixWord ++ tailWord_94281).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94281).length < 2 ^ (prefixWord ++ tailWord_94281).sum := by decide
  have hdescent : baseEnd_94281 < baseStart_94281 := by decide
  rcases family_descends (prefixWord ++ tailWord_94281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94329 : List Nat := [1, 2, 1, 3, 4, 2, 1, 3, 4]
def baseStart_94329 : Nat := 118140960795 + 94329 * 2 ^ 59
def prefixEnd_94329 : Nat := 4983230072969 + 3 ^ 40 * 94329 * 2
def baseEnd_94329 : Nat := 21527162959140742690531

theorem tailTrace_94329 : CollatzResearch.WordTrace tailWord_94329 prefixEnd_94329 21527162959140742690531 := by
  unfold tailWord_94329
  simp only [CollatzResearch.WordTrace]
  refine ⟨3440461275269617955718041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2293640850179745303812027 3440461275269617955718041)
  ·
    refine ⟨2580345956452213466788531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3440461275269617955718041 2580345956452213466788531)
    ·
      refine ⟨3870518934678320200182797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2580345956452213466788531 3870518934678320200182797)
      ·
        refine ⟨1451444600504370075068549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3870518934678320200182797 1451444600504370075068549)
        ·
          refine ⟨272145862594569389075353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1451444600504370075068549 272145862594569389075353)
          ·
            refine ⟨204109396945927041806515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 272145862594569389075353 204109396945927041806515)
            ·
              refine ⟨306164095418890562709773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 204109396945927041806515 306164095418890562709773)
              ·
                refine ⟨114811535782083961016165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 306164095418890562709773 114811535782083961016165)
                ·
                  refine ⟨21527162959140742690531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 114811535782083961016165 21527162959140742690531)
                  ·
                    rfl

theorem cell21_94329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 3, 4].length) (baseStart_94329 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_94329 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_94329 prefixEnd_94329 := by exact prefixLift 94329
  have htrace : WordTrace (prefixWord ++ tailWord_94329) baseStart_94329 baseEnd_94329 := by
    simpa [prefixWord, tailWord_94329, baseEnd_94329] using wordTrace_append hprefix tailTrace_94329
  have hstable : (prefixWord ++ tailWord_94329).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94329).length < 2 ^ (prefixWord ++ tailWord_94329).sum := by decide
  have hdescent : baseEnd_94329 < baseStart_94329 := by decide
  rcases family_descends (prefixWord ++ tailWord_94329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94366 : List Nat := [4, 3, 1, 1, 3, 2, 2, 2, 3]
def baseStart_94366 : Nat := 118140960795 + 94366 * 2 ^ 59
def prefixEnd_94366 : Nat := 4983230072969 + 3 ^ 40 * 94366 * 2
def baseEnd_94366 : Nat := 21535606863236900573789

theorem tailTrace_94366 : CollatzResearch.WordTrace tailWord_94366 prefixEnd_94366 21535606863236900573789 := by
  unfold tailWord_94366
  simp only [CollatzResearch.WordTrace]
  refine ⟨430226347016946659351869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2294540517423715516543301 430226347016946659351869)
  ·
    refine ⟨161334880131354997256951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 430226347016946659351869 161334880131354997256951)
    ·
      refine ⟨242002320197032495885427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161334880131354997256951 242002320197032495885427)
      ·
        refine ⟨363003480295548743828141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242002320197032495885427 363003480295548743828141)
        ·
          refine ⟨136126305110830778935553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 363003480295548743828141 136126305110830778935553)
          ·
            refine ⟨102094728833123084201665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 136126305110830778935553 102094728833123084201665)
            ·
              refine ⟨76571046624842313151249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102094728833123084201665 76571046624842313151249)
              ·
                refine ⟨57428284968631734863437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76571046624842313151249 57428284968631734863437)
                ·
                  refine ⟨21535606863236900573789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57428284968631734863437 21535606863236900573789)
                  ·
                    rfl

theorem cell21_94366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 2, 2, 3].length) (baseStart_94366 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_94366 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_94366 prefixEnd_94366 := by exact prefixLift 94366
  have htrace : WordTrace (prefixWord ++ tailWord_94366) baseStart_94366 baseEnd_94366 := by
    simpa [prefixWord, tailWord_94366, baseEnd_94366] using wordTrace_append hprefix tailTrace_94366
  have hstable : (prefixWord ++ tailWord_94366).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94366).length < 2 ^ (prefixWord ++ tailWord_94366).sum := by decide
  have hdescent : baseEnd_94366 < baseStart_94366 := by decide
  rcases family_descends (prefixWord ++ tailWord_94366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94422 : List Nat := [5, 2, 1, 2, 1, 2, 1, 1, 6]
def baseStart_94422 : Nat := 118140960795 + 94422 * 2 ^ 59
def prefixEnd_94422 : Nat := 4983230072969 + 3 ^ 40 * 94422 * 2
def baseEnd_94422 : Nat := 21548386826193247640341

theorem tailTrace_94422 : CollatzResearch.WordTrace tailWord_94422 prefixEnd_94422 21548386826193247640341 := by
  unfold tailWord_94422
  simp only [CollatzResearch.WordTrace]
  refine ⟨215240828995793427428345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2295902175955129892569013 215240828995793427428345)
  ·
    refine ⟨161430621746845070571259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215240828995793427428345 161430621746845070571259)
    ·
      refine ⟨242145932620267605856889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161430621746845070571259 242145932620267605856889)
      ·
        refine ⟨181609449465200704392667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 242145932620267605856889 181609449465200704392667)
        ·
          refine ⟨272414174197801056589001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 181609449465200704392667 272414174197801056589001)
          ·
            refine ⟨204310630648350792441751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 272414174197801056589001 204310630648350792441751)
            ·
              refine ⟨306465945972526188662627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 204310630648350792441751 306465945972526188662627)
              ·
                refine ⟨459698918958789282993941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 306465945972526188662627 459698918958789282993941)
                ·
                  refine ⟨21548386826193247640341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 459698918958789282993941 21548386826193247640341)
                  ·
                    rfl

theorem cell21_94422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_94422 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_94422 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_94422 prefixEnd_94422 := by exact prefixLift 94422
  have htrace : WordTrace (prefixWord ++ tailWord_94422) baseStart_94422 baseEnd_94422 := by
    simpa [prefixWord, tailWord_94422, baseEnd_94422] using wordTrace_append hprefix tailTrace_94422
  have hstable : (prefixWord ++ tailWord_94422).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94422).length < 2 ^ (prefixWord ++ tailWord_94422).sum := by decide
  have hdescent : baseEnd_94422 < baseStart_94422 := by decide
  rcases family_descends (prefixWord ++ tailWord_94422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94450 : List Nat := [3, 2, 1, 3, 2, 1, 2, 2, 5]
def baseStart_94450 : Nat := 118140960795 + 94450 * 2 ^ 59
def prefixEnd_94450 : Nat := 4983230072969 + 3 ^ 40 * 94450 * 2
def baseEnd_94450 : Nat := 21554776807671421173617

theorem tailTrace_94450 : CollatzResearch.WordTrace tailWord_94450 prefixEnd_94450 21554776807671421173617 := by
  unfold tailWord_94450
  simp only [CollatzResearch.WordTrace]
  refine ⟨861218626957813905218201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2296583005220837080581869 861218626957813905218201)
  ·
    refine ⟨645913970218360428913651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 861218626957813905218201 645913970218360428913651)
    ·
      refine ⟨968870955327540643370477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 645913970218360428913651 968870955327540643370477)
      ·
        refine ⟨363326608247827741263929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 968870955327540643370477 363326608247827741263929)
        ·
          refine ⟨272494956185870805947947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 363326608247827741263929 272494956185870805947947)
          ·
            refine ⟨408742434278806208921921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 272494956185870805947947 408742434278806208921921)
            ·
              refine ⟨306556825709104656691441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 408742434278806208921921 306556825709104656691441)
              ·
                refine ⟨229917619281828492518581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 306556825709104656691441 229917619281828492518581)
                ·
                  refine ⟨21554776807671421173617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 229917619281828492518581 21554776807671421173617)
                  ·
                    rfl

theorem cell21_94450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 2, 5].length) (baseStart_94450 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_94450 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_94450 prefixEnd_94450 := by exact prefixLift 94450
  have htrace : WordTrace (prefixWord ++ tailWord_94450) baseStart_94450 baseEnd_94450 := by
    simpa [prefixWord, tailWord_94450, baseEnd_94450] using wordTrace_append hprefix tailTrace_94450
  have hstable : (prefixWord ++ tailWord_94450).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94450).length < 2 ^ (prefixWord ++ tailWord_94450).sum := by decide
  have hdescent : baseEnd_94450 < baseStart_94450 := by decide
  rcases family_descends (prefixWord ++ tailWord_94450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94495 : List Nat := [1, 1, 2, 4, 3, 2, 2, 6]
def baseStart_94495 : Nat := 118140960795 + 94495 * 2 ^ 59
def prefixEnd_94495 : Nat := 4983230072969 + 3 ^ 40 * 94495 * 2
def baseEnd_94495 : Nat := 7188348806920447641175

theorem tailTrace_94495 : CollatzResearch.WordTrace tailWord_94495 prefixEnd_94495 7188348806920447641175 := by
  unfold tailWord_94495
  simp only [CollatzResearch.WordTrace]
  refine ⟨3446515792668228306260939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2297677195112152204173959 3446515792668228306260939)
  ·
    refine ⟨5169773689002342459391409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3446515792668228306260939 5169773689002342459391409)
    ·
      refine ⟨3877330266751756844543557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5169773689002342459391409 3877330266751756844543557)
      ·
        refine ⟨726999425015954408351917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3877330266751756844543557 726999425015954408351917)
        ·
          refine ⟨272624784380982903131969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 726999425015954408351917 272624784380982903131969)
          ·
            refine ⟨204468588285737177348977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 272624784380982903131969 204468588285737177348977)
            ·
              refine ⟨153351441214302883011733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 204468588285737177348977 153351441214302883011733)
              ·
                refine ⟨7188348806920447641175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 153351441214302883011733 7188348806920447641175)
                ·
                  rfl

theorem cell21_94495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 2, 2, 6].length) (baseStart_94495 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_94495 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_94495 prefixEnd_94495 := by exact prefixLift 94495
  have htrace : WordTrace (prefixWord ++ tailWord_94495) baseStart_94495 baseEnd_94495 := by
    simpa [prefixWord, tailWord_94495, baseEnd_94495] using wordTrace_append hprefix tailTrace_94495
  have hstable : (prefixWord ++ tailWord_94495).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94495).length < 2 ^ (prefixWord ++ tailWord_94495).sum := by decide
  have hdescent : baseEnd_94495 < baseStart_94495 := by decide
  rcases family_descends (prefixWord ++ tailWord_94495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94498 : List Nat := [3, 3, 1, 1, 3, 1, 4, 1, 4]
def baseStart_94498 : Nat := 118140960795 + 94498 * 2 ^ 59
def prefixEnd_94498 : Nat := 4983230072969 + 3 ^ 40 * 94498 * 2
def baseEnd_94498 : Nat := 21565731061634004373519

theorem tailTrace_94498 : CollatzResearch.WordTrace tailWord_94498 prefixEnd_94498 21565731061634004373519 := by
  unfold tailWord_94498
  simp only [CollatzResearch.WordTrace]
  refine ⟨861656302914339954655037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2297750141104906545746765 861656302914339954655037)
  ·
    refine ⟨323121113592877482995639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 861656302914339954655037 323121113592877482995639)
    ·
      refine ⟨484681670389316224493459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 323121113592877482995639 484681670389316224493459)
      ·
        refine ⟨727022505583974336740189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 484681670389316224493459 727022505583974336740189)
        ·
          refine ⟨272633439593990376277571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 727022505583974336740189 272633439593990376277571)
          ·
            refine ⟨408950159390985564416357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 272633439593990376277571 408950159390985564416357)
            ·
              refine ⟨76678154885809793328067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 408950159390985564416357 76678154885809793328067)
              ·
                refine ⟨115017232328714689992101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76678154885809793328067 115017232328714689992101)
                ·
                  refine ⟨21565731061634004373519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 115017232328714689992101 21565731061634004373519)
                  ·
                    rfl

theorem cell21_94498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 4, 1, 4].length) (baseStart_94498 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_94498 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_94498 prefixEnd_94498 := by exact prefixLift 94498
  have htrace : WordTrace (prefixWord ++ tailWord_94498) baseStart_94498 baseEnd_94498 := by
    simpa [prefixWord, tailWord_94498, baseEnd_94498] using wordTrace_append hprefix tailTrace_94498
  have hstable : (prefixWord ++ tailWord_94498).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94498).length < 2 ^ (prefixWord ++ tailWord_94498).sum := by decide
  have hdescent : baseEnd_94498 < baseStart_94498 := by decide
  rcases family_descends (prefixWord ++ tailWord_94498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94678 : List Nat := [5, 2, 1, 1, 1, 1, 2, 1, 7]
def baseStart_94678 : Nat := 118140960795 + 94678 * 2 ^ 59
def prefixEnd_94678 : Nat := 4983230072969 + 3 ^ 40 * 94678 * 2
def baseEnd_94678 : Nat := 21606809513993691373151

theorem tailTrace_94678 : CollatzResearch.WordTrace tailWord_94678 prefixEnd_94678 21606809513993691373151 := by
  unfold tailWord_94678
  simp only [CollatzResearch.WordTrace]
  refine ⟨215824396937828160010793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2302126900670167040115125 215824396937828160010793)
  ·
    refine ⟨161868297703371120008095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 215824396937828160010793 161868297703371120008095)
    ·
      refine ⟨242802446555056680012143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 161868297703371120008095 242802446555056680012143)
      ·
        refine ⟨364203669832585020018215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 242802446555056680012143 364203669832585020018215)
        ·
          refine ⟨546305504748877530027323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 364203669832585020018215 546305504748877530027323)
          ·
            refine ⟨819458257123316295040985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 546305504748877530027323 819458257123316295040985)
            ·
              refine ⟨614593692842487221280739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 819458257123316295040985 614593692842487221280739)
              ·
                refine ⟨921890539263730831921109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 614593692842487221280739 921890539263730831921109)
                ·
                  refine ⟨21606809513993691373151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 921890539263730831921109 21606809513993691373151)
                  ·
                    rfl

theorem cell21_94678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_94678 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_94678 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_94678 prefixEnd_94678 := by exact prefixLift 94678
  have htrace : WordTrace (prefixWord ++ tailWord_94678) baseStart_94678 baseEnd_94678 := by
    simpa [prefixWord, tailWord_94678, baseEnd_94678] using wordTrace_append hprefix tailTrace_94678
  have hstable : (prefixWord ++ tailWord_94678).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94678).length < 2 ^ (prefixWord ++ tailWord_94678).sum := by decide
  have hdescent : baseEnd_94678 < baseStart_94678 := by decide
  rcases family_descends (prefixWord ++ tailWord_94678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94706 : List Nat := [3, 2, 1, 4, 11]
def baseStart_94706 : Nat := 118140960795 + 94706 * 2 ^ 59
def prefixEnd_94706 : Nat := 4983230072969 + 3 ^ 40 * 94706 * 2
def baseEnd_94706 : Nat := 266829623400887221067

theorem tailTrace_94706 : CollatzResearch.WordTrace tailWord_94706 prefixEnd_94706 266829623400887221067 := by
  unfold tailWord_94706
  simp only [CollatzResearch.WordTrace]
  refine ⟨863552898725952835547993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2302807729935874228127981 863552898725952835547993)
  ·
    refine ⟨647664674044464626660995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 863552898725952835547993 647664674044464626660995)
    ·
      refine ⟨971497011066696939991493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 647664674044464626660995 971497011066696939991493)
      ·
        refine ⟨182155689575005676248405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 971497011066696939991493 182155689575005676248405)
        ·
          refine ⟨266829623400887221067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 182155689575005676248405 266829623400887221067)
          ·
            rfl

theorem cell21_94706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 11].length) (baseStart_94706 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_94706 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_94706 prefixEnd_94706 := by exact prefixLift 94706
  have htrace : WordTrace (prefixWord ++ tailWord_94706) baseStart_94706 baseEnd_94706 := by
    simpa [prefixWord, tailWord_94706, baseEnd_94706] using wordTrace_append hprefix tailTrace_94706
  have hstable : (prefixWord ++ tailWord_94706).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94706).length < 2 ^ (prefixWord ++ tailWord_94706).sum := by decide
  have hdescent : baseEnd_94706 < baseStart_94706 := by decide
  rcases family_descends (prefixWord ++ tailWord_94706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94720 : List Nat := [2, 1, 1, 2, 1, 1, 1, 1, 11]
def baseStart_94720 : Nat := 118140960795 + 94720 * 2 ^ 59
def prefixEnd_94720 : Nat := 4983230072969 + 3 ^ 40 * 94720 * 2
def baseEnd_94720 : Nat := 21616394486210951673065

theorem tailTrace_94720 : CollatzResearch.WordTrace tailWord_94720 prefixEnd_94720 21616394486210951673065 := by
  unfold tailWord_94720
  simp only [CollatzResearch.WordTrace]
  refine ⟨1727361108426545866600807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2303148144568727822134409 1727361108426545866600807)
  ·
    refine ⟨2591041662639818799901211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1727361108426545866600807 2591041662639818799901211)
    ·
      refine ⟨3886562493959728199851817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2591041662639818799901211 3886562493959728199851817)
      ·
        refine ⟨2914921870469796149888863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3886562493959728199851817 2914921870469796149888863)
        ·
          refine ⟨4372382805704694224833295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2914921870469796149888863 4372382805704694224833295)
          ·
            refine ⟨6558574208557041337249943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4372382805704694224833295 6558574208557041337249943)
            ·
              refine ⟨9837861312835562005874915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6558574208557041337249943 9837861312835562005874915)
              ·
                refine ⟨14756791969253343008812373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9837861312835562005874915 14756791969253343008812373)
                ·
                  refine ⟨21616394486210951673065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 14756791969253343008812373 21616394486210951673065)
                  ·
                    rfl

theorem cell21_94720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 11].length) (baseStart_94720 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_94720 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_94720 prefixEnd_94720 := by exact prefixLift 94720
  have htrace : WordTrace (prefixWord ++ tailWord_94720) baseStart_94720 baseEnd_94720 := by
    simpa [prefixWord, tailWord_94720, baseEnd_94720] using wordTrace_append hprefix tailTrace_94720
  have hstable : (prefixWord ++ tailWord_94720).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94720).length < 2 ^ (prefixWord ++ tailWord_94720).sum := by decide
  have hdescent : baseEnd_94720 < baseStart_94720 := by decide
  rcases family_descends (prefixWord ++ tailWord_94720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94751 : List Nat := [1, 1, 2, 4, 1, 1, 1, 4, 6]
def baseStart_94751 : Nat := 118140960795 + 94751 * 2 ^ 59
def prefixEnd_94751 : Nat := 4983230072969 + 3 ^ 40 * 94751 * 2
def baseEnd_94751 : Nat := 21623469108561786656335

theorem tailTrace_94751 : CollatzResearch.WordTrace tailWord_94751 prefixEnd_94751 21623469108561786656335 := by
  unfold tailWord_94751
  simp only [CollatzResearch.WordTrace]
  refine ⟨3455852879740784027580107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2303901919827189351720071 3455852879740784027580107)
  ·
    refine ⟨5183779319611176041370161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3455852879740784027580107 5183779319611176041370161)
    ·
      refine ⟨3887834489708382031027621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5183779319611176041370161 3887834489708382031027621)
      ·
        refine ⟨728968966820321630817679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3887834489708382031027621 728968966820321630817679)
        ·
          refine ⟨1093453450230482446226519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 728968966820321630817679 1093453450230482446226519)
          ·
            refine ⟨1640180175345723669339779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1093453450230482446226519 1640180175345723669339779)
            ·
              refine ⟨2460270263018585504009669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1640180175345723669339779 2460270263018585504009669)
              ·
                refine ⟨461300674315984782001813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2460270263018585504009669 461300674315984782001813)
                ·
                  refine ⟨21623469108561786656335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 461300674315984782001813 21623469108561786656335)
                  ·
                    rfl

theorem cell21_94751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 4, 6].length) (baseStart_94751 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_94751 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_94751 prefixEnd_94751 := by exact prefixLift 94751
  have htrace : WordTrace (prefixWord ++ tailWord_94751) baseStart_94751 baseEnd_94751 := by
    simpa [prefixWord, tailWord_94751, baseEnd_94751] using wordTrace_append hprefix tailTrace_94751
  have hstable : (prefixWord ++ tailWord_94751).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94751).length < 2 ^ (prefixWord ++ tailWord_94751).sum := by decide
  have hdescent : baseEnd_94751 < baseStart_94751 := by decide
  rcases family_descends (prefixWord ++ tailWord_94751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94768 : List Nat := [2, 1, 1, 1, 2, 3, 5, 2, 4]
def baseStart_94768 : Nat := 118140960795 + 94768 * 2 ^ 59
def prefixEnd_94768 : Nat := 4983230072969 + 3 ^ 40 * 94768 * 2
def baseEnd_94768 : Nat := 21627348740173534872967

theorem tailTrace_94768 : CollatzResearch.WordTrace tailWord_94768 prefixEnd_94768 21627348740173534872967 := by
  unfold tailWord_94768
  simp only [CollatzResearch.WordTrace]
  refine ⟨1728236460339597965474479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2304315280452797287299305 1728236460339597965474479)
  ·
    refine ⟨2592354690509396948211719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1728236460339597965474479 2592354690509396948211719)
    ·
      refine ⟨3888532035764095422317579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2592354690509396948211719 3888532035764095422317579)
      ·
        refine ⟨5832798053646143133476369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3888532035764095422317579 5832798053646143133476369)
        ·
          refine ⟨4374598540234607350107277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5832798053646143133476369 4374598540234607350107277)
          ·
            refine ⟨1640474452587977756290229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4374598540234607350107277 1640474452587977756290229)
            ·
              refine ⟨153794479930122914652209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1640474452587977756290229 153794479930122914652209)
              ·
                refine ⟨115345859947592185989157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 153794479930122914652209 115345859947592185989157)
                ·
                  refine ⟨21627348740173534872967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 115345859947592185989157 21627348740173534872967)
                  ·
                    rfl

theorem cell21_94768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 5, 2, 4].length) (baseStart_94768 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_94768 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_94768 prefixEnd_94768 := by exact prefixLift 94768
  have htrace : WordTrace (prefixWord ++ tailWord_94768) baseStart_94768 baseEnd_94768 := by
    simpa [prefixWord, tailWord_94768, baseEnd_94768] using wordTrace_append hprefix tailTrace_94768
  have hstable : (prefixWord ++ tailWord_94768).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94768).length < 2 ^ (prefixWord ++ tailWord_94768).sum := by decide
  have hdescent : baseEnd_94768 < baseStart_94768 := by decide
  rcases family_descends (prefixWord ++ tailWord_94768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94830 : List Nat := [4, 1, 2, 2, 2, 1, 3, 1, 5]
def baseStart_94830 : Nat := 118140960795 + 94830 * 2 ^ 59
def prefixEnd_94830 : Nat := 4983230072969 + 3 ^ 40 * 94830 * 2
def baseEnd_94830 : Nat := 21641497984875204839507

theorem tailTrace_94830 : CollatzResearch.WordTrace tailWord_94830 prefixEnd_94830 21641497984875204839507 := by
  unfold tailWord_94830
  simp only [CollatzResearch.WordTrace]
  refine ⟨432341780806822564963243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2305822830969720346470629 432341780806822564963243)
  ·
    refine ⟨648512671210233847444865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 432341780806822564963243 648512671210233847444865)
    ·
      refine ⟨486384503407675385583649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 648512671210233847444865 486384503407675385583649)
      ·
        refine ⟨364788377555756539187737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 486384503407675385583649 364788377555756539187737)
        ·
          refine ⟨273591283166817404390803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 364788377555756539187737 273591283166817404390803)
          ·
            refine ⟨410386924750226106586205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 273591283166817404390803 410386924750226106586205)
            ·
              refine ⟨153895096781334789969827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 410386924750226106586205 153895096781334789969827)
              ·
                refine ⟨230842645172002184954741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 153895096781334789969827 230842645172002184954741)
                ·
                  refine ⟨21641497984875204839507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 230842645172002184954741 21641497984875204839507)
                  ·
                    rfl

theorem cell21_94830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 3, 1, 5].length) (baseStart_94830 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_94830 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_94830 prefixEnd_94830 := by exact prefixLift 94830
  have htrace : WordTrace (prefixWord ++ tailWord_94830) baseStart_94830 baseEnd_94830 := by
    simpa [prefixWord, tailWord_94830, baseEnd_94830] using wordTrace_append hprefix tailTrace_94830
  have hstable : (prefixWord ++ tailWord_94830).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94830).length < 2 ^ (prefixWord ++ tailWord_94830).sum := by decide
  have hdescent : baseEnd_94830 < baseStart_94830 := by decide
  rcases family_descends (prefixWord ++ tailWord_94830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94881 : List Nat := [1, 2, 3, 3, 4, 1, 2, 2, 3]
def baseStart_94881 : Nat := 118140960795 + 94881 * 2 ^ 59
def prefixEnd_94881 : Nat := 4983230072969 + 3 ^ 40 * 94881 * 2
def baseEnd_94881 : Nat := 21653136879710449489403

theorem tailTrace_94881 : CollatzResearch.WordTrace tailWord_94881 prefixEnd_94881 21653136879710449489403 := by
  unfold tailWord_94881
  simp only [CollatzResearch.WordTrace]
  refine ⟨3460594369269816229812497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2307062912846544153208331 3460594369269816229812497)
  ·
    refine ⟨2595445776952362172359373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3460594369269816229812497 2595445776952362172359373)
    ·
      refine ⟨973292166357135814634765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2595445776952362172359373 973292166357135814634765)
      ·
        refine ⟨364984562383925930488037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 973292166357135814634765 364984562383925930488037)
        ·
          refine ⟨68434605446986111966507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 364984562383925930488037 68434605446986111966507)
          ·
            refine ⟨102651908170479167949761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68434605446986111966507 102651908170479167949761)
            ·
              refine ⟨76988931127859375962321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102651908170479167949761 76988931127859375962321)
              ·
                refine ⟨57741698345894531971741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76988931127859375962321 57741698345894531971741)
                ·
                  refine ⟨21653136879710449489403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57741698345894531971741 21653136879710449489403)
                  ·
                    rfl

theorem cell21_94881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 2, 2, 3].length) (baseStart_94881 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_94881 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_94881 prefixEnd_94881 := by exact prefixLift 94881
  have htrace : WordTrace (prefixWord ++ tailWord_94881) baseStart_94881 baseEnd_94881 := by
    simpa [prefixWord, tailWord_94881, baseEnd_94881] using wordTrace_append hprefix tailTrace_94881
  have hstable : (prefixWord ++ tailWord_94881).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94881).length < 2 ^ (prefixWord ++ tailWord_94881).sum := by decide
  have hdescent : baseEnd_94881 < baseStart_94881 := by decide
  rcases family_descends (prefixWord ++ tailWord_94881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94993 : List Nat := [1, 2, 2, 1, 1, 3, 11]
def baseStart_94993 : Nat := 118140960795 + 94993 * 2 ^ 59
def prefixEnd_94993 : Nat := 4983230072969 + 3 ^ 40 * 94993 * 2
def baseEnd_94993 : Nat := 2408744089513682624723

theorem tailTrace_94993 : CollatzResearch.WordTrace tailWord_94993 prefixEnd_94993 2408744089513682624723 := by
  unfold tailWord_94993
  simp only [CollatzResearch.WordTrace]
  refine ⟨3464679344864059357889633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2309786229909372905259755 3464679344864059357889633)
  ·
    refine ⟨2598509508648044518417225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3464679344864059357889633 2598509508648044518417225)
    ·
      refine ⟨1948882131486033388812919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2598509508648044518417225 1948882131486033388812919)
      ·
        refine ⟨2923323197229050083219379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1948882131486033388812919 2923323197229050083219379)
        ·
          refine ⟨4384984795843575124829069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2923323197229050083219379 4384984795843575124829069)
          ·
            refine ⟨1644369298441340671810901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4384984795843575124829069 1644369298441340671810901)
            ·
              refine ⟨2408744089513682624723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 1644369298441340671810901 2408744089513682624723)
              ·
                rfl

theorem cell21_94993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 11].length) (baseStart_94993 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_94993 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_94993 prefixEnd_94993 := by exact prefixLift 94993
  have htrace : WordTrace (prefixWord ++ tailWord_94993) baseStart_94993 baseEnd_94993 := by
    simpa [prefixWord, tailWord_94993, baseEnd_94993] using wordTrace_append hprefix tailTrace_94993
  have hstable : (prefixWord ++ tailWord_94993).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94993).length < 2 ^ (prefixWord ++ tailWord_94993).sum := by decide
  have hdescent : baseEnd_94993 < baseStart_94993 := by decide
  rcases family_descends (prefixWord ++ tailWord_94993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_94999 : List Nat := [1, 1, 3, 4, 4, 1, 1, 1, 5]
def baseStart_94999 : Nat := 118140960795 + 94999 * 2 ^ 59
def prefixEnd_94999 : Nat := 4983230072969 + 3 ^ 40 * 94999 * 2
def baseEnd_94999 : Nat := 21680066087368466522495

theorem tailTrace_94999 : CollatzResearch.WordTrace tailWord_94999 prefixEnd_94999 21680066087368466522495 := by
  unfold tailWord_94999
  simp only [CollatzResearch.WordTrace]
  refine ⟨3464898182842322382608051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2309932121894881588405367 3464898182842322382608051)
  ·
    refine ⟨5197347274263483573912077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3464898182842322382608051 5197347274263483573912077)
    ·
      refine ⟨1949005227848806340217029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5197347274263483573912077 1949005227848806340217029)
      ·
        refine ⟨365438480221651188790693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1949005227848806340217029 365438480221651188790693)
        ·
          refine ⟨68519715041559597898255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 365438480221651188790693 68519715041559597898255)
          ·
            refine ⟨102779572562339396847383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68519715041559597898255 102779572562339396847383)
            ·
              refine ⟨154169358843509095271075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102779572562339396847383 154169358843509095271075)
              ·
                refine ⟨231254038265263642906613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 154169358843509095271075 231254038265263642906613)
                ·
                  refine ⟨21680066087368466522495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 231254038265263642906613 21680066087368466522495)
                  ·
                    rfl

theorem cell21_94999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 1, 1, 5].length) (baseStart_94999 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_94999 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_94999 prefixEnd_94999 := by exact prefixLift 94999
  have htrace : WordTrace (prefixWord ++ tailWord_94999) baseStart_94999 baseEnd_94999 := by
    simpa [prefixWord, tailWord_94999, baseEnd_94999] using wordTrace_append hprefix tailTrace_94999
  have hstable : (prefixWord ++ tailWord_94999).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_94999).length < 2 ^ (prefixWord ++ tailWord_94999).sum := by decide
  have hdescent : baseEnd_94999 < baseStart_94999 := by decide
  rcases family_descends (prefixWord ++ tailWord_94999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95010 : List Nat := [3, 3, 1, 1, 2, 2, 1, 8]
def baseStart_95010 : Nat := 118140960795 + 95010 * 2 ^ 59
def prefixEnd_95010 : Nat := 4983230072969 + 3 ^ 40 * 95010 * 2
def baseEnd_95010 : Nat := 7227525479078297279713

theorem tailTrace_95010 : CollatzResearch.WordTrace tailWord_95010 prefixEnd_95010 7227525479078297279713 := by
  unfold tailWord_95010
  simp only [CollatzResearch.WordTrace]
  refine ⟨866324846450617815314621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2310199590534980840838989 866324846450617815314621)
  ·
    refine ⟨324871817418981680742983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 866324846450617815314621 324871817418981680742983)
    ·
      refine ⟨487307726128472521114475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 324871817418981680742983 487307726128472521114475)
      ·
        refine ⟨730961589192708781671713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 487307726128472521114475 730961589192708781671713)
        ·
          refine ⟨548221191894531586253785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 730961589192708781671713 548221191894531586253785)
          ·
            refine ⟨411165893920898689690339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 548221191894531586253785 411165893920898689690339)
            ·
              refine ⟨616748840881348034535509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 411165893920898689690339 616748840881348034535509)
              ·
                refine ⟨7227525479078297279713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 616748840881348034535509 7227525479078297279713)
                ·
                  rfl

theorem cell21_95010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 8].length) (baseStart_95010 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_95010 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_95010 prefixEnd_95010 := by exact prefixLift 95010
  have htrace : WordTrace (prefixWord ++ tailWord_95010) baseStart_95010 baseEnd_95010 := by
    simpa [prefixWord, tailWord_95010, baseEnd_95010] using wordTrace_append hprefix tailTrace_95010
  have hstable : (prefixWord ++ tailWord_95010).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95010).length < 2 ^ (prefixWord ++ tailWord_95010).sum := by decide
  have hdescent : baseEnd_95010 < baseStart_95010 := by decide
  rcases family_descends (prefixWord ++ tailWord_95010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95024 : List Nat := [2, 1, 1, 1, 2, 2, 1, 6, 5]
def baseStart_95024 : Nat := 118140960795 + 95024 * 2 ^ 59
def prefixEnd_95024 : Nat := 4983230072969 + 3 ^ 40 * 95024 * 2
def baseEnd_95024 : Nat := 21685771427973978605777

theorem tailTrace_95024 : CollatzResearch.WordTrace tailWord_95024 prefixEnd_95024 21685771427973978605777 := by
  unfold tailWord_95024
  simp only [CollatzResearch.WordTrace]
  refine ⟨1732905003875875826134063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2310540005167834434845417 1732905003875875826134063)
  ·
    refine ⟨2599357505813813739201095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1732905003875875826134063 2599357505813813739201095)
    ·
      refine ⟨3899036258720720608801643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2599357505813813739201095 3899036258720720608801643)
      ·
        refine ⟨5848554388081080913202465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3899036258720720608801643 5848554388081080913202465)
        ·
          refine ⟨4386415791060810684901849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5848554388081080913202465 4386415791060810684901849)
          ·
            refine ⟨3289811843295608013676387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4386415791060810684901849 3289811843295608013676387)
            ·
              refine ⟨4934717764943412020514581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3289811843295608013676387 4934717764943412020514581)
              ·
                refine ⟨231314895231722438461621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4934717764943412020514581 231314895231722438461621)
                ·
                  refine ⟨21685771427973978605777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 231314895231722438461621 21685771427973978605777)
                  ·
                    rfl

theorem cell21_95024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 6, 5].length) (baseStart_95024 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_95024 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_95024 prefixEnd_95024 := by exact prefixLift 95024
  have htrace : WordTrace (prefixWord ++ tailWord_95024) baseStart_95024 baseEnd_95024 := by
    simpa [prefixWord, tailWord_95024, baseEnd_95024] using wordTrace_append hprefix tailTrace_95024
  have hstable : (prefixWord ++ tailWord_95024).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95024).length < 2 ^ (prefixWord ++ tailWord_95024).sum := by decide
  have hdescent : baseEnd_95024 < baseStart_95024 := by decide
  rcases family_descends (prefixWord ++ tailWord_95024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95044 : List Nat := [2, 3, 4, 2, 2, 8]
def baseStart_95044 : Nat := 118140960795 + 95044 * 2 ^ 59
def prefixEnd_95044 : Nat := 4983230072969 + 3 ^ 40 * 95044 * 2
def baseEnd_95044 : Nat := 803345766683644010089

theorem tailTrace_95044 : CollatzResearch.WordTrace tailWord_95044 prefixEnd_95044 803345766683644010089 := by
  unfold tailWord_95044
  simp only [CollatzResearch.WordTrace]
  refine ⟨1733269733839647533998093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2311026311786196711997457 1733269733839647533998093)
  ·
    refine ⟨649976150189867825249285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1733269733839647533998093 649976150189867825249285)
    ·
      refine ⟨121870528160600217234241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 649976150189867825249285 121870528160600217234241)
      ·
        refine ⟨91402896120450162925681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121870528160600217234241 91402896120450162925681)
        ·
          refine ⟨68552172090337622194261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91402896120450162925681 68552172090337622194261)
          ·
            refine ⟨803345766683644010089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 68552172090337622194261 803345766683644010089)
            ·
              rfl

theorem cell21_95044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 8].length) (baseStart_95044 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_95044 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_95044 prefixEnd_95044 := by exact prefixLift 95044
  have htrace : WordTrace (prefixWord ++ tailWord_95044) baseStart_95044 baseEnd_95044 := by
    simpa [prefixWord, tailWord_95044, baseEnd_95044] using wordTrace_append hprefix tailTrace_95044
  have hstable : (prefixWord ++ tailWord_95044).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95044).length < 2 ^ (prefixWord ++ tailWord_95044).sum := by decide
  have hdescent : baseEnd_95044 < baseStart_95044 := by decide
  rcases family_descends (prefixWord ++ tailWord_95044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95058 : List Nat := [3, 2, 2, 1, 1, 2, 3, 4, 3]
def baseStart_95058 : Nat := 118140960795 + 95058 * 2 ^ 59
def prefixEnd_95058 : Nat := 4983230072969 + 3 ^ 40 * 95058 * 2
def baseEnd_95058 : Nat := 21693530691197475039041

theorem tailTrace_95058 : CollatzResearch.WordTrace tailWord_95058 prefixEnd_95058 21693530691197475039041 := by
  unfold tailWord_95058
  simp only [CollatzResearch.WordTrace]
  refine ⟨866762522407143864751457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2311366726419050306003885 866762522407143864751457)
  ·
    refine ⟨650071891805357898563593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 866762522407143864751457 650071891805357898563593)
    ·
      refine ⟨487553918854018423922695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 650071891805357898563593 487553918854018423922695)
      ·
        refine ⟨731330878281027635884043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 487553918854018423922695 731330878281027635884043)
        ·
          refine ⟨1096996317421541453826065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 731330878281027635884043 1096996317421541453826065)
          ·
            refine ⟨822747238066156090369549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1096996317421541453826065 822747238066156090369549)
            ·
              refine ⟨308530214274808533888581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 822747238066156090369549 308530214274808533888581)
              ·
                refine ⟨57849415176526600104109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 308530214274808533888581 57849415176526600104109)
                ·
                  refine ⟨21693530691197475039041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57849415176526600104109 21693530691197475039041)
                  ·
                    rfl

theorem cell21_95058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 4, 3].length) (baseStart_95058 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_95058 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_95058 prefixEnd_95058 := by exact prefixLift 95058
  have htrace : WordTrace (prefixWord ++ tailWord_95058) baseStart_95058 baseEnd_95058 := by
    simpa [prefixWord, tailWord_95058, baseEnd_95058] using wordTrace_append hprefix tailTrace_95058
  have hstable : (prefixWord ++ tailWord_95058).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95058).length < 2 ^ (prefixWord ++ tailWord_95058).sum := by decide
  have hdescent : baseEnd_95058 < baseStart_95058 := by decide
  rcases family_descends (prefixWord ++ tailWord_95058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95106 : List Nat := [3, 4, 2, 2, 1, 1, 1, 1, 6]
def baseStart_95106 : Nat := 118140960795 + 95106 * 2 ^ 59
def prefixEnd_95106 : Nat := 4983230072969 + 3 ^ 40 * 95106 * 2
def baseEnd_95106 : Nat := 21704484945160058238943

theorem tailTrace_95106 : CollatzResearch.WordTrace tailWord_95106 prefixEnd_95106 21704484945160058238943 := by
  unfold tailWord_95106
  simp only [CollatzResearch.WordTrace]
  refine ⟨867200198363669914188293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2312533862303119771168781 867200198363669914188293)
  ·
    refine ⟨162600037193188108910305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 867200198363669914188293 162600037193188108910305)
    ·
      refine ⟨121950027894891081682729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162600037193188108910305 121950027894891081682729)
      ·
        refine ⟨91462520921168311262047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121950027894891081682729 91462520921168311262047)
        ·
          refine ⟨137193781381752466893071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91462520921168311262047 137193781381752466893071)
          ·
            refine ⟨205790672072628700339607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137193781381752466893071 205790672072628700339607)
            ·
              refine ⟨308686008108943050509411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 205790672072628700339607 308686008108943050509411)
              ·
                refine ⟨463029012163414575764117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 308686008108943050509411 463029012163414575764117)
                ·
                  refine ⟨21704484945160058238943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 463029012163414575764117 21704484945160058238943)
                  ·
                    rfl

theorem cell21_95106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_95106 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_95106 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_95106 prefixEnd_95106 := by exact prefixLift 95106
  have htrace : WordTrace (prefixWord ++ tailWord_95106) baseStart_95106 baseEnd_95106 := by
    simpa [prefixWord, tailWord_95106, baseEnd_95106] using wordTrace_append hprefix tailTrace_95106
  have hstable : (prefixWord ++ tailWord_95106).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95106).length < 2 ^ (prefixWord ++ tailWord_95106).sum := by decide
  have hdescent : baseEnd_95106 < baseStart_95106 := by decide
  rcases family_descends (prefixWord ++ tailWord_95106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95145 : List Nat := [1, 2, 1, 1, 1, 1, 7, 7]
def baseStart_95145 : Nat := 118140960795 + 95145 * 2 ^ 59
def prefixEnd_95145 : Nat := 4983230072969 + 3 ^ 40 * 95145 * 2
def baseEnd_95145 : Nat := 7237795092168219029621

theorem tailTrace_95145 : CollatzResearch.WordTrace tailWord_95145 prefixEnd_95145 7237795092168219029621 := by
  unfold tailWord_95145
  simp only [CollatzResearch.WordTrace]
  refine ⟨3470223240313389317422889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2313482160208926211615259 3470223240313389317422889)
  ·
    refine ⟨2602667430235041988067167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3470223240313389317422889 2602667430235041988067167)
    ·
      refine ⟨3904001145352562982100751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2602667430235041988067167 3904001145352562982100751)
      ·
        refine ⟨5856001718028844473151127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3904001145352562982100751 5856001718028844473151127)
        ·
          refine ⟨8784002577043266709726691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5856001718028844473151127 8784002577043266709726691)
          ·
            refine ⟨13176003865564900064590037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8784002577043266709726691 13176003865564900064590037)
            ·
              refine ⟨308812590599177345263829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 13176003865564900064590037 308812590599177345263829)
              ·
                refine ⟨7237795092168219029621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 308812590599177345263829 7237795092168219029621)
                ·
                  rfl

theorem cell21_95145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 7].length) (baseStart_95145 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_95145 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_95145 prefixEnd_95145 := by exact prefixLift 95145
  have htrace : WordTrace (prefixWord ++ tailWord_95145) baseStart_95145 baseEnd_95145 := by
    simpa [prefixWord, tailWord_95145, baseEnd_95145] using wordTrace_append hprefix tailTrace_95145
  have hstable : (prefixWord ++ tailWord_95145).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95145).length < 2 ^ (prefixWord ++ tailWord_95145).sum := by decide
  have hdescent : baseEnd_95145 < baseStart_95145 := by decide
  rcases family_descends (prefixWord ++ tailWord_95145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95174 : List Nat := [6, 1, 3, 1, 2, 1, 2, 1, 4]
def baseStart_95174 : Nat := 118140960795 + 95174 * 2 ^ 59
def prefixEnd_95174 : Nat := 4983230072969 + 3 ^ 40 * 95174 * 2
def baseEnd_95174 : Nat := 21720003471607051105471

theorem tailTrace_95174 : CollatzResearch.WordTrace tailWord_95174 prefixEnd_95174 21720003471607051105471 := by
  unfold tailWord_95174
  simp only [CollatzResearch.WordTrace]
  refine ⟨108477529912760227194643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 2314187304805551513485717 108477529912760227194643)
  ·
    refine ⟨162716294869140340791965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108477529912760227194643 162716294869140340791965)
    ·
      refine ⟨61018610575927627796987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162716294869140340791965 61018610575927627796987)
      ·
        refine ⟨91527915863891441695481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61018610575927627796987 91527915863891441695481)
        ·
          refine ⟨68645936897918581271611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91527915863891441695481 68645936897918581271611)
          ·
            refine ⟨102968905346877871907417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68645936897918581271611 102968905346877871907417)
            ·
              refine ⟨77226679010158403930563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102968905346877871907417 77226679010158403930563)
              ·
                refine ⟨115840018515237605895845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77226679010158403930563 115840018515237605895845)
                ·
                  refine ⟨21720003471607051105471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 115840018515237605895845 21720003471607051105471)
                  ·
                    rfl

theorem cell21_95174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 2, 1, 4].length) (baseStart_95174 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_95174 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_95174 prefixEnd_95174 := by exact prefixLift 95174
  have htrace : WordTrace (prefixWord ++ tailWord_95174) baseStart_95174 baseEnd_95174 := by
    simpa [prefixWord, tailWord_95174, baseEnd_95174] using wordTrace_append hprefix tailTrace_95174
  have hstable : (prefixWord ++ tailWord_95174).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95174).length < 2 ^ (prefixWord ++ tailWord_95174).sum := by decide
  have hdescent : baseEnd_95174 < baseStart_95174 := by decide
  rcases family_descends (prefixWord ++ tailWord_95174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95255 : List Nat := [1, 1, 3, 5, 1, 2, 3, 5]
def baseStart_95255 : Nat := 118140960795 + 95255 * 2 ^ 59
def prefixEnd_95255 : Nat := 4983230072969 + 3 ^ 40 * 95255 * 2
def baseEnd_95255 : Nat := 7246162925056303418435

theorem tailTrace_95255 : CollatzResearch.WordTrace tailWord_95255 prefixEnd_95255 7246162925056303418435 := by
  unfold tailWord_95255
  simp only [CollatzResearch.WordTrace]
  refine ⟨3474235269914878103927219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2316156846609918735951479 3474235269914878103927219)
  ·
    refine ⟨5211352904872317155890829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3474235269914878103927219 5211352904872317155890829)
    ·
      refine ⟨1954257339327118933459061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5211352904872317155890829 1954257339327118933459061)
      ·
        refine ⟨183211625561917400011787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1954257339327118933459061 183211625561917400011787)
        ·
          refine ⟨274817438342876100017681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183211625561917400011787 274817438342876100017681)
          ·
            refine ⟨206113078757157075013261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 274817438342876100017681 206113078757157075013261)
            ·
              refine ⟨77292404533933903129973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 206113078757157075013261 77292404533933903129973)
              ·
                refine ⟨7246162925056303418435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 77292404533933903129973 7246162925056303418435)
                ·
                  rfl

theorem cell21_95255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 3, 5].length) (baseStart_95255 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_95255 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_95255 prefixEnd_95255 := by exact prefixLift 95255
  have htrace : WordTrace (prefixWord ++ tailWord_95255) baseStart_95255 baseEnd_95255 := by
    simpa [prefixWord, tailWord_95255, baseEnd_95255] using wordTrace_append hprefix tailTrace_95255
  have hstable : (prefixWord ++ tailWord_95255).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95255).length < 2 ^ (prefixWord ++ tailWord_95255).sum := by decide
  have hdescent : baseEnd_95255 < baseStart_95255 := by decide
  rcases family_descends (prefixWord ++ tailWord_95255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95286 : List Nat := [5, 1, 2, 1, 1, 3, 2, 1, 5]
def baseStart_95286 : Nat := 118140960795 + 95286 * 2 ^ 59
def prefixEnd_95286 : Nat := 4983230072969 + 3 ^ 40 * 95286 * 2
def baseEnd_95286 : Nat := 21745563397519745238575

theorem tailTrace_95286 : CollatzResearch.WordTrace tailWord_95286 prefixEnd_95286 21745563397519745238575 := by
  unfold tailWord_95286
  simp only [CollatzResearch.WordTrace]
  refine ⟨217210370800160649894107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2316910621868380265537141 217210370800160649894107)
  ·
    refine ⟨325815556200240974841161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 217210370800160649894107 325815556200240974841161)
    ·
      refine ⟨244361667150180731130871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 325815556200240974841161 244361667150180731130871)
      ·
        refine ⟨366542500725271096696307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244361667150180731130871 366542500725271096696307)
        ·
          refine ⟨549813751087906645044461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 366542500725271096696307 549813751087906645044461)
          ·
            refine ⟨206180156657964991891673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 549813751087906645044461 206180156657964991891673)
            ·
              refine ⟨154635117493473743918755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 206180156657964991891673 154635117493473743918755)
              ·
                refine ⟨231952676240210615878133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 154635117493473743918755 231952676240210615878133)
                ·
                  refine ⟨21745563397519745238575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 231952676240210615878133 21745563397519745238575)
                  ·
                    rfl

theorem cell21_95286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 2, 1, 5].length) (baseStart_95286 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_95286 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_95286 prefixEnd_95286 := by exact prefixLift 95286
  have htrace : WordTrace (prefixWord ++ tailWord_95286) baseStart_95286 baseEnd_95286 := by
    simpa [prefixWord, tailWord_95286, baseEnd_95286] using wordTrace_append hprefix tailTrace_95286
  have hstable : (prefixWord ++ tailWord_95286).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95286).length < 2 ^ (prefixWord ++ tailWord_95286).sum := by decide
  have hdescent : baseEnd_95286 < baseStart_95286 := by decide
  rcases family_descends (prefixWord ++ tailWord_95286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95314 : List Nat := [3, 2, 2, 1, 3, 2, 1, 7]
def baseStart_95314 : Nat := 118140960795 + 95314 * 2 ^ 59
def prefixEnd_95314 : Nat := 4983230072969 + 3 ^ 40 * 95314 * 2
def baseEnd_95314 : Nat := 7250651126332639590617

theorem tailTrace_95314 : CollatzResearch.WordTrace tailWord_95314 prefixEnd_95314 7250651126332639590617 := by
  unfold tailWord_95314
  simp only [CollatzResearch.WordTrace]
  refine ⟨869096794175282795081249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2317591451134087453549997 869096794175282795081249)
  ·
    refine ⟨651822595631462096310937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 869096794175282795081249 651822595631462096310937)
    ·
      refine ⟨488866946723596572233203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 651822595631462096310937 488866946723596572233203)
      ·
        refine ⟨733300420085394858349805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 488866946723596572233203 733300420085394858349805)
        ·
          refine ⟨274987657532023071881177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 733300420085394858349805 274987657532023071881177)
          ·
            refine ⟨206240743149017303910883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 274987657532023071881177 206240743149017303910883)
            ·
              refine ⟨309361114723525955866325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 206240743149017303910883 309361114723525955866325)
              ·
                refine ⟨7250651126332639590617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 309361114723525955866325 7250651126332639590617)
                ·
                  rfl

theorem cell21_95314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 7].length) (baseStart_95314 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_95314 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_95314 prefixEnd_95314 := by exact prefixLift 95314
  have htrace : WordTrace (prefixWord ++ tailWord_95314) baseStart_95314 baseEnd_95314 := by
    simpa [prefixWord, tailWord_95314, baseEnd_95314] using wordTrace_append hprefix tailTrace_95314
  have hstable : (prefixWord ++ tailWord_95314).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95314).length < 2 ^ (prefixWord ++ tailWord_95314).sum := by decide
  have hdescent : baseEnd_95314 < baseStart_95314 := by decide
  rcases family_descends (prefixWord ++ tailWord_95314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95390 : List Nat := [4, 3, 1, 1, 2, 10]
def baseStart_95390 : Nat := 118140960795 + 95390 * 2 ^ 59
def prefixEnd_95390 : Nat := 4983230072969 + 3 ^ 40 * 95390 * 2
def baseEnd_95390 : Nat := 806270282016247240927

theorem tailTrace_95390 : CollatzResearch.WordTrace tailWord_95390 prefixEnd_95390 806270282016247240927 := by
  unfold tailWord_95390
  simp only [CollatzResearch.WordTrace]
  refine ⟨434894890553224520011453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2319439416283864106727749 434894890553224520011453)
  ·
    refine ⟨163085583957459195004295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 434894890553224520011453 163085583957459195004295)
    ·
      refine ⟨244628375936188792506443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163085583957459195004295 244628375936188792506443)
      ·
        refine ⟨366942563904283188759665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244628375936188792506443 366942563904283188759665)
        ·
          refine ⟨275206922928212391569749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 366942563904283188759665 275206922928212391569749)
          ·
            refine ⟨806270282016247240927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 275206922928212391569749 806270282016247240927)
            ·
              rfl

theorem cell21_95390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 10].length) (baseStart_95390 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_95390 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_95390 prefixEnd_95390 := by exact prefixLift 95390
  have htrace : WordTrace (prefixWord ++ tailWord_95390) baseStart_95390 baseEnd_95390 := by
    simpa [prefixWord, tailWord_95390, baseEnd_95390] using wordTrace_append hprefix tailTrace_95390
  have hstable : (prefixWord ++ tailWord_95390).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95390).length < 2 ^ (prefixWord ++ tailWord_95390).sum := by decide
  have hdescent : baseEnd_95390 < baseStart_95390 := by decide
  rcases family_descends (prefixWord ++ tailWord_95390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95418 : List Nat := [3, 1, 1, 1, 2, 2, 1, 2, 8]
def baseStart_95418 : Nat := 118140960795 + 95418 * 2 ^ 59
def prefixEnd_95418 : Nat := 4983230072969 + 3 ^ 40 * 95418 * 2
def baseEnd_95418 : Nat := 21775687595916849038305

theorem tailTrace_95418 : CollatzResearch.WordTrace tailWord_95418 prefixEnd_95418 21775687595916849038305 := by
  unfold tailWord_95418
  simp only [CollatzResearch.WordTrace]
  refine ⟨870045092081089235527727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2320120245549571294740605 870045092081089235527727)
  ·
    refine ⟨1305067638121633853291591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 870045092081089235527727 1305067638121633853291591)
    ·
      refine ⟨1957601457182450779937387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1305067638121633853291591 1957601457182450779937387)
      ·
        refine ⟨2936402185773676169906081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1957601457182450779937387 2936402185773676169906081)
        ·
          refine ⟨2202301639330257127429561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2936402185773676169906081 2202301639330257127429561)
          ·
            refine ⟨1651726229497692845572171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2202301639330257127429561 1651726229497692845572171)
            ·
              refine ⟨2477589344246539268358257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1651726229497692845572171 2477589344246539268358257)
              ·
                refine ⟨1858192008184904451268693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2477589344246539268358257 1858192008184904451268693)
                ·
                  refine ⟨21775687595916849038305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1858192008184904451268693 21775687595916849038305)
                  ·
                    rfl

theorem cell21_95418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 8].length) (baseStart_95418 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_95418 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_95418 prefixEnd_95418 := by exact prefixLift 95418
  have htrace : WordTrace (prefixWord ++ tailWord_95418) baseStart_95418 baseEnd_95418 := by
    simpa [prefixWord, tailWord_95418, baseEnd_95418] using wordTrace_append hprefix tailTrace_95418
  have hstable : (prefixWord ++ tailWord_95418).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95418).length < 2 ^ (prefixWord ++ tailWord_95418).sum := by decide
  have hdescent : baseEnd_95418 < baseStart_95418 := by decide
  rcases family_descends (prefixWord ++ tailWord_95418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95469 : List Nat := [1, 5, 1, 2, 2, 2, 3, 1, 4]
def baseStart_95469 : Nat := 118140960795 + 95469 * 2 ^ 59
def prefixEnd_95469 : Nat := 4983230072969 + 3 ^ 40 * 95469 * 2
def baseEnd_95469 : Nat := 21787326490752093688201

theorem tailTrace_95469 : CollatzResearch.WordTrace tailWord_95469 prefixEnd_95469 21787326490752093688201 := by
  unfold tailWord_95469
  simp only [CollatzResearch.WordTrace]
  refine ⟨3482040491139592652217461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2321360327426395101478307 3482040491139592652217461)
  ·
    refine ⟨326441296044336811145387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3482040491139592652217461 326441296044336811145387)
    ·
      refine ⟨489661944066505216718081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 326441296044336811145387 489661944066505216718081)
      ·
        refine ⟨367246458049878912538561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 489661944066505216718081 367246458049878912538561)
        ·
          refine ⟨275434843537409184403921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 367246458049878912538561 275434843537409184403921)
          ·
            refine ⟨206576132653056888302941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 275434843537409184403921 206576132653056888302941)
            ·
              refine ⟨77466049744896333113603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 206576132653056888302941 77466049744896333113603)
              ·
                refine ⟨116199074617344499670405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77466049744896333113603 116199074617344499670405)
                ·
                  refine ⟨21787326490752093688201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 116199074617344499670405 21787326490752093688201)
                  ·
                    rfl

theorem cell21_95469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 3, 1, 4].length) (baseStart_95469 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_95469 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_95469 prefixEnd_95469 := by exact prefixLift 95469
  have htrace : WordTrace (prefixWord ++ tailWord_95469) baseStart_95469 baseEnd_95469 := by
    simpa [prefixWord, tailWord_95469, baseEnd_95469] using wordTrace_append hprefix tailTrace_95469
  have hstable : (prefixWord ++ tailWord_95469).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95469).length < 2 ^ (prefixWord ++ tailWord_95469).sum := by decide
  have hdescent : baseEnd_95469 < baseStart_95469 := by decide
  rcases family_descends (prefixWord ++ tailWord_95469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95511 : List Nat := [1, 1, 3, 4, 1, 1, 2, 4, 4]
def baseStart_95511 : Nat := 118140960795 + 95511 * 2 ^ 59
def prefixEnd_95511 : Nat := 4983230072969 + 3 ^ 40 * 95511 * 2
def baseEnd_95511 : Nat := 21796911462969353988115

theorem tailTrace_95511 : CollatzResearch.WordTrace tailWord_95511 prefixEnd_95511 21796911462969353988115 := by
  unfold tailWord_95511
  simp only [CollatzResearch.WordTrace]
  refine ⟨3483572356987433825246387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2322381571324955883497591 3483572356987433825246387)
  ·
    refine ⟨5225358535481150737869581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3483572356987433825246387 5225358535481150737869581)
    ·
      refine ⟨1959509450805431526701093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5225358535481150737869581 1959509450805431526701093)
      ·
        refine ⟨367408022026018411256455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1959509450805431526701093 367408022026018411256455)
        ·
          refine ⟨551112033039027616884683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 367408022026018411256455 551112033039027616884683)
          ·
            refine ⟨826668049558541425327025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 551112033039027616884683 826668049558541425327025)
            ·
              refine ⟨620001037168906068995269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 826668049558541425327025 620001037168906068995269)
              ·
                refine ⟨116250194469169887936613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 620001037168906068995269 116250194469169887936613)
                ·
                  refine ⟨21796911462969353988115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 116250194469169887936613 21796911462969353988115)
                  ·
                    rfl

theorem cell21_95511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 4, 4].length) (baseStart_95511 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_95511 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_95511 prefixEnd_95511 := by exact prefixLift 95511
  have htrace : WordTrace (prefixWord ++ tailWord_95511) baseStart_95511 baseEnd_95511 := by
    simpa [prefixWord, tailWord_95511, baseEnd_95511] using wordTrace_append hprefix tailTrace_95511
  have hstable : (prefixWord ++ tailWord_95511).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95511).length < 2 ^ (prefixWord ++ tailWord_95511).sum := by decide
  have hdescent : baseEnd_95511 < baseStart_95511 := by decide
  rcases family_descends (prefixWord ++ tailWord_95511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95525 : List Nat := [1, 3, 1, 2, 4, 1, 1, 8]
def baseStart_95525 : Nat := 118140960795 + 95525 * 2 ^ 59
def prefixEnd_95525 : Nat := 4983230072969 + 3 ^ 40 * 95525 * 2
def baseEnd_95525 : Nat := 7266702151236146918251

theorem tailTrace_95525 : CollatzResearch.WordTrace tailWord_95525 prefixEnd_95525 7266702151236146918251 := by
  unfold tailWord_95525
  simp only [CollatzResearch.WordTrace]
  refine ⟨3484082978936714216256029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2322721985957809477504019 3484082978936714216256029)
  ·
    refine ⟨1306531117101267831096011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3484082978936714216256029 1306531117101267831096011)
    ·
      refine ⟨1959796675651901746644017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1306531117101267831096011 1959796675651901746644017)
      ·
        refine ⟨1469847506738926309983013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1959796675651901746644017 1469847506738926309983013)
        ·
          refine ⟨275596407513548683121815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1469847506738926309983013 275596407513548683121815)
          ·
            refine ⟨413394611270323024682723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 275596407513548683121815 413394611270323024682723)
            ·
              refine ⟨620091916905484537024085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 413394611270323024682723 620091916905484537024085)
              ·
                refine ⟨7266702151236146918251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 620091916905484537024085 7266702151236146918251)
                ·
                  rfl

theorem cell21_95525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 8].length) (baseStart_95525 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_95525 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_95525 prefixEnd_95525 := by exact prefixLift 95525
  have htrace : WordTrace (prefixWord ++ tailWord_95525) baseStart_95525 baseEnd_95525 := by
    simpa [prefixWord, tailWord_95525, baseEnd_95525] using wordTrace_append hprefix tailTrace_95525
  have hstable : (prefixWord ++ tailWord_95525).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95525).length < 2 ^ (prefixWord ++ tailWord_95525).sum := by decide
  have hdescent : baseEnd_95525 < baseStart_95525 := by decide
  rcases family_descends (prefixWord ++ tailWord_95525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95528 : List Nat := [2, 1, 5, 1, 2, 2, 1, 3, 4]
def baseStart_95528 : Nat := 118140960795 + 95528 * 2 ^ 59
def prefixEnd_95528 : Nat := 4983230072969 + 3 ^ 40 * 95528 * 2
def baseEnd_95528 : Nat := 21800791094581102204747

theorem tailTrace_95528 : CollatzResearch.WordTrace tailWord_95528 prefixEnd_95528 21800791094581102204747 := by
  unfold tailWord_95528
  simp only [CollatzResearch.WordTrace]
  refine ⟨1742096198962922864307619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2322794931950563819076825 1742096198962922864307619)
  ·
    refine ⟨2613144298444384296461429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1742096198962922864307619 2613144298444384296461429)
    ·
      refine ⟨244982277979161027793259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2613144298444384296461429 244982277979161027793259)
      ·
        refine ⟨367473416968741541689889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244982277979161027793259 367473416968741541689889)
        ·
          refine ⟨275605062726556156267417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 367473416968741541689889 275605062726556156267417)
          ·
            refine ⟨206703797044917117200563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 275605062726556156267417 206703797044917117200563)
            ·
              refine ⟨310055695567375675800845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 206703797044917117200563 310055695567375675800845)
              ·
                refine ⟨116270885837765878425317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 310055695567375675800845 116270885837765878425317)
                ·
                  refine ⟨21800791094581102204747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 116270885837765878425317 21800791094581102204747)
                  ·
                    rfl

theorem cell21_95528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 3, 4].length) (baseStart_95528 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_95528 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_95528 prefixEnd_95528 := by exact prefixLift 95528
  have htrace : WordTrace (prefixWord ++ tailWord_95528) baseStart_95528 baseEnd_95528 := by
    simpa [prefixWord, tailWord_95528, baseEnd_95528] using wordTrace_append hprefix tailTrace_95528
  have hstable : (prefixWord ++ tailWord_95528).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95528).length < 2 ^ (prefixWord ++ tailWord_95528).sum := by decide
  have hdescent : baseEnd_95528 < baseStart_95528 := by decide
  rcases family_descends (prefixWord ++ tailWord_95528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95565 : List Nat := [1, 6, 1, 3, 1, 2, 2, 2, 3]
def baseStart_95565 : Nat := 118140960795 + 95565 * 2 ^ 59
def prefixEnd_95565 : Nat := 4983230072969 + 3 ^ 40 * 95565 * 2
def baseEnd_95565 : Nat := 21809234998677260088005

theorem tailTrace_95565 : CollatzResearch.WordTrace tailWord_95565 prefixEnd_95565 21809234998677260088005 := by
  unfold tailWord_95565
  simp only [CollatzResearch.WordTrace]
  refine ⟨3485541898791801047712149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2323694599194534031808099 3485541898791801047712149)
  ·
    refine ⟨163384776505865674111507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 3485541898791801047712149 163384776505865674111507)
    ·
      refine ⟨245077164758798511167261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 163384776505865674111507 245077164758798511167261)
      ·
        refine ⟨91903936784549441687723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 245077164758798511167261 91903936784549441687723)
        ·
          refine ⟨137855905176824162531585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91903936784549441687723 137855905176824162531585)
          ·
            refine ⟨103391928882618121898689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137855905176824162531585 103391928882618121898689)
            ·
              refine ⟨77543946661963591424017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103391928882618121898689 77543946661963591424017)
              ·
                refine ⟨58157959996472693568013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77543946661963591424017 58157959996472693568013)
                ·
                  refine ⟨21809234998677260088005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58157959996472693568013 21809234998677260088005)
                  ·
                    rfl

theorem cell21_95565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 2, 2, 3].length) (baseStart_95565 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_95565 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_95565 prefixEnd_95565 := by exact prefixLift 95565
  have htrace : WordTrace (prefixWord ++ tailWord_95565) baseStart_95565 baseEnd_95565 := by
    simpa [prefixWord, tailWord_95565, baseEnd_95565] using wordTrace_append hprefix tailTrace_95565
  have hstable : (prefixWord ++ tailWord_95565).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95565).length < 2 ^ (prefixWord ++ tailWord_95565).sum := by decide
  have hdescent : baseEnd_95565 < baseStart_95565 := by decide
  rcases family_descends (prefixWord ++ tailWord_95565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95587 : List Nat := [1, 1, 1, 5, 2, 2, 2, 3, 4]
def baseStart_95587 : Nat := 118140960795 + 95587 * 2 ^ 59
def prefixEnd_95587 : Nat := 4983230072969 + 3 ^ 40 * 95587 * 2
def baseEnd_95587 : Nat := 21814255698410110721293

theorem tailTrace_95587 : CollatzResearch.WordTrace tailWord_95587 prefixEnd_95587 21814255698410110721293 := by
  unfold tailWord_95587
  simp only [CollatzResearch.WordTrace]
  refine ⟨3486344304712098805013015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2324229536474732536675343 3486344304712098805013015)
  ·
    refine ⟨5229516457068148207519523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3486344304712098805013015 5229516457068148207519523)
    ·
      refine ⟨7844274685602222311279285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5229516457068148207519523 7844274685602222311279285)
      ·
        refine ⟨735400751775208341682433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7844274685602222311279285 735400751775208341682433)
        ·
          refine ⟨551550563831406256261825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 735400751775208341682433 551550563831406256261825)
          ·
            refine ⟨413662922873554692196369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 551550563831406256261825 413662922873554692196369)
            ·
              refine ⟨310247192155166019147277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 413662922873554692196369 310247192155166019147277)
              ·
                refine ⟨116342697058187257180229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 310247192155166019147277 116342697058187257180229)
                ·
                  refine ⟨21814255698410110721293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 116342697058187257180229 21814255698410110721293)
                  ·
                    rfl

theorem cell21_95587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 3, 4].length) (baseStart_95587 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_95587 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_95587 prefixEnd_95587 := by exact prefixLift 95587
  have htrace : WordTrace (prefixWord ++ tailWord_95587) baseStart_95587 baseEnd_95587 := by
    simpa [prefixWord, tailWord_95587, baseEnd_95587] using wordTrace_append hprefix tailTrace_95587
  have hstable : (prefixWord ++ tailWord_95587).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95587).length < 2 ^ (prefixWord ++ tailWord_95587).sum := by decide
  have hdescent : baseEnd_95587 < baseStart_95587 := by decide
  rcases family_descends (prefixWord ++ tailWord_95587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95736 : List Nat := [2, 1, 2, 1, 1, 14]
def baseStart_95736 : Nat := 118140960795 + 95736 * 2 ^ 59
def prefixEnd_95736 : Nat := 4983230072969 + 3 ^ 40 * 95736 * 2
def baseEnd_95736 : Nat := 809194797348850471765

theorem tailTrace_95736 : CollatzResearch.WordTrace tailWord_95736 prefixEnd_95736 809194797348850471765 := by
  unfold tailWord_95736
  simp only [CollatzResearch.WordTrace]
  refine ⟨1745889390586148626093531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2327852520781531501458041 1745889390586148626093531)
  ·
    refine ⟨2618834085879222939140297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1745889390586148626093531 2618834085879222939140297)
    ·
      refine ⟨1964125564409417204355223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2618834085879222939140297 1964125564409417204355223)
      ·
        refine ⟨2946188346614125806532835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1964125564409417204355223 2946188346614125806532835)
        ·
          refine ⟨4419282519921188709799253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2946188346614125806532835 4419282519921188709799253)
          ·
            refine ⟨809194797348850471765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 4419282519921188709799253 809194797348850471765)
            ·
              rfl

theorem cell21_95736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 14].length) (baseStart_95736 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_95736 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_95736 prefixEnd_95736 := by exact prefixLift 95736
  have htrace : WordTrace (prefixWord ++ tailWord_95736) baseStart_95736 baseEnd_95736 := by
    simpa [prefixWord, tailWord_95736, baseEnd_95736] using wordTrace_append hprefix tailTrace_95736
  have hstable : (prefixWord ++ tailWord_95736).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95736).length < 2 ^ (prefixWord ++ tailWord_95736).sum := by decide
  have hdescent : baseEnd_95736 < baseStart_95736 := by decide
  rcases family_descends (prefixWord ++ tailWord_95736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95801 : List Nat := [1, 2, 1, 5, 1, 2, 2, 4, 3]
def baseStart_95801 : Nat := 118140960795 + 95801 * 2 ^ 59
def prefixEnd_95801 : Nat := 4983230072969 + 3 ^ 40 * 95801 * 2
def baseEnd_95801 : Nat := 21863093413993294154189

theorem tailTrace_95801 : CollatzResearch.WordTrace tailWord_95801 prefixEnd_95801 21863093413993294154189 := by
  unfold tailWord_95801
  simp only [CollatzResearch.WordTrace]
  refine ⟨3494149525936813353303257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2329433017291208902202171 3494149525936813353303257)
  ·
    refine ⟨2620612144452610014977443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3494149525936813353303257 2620612144452610014977443)
    ·
      refine ⟨3930918216678915022466165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2620612144452610014977443 3930918216678915022466165)
      ·
        refine ⟨368523582813648283356203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3930918216678915022466165 368523582813648283356203)
        ·
          refine ⟨552785374220472425034305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 368523582813648283356203 552785374220472425034305)
          ·
            refine ⟨414589030665354318775729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 552785374220472425034305 414589030665354318775729)
            ·
              refine ⟨310941772999015739081797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 414589030665354318775729 310941772999015739081797)
              ·
                refine ⟨58301582437315451077837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 310941772999015739081797 58301582437315451077837)
                ·
                  refine ⟨21863093413993294154189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58301582437315451077837 21863093413993294154189)
                  ·
                    rfl

theorem cell21_95801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 4, 3].length) (baseStart_95801 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_95801 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_95801 prefixEnd_95801 := by exact prefixLift 95801
  have htrace : WordTrace (prefixWord ++ tailWord_95801) baseStart_95801 baseEnd_95801 := by
    simpa [prefixWord, tailWord_95801, baseEnd_95801] using wordTrace_append hprefix tailTrace_95801
  have hstable : (prefixWord ++ tailWord_95801).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95801).length < 2 ^ (prefixWord ++ tailWord_95801).sum := by decide
  have hdescent : baseEnd_95801 < baseStart_95801 := by decide
  rcases family_descends (prefixWord ++ tailWord_95801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_95919 : List Nat := [1, 1, 2, 1, 2, 4, 2, 3, 5]
def baseStart_95919 : Nat := 118140960795 + 95919 * 2 ^ 59
def prefixEnd_95919 : Nat := 4983230072969 + 3 ^ 40 * 95919 * 2
def baseEnd_95919 : Nat := 21890022621651311187281

theorem tailTrace_95919 : CollatzResearch.WordTrace tailWord_95919 prefixEnd_95919 21890022621651311187281 := by
  unfold tailWord_95919
  simp only [CollatzResearch.WordTrace]
  refine ⟨3498453339509319506098811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2332302226339546337399207 3498453339509319506098811)
  ·
    refine ⟨5247680009263979259148217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3498453339509319506098811 5247680009263979259148217)
    ·
      refine ⟨3935760006947984444361163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5247680009263979259148217 3935760006947984444361163)
      ·
        refine ⟨5903640010421976666541745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3935760006947984444361163 5903640010421976666541745)
        ·
          refine ⟨4427730007816482499906309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5903640010421976666541745 4427730007816482499906309)
          ·
            refine ⟨830199376465590468732433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4427730007816482499906309 830199376465590468732433)
            ·
              refine ⟨622649532349192851549325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 830199376465590468732433 622649532349192851549325)
              ·
                refine ⟨233493574630947319330997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 622649532349192851549325 233493574630947319330997)
                ·
                  refine ⟨21890022621651311187281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 233493574630947319330997 21890022621651311187281)
                  ·
                    rfl

theorem cell21_95919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 3, 5].length) (baseStart_95919 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_95919 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_95919 prefixEnd_95919 := by exact prefixLift 95919
  have htrace : WordTrace (prefixWord ++ tailWord_95919) baseStart_95919 baseEnd_95919 := by
    simpa [prefixWord, tailWord_95919, baseEnd_95919] using wordTrace_append hprefix tailTrace_95919
  have hstable : (prefixWord ++ tailWord_95919).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_95919).length < 2 ^ (prefixWord ++ tailWord_95919).sum := by decide
  have hdescent : baseEnd_95919 < baseStart_95919 := by decide
  rcases family_descends (prefixWord ++ tailWord_95919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
