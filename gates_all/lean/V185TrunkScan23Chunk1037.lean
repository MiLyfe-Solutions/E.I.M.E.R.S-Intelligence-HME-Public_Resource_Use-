import V185TrunkScan23Chunk1036

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6139852 : List Nat := [2, 2, 1, 4, 1, 2, 3, 2, 2, 2, 2]
def baseStart_6139852 : Nat := 118140960795 + 6139852 * 2 ^ 59
def prefixEnd_6139852 : Nat := 4983230072969 + 3 ^ 40 * 6139852 * 2
def baseEnd_6139852 : Nat := 3152695223469217034513341

theorem tailTrace_6139852 : CollatzResearch.WordTrace tailWord_6139852 prefixEnd_6139852 3152695223469217034513341 := by
  unfold tailWord_6139852
  simp only [CollatzResearch.WordTrace]
  refine ⟨111969399876186141041570905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149292533168248188055427873 111969399876186141041570905)
  ·
    refine ⟨83977049907139605781178179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111969399876186141041570905 83977049907139605781178179)
    ·
      refine ⟨125965574860709408671767269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83977049907139605781178179 125965574860709408671767269)
      ·
        refine ⟨23618545286383014125956363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 125965574860709408671767269 23618545286383014125956363)
        ·
          refine ⟨35427817929574521188934545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23618545286383014125956363 35427817929574521188934545)
          ·
            refine ⟨26570863447180890891700909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35427817929574521188934545 26570863447180890891700909)
            ·
              refine ⟨9964073792692834084387841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26570863447180890891700909 9964073792692834084387841)
              ·
                refine ⟨7473055344519625563290881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9964073792692834084387841 7473055344519625563290881)
                ·
                  refine ⟨5604791508389719172468161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7473055344519625563290881 5604791508389719172468161)
                  ·
                    refine ⟨4203593631292289379351121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5604791508389719172468161 4203593631292289379351121)
                    ·
                      refine ⟨3152695223469217034513341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4203593631292289379351121 3152695223469217034513341)
                      ·
                        rfl

theorem cell23_6139852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 3, 2, 2, 2, 2].length) (baseStart_6139852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6139852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6139852 prefixEnd_6139852 := by exact prefixLift 6139852
  have htrace : WordTrace (prefixWord ++ tailWord_6139852) baseStart_6139852 baseEnd_6139852 := by
    simpa [prefixWord, tailWord_6139852, baseEnd_6139852] using wordTrace_append hprefix tailTrace_6139852
  have hstable : (prefixWord ++ tailWord_6139852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6139852).length < 2 ^ (prefixWord ++ tailWord_6139852).sum := by decide
  have hdescent : baseEnd_6139852 < baseStart_6139852 := by decide
  rcases family_descends (prefixWord ++ tailWord_6139852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6139869 : List Nat := [1, 4, 3, 1, 4, 1, 1, 1, 1, 4, 2]
def baseStart_6139869 : Nat := 118140960795 + 6139869 * 2 ^ 59
def prefixEnd_6139869 : Nat := 4983230072969 + 3 ^ 40 * 6139869 * 2
def baseEnd_6139869 : Nat := 3152703952640343468000763

theorem tailTrace_6139869 : CollatzResearch.WordTrace tailWord_6139869 prefixEnd_6139869 3152703952640343468000763 := by
  unfold tailWord_6139869
  simp only [CollatzResearch.WordTrace]
  refine ⟨223939419793310693986510661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149292946528873795991007107 223939419793310693986510661)
  ·
    refine ⟨41988641211245755122470749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 223939419793310693986510661 41988641211245755122470749)
    ·
      refine ⟨15745740454217158170926531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41988641211245755122470749 15745740454217158170926531)
      ·
        refine ⟨23618610681325737256389797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15745740454217158170926531 23618610681325737256389797)
        ·
          refine ⟨4428489502748575735573087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23618610681325737256389797 4428489502748575735573087)
          ·
            refine ⟨6642734254122863603359631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4428489502748575735573087 6642734254122863603359631)
            ·
              refine ⟨9964101381184295405039447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6642734254122863603359631 9964101381184295405039447)
              ·
                refine ⟨14946152071776443107559171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9964101381184295405039447 14946152071776443107559171)
                ·
                  refine ⟨22419228107664664661338757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14946152071776443107559171 22419228107664664661338757)
                  ·
                    refine ⟨4203605270187124624001017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22419228107664664661338757 4203605270187124624001017)
                    ·
                      refine ⟨3152703952640343468000763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4203605270187124624001017 3152703952640343468000763)
                      ·
                        rfl

theorem cell23_6139869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 1, 1, 1, 4, 2].length) (baseStart_6139869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6139869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6139869 prefixEnd_6139869 := by exact prefixLift 6139869
  have htrace : WordTrace (prefixWord ++ tailWord_6139869) baseStart_6139869 baseEnd_6139869 := by
    simpa [prefixWord, tailWord_6139869, baseEnd_6139869] using wordTrace_append hprefix tailTrace_6139869
  have hstable : (prefixWord ++ tailWord_6139869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6139869).length < 2 ^ (prefixWord ++ tailWord_6139869).sum := by decide
  have hdescent : baseEnd_6139869 < baseStart_6139869 := by decide
  rcases family_descends (prefixWord ++ tailWord_6139869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6139871 : List Nat := [1, 1, 2, 3, 4, 1, 1, 2, 1, 7]
def baseStart_6139871 : Nat := 118140960795 + 6139871 * 2 ^ 59
def prefixEnd_6139871 : Nat := 4983230072969 + 3 ^ 40 * 6139871 * 2
def baseEnd_6139871 : Nat := 1050901659867217486725251

theorem tailTrace_6139871 : CollatzResearch.WordTrace tailWord_6139871 prefixEnd_6139871 1050901659867217486725251 := by
  unfold tailWord_6139871
  simp only [CollatzResearch.WordTrace]
  refine ⟨223939492739303448328083467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149292995159535632218722311 223939492739303448328083467)
  ·
    refine ⟨335909239108955172492125201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223939492739303448328083467 335909239108955172492125201)
    ·
      refine ⟨251931929331716379369093901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 335909239108955172492125201 251931929331716379369093901)
      ·
        refine ⟨94474473499393642263410213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 251931929331716379369093901 94474473499393642263410213)
        ·
          refine ⟨17713963781136307924389415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 94474473499393642263410213 17713963781136307924389415)
          ·
            refine ⟨26570945671704461886584123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17713963781136307924389415 26570945671704461886584123)
            ·
              refine ⟨39856418507556692829876185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26570945671704461886584123 39856418507556692829876185)
              ·
                refine ⟨29892313880667519622407139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39856418507556692829876185 29892313880667519622407139)
                ·
                  refine ⟨44838470821001279433610709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29892313880667519622407139 44838470821001279433610709)
                  ·
                    refine ⟨1050901659867217486725251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44838470821001279433610709 1050901659867217486725251)
                    ·
                      rfl

theorem cell23_6139871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 2, 1, 7].length) (baseStart_6139871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6139871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6139871 prefixEnd_6139871 := by exact prefixLift 6139871
  have htrace : WordTrace (prefixWord ++ tailWord_6139871) baseStart_6139871 baseEnd_6139871 := by
    simpa [prefixWord, tailWord_6139871, baseEnd_6139871] using wordTrace_append hprefix tailTrace_6139871
  have hstable : (prefixWord ++ tailWord_6139871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6139871).length < 2 ^ (prefixWord ++ tailWord_6139871).sum := by decide
  have hdescent : baseEnd_6139871 < baseStart_6139871 := by decide
  rcases family_descends (prefixWord ++ tailWord_6139871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6139891 : List Nat := [1, 1, 1, 2, 2, 2, 1, 2, 6, 1, 4]
def baseStart_6139891 : Nat := 118140960795 + 6139891 * 2 ^ 59
def prefixEnd_6139891 : Nat := 4983230072969 + 3 ^ 40 * 6139891 * 2
def baseEnd_6139891 : Nat := 3152715249214742381925661

theorem tailTrace_6139891 : CollatzResearch.WordTrace tailWord_6139891 prefixEnd_6139891 3152715249214742381925661 := by
  unfold tailWord_6139891
  simp only [CollatzResearch.WordTrace]
  refine ⟨223940222199230991743811527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149293481466153994495874351 223940222199230991743811527)
  ·
    refine ⟨335910333298846487615717291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223940222199230991743811527 335910333298846487615717291)
    ·
      refine ⟨503865499948269731423575937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 335910333298846487615717291 503865499948269731423575937)
      ·
        refine ⟨377899124961202298567681953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 503865499948269731423575937 377899124961202298567681953)
        ·
          refine ⟨283424343720901723925761465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 377899124961202298567681953 283424343720901723925761465)
          ·
            refine ⟨212568257790676292944321099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 283424343720901723925761465 212568257790676292944321099)
            ·
              refine ⟨318852386686014439416481649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 212568257790676292944321099 318852386686014439416481649)
              ·
                refine ⟨239139290014510829562361237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 318852386686014439416481649 239139290014510829562361237)
                ·
                  refine ⟨11209654219430195135735683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 239139290014510829562361237 11209654219430195135735683)
                  ·
                    refine ⟨16814481329145292703603525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11209654219430195135735683 16814481329145292703603525)
                    ·
                      refine ⟨3152715249214742381925661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16814481329145292703603525 3152715249214742381925661)
                      ·
                        rfl

theorem cell23_6139891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 6, 1, 4].length) (baseStart_6139891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6139891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6139891 prefixEnd_6139891 := by exact prefixLift 6139891
  have htrace : WordTrace (prefixWord ++ tailWord_6139891) baseStart_6139891 baseEnd_6139891 := by
    simpa [prefixWord, tailWord_6139891, baseEnd_6139891] using wordTrace_append hprefix tailTrace_6139891
  have hstable : (prefixWord ++ tailWord_6139891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6139891).length < 2 ^ (prefixWord ++ tailWord_6139891).sum := by decide
  have hdescent : baseEnd_6139891 < baseStart_6139891 := by decide
  rcases family_descends (prefixWord ++ tailWord_6139891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6139928 : List Nat := [2, 1, 2, 3, 2, 1, 1, 2, 4, 2, 3]
def baseStart_6139928 : Nat := 118140960795 + 6139928 * 2 ^ 59
def prefixEnd_6139928 : Nat := 4983230072969 + 3 ^ 40 * 6139928 * 2
def baseEnd_6139928 : Nat := 3152734247998958737162991

theorem tailTrace_6139928 : CollatzResearch.WordTrace tailWord_6139928 prefixEnd_6139928 3152734247998958737162991 := by
  unfold tailWord_6139928
  simp only [CollatzResearch.WordTrace]
  refine ⟨111970785850048473531454219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149294381133397964708605625 111970785850048473531454219)
  ·
    refine ⟨167956178775072710297181329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111970785850048473531454219 167956178775072710297181329)
    ·
      refine ⟨125967134081304532722885997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167956178775072710297181329 125967134081304532722885997)
      ·
        refine ⟨47237675280489199771082249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125967134081304532722885997 47237675280489199771082249)
        ·
          refine ⟨35428256460366899828311687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47237675280489199771082249 35428256460366899828311687)
          ·
            refine ⟨53142384690550349742467531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35428256460366899828311687 53142384690550349742467531)
            ·
              refine ⟨79713577035825524613701297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53142384690550349742467531 79713577035825524613701297)
              ·
                refine ⟨59785182776869143460275973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79713577035825524613701297 59785182776869143460275973)
                ·
                  refine ⟨11209721770662964398801745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59785182776869143460275973 11209721770662964398801745)
                  ·
                    refine ⟨8407291327997223299101309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11209721770662964398801745 8407291327997223299101309)
                    ·
                      refine ⟨3152734247998958737162991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8407291327997223299101309 3152734247998958737162991)
                      ·
                        rfl

theorem cell23_6139928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 2, 4, 2, 3].length) (baseStart_6139928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6139928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6139928 prefixEnd_6139928 := by exact prefixLift 6139928
  have htrace : WordTrace (prefixWord ++ tailWord_6139928) baseStart_6139928 baseEnd_6139928 := by
    simpa [prefixWord, tailWord_6139928, baseEnd_6139928] using wordTrace_append hprefix tailTrace_6139928
  have hstable : (prefixWord ++ tailWord_6139928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6139928).length < 2 ^ (prefixWord ++ tailWord_6139928).sum := by decide
  have hdescent : baseEnd_6139928 < baseStart_6139928 := by decide
  rcases family_descends (prefixWord ++ tailWord_6139928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6139969 : List Nat := [1, 2, 5, 1, 2, 1, 4, 2, 1, 4]
def baseStart_6139969 : Nat := 118140960795 + 6139969 * 2 ^ 59
def prefixEnd_6139969 : Nat := 4983230072969 + 3 ^ 40 * 6139969 * 2
def baseEnd_6139969 : Nat := 1050918433568597692250101

theorem tailTrace_6139969 : CollatzResearch.WordTrace tailWord_6139969 prefixEnd_6139969 1050918433568597692250101 := by
  unfold tailWord_6139969
  simp only [CollatzResearch.WordTrace]
  refine ⟨223943067092948411065150961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149295378061965607376767307 223943067092948411065150961)
  ·
    refine ⟨167957300319711308298863221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223943067092948411065150961 167957300319711308298863221)
    ·
      refine ⟨15745996904972935153018427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 167957300319711308298863221 15745996904972935153018427)
      ·
        refine ⟨23618995357459402729527641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15745996904972935153018427 23618995357459402729527641)
        ·
          refine ⟨17714246518094552047145731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23618995357459402729527641 17714246518094552047145731)
          ·
            refine ⟨26571369777141828070718597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17714246518094552047145731 26571369777141828070718597)
            ·
              refine ⟨4982131833214092763259737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26571369777141828070718597 4982131833214092763259737)
              ·
                refine ⟨3736598874910569572444803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4982131833214092763259737 3736598874910569572444803)
                ·
                  refine ⟨5604898312365854358667205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3736598874910569572444803 5604898312365854358667205)
                  ·
                    refine ⟨1050918433568597692250101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5604898312365854358667205 1050918433568597692250101)
                    ·
                      rfl

theorem cell23_6139969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 4, 2, 1, 4].length) (baseStart_6139969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6139969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6139969 prefixEnd_6139969 := by exact prefixLift 6139969
  have htrace : WordTrace (prefixWord ++ tailWord_6139969) baseStart_6139969 baseEnd_6139969 := by
    simpa [prefixWord, tailWord_6139969, baseEnd_6139969] using wordTrace_append hprefix tailTrace_6139969
  have hstable : (prefixWord ++ tailWord_6139969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6139969).length < 2 ^ (prefixWord ++ tailWord_6139969).sum := by decide
  have hdescent : baseEnd_6139969 < baseStart_6139969 := by decide
  rcases family_descends (prefixWord ++ tailWord_6139969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6139975 : List Nat := [1, 1, 4, 1, 3, 1, 2, 3, 3, 1, 3]
def baseStart_6139975 : Nat := 118140960795 + 6139975 * 2 ^ 59
def prefixEnd_6139975 : Nat := 4983230072969 + 3 ^ 40 * 6139975 * 2
def baseEnd_6139975 : Nat := 3152758381589720053275275

theorem tailTrace_6139975 : CollatzResearch.WordTrace tailWord_6139975 prefixEnd_6139975 3152758381589720053275275 := by
  unfold tailWord_6139975
  simp only [CollatzResearch.WordTrace]
  refine ⟨223943285930926674089869379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149295523953951116059912919 223943285930926674089869379)
  ·
    refine ⟨335914928896390011134804069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223943285930926674089869379 335914928896390011134804069)
    ·
      refine ⟨62984049168073127087775763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 335914928896390011134804069 62984049168073127087775763)
      ·
        refine ⟨94476073752109690631663645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62984049168073127087775763 94476073752109690631663645)
        ·
          refine ⟨35428527657041133986873867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94476073752109690631663645 35428527657041133986873867)
          ·
            refine ⟨53142791485561700980310801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35428527657041133986873867 53142791485561700980310801)
            ·
              refine ⟨39857093614171275735233101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53142791485561700980310801 39857093614171275735233101)
              ·
                refine ⟨14946410105314228400712413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39857093614171275735233101 14946410105314228400712413)
                ·
                  refine ⟨5604903789492835650267155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14946410105314228400712413 5604903789492835650267155)
                  ·
                    refine ⟨8407355684239253475400733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5604903789492835650267155 8407355684239253475400733)
                    ·
                      refine ⟨3152758381589720053275275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8407355684239253475400733 3152758381589720053275275)
                      ·
                        rfl

theorem cell23_6139975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 3, 3, 1, 3].length) (baseStart_6139975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6139975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6139975 prefixEnd_6139975 := by exact prefixLift 6139975
  have htrace : WordTrace (prefixWord ++ tailWord_6139975) baseStart_6139975 baseEnd_6139975 := by
    simpa [prefixWord, tailWord_6139975, baseEnd_6139975] using wordTrace_append hprefix tailTrace_6139975
  have hstable : (prefixWord ++ tailWord_6139975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6139975).length < 2 ^ (prefixWord ++ tailWord_6139975).sum := by decide
  have hdescent : baseEnd_6139975 < baseStart_6139975 := by decide
  rcases family_descends (prefixWord ++ tailWord_6139975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6140012 : List Nat := [2, 2, 1, 1, 3, 5, 2, 1, 1, 5]
def baseStart_6140012 : Nat := 118140960795 + 6140012 * 2 ^ 59
def prefixEnd_6140012 : Nat := 4983230072969 + 3 ^ 40 * 6140012 * 2
def baseEnd_6140012 : Nat := 1050925793457978802837535

theorem tailTrace_6140012 : CollatzResearch.WordTrace tailWord_6140012 prefixEnd_6140012 1050925793457978802837535 := by
  unfold tailWord_6140012
  simp only [CollatzResearch.WordTrace]
  refine ⟨111972317715896314704483145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149296423621195086272644193 111972317715896314704483145)
  ·
    refine ⟨83979238286922236028362359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111972317715896314704483145 83979238286922236028362359)
    ·
      refine ⟨125968857430383354042543539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83979238286922236028362359 125968857430383354042543539)
      ·
        refine ⟨188953286145575031063815309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125968857430383354042543539 188953286145575031063815309)
        ·
          refine ⟨70857482304590636648930741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 188953286145575031063815309 70857482304590636648930741)
          ·
            refine ⟨6642888966055372185837257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 70857482304590636648930741 6642888966055372185837257)
            ·
              refine ⟨4982166724541529139377943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6642888966055372185837257 4982166724541529139377943)
              ·
                refine ⟨7473250086812293709066915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4982166724541529139377943 7473250086812293709066915)
                ·
                  refine ⟨11209875130218440563600373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7473250086812293709066915 11209875130218440563600373)
                  ·
                    refine ⟨1050925793457978802837535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11209875130218440563600373 1050925793457978802837535)
                    ·
                      rfl

theorem cell23_6140012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 5].length) (baseStart_6140012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6140012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6140012 prefixEnd_6140012 := by exact prefixLift 6140012
  have htrace : WordTrace (prefixWord ++ tailWord_6140012) baseStart_6140012 baseEnd_6140012 := by
    simpa [prefixWord, tailWord_6140012, baseEnd_6140012] using wordTrace_append hprefix tailTrace_6140012
  have hstable : (prefixWord ++ tailWord_6140012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6140012).length < 2 ^ (prefixWord ++ tailWord_6140012).sum := by decide
  have hdescent : baseEnd_6140012 < baseStart_6140012 := by decide
  rcases family_descends (prefixWord ++ tailWord_6140012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6140015 : List Nat := [1, 1, 2, 1, 3, 5, 1, 3, 1, 1, 4]
def baseStart_6140015 : Nat := 118140960795 + 6140015 * 2 ^ 59
def prefixEnd_6140015 : Nat := 4983230072969 + 3 ^ 40 * 6140015 * 2
def baseEnd_6140015 : Nat := 3152778920815899896775091

theorem tailTrace_6140015 : CollatzResearch.WordTrace tailWord_6140015 prefixEnd_6140015 3152778920815899896775091 := by
  unfold tailWord_6140015
  simp only [CollatzResearch.WordTrace]
  refine ⟨223944744850781760921325499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149296496567187840614216999 223944744850781760921325499)
  ·
    refine ⟨335917117276172641381988249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223944744850781760921325499 335917117276172641381988249)
    ·
      refine ⟨251937837957129481036491187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 335917117276172641381988249 251937837957129481036491187)
      ·
        refine ⟨377906756935694221554736781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251937837957129481036491187 377906756935694221554736781)
        ·
          refine ⟨141715033850885333083026293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 377906756935694221554736781 141715033850885333083026293)
          ·
            refine ⟨13285784423520499976533715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 141715033850885333083026293 13285784423520499976533715)
            ·
              refine ⟨19928676635280749964800573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13285784423520499976533715 19928676635280749964800573)
              ·
                refine ⟨7473253738230281236800215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19928676635280749964800573 7473253738230281236800215)
                ·
                  refine ⟨11209880607345421855200323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7473253738230281236800215 11209880607345421855200323)
                  ·
                    refine ⟨16814820911018132782800485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11209880607345421855200323 16814820911018132782800485)
                    ·
                      refine ⟨3152778920815899896775091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16814820911018132782800485 3152778920815899896775091)
                      ·
                        rfl

theorem cell23_6140015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 3, 1, 1, 4].length) (baseStart_6140015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6140015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6140015 prefixEnd_6140015 := by exact prefixLift 6140015
  have htrace : WordTrace (prefixWord ++ tailWord_6140015) baseStart_6140015 baseEnd_6140015 := by
    simpa [prefixWord, tailWord_6140015, baseEnd_6140015] using wordTrace_append hprefix tailTrace_6140015
  have hstable : (prefixWord ++ tailWord_6140015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6140015).length < 2 ^ (prefixWord ++ tailWord_6140015).sum := by decide
  have hdescent : baseEnd_6140015 < baseStart_6140015 := by decide
  rcases family_descends (prefixWord ++ tailWord_6140015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6140025 : List Nat := [1, 2, 1, 3, 4, 2, 1, 1, 4, 4]
def baseStart_6140025 : Nat := 118140960795 + 6140025 * 2 ^ 59
def prefixEnd_6140025 : Nat := 4983230072969 + 3 ^ 40 * 6140025 * 2
def baseEnd_6140025 : Nat := 1050928018540814952550015

theorem tailTrace_6140025 : CollatzResearch.WordTrace tailWord_6140025 prefixEnd_6140025 1050928018540814952550015 := by
  unfold tailWord_6140025
  simp only [CollatzResearch.WordTrace]
  refine ⟨223945109580745532629189529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149296739720497021752793019 223945109580745532629189529)
  ·
    refine ⟨167958832185559149471892147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223945109580745532629189529 167958832185559149471892147)
    ·
      refine ⟨251938248278338724207838221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167958832185559149471892147 251938248278338724207838221)
      ·
        refine ⟨94476843104377021577939333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 251938248278338724207838221 94476843104377021577939333)
        ·
          refine ⟨17714408082070691545863625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 94476843104377021577939333 17714408082070691545863625)
          ·
            refine ⟨13285806061553018659397719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17714408082070691545863625 13285806061553018659397719)
            ·
              refine ⟨19928709092329527989096579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13285806061553018659397719 19928709092329527989096579)
              ·
                refine ⟨29893063638494291983644869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19928709092329527989096579 29893063638494291983644869)
                ·
                  refine ⟨5604949432217679746933413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29893063638494291983644869 5604949432217679746933413)
                  ·
                    refine ⟨1050928018540814952550015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5604949432217679746933413 1050928018540814952550015)
                    ·
                      rfl

theorem cell23_6140025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 1, 4, 4].length) (baseStart_6140025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6140025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6140025 prefixEnd_6140025 := by exact prefixLift 6140025
  have htrace : WordTrace (prefixWord ++ tailWord_6140025) baseStart_6140025 baseEnd_6140025 := by
    simpa [prefixWord, tailWord_6140025, baseEnd_6140025] using wordTrace_append hprefix tailTrace_6140025
  have hstable : (prefixWord ++ tailWord_6140025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6140025).length < 2 ^ (prefixWord ++ tailWord_6140025).sum := by decide
  have hdescent : baseEnd_6140025 < baseStart_6140025 := by decide
  rcases family_descends (prefixWord ++ tailWord_6140025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6140082 : List Nat := [3, 2, 1, 1, 1, 3, 2, 4, 2, 1, 3]
def baseStart_6140082 : Nat := 118140960795 + 6140082 * 2 ^ 59
def prefixEnd_6140082 : Nat := 4983230072969 + 3 ^ 40 * 6140082 * 2
def baseEnd_6140082 : Nat := 3152813324019751134637283

theorem tailTrace_6140082 : CollatzResearch.WordTrace tailWord_6140082 prefixEnd_6140082 3152813324019751134637283 := by
  unfold tailWord_6140082
  simp only [CollatzResearch.WordTrace]
  refine ⟨55986797135384757841003625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149298125694359354242676333 55986797135384757841003625)
  ·
    refine ⟨41990097851538568380752719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55986797135384757841003625 41990097851538568380752719)
    ·
      refine ⟨62985146777307852571129079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41990097851538568380752719 62985146777307852571129079)
      ·
        refine ⟨94477720165961778856693619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62985146777307852571129079 94477720165961778856693619)
        ·
          refine ⟨141716580248942668285040429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94477720165961778856693619 141716580248942668285040429)
          ·
            refine ⟨53143717593353500606890161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 141716580248942668285040429 53143717593353500606890161)
            ·
              refine ⟨39857788195015125455167621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53143717593353500606890161 39857788195015125455167621)
              ·
                refine ⟨7473335286565336022843929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39857788195015125455167621 7473335286565336022843929)
                ·
                  refine ⟨5605001464924002017132947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7473335286565336022843929 5605001464924002017132947)
                  ·
                    refine ⟨8407502197386003025699421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5605001464924002017132947 8407502197386003025699421)
                    ·
                      refine ⟨3152813324019751134637283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8407502197386003025699421 3152813324019751134637283)
                      ·
                        rfl

theorem cell23_6140082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 4, 2, 1, 3].length) (baseStart_6140082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6140082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6140082 prefixEnd_6140082 := by exact prefixLift 6140082
  have htrace : WordTrace (prefixWord ++ tailWord_6140082) baseStart_6140082 baseEnd_6140082 := by
    simpa [prefixWord, tailWord_6140082, baseEnd_6140082] using wordTrace_append hprefix tailTrace_6140082
  have hstable : (prefixWord ++ tailWord_6140082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6140082).length < 2 ^ (prefixWord ++ tailWord_6140082).sum := by decide
  have hdescent : baseEnd_6140082 < baseStart_6140082 := by decide
  rcases family_descends (prefixWord ++ tailWord_6140082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6140088 : List Nat := [2, 1, 2, 1, 2, 1, 4, 1, 2, 3, 4]
def baseStart_6140088 : Nat := 118140960795 + 6140088 * 2 ^ 59
def prefixEnd_6140088 : Nat := 4983230072969 + 3 ^ 40 * 6140088 * 2
def baseEnd_6140088 : Nat := 3152816404903678111162255

theorem tailTrace_6140088 : CollatzResearch.WordTrace tailWord_6140088 prefixEnd_6140088 3152816404903678111162255 := by
  unfold tailWord_6140088
  simp only [CollatzResearch.WordTrace]
  refine ⟨111973703689758647194366459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149298271586344862925821945 111973703689758647194366459)
  ·
    refine ⟨167960555534637970791549689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111973703689758647194366459 167960555534637970791549689)
    ·
      refine ⟨125970416650978478093662267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167960555534637970791549689 125970416650978478093662267)
      ·
        refine ⟨188955624976467717140493401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125970416650978478093662267 188955624976467717140493401)
        ·
          refine ⟨141716718732350787855370051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188955624976467717140493401 141716718732350787855370051)
          ·
            refine ⟨212575078098526181783055077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141716718732350787855370051 212575078098526181783055077)
            ·
              refine ⟨39857827143473659084322827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 212575078098526181783055077 39857827143473659084322827)
              ·
                refine ⟨59786740715210488626484241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39857827143473659084322827 59786740715210488626484241)
                ·
                  refine ⟨44840055536407866469863181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59786740715210488626484241 44840055536407866469863181)
                  ·
                    refine ⟨16815020826152949926198693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44840055536407866469863181 16815020826152949926198693)
                    ·
                      refine ⟨3152816404903678111162255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16815020826152949926198693 3152816404903678111162255)
                      ·
                        rfl

theorem cell23_6140088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 1, 2, 3, 4].length) (baseStart_6140088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6140088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6140088 prefixEnd_6140088 := by exact prefixLift 6140088
  have htrace : WordTrace (prefixWord ++ tailWord_6140088) baseStart_6140088 baseEnd_6140088 := by
    simpa [prefixWord, tailWord_6140088, baseEnd_6140088] using wordTrace_append hprefix tailTrace_6140088
  have hstable : (prefixWord ++ tailWord_6140088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6140088).length < 2 ^ (prefixWord ++ tailWord_6140088).sum := by decide
  have hdescent : baseEnd_6140088 < baseStart_6140088 := by decide
  rcases family_descends (prefixWord ++ tailWord_6140088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6140122 : List Nat := [3, 1, 1, 2, 2, 1, 2, 1, 6, 2, 2]
def baseStart_6140122 : Nat := 118140960795 + 6140122 * 2 ^ 59
def prefixEnd_6140122 : Nat := 4983230072969 + 3 ^ 40 * 6140122 * 2
def baseEnd_6140122 : Nat := 3152833863245930978137099

theorem tailTrace_6140122 : CollatzResearch.WordTrace tailWord_6140122 prefixEnd_6140122 3152833863245930978137099 := by
  unfold tailWord_6140122
  simp only [CollatzResearch.WordTrace]
  refine ⟨55987161865348529548867655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149299098307596078796980413 55987161865348529548867655)
  ·
    refine ⟨83980742798022794323301483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55987161865348529548867655 83980742798022794323301483)
    ·
      refine ⟨125971114197034191484952225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83980742798022794323301483 125971114197034191484952225)
      ·
        refine ⟨94478335647775643613714169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125971114197034191484952225 94478335647775643613714169)
        ·
          refine ⟨70858751735831732710285627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94478335647775643613714169 70858751735831732710285627)
          ·
            refine ⟨106288127603747599065428441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70858751735831732710285627 106288127603747599065428441)
            ·
              refine ⟨79716095702810699299071331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106288127603747599065428441 79716095702810699299071331)
              ·
                refine ⟨119574143554216048948606997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79716095702810699299071331 119574143554216048948606997)
                ·
                  refine ⟨5605037979103877294465953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 119574143554216048948606997 5605037979103877294465953)
                  ·
                    refine ⟨4203778484327907970849465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5605037979103877294465953 4203778484327907970849465)
                    ·
                      refine ⟨3152833863245930978137099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4203778484327907970849465 3152833863245930978137099)
                      ·
                        rfl

theorem cell23_6140122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 6, 2, 2].length) (baseStart_6140122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6140122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6140122 prefixEnd_6140122 := by exact prefixLift 6140122
  have htrace : WordTrace (prefixWord ++ tailWord_6140122) baseStart_6140122 baseEnd_6140122 := by
    simpa [prefixWord, tailWord_6140122, baseEnd_6140122] using wordTrace_append hprefix tailTrace_6140122
  have hstable : (prefixWord ++ tailWord_6140122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6140122).length < 2 ^ (prefixWord ++ tailWord_6140122).sum := by decide
  have hdescent : baseEnd_6140122 < baseStart_6140122 := by decide
  rcases family_descends (prefixWord ++ tailWord_6140122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6140139 : List Nat := [1, 1, 1, 1, 2, 5, 4, 2, 2, 2, 2]
def baseStart_6140139 : Nat := 118140960795 + 6140139 * 2 ^ 59
def prefixEnd_6140139 : Nat := 4983230072969 + 3 ^ 40 * 6140139 * 2
def baseEnd_6140139 : Nat := 3152842592417057411624521

theorem tailTrace_6140139 : CollatzResearch.WordTrace tailWord_6140139 prefixEnd_6140139 3152842592417057411624521 := by
  unfold tailWord_6140139
  simp only [CollatzResearch.WordTrace]
  refine ⟨223949267502332530098839471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149299511668221686732559647 223949267502332530098839471)
  ·
    refine ⟨335923901253498795148259207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223949267502332530098839471 335923901253498795148259207)
    ·
      refine ⟨503885851880248192722388811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 335923901253498795148259207 503885851880248192722388811)
      ·
        refine ⟨755828777820372289083583217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 503885851880248192722388811 755828777820372289083583217)
        ·
          refine ⟨566871583365279216812687413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 755828777820372289083583217 566871583365279216812687413)
          ·
            refine ⟨53144210940494926576189445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 566871583365279216812687413 53144210940494926576189445)
            ·
              refine ⟨9964539551342798733035521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53144210940494926576189445 9964539551342798733035521)
              ·
                refine ⟨7473404663507099049776641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9964539551342798733035521 7473404663507099049776641)
                ·
                  refine ⟨5605053497630324287332481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7473404663507099049776641 5605053497630324287332481)
                  ·
                    refine ⟨4203790123222743215499361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5605053497630324287332481 4203790123222743215499361)
                    ·
                      refine ⟨3152842592417057411624521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4203790123222743215499361 3152842592417057411624521)
                      ·
                        rfl

theorem cell23_6140139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 4, 2, 2, 2, 2].length) (baseStart_6140139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6140139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6140139 prefixEnd_6140139 := by exact prefixLift 6140139
  have htrace : WordTrace (prefixWord ++ tailWord_6140139) baseStart_6140139 baseEnd_6140139 := by
    simpa [prefixWord, tailWord_6140139, baseEnd_6140139] using wordTrace_append hprefix tailTrace_6140139
  have hstable : (prefixWord ++ tailWord_6140139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6140139).length < 2 ^ (prefixWord ++ tailWord_6140139).sum := by decide
  have hdescent : baseEnd_6140139 < baseStart_6140139 := by decide
  rcases family_descends (prefixWord ++ tailWord_6140139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6140162 : List Nat := [3, 4, 1, 1, 2, 2, 1, 2, 7]
def baseStart_6140162 : Nat := 118140960795 + 6140162 * 2 ^ 59
def prefixEnd_6140162 : Nat := 4983230072969 + 3 ^ 40 * 6140162 * 2
def baseEnd_6140162 : Nat := 350317155830234535737435

theorem tailTrace_6140162 : CollatzResearch.WordTrace tailWord_6140162 prefixEnd_6140162 350317155830234535737435 := by
  unfold tailWord_6140162
  simp only [CollatzResearch.WordTrace]
  refine ⟨55987526595312301256731685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149300070920832803351284493 55987526595312301256731685)
  ·
    refine ⟨10497661236621056485637191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55987526595312301256731685 10497661236621056485637191)
    ·
      refine ⟨15746491854931584728455787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10497661236621056485637191 15746491854931584728455787)
      ·
        refine ⟨23619737782397377092683681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15746491854931584728455787 23619737782397377092683681)
        ·
          refine ⟨17714803336798032819512761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23619737782397377092683681 17714803336798032819512761)
          ·
            refine ⟨13286102502598524614634571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17714803336798032819512761 13286102502598524614634571)
            ·
              refine ⟨19929153753897786921951857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13286102502598524614634571 19929153753897786921951857)
              ·
                refine ⟨14946865315423340191463893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19929153753897786921951857 14946865315423340191463893)
                ·
                  refine ⟨350317155830234535737435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14946865315423340191463893 350317155830234535737435)
                  ·
                    rfl

theorem cell23_6140162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 2, 7].length) (baseStart_6140162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6140162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6140162 prefixEnd_6140162 := by exact prefixLift 6140162
  have htrace : WordTrace (prefixWord ++ tailWord_6140162) baseStart_6140162 baseEnd_6140162 := by
    simpa [prefixWord, tailWord_6140162, baseEnd_6140162] using wordTrace_append hprefix tailTrace_6140162
  have hstable : (prefixWord ++ tailWord_6140162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6140162).length < 2 ^ (prefixWord ++ tailWord_6140162).sum := by decide
  have hdescent : baseEnd_6140162 < baseStart_6140162 := by decide
  rcases family_descends (prefixWord ++ tailWord_6140162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6140190 : List Nat := [4, 3, 2, 1, 1, 3, 1, 2, 2, 2, 2]
def baseStart_6140190 : Nat := 118140960795 + 6140190 * 2 ^ 59
def prefixEnd_6140190 : Nat := 4983230072969 + 3 ^ 40 * 6140190 * 2
def baseEnd_6140190 : Nat := 3152868779930436712086787

theorem tailTrace_6140190 : CollatzResearch.WordTrace tailWord_6140190 prefixEnd_6140190 3152868779930436712086787 := by
  unfold tailWord_6140190
  simp only [CollatzResearch.WordTrace]
  refine ⟨27993890953143470726118253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149300751750098510539297349 27993890953143470726118253)
  ·
    refine ⟨10497709107428801522294345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27993890953143470726118253 10497709107428801522294345)
    ·
      refine ⟨7873281830571601141720759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10497709107428801522294345 7873281830571601141720759)
      ·
        refine ⟨11809922745857401712581139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7873281830571601141720759 11809922745857401712581139)
        ·
          refine ⟨17714884118786102568871709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11809922745857401712581139 17714884118786102568871709)
          ·
            refine ⟨6643081544544788463326891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17714884118786102568871709 6643081544544788463326891)
            ·
              refine ⟨9964622316817182694990337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6643081544544788463326891 9964622316817182694990337)
              ·
                refine ⟨7473466737612887021242753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9964622316817182694990337 7473466737612887021242753)
                ·
                  refine ⟨5605100053209665265932065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7473466737612887021242753 5605100053209665265932065)
                  ·
                    refine ⟨4203825039907248949449049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5605100053209665265932065 4203825039907248949449049)
                    ·
                      refine ⟨3152868779930436712086787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4203825039907248949449049 3152868779930436712086787)
                      ·
                        rfl

theorem cell23_6140190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 3, 1, 2, 2, 2, 2].length) (baseStart_6140190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6140190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6140190 prefixEnd_6140190 := by exact prefixLift 6140190
  have htrace : WordTrace (prefixWord ++ tailWord_6140190) baseStart_6140190 baseEnd_6140190 := by
    simpa [prefixWord, tailWord_6140190, baseEnd_6140190] using wordTrace_append hprefix tailTrace_6140190
  have hstable : (prefixWord ++ tailWord_6140190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6140190).length < 2 ^ (prefixWord ++ tailWord_6140190).sum := by decide
  have hdescent : baseEnd_6140190 < baseStart_6140190 := by decide
  rcases family_descends (prefixWord ++ tailWord_6140190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6140195 : List Nat := [1, 1, 1, 4, 2, 2, 2, 1, 4, 1, 4]
def baseStart_6140195 : Nat := 118140960795 + 6140195 * 2 ^ 59
def prefixEnd_6140195 : Nat := 4983230072969 + 3 ^ 40 * 6140195 * 2
def baseEnd_6140195 : Nat := 3152871347333709192524263

theorem tailTrace_6140195 : CollatzResearch.WordTrace tailWord_6140195 prefixEnd_6140195 3152871347333709192524263 := by
  unfold tailWord_6140195
  simp only [CollatzResearch.WordTrace]
  refine ⟨223951309990129651662878039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149300873326753101108585359 223951309990129651662878039)
  ·
    refine ⟨335926964985194477494317059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223951309990129651662878039 335926964985194477494317059)
    ·
      refine ⟨503890447477791716241475589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 335926964985194477494317059 503890447477791716241475589)
      ·
        refine ⟨94479458902085946795276673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 503890447477791716241475589 94479458902085946795276673)
        ·
          refine ⟨70859594176564460096457505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94479458902085946795276673 70859594176564460096457505)
          ·
            refine ⟨53144695632423345072343129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70859594176564460096457505 53144695632423345072343129)
            ·
              refine ⟨39858521724317508804257347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53144695632423345072343129 39858521724317508804257347)
              ·
                refine ⟨59787782586476263206386021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39858521724317508804257347 59787782586476263206386021)
                ·
                  refine ⟨11210209234964299351197379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59787782586476263206386021 11210209234964299351197379)
                  ·
                    refine ⟨16815313852446449026796069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11210209234964299351197379 16815313852446449026796069)
                    ·
                      refine ⟨3152871347333709192524263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16815313852446449026796069 3152871347333709192524263)
                      ·
                        rfl

theorem cell23_6140195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 1, 4, 1, 4].length) (baseStart_6140195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6140195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6140195 prefixEnd_6140195 := by exact prefixLift 6140195
  have htrace : WordTrace (prefixWord ++ tailWord_6140195) baseStart_6140195 baseEnd_6140195 := by
    simpa [prefixWord, tailWord_6140195, baseEnd_6140195] using wordTrace_append hprefix tailTrace_6140195
  have hstable : (prefixWord ++ tailWord_6140195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6140195).length < 2 ^ (prefixWord ++ tailWord_6140195).sum := by decide
  have hdescent : baseEnd_6140195 < baseStart_6140195 := by decide
  rcases family_descends (prefixWord ++ tailWord_6140195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6140212 : List Nat := [2, 5, 1, 1, 1, 2, 1, 2, 1, 3, 4]
def baseStart_6140212 : Nat := 118140960795 + 6140212 * 2 ^ 59
def prefixEnd_6140212 : Nat := 4983230072969 + 3 ^ 40 * 6140212 * 2
def baseEnd_6140212 : Nat := 3152880076504835626011685

theorem tailTrace_6140212 : CollatzResearch.WordTrace tailWord_6140212 prefixEnd_6140212 3152880076504835626011685 := by
  unfold tailWord_6140212
  simp only [CollatzResearch.WordTrace]
  refine ⟨111975965015534031783123445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149301286687378709044164593 111975965015534031783123445)
  ·
    refine ⟨10497746720206315479667823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 111975965015534031783123445 10497746720206315479667823)
    ·
      refine ⟨15746620080309473219501735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10497746720206315479667823 15746620080309473219501735)
      ·
        refine ⟨23619930120464209829252603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15746620080309473219501735 23619930120464209829252603)
        ·
          refine ⟨35429895180696314743878905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23619930120464209829252603 35429895180696314743878905)
          ·
            refine ⟨26572421385522236057909179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35429895180696314743878905 26572421385522236057909179)
            ·
              refine ⟨39858632078283354086863769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26572421385522236057909179 39858632078283354086863769)
              ·
                refine ⟨29893974058712515565147827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39858632078283354086863769 29893974058712515565147827)
                ·
                  refine ⟨44840961088068773347721741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29893974058712515565147827 44840961088068773347721741)
                  ·
                    refine ⟨16815360408025790005395653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44840961088068773347721741 16815360408025790005395653)
                    ·
                      refine ⟨3152880076504835626011685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16815360408025790005395653 3152880076504835626011685)
                      ·
                        rfl

theorem cell23_6140212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_6140212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6140212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6140212 prefixEnd_6140212 := by exact prefixLift 6140212
  have htrace : WordTrace (prefixWord ++ tailWord_6140212) baseStart_6140212 baseEnd_6140212 := by
    simpa [prefixWord, tailWord_6140212, baseEnd_6140212] using wordTrace_append hprefix tailTrace_6140212
  have hstable : (prefixWord ++ tailWord_6140212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6140212).length < 2 ^ (prefixWord ++ tailWord_6140212).sum := by decide
  have hdescent : baseEnd_6140212 < baseStart_6140212 := by decide
  rcases family_descends (prefixWord ++ tailWord_6140212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6140256 : List Nat := [2, 1, 1, 3, 6, 1, 1, 1, 3, 4]
def baseStart_6140256 : Nat := 118140960795 + 6140256 * 2 ^ 59
def prefixEnd_6140256 : Nat := 4983230072969 + 3 ^ 40 * 6140256 * 2
def baseEnd_6140256 : Nat := 1050967556551211151287161

theorem tailTrace_6140256 : CollatzResearch.WordTrace tailWord_6140256 prefixEnd_6140256 1050967556551211151287161 := by
  unfold tailWord_6140256
  simp only [CollatzResearch.WordTrace]
  refine ⟨111976767421454329540424311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149302356561939106053899081 111976767421454329540424311)
  ·
    refine ⟨167965151132181494310636467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111976767421454329540424311 167965151132181494310636467)
    ·
      refine ⟨251947726698272241465954701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167965151132181494310636467 251947726698272241465954701)
      ·
        refine ⟨94480397511852090549733013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 251947726698272241465954701 94480397511852090549733013)
        ·
          refine ⟨4428768633368066744518735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 94480397511852090549733013 4428768633368066744518735)
          ·
            refine ⟨6643152950052100116778103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4428768633368066744518735 6643152950052100116778103)
            ·
              refine ⟨9964729425078150175167155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6643152950052100116778103 9964729425078150175167155)
              ·
                refine ⟨14947094137617225262750733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9964729425078150175167155 14947094137617225262750733)
                ·
                  refine ⟨5605160301606459473531525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14947094137617225262750733 5605160301606459473531525)
                  ·
                    refine ⟨1050967556551211151287161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5605160301606459473531525 1050967556551211151287161)
                    ·
                      rfl

theorem cell23_6140256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 1, 1, 3, 4].length) (baseStart_6140256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6140256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6140256 prefixEnd_6140256 := by exact prefixLift 6140256
  have htrace : WordTrace (prefixWord ++ tailWord_6140256) baseStart_6140256 baseEnd_6140256 := by
    simpa [prefixWord, tailWord_6140256, baseEnd_6140256] using wordTrace_append hprefix tailTrace_6140256
  have hstable : (prefixWord ++ tailWord_6140256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6140256).length < 2 ^ (prefixWord ++ tailWord_6140256).sum := by decide
  have hdescent : baseEnd_6140256 < baseStart_6140256 := by decide
  rcases family_descends (prefixWord ++ tailWord_6140256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6140265 : List Nat := [1, 2, 1, 1, 1, 3, 4, 2, 3, 5]
def baseStart_6140265 : Nat := 118140960795 + 6140265 * 2 ^ 59
def prefixEnd_6140265 : Nat := 4983230072969 + 3 ^ 40 * 6140265 * 2
def baseEnd_6140265 : Nat := 1050969096993174639549647

theorem tailTrace_6140265 : CollatzResearch.WordTrace tailWord_6140265 prefixEnd_6140265 1050969096993174639549647 := by
  unfold tailWord_6140265
  simp only [CollatzResearch.WordTrace]
  refine ⟨223953863099876053617926249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149302575399917369078617499 223953863099876053617926249)
  ·
    refine ⟨167965397324907040213444687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223953863099876053617926249 167965397324907040213444687)
    ·
      refine ⟨251948095987360560320167031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167965397324907040213444687 251948095987360560320167031)
      ·
        refine ⟨377922143981040840480250547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251948095987360560320167031 377922143981040840480250547)
        ·
          refine ⟨566883215971561260720375821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 377922143981040840480250547 566883215971561260720375821)
          ·
            refine ⟨212581205989335472770140933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 566883215971561260720375821 212581205989335472770140933)
            ·
              refine ⟨39858976123000401144401425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 212581205989335472770140933 39858976123000401144401425)
              ·
                refine ⟨29894232092250300858301069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39858976123000401144401425 29894232092250300858301069)
                ·
                  refine ⟨11210337034593862821862901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29894232092250300858301069 11210337034593862821862901)
                  ·
                    refine ⟨1050969096993174639549647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11210337034593862821862901 1050969096993174639549647)
                    ·
                      rfl

theorem cell23_6140265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 2, 3, 5].length) (baseStart_6140265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6140265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6140265 prefixEnd_6140265 := by exact prefixLift 6140265
  have htrace : WordTrace (prefixWord ++ tailWord_6140265) baseStart_6140265 baseEnd_6140265 := by
    simpa [prefixWord, tailWord_6140265, baseEnd_6140265] using wordTrace_append hprefix tailTrace_6140265
  have hstable : (prefixWord ++ tailWord_6140265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6140265).length < 2 ^ (prefixWord ++ tailWord_6140265).sum := by decide
  have hdescent : baseEnd_6140265 < baseStart_6140265 := by decide
  rcases family_descends (prefixWord ++ tailWord_6140265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6140296 : List Nat := [2, 1, 3, 3, 1, 1, 2, 5, 1, 1, 3]
def baseStart_6140296 : Nat := 118140960795 + 6140296 * 2 ^ 59
def prefixEnd_6140296 : Nat := 4983230072969 + 3 ^ 40 * 6140296 * 2
def baseEnd_6140296 : Nat := 3152923208879813297361299

theorem tailTrace_6140296 : CollatzResearch.WordTrace tailWord_6140296 prefixEnd_6140296 3152923208879813297361299 := by
  unfold tailWord_6140296
  simp only [CollatzResearch.WordTrace]
  refine ⟨111977496881381872956152371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149303329175175830608203161 111977496881381872956152371)
  ·
    refine ⟨167966245322072809434228557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111977496881381872956152371 167966245322072809434228557)
    ·
      refine ⟨62987341995777303537835709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167966245322072809434228557 62987341995777303537835709)
      ·
        refine ⟨23620253248416488826688391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62987341995777303537835709 23620253248416488826688391)
        ·
          refine ⟨35430379872624733240032587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23620253248416488826688391 35430379872624733240032587)
          ·
            refine ⟨53145569808937099860048881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35430379872624733240032587 53145569808937099860048881)
            ·
              refine ⟨39859177356702824895036661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53145569808937099860048881 39859177356702824895036661)
              ·
                refine ⟨3736797877190889833909687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39859177356702824895036661 3736797877190889833909687)
                ·
                  refine ⟨5605196815786334750864531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3736797877190889833909687 5605196815786334750864531)
                  ·
                    refine ⟨8407795223679502126296797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5605196815786334750864531 8407795223679502126296797)
                    ·
                      refine ⟨3152923208879813297361299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8407795223679502126296797 3152923208879813297361299)
                      ·
                        rfl

theorem cell23_6140296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 5, 1, 1, 3].length) (baseStart_6140296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6140296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6140296 prefixEnd_6140296 := by exact prefixLift 6140296
  have htrace : WordTrace (prefixWord ++ tailWord_6140296) baseStart_6140296 baseEnd_6140296 := by
    simpa [prefixWord, tailWord_6140296, baseEnd_6140296] using wordTrace_append hprefix tailTrace_6140296
  have hstable : (prefixWord ++ tailWord_6140296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6140296).length < 2 ^ (prefixWord ++ tailWord_6140296).sum := by decide
  have hdescent : baseEnd_6140296 < baseStart_6140296 := by decide
  rcases family_descends (prefixWord ++ tailWord_6140296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6140299 : List Nat := [1, 1, 1, 1, 4, 5, 3, 1, 1, 5]
def baseStart_6140299 : Nat := 118140960795 + 6140299 * 2 ^ 59
def prefixEnd_6140299 : Nat := 4983230072969 + 3 ^ 40 * 6140299 * 2
def baseEnd_6140299 : Nat := 1050974916440592261874595

theorem tailTrace_6140299 : CollatzResearch.WordTrace tailWord_6140299 prefixEnd_6140299 1050974916440592261874595 := by
  unfold tailWord_6140299
  simp only [CollatzResearch.WordTrace]
  refine ⟨223955103181752877424663951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149303402121168584949775967 223955103181752877424663951)
  ·
    refine ⟨335932654772629316136995927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223955103181752877424663951 335932654772629316136995927)
    ·
      refine ⟨503898982158943974205493891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 335932654772629316136995927 503898982158943974205493891)
      ·
        refine ⟨755848473238415961308240837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 503898982158943974205493891 755848473238415961308240837)
        ·
          refine ⟨141721588732202992745295157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 755848473238415961308240837 141721588732202992745295157)
          ·
            refine ⟨13286398943644030569871421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 141721588732202992745295157 13286398943644030569871421)
            ·
              refine ⟨4982399603866511463701783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13286398943644030569871421 4982399603866511463701783)
              ·
                refine ⟨7473599405799767195552675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4982399603866511463701783 7473599405799767195552675)
                ·
                  refine ⟨11210399108699650793329013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7473599405799767195552675 11210399108699650793329013)
                  ·
                    refine ⟨1050974916440592261874595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11210399108699650793329013 1050974916440592261874595)
                    ·
                      rfl

theorem cell23_6140299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 3, 1, 1, 5].length) (baseStart_6140299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6140299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6140299 prefixEnd_6140299 := by exact prefixLift 6140299
  have htrace : WordTrace (prefixWord ++ tailWord_6140299) baseStart_6140299 baseEnd_6140299 := by
    simpa [prefixWord, tailWord_6140299, baseEnd_6140299] using wordTrace_append hprefix tailTrace_6140299
  have hstable : (prefixWord ++ tailWord_6140299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6140299).length < 2 ^ (prefixWord ++ tailWord_6140299).sum := by decide
  have hdescent : baseEnd_6140299 < baseStart_6140299 := by decide
  rcases family_descends (prefixWord ++ tailWord_6140299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6140322 : List Nat := [3, 3, 1, 2, 1, 1, 2, 1, 3, 1, 5]
def baseStart_6140322 : Nat := 118140960795 + 6140322 * 2 ^ 59
def prefixEnd_6140322 : Nat := 4983230072969 + 3 ^ 40 * 6140322 * 2
def baseEnd_6140322 : Nat := 3152936559376830195636179

theorem tailTrace_6140322 : CollatzResearch.WordTrace tailWord_6140322 prefixEnd_6140322 3152936559376830195636179 := by
  unfold tailWord_6140322
  simp only [CollatzResearch.WordTrace]
  refine ⟨55988985515167388088187805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149303961373779701568500813 55988985515167388088187805)
  ·
    refine ⟨20995869568187770533070427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55988985515167388088187805 20995869568187770533070427)
    ·
      refine ⟨31493804352281655799605641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20995869568187770533070427 31493804352281655799605641)
      ·
        refine ⟨23620353264211241849704231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31493804352281655799605641 23620353264211241849704231)
        ·
          refine ⟨35430529896316862774556347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23620353264211241849704231 35430529896316862774556347)
          ·
            refine ⟨53145794844475294161834521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35430529896316862774556347 53145794844475294161834521)
            ·
              refine ⟨39859346133356470621375891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53145794844475294161834521 39859346133356470621375891)
              ·
                refine ⟨59789019200034705932063837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39859346133356470621375891 59789019200034705932063837)
                ·
                  refine ⟨22420882200013014724523939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59789019200034705932063837 22420882200013014724523939)
                  ·
                    refine ⟨33631323300019522086785909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22420882200013014724523939 33631323300019522086785909)
                    ·
                      refine ⟨3152936559376830195636179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33631323300019522086785909 3152936559376830195636179)
                      ·
                        rfl

theorem cell23_6140322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_6140322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6140322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6140322 prefixEnd_6140322 := by exact prefixLift 6140322
  have htrace : WordTrace (prefixWord ++ tailWord_6140322) baseStart_6140322 baseEnd_6140322 := by
    simpa [prefixWord, tailWord_6140322, baseEnd_6140322] using wordTrace_append hprefix tailTrace_6140322
  have hstable : (prefixWord ++ tailWord_6140322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6140322).length < 2 ^ (prefixWord ++ tailWord_6140322).sum := by decide
  have hdescent : baseEnd_6140322 < baseStart_6140322 := by decide
  rcases family_descends (prefixWord ++ tailWord_6140322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6140330 : List Nat := [3, 1, 6, 1, 1, 1, 1, 2, 3, 1, 3]
def baseStart_6140330 : Nat := 118140960795 + 6140330 * 2 ^ 59
def prefixEnd_6140330 : Nat := 4983230072969 + 3 ^ 40 * 6140330 * 2
def baseEnd_6140330 : Nat := 3152940667222066164336143

theorem tailTrace_6140330 : CollatzResearch.WordTrace tailWord_6140330 prefixEnd_6140330 3152940667222066164336143 := by
  unfold tailWord_6140330
  simp only [CollatzResearch.WordTrace]
  refine ⟨55989058461160142429760611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149304155896427046479361629 55989058461160142429760611)
  ·
    refine ⟨83983587691740213644640917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55989058461160142429760611 83983587691740213644640917)
    ·
      refine ⟨3936730673050322514592543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 83983587691740213644640917 3936730673050322514592543)
      ·
        refine ⟨5905096009575483771888815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3936730673050322514592543 5905096009575483771888815)
        ·
          refine ⟨8857644014363225657833223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5905096009575483771888815 8857644014363225657833223)
          ·
            refine ⟨13286466021544838486749835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8857644014363225657833223 13286466021544838486749835)
            ·
              refine ⟨19929699032317257730124753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13286466021544838486749835 19929699032317257730124753)
              ·
                refine ⟨14947274274237943297593565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19929699032317257730124753 14947274274237943297593565)
                ·
                  refine ⟨5605227852839228736597587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14947274274237943297593565 5605227852839228736597587)
                  ·
                    refine ⟨8407841779258843104896381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5605227852839228736597587 8407841779258843104896381)
                    ·
                      refine ⟨3152940667222066164336143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8407841779258843104896381 3152940667222066164336143)
                      ·
                        rfl

theorem cell23_6140330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_6140330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6140330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6140330 prefixEnd_6140330 := by exact prefixLift 6140330
  have htrace : WordTrace (prefixWord ++ tailWord_6140330) baseStart_6140330 baseEnd_6140330 := by
    simpa [prefixWord, tailWord_6140330, baseEnd_6140330] using wordTrace_append hprefix tailTrace_6140330
  have hstable : (prefixWord ++ tailWord_6140330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6140330).length < 2 ^ (prefixWord ++ tailWord_6140330).sum := by decide
  have hdescent : baseEnd_6140330 < baseStart_6140330 := by decide
  rcases family_descends (prefixWord ++ tailWord_6140330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6140370 : List Nat := [3, 2, 2, 4, 1, 1, 2, 1, 3, 2, 2]
def baseStart_6140370 : Nat := 118140960795 + 6140370 * 2 ^ 59
def prefixEnd_6140370 : Nat := 4983230072969 + 3 ^ 40 * 6140370 * 2
def baseEnd_6140370 : Nat := 3152961206448246007835959

theorem tailTrace_6140370 : CollatzResearch.WordTrace tailWord_6140370 prefixEnd_6140370 3152961206448246007835959 := by
  unfold tailWord_6140370
  simp only [CollatzResearch.WordTrace]
  refine ⟨55989423191123914137624641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149305128509663771033665709 55989423191123914137624641)
  ·
    refine ⟨41992067393342935603218481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55989423191123914137624641 41992067393342935603218481)
    ·
      refine ⟨31494050545007201702413861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41992067393342935603218481 31494050545007201702413861)
      ·
        refine ⟨5905134477188850319202599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31494050545007201702413861 5905134477188850319202599)
        ·
          refine ⟨8857701715783275478803899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5905134477188850319202599 8857701715783275478803899)
          ·
            refine ⟨13286552573674913218205849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8857701715783275478803899 13286552573674913218205849)
            ·
              refine ⟨9964914430256184913654387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13286552573674913218205849 9964914430256184913654387)
              ·
                refine ⟨14947371645384277370481581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9964914430256184913654387 14947371645384277370481581)
                ·
                  refine ⟨5605264367019104013930593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14947371645384277370481581 5605264367019104013930593)
                  ·
                    refine ⟨4203948275264328010447945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5605264367019104013930593 4203948275264328010447945)
                    ·
                      refine ⟨3152961206448246007835959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4203948275264328010447945 3152961206448246007835959)
                      ·
                        rfl

theorem cell23_6140370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_6140370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6140370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6140370 prefixEnd_6140370 := by exact prefixLift 6140370
  have htrace : WordTrace (prefixWord ++ tailWord_6140370) baseStart_6140370 baseEnd_6140370 := by
    simpa [prefixWord, tailWord_6140370, baseEnd_6140370] using wordTrace_append hprefix tailTrace_6140370
  have hstable : (prefixWord ++ tailWord_6140370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6140370).length < 2 ^ (prefixWord ++ tailWord_6140370).sum := by decide
  have hdescent : baseEnd_6140370 < baseStart_6140370 := by decide
  rcases family_descends (prefixWord ++ tailWord_6140370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6140396 : List Nat := [2, 2, 1, 1, 2, 1, 6, 2, 1, 3, 2]
def baseStart_6140396 : Nat := 118140960795 + 6140396 * 2 ^ 59
def prefixEnd_6140396 : Nat := 4983230072969 + 3 ^ 40 * 6140396 * 2
def baseEnd_6140396 : Nat := 3152974556945262906110839

theorem tailTrace_6140396 : CollatzResearch.WordTrace tailWord_6140396 prefixEnd_6140396 3152974556945262906110839 := by
  unfold tailWord_6140396
  simp only [CollatzResearch.WordTrace]
  refine ⟨111979320531200731495472521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149305760708267641993963361 111979320531200731495472521)
  ·
    refine ⟨83984490398400548621604391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111979320531200731495472521 83984490398400548621604391)
    ·
      refine ⟨125976735597600822932406587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83984490398400548621604391 125976735597600822932406587)
      ·
        refine ⟨188965103396401234398609881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125976735597600822932406587 188965103396401234398609881)
        ·
          refine ⟨141723827547300925798957411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 188965103396401234398609881 141723827547300925798957411)
          ·
            refine ⟨212585741320951388698436117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141723827547300925798957411 212585741320951388698436117)
            ·
              refine ⟨9964956624419596345239193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 212585741320951388698436117 9964956624419596345239193)
              ·
                refine ⟨7473717468314697258929395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9964956624419596345239193 7473717468314697258929395)
                ·
                  refine ⟨11210576202472045888394093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7473717468314697258929395 11210576202472045888394093)
                  ·
                    refine ⟨4203966075927017208147785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11210576202472045888394093 4203966075927017208147785)
                    ·
                      refine ⟨3152974556945262906110839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4203966075927017208147785 3152974556945262906110839)
                      ·
                        rfl

theorem cell23_6140396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 3, 2].length) (baseStart_6140396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6140396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6140396 prefixEnd_6140396 := by exact prefixLift 6140396
  have htrace : WordTrace (prefixWord ++ tailWord_6140396) baseStart_6140396 baseEnd_6140396 := by
    simpa [prefixWord, tailWord_6140396, baseEnd_6140396] using wordTrace_append hprefix tailTrace_6140396
  have hstable : (prefixWord ++ tailWord_6140396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6140396).length < 2 ^ (prefixWord ++ tailWord_6140396).sum := by decide
  have hdescent : baseEnd_6140396 < baseStart_6140396 := by decide
  rcases family_descends (prefixWord ++ tailWord_6140396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6140409 : List Nat := [1, 2, 1, 3, 1, 2, 2, 4, 1, 4, 2]
def baseStart_6140409 : Nat := 118140960795 + 6140409 * 2 ^ 59
def prefixEnd_6140409 : Nat := 4983230072969 + 3 ^ 40 * 6140409 * 2
def baseEnd_6140409 : Nat := 3152981232193771355248279

theorem tailTrace_6140409 : CollatzResearch.WordTrace tailWord_6140409 prefixEnd_6140409 3152981232193771355248279 := by
  unfold tailWord_6140409
  simp only [CollatzResearch.WordTrace]
  refine ⟨223959115211354366211168281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149306076807569577474112187 223959115211354366211168281)
  ·
    refine ⟨167969336408515774658376211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223959115211354366211168281 167969336408515774658376211)
    ·
      refine ⟨251954004612773661987564317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167969336408515774658376211 251954004612773661987564317)
      ·
        refine ⟨94482751729790123245336619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 251954004612773661987564317 94482751729790123245336619)
        ·
          refine ⟨141724127594685184868004929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94482751729790123245336619 141724127594685184868004929)
          ·
            refine ⟨106293095696013888651003697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141724127594685184868004929 106293095696013888651003697)
            ·
              refine ⟨79719821772010416488252773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106293095696013888651003697 79719821772010416488252773)
              ·
                refine ⟨14947466582251953091547395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 79719821772010416488252773 14947466582251953091547395)
                ·
                  refine ⟨22421199873377929637321093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14947466582251953091547395 22421199873377929637321093)
                  ·
                    refine ⟨4203974976258361806997705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22421199873377929637321093 4203974976258361806997705)
                    ·
                      refine ⟨3152981232193771355248279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4203974976258361806997705 3152981232193771355248279)
                      ·
                        rfl

theorem cell23_6140409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 4, 1, 4, 2].length) (baseStart_6140409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6140409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6140409 prefixEnd_6140409 := by exact prefixLift 6140409
  have htrace : WordTrace (prefixWord ++ tailWord_6140409) baseStart_6140409 baseEnd_6140409 := by
    simpa [prefixWord, tailWord_6140409, baseEnd_6140409] using wordTrace_append hprefix tailTrace_6140409
  have hstable : (prefixWord ++ tailWord_6140409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6140409).length < 2 ^ (prefixWord ++ tailWord_6140409).sum := by decide
  have hdescent : baseEnd_6140409 < baseStart_6140409 := by decide
  rcases family_descends (prefixWord ++ tailWord_6140409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6140412 : List Nat := [2, 2, 2, 1, 2, 1, 1, 2, 1, 6, 3]
def baseStart_6140412 : Nat := 118140960795 + 6140412 * 2 ^ 59
def prefixEnd_6140412 : Nat := 4983230072969 + 3 ^ 40 * 6140412 * 2
def baseEnd_6140412 : Nat := 3152982772635734843510765

theorem tailTrace_6140412 : CollatzResearch.WordTrace tailWord_6140412 prefixEnd_6140412 3152982772635734843510765 := by
  unfold tailWord_6140412
  simp only [CollatzResearch.WordTrace]
  refine ⟨111979612315171748861763745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149306149753562331815684993 111979612315171748861763745)
  ·
    refine ⟨83984709236378811646322809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111979612315171748861763745 83984709236378811646322809)
    ·
      refine ⟨62988531927284108734742107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83984709236378811646322809 62988531927284108734742107)
      ·
        refine ⟨94482797890926163102113161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62988531927284108734742107 94482797890926163102113161)
        ·
          refine ⟨70862098418194622326584871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94482797890926163102113161 70862098418194622326584871)
          ·
            refine ⟨106293147627291933489877307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70862098418194622326584871 106293147627291933489877307)
            ·
              refine ⟨159439721440937900234815961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106293147627291933489877307 159439721440937900234815961)
              ·
                refine ⟨119579791080703425176111971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 159439721440937900234815961 119579791080703425176111971)
                ·
                  refine ⟨179369686621055137764167957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 119579791080703425176111971 179369686621055137764167957)
                  ·
                    refine ⟨8407954060361959582695373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 179369686621055137764167957 8407954060361959582695373)
                    ·
                      refine ⟨3152982772635734843510765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8407954060361959582695373 3152982772635734843510765)
                      ·
                        rfl

theorem cell23_6140412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 1, 6, 3].length) (baseStart_6140412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6140412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6140412 prefixEnd_6140412 := by exact prefixLift 6140412
  have htrace : WordTrace (prefixWord ++ tailWord_6140412) baseStart_6140412 baseEnd_6140412 := by
    simpa [prefixWord, tailWord_6140412, baseEnd_6140412] using wordTrace_append hprefix tailTrace_6140412
  have hstable : (prefixWord ++ tailWord_6140412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6140412).length < 2 ^ (prefixWord ++ tailWord_6140412).sum := by decide
  have hdescent : baseEnd_6140412 < baseStart_6140412 := by decide
  rcases family_descends (prefixWord ++ tailWord_6140412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6140426 : List Nat := [3, 1, 2, 2, 2, 1, 1, 3, 4, 2, 2]
def baseStart_6140426 : Nat := 118140960795 + 6140426 * 2 ^ 59
def prefixEnd_6140426 : Nat := 4983230072969 + 3 ^ 40 * 6140426 * 2
def baseEnd_6140426 : Nat := 3152989961364897788735701

theorem tailTrace_6140426 : CollatzResearch.WordTrace tailWord_6140426 prefixEnd_6140426 3152989961364897788735701 := by
  unfold tailWord_6140426
  simp only [CollatzResearch.WordTrace]
  refine ⟨55989933813073194528634283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149306490168195185409691421 55989933813073194528634283)
  ·
    refine ⟨83984900719609791792951425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55989933813073194528634283 83984900719609791792951425)
    ·
      refine ⟨62988675539707343844713569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83984900719609791792951425 62988675539707343844713569)
      ·
        refine ⟨47241506654780507883535177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62988675539707343844713569 47241506654780507883535177)
        ·
          refine ⟨35431129991085380912651383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47241506654780507883535177 35431129991085380912651383)
          ·
            refine ⟨53146694986628071368977075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35431129991085380912651383 53146694986628071368977075)
            ·
              refine ⟨79720042479942107053465613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53146694986628071368977075 79720042479942107053465613)
              ·
                refine ⟨29895015929978290145049605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79720042479942107053465613 29895015929978290145049605)
                ·
                  refine ⟨5605315486870929402196801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29895015929978290145049605 5605315486870929402196801)
                  ·
                    refine ⟨4203986615153197051647601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5605315486870929402196801 4203986615153197051647601)
                    ·
                      refine ⟨3152989961364897788735701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4203986615153197051647601 3152989961364897788735701)
                      ·
                        rfl

theorem cell23_6140426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 3, 4, 2, 2].length) (baseStart_6140426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6140426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6140426 prefixEnd_6140426 := by exact prefixLift 6140426
  have htrace : WordTrace (prefixWord ++ tailWord_6140426) baseStart_6140426 baseEnd_6140426 := by
    simpa [prefixWord, tailWord_6140426, baseEnd_6140426] using wordTrace_append hprefix tailTrace_6140426
  have hstable : (prefixWord ++ tailWord_6140426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6140426).length < 2 ^ (prefixWord ++ tailWord_6140426).sum := by decide
  have hdescent : baseEnd_6140426 < baseStart_6140426 := by decide
  rcases family_descends (prefixWord ++ tailWord_6140426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6140472 : List Nat := [2, 1, 2, 1, 4, 1, 1, 1, 3, 2, 5]
def baseStart_6140472 : Nat := 118140960795 + 6140472 * 2 ^ 59
def prefixEnd_6140472 : Nat := 4983230072969 + 3 ^ 40 * 6140472 * 2
def baseEnd_6140472 : Nat := 3153013581475004608760489

theorem tailTrace_6140472 : CollatzResearch.WordTrace tailWord_6140472 prefixEnd_6140472 3153013581475004608760489 := by
  unfold tailWord_6140472
  simp only [CollatzResearch.WordTrace]
  refine ⟨111980706505063063985355835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149307608673417418647141113 111980706505063063985355835)
  ·
    refine ⟨167971059757594595978033753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111980706505063063985355835 167971059757594595978033753)
    ·
      refine ⟨125978294818195946983525315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167971059757594595978033753 125978294818195946983525315)
      ·
        refine ⟨188967442227293920475287973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 125978294818195946983525315 188967442227293920475287973)
        ·
          refine ⟨35431395417617610089116495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 188967442227293920475287973 35431395417617610089116495)
          ·
            refine ⟨53147093126426415133674743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35431395417617610089116495 53147093126426415133674743)
            ·
              refine ⟨79720639689639622700512115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53147093126426415133674743 79720639689639622700512115)
              ·
                refine ⟨119580959534459434050768173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79720639689639622700512115 119580959534459434050768173)
                ·
                  refine ⟨44842859825422287769038065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 119580959534459434050768173 44842859825422287769038065)
                  ·
                    refine ⟨33632144869066715826778549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44842859825422287769038065 33632144869066715826778549)
                    ·
                      refine ⟨3153013581475004608760489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33632144869066715826778549 3153013581475004608760489)
                      ·
                        rfl

theorem cell23_6140472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 3, 2, 5].length) (baseStart_6140472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6140472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6140472 prefixEnd_6140472 := by exact prefixLift 6140472
  have htrace : WordTrace (prefixWord ++ tailWord_6140472) baseStart_6140472 baseEnd_6140472 := by
    simpa [prefixWord, tailWord_6140472, baseEnd_6140472] using wordTrace_append hprefix tailTrace_6140472
  have hstable : (prefixWord ++ tailWord_6140472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6140472).length < 2 ^ (prefixWord ++ tailWord_6140472).sum := by decide
  have hdescent : baseEnd_6140472 < baseStart_6140472 := by decide
  rcases family_descends (prefixWord ++ tailWord_6140472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6140577 : List Nat := [1, 2, 3, 3, 4, 1, 1, 3, 1, 4]
def baseStart_6140577 : Nat := 118140960795 + 6140577 * 2 ^ 59
def prefixEnd_6140577 : Nat := 4983230072969 + 3 ^ 40 * 6140577 * 2
def baseEnd_6140577 : Nat := 1051022498981242232649169

theorem tailTrace_6140577 : CollatzResearch.WordTrace tailWord_6140577 prefixEnd_6140577 1051022498981242232649169 := by
  unfold tailWord_6140577
  simp only [CollatzResearch.WordTrace]
  refine ⟨223965242674745730903283985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149310161783163820602189323 223965242674745730903283985)
  ·
    refine ⟨167973932006059298177462989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223965242674745730903283985 167973932006059298177462989)
    ·
      refine ⟨62990224502272236816548621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167973932006059298177462989 62990224502272236816548621)
      ·
        refine ⟨23621334188352088806205733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62990224502272236816548621 23621334188352088806205733)
        ·
          refine ⟨4429000160316016651163575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23621334188352088806205733 4429000160316016651163575)
          ·
            refine ⟨6643500240474024976745363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4429000160316016651163575 6643500240474024976745363)
            ·
              refine ⟨9965250360711037465118045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6643500240474024976745363 9965250360711037465118045)
              ·
                refine ⟨3736968885266639049419267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9965250360711037465118045 3736968885266639049419267)
                ·
                  refine ⟨5605453327899958574128901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3736968885266639049419267 5605453327899958574128901)
                  ·
                    refine ⟨1051022498981242232649169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5605453327899958574128901 1051022498981242232649169)
                    ·
                      rfl

theorem cell23_6140577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 1, 3, 1, 4].length) (baseStart_6140577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6140577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6140577 prefixEnd_6140577 := by exact prefixLift 6140577
  have htrace : WordTrace (prefixWord ++ tailWord_6140577) baseStart_6140577 baseEnd_6140577 := by
    simpa [prefixWord, tailWord_6140577, baseEnd_6140577] using wordTrace_append hprefix tailTrace_6140577
  have hstable : (prefixWord ++ tailWord_6140577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6140577).length < 2 ^ (prefixWord ++ tailWord_6140577).sum := by decide
  have hdescent : baseEnd_6140577 < baseStart_6140577 := by decide
  rcases family_descends (prefixWord ++ tailWord_6140577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6140606 : List Nat := [4, 2, 1, 1, 2, 1, 2, 2, 3, 1, 4]
def baseStart_6140606 : Nat := 118140960795 + 6140606 * 2 ^ 59
def prefixEnd_6140606 : Nat := 4983230072969 + 3 ^ 40 * 6140606 * 2
def baseEnd_6140606 : Nat := 3153082387882707084484873

theorem tailTrace_6140606 : CollatzResearch.WordTrace tailWord_6140606 prefixEnd_6140606 3153082387882707084484873 := by
  unfold tailWord_6140606
  simp only [CollatzResearch.WordTrace]
  refine ⟨27995787548955083607011209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149310866927760445904059781 27995787548955083607011209)
  ·
    refine ⟨20996840661716312705258407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27995787548955083607011209 20996840661716312705258407)
    ·
      refine ⟨31495260992574469057887611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20996840661716312705258407 31495260992574469057887611)
      ·
        refine ⟨47242891488861703586831417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31495260992574469057887611 47242891488861703586831417)
        ·
          refine ⟨35432168616646277690123563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47242891488861703586831417 35432168616646277690123563)
          ·
            refine ⟨53148252924969416535185345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35432168616646277690123563 53148252924969416535185345)
            ·
              refine ⟨39861189693727062401389009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53148252924969416535185345 39861189693727062401389009)
              ·
                refine ⟨29895892270295296801041757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39861189693727062401389009 29895892270295296801041757)
                ·
                  refine ⟨11210959601360736300390659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29895892270295296801041757 11210959601360736300390659)
                  ·
                    refine ⟨16816439402041104450585989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11210959601360736300390659 16816439402041104450585989)
                    ·
                      refine ⟨3153082387882707084484873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16816439402041104450585989 3153082387882707084484873)
                      ·
                        rfl

theorem cell23_6140606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 2, 3, 1, 4].length) (baseStart_6140606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6140606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6140606 prefixEnd_6140606 := by exact prefixLift 6140606
  have htrace : WordTrace (prefixWord ++ tailWord_6140606) baseStart_6140606 baseEnd_6140606 := by
    simpa [prefixWord, tailWord_6140606, baseEnd_6140606] using wordTrace_append hprefix tailTrace_6140606
  have hstable : (prefixWord ++ tailWord_6140606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6140606).length < 2 ^ (prefixWord ++ tailWord_6140606).sum := by decide
  have hdescent : baseEnd_6140606 < baseStart_6140606 := by decide
  rcases family_descends (prefixWord ++ tailWord_6140606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6140640 : List Nat := [2, 1, 1, 3, 1, 2, 1, 7, 1, 2, 2]
def baseStart_6140640 : Nat := 118140960795 + 6140640 * 2 ^ 59
def prefixEnd_6140640 : Nat := 4983230072969 + 3 ^ 40 * 6140640 * 2
def baseEnd_6140640 : Nat := 3153099846224959951459717

theorem tailTrace_6140640 : CollatzResearch.WordTrace tailWord_6140640 prefixEnd_6140640 3153099846224959951459717 := by
  unfold tailWord_6140640
  simp only [CollatzResearch.WordTrace]
  refine ⟨111983770236758746331413687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149311693649011661775218249 111983770236758746331413687)
  ·
    refine ⟨167975655355138119497120531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111983770236758746331413687 167975655355138119497120531)
    ·
      refine ⟨251963483032707179245680797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167975655355138119497120531 251963483032707179245680797)
      ·
        refine ⟨94486306137265192217130299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 251963483032707179245680797 94486306137265192217130299)
        ·
          refine ⟨141729459205897788325695449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94486306137265192217130299 141729459205897788325695449)
          ·
            refine ⟨106297094404423341244271587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141729459205897788325695449 106297094404423341244271587)
            ·
              refine ⟨159445641606635011866407381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106297094404423341244271587 159445641606635011866407381)
              ·
                refine ⟨3737007225155508090618923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 159445641606635011866407381 3737007225155508090618923)
                ·
                  refine ⟨5605510837733262135928385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3737007225155508090618923 5605510837733262135928385)
                  ·
                    refine ⟨4204133128299946601946289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5605510837733262135928385 4204133128299946601946289)
                    ·
                      refine ⟨3153099846224959951459717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4204133128299946601946289 3153099846224959951459717)
                      ·
                        rfl

theorem cell23_6140640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 7, 1, 2, 2].length) (baseStart_6140640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6140640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6140640 prefixEnd_6140640 := by exact prefixLift 6140640
  have htrace : WordTrace (prefixWord ++ tailWord_6140640) baseStart_6140640 baseEnd_6140640 := by
    simpa [prefixWord, tailWord_6140640, baseEnd_6140640] using wordTrace_append hprefix tailTrace_6140640
  have hstable : (prefixWord ++ tailWord_6140640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6140640).length < 2 ^ (prefixWord ++ tailWord_6140640).sum := by decide
  have hdescent : baseEnd_6140640 < baseStart_6140640 := by decide
  rcases family_descends (prefixWord ++ tailWord_6140640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6140643 : List Nat := [1, 1, 1, 7, 1, 3, 1, 1, 1, 1, 5]
def baseStart_6140643 : Nat := 118140960795 + 6140643 * 2 ^ 59
def prefixEnd_6140643 : Nat := 4983230072969 + 3 ^ 40 * 6140643 * 2
def baseEnd_6140643 : Nat := 3153101386666923439722203

theorem tailTrace_6140643 : CollatzResearch.WordTrace tailWord_6140643 prefixEnd_6140643 3153101386666923439722203 := by
  unfold tailWord_6140643
  simp only [CollatzResearch.WordTrace]
  refine ⟨223967649892506624175186583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149311766595004416116791055 223967649892506624175186583)
  ·
    refine ⟨335951474838759936262779875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223967649892506624175186583 335951474838759936262779875)
    ·
      refine ⟨503927212258139904394169813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 335951474838759936262779875 503927212258139904394169813)
      ·
        refine ⟨11810794037300154009238355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 503927212258139904394169813 11810794037300154009238355)
        ·
          refine ⟨17716191055950231013857533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11810794037300154009238355 17716191055950231013857533)
          ·
            refine ⟨6643571645981336630196575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17716191055950231013857533 6643571645981336630196575)
            ·
              refine ⟨9965357468972004945294863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6643571645981336630196575 9965357468972004945294863)
              ·
                refine ⟨14948036203458007417942295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9965357468972004945294863 14948036203458007417942295)
                ·
                  refine ⟨22422054305187011126913443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14948036203458007417942295 22422054305187011126913443)
                  ·
                    refine ⟨33633081457780516690370165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22422054305187011126913443 33633081457780516690370165)
                    ·
                      refine ⟨3153101386666923439722203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33633081457780516690370165 3153101386666923439722203)
                      ·
                        rfl

theorem cell23_6140643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_6140643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6140643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6140643 prefixEnd_6140643 := by exact prefixLift 6140643
  have htrace : WordTrace (prefixWord ++ tailWord_6140643) baseStart_6140643 baseEnd_6140643 := by
    simpa [prefixWord, tailWord_6140643, baseEnd_6140643] using wordTrace_append hprefix tailTrace_6140643
  have hstable : (prefixWord ++ tailWord_6140643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6140643).length < 2 ^ (prefixWord ++ tailWord_6140643).sum := by decide
  have hdescent : baseEnd_6140643 < baseStart_6140643 := by decide
  rcases family_descends (prefixWord ++ tailWord_6140643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6140683 : List Nat := [1, 1, 1, 1, 5, 1, 1, 6, 1, 3, 2]
def baseStart_6140683 : Nat := 118140960795 + 6140683 * 2 ^ 59
def prefixEnd_6140683 : Nat := 4983230072969 + 3 ^ 40 * 6140683 * 2
def baseEnd_6140683 : Nat := 3153121925893103283222019

theorem tailTrace_6140683 : CollatzResearch.WordTrace tailWord_6140683 prefixEnd_6140683 3153121925893103283222019 := by
  unfold tailWord_6140683
  simp only [CollatzResearch.WordTrace]
  refine ⟨223969108812361711006642703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149312739208241140671095135 223969108812361711006642703)
  ·
    refine ⟨335953663218542566509964055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223969108812361711006642703 335953663218542566509964055)
    ·
      refine ⟨503930494827813849764946083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 335953663218542566509964055 503930494827813849764946083)
      ·
        refine ⟨755895742241720774647419125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 503930494827813849764946083 755895742241720774647419125)
        ·
          refine ⟨70865225835161322623195543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 755895742241720774647419125 70865225835161322623195543)
          ·
            refine ⟨106297838752741983934793315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70865225835161322623195543 106297838752741983934793315)
            ·
              refine ⟨159446758129112975902189973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106297838752741983934793315 159446758129112975902189973)
              ·
                refine ⟨7474066787302170745415155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 159446758129112975902189973 7474066787302170745415155)
                ·
                  refine ⟨11211100180953256118122733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7474066787302170745415155 11211100180953256118122733)
                  ·
                    refine ⟨4204162567857471044296025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11211100180953256118122733 4204162567857471044296025)
                    ·
                      refine ⟨3153121925893103283222019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4204162567857471044296025 3153121925893103283222019)
                      ·
                        rfl

theorem cell23_6140683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 6, 1, 3, 2].length) (baseStart_6140683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6140683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6140683 prefixEnd_6140683 := by exact prefixLift 6140683
  have htrace : WordTrace (prefixWord ++ tailWord_6140683) baseStart_6140683 baseEnd_6140683 := by
    simpa [prefixWord, tailWord_6140683, baseEnd_6140683] using wordTrace_append hprefix tailTrace_6140683
  have hstable : (prefixWord ++ tailWord_6140683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6140683).length < 2 ^ (prefixWord ++ tailWord_6140683).sum := by decide
  have hdescent : baseEnd_6140683 < baseStart_6140683 := by decide
  rcases family_descends (prefixWord ++ tailWord_6140683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6140700 : List Nat := [2, 2, 3, 1, 1, 4, 1, 3, 1, 3, 2]
def baseStart_6140700 : Nat := 118140960795 + 6140700 * 2 ^ 59
def prefixEnd_6140700 : Nat := 4983230072969 + 3 ^ 40 * 6140700 * 2
def baseEnd_6140700 : Nat := 3153130655064229716709441

theorem tailTrace_6140700 : CollatzResearch.WordTrace tailWord_6140700 prefixEnd_6140700 3153130655064229716709441 := by
  unfold tailWord_6140700
  simp only [CollatzResearch.WordTrace]
  refine ⟨111984864426650061455005777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149313152568866748606674369 111984864426650061455005777)
  ·
    refine ⟨83988648319987546091254333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111984864426650061455005777 83988648319987546091254333)
    ·
      refine ⟨31495743119995329784220375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 83988648319987546091254333 31495743119995329784220375)
      ·
        refine ⟨47243614679992994676330563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31495743119995329784220375 47243614679992994676330563)
        ·
          refine ⟨70865422019989492014495845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47243614679992994676330563 70865422019989492014495845)
          ·
            refine ⟨13287266628748029752717971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70865422019989492014495845 13287266628748029752717971)
            ·
              refine ⟨19930899943122044629076957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13287266628748029752717971 19930899943122044629076957)
              ·
                refine ⟨7474087478670766735903859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19930899943122044629076957 7474087478670766735903859)
                ·
                  refine ⟨11211131218006150103855789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7474087478670766735903859 11211131218006150103855789)
                  ·
                    refine ⟨4204174206752306288945921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11211131218006150103855789 4204174206752306288945921)
                    ·
                      refine ⟨3153130655064229716709441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4204174206752306288945921 3153130655064229716709441)
                      ·
                        rfl

theorem cell23_6140700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 3, 1, 3, 2].length) (baseStart_6140700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6140700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6140700 prefixEnd_6140700 := by exact prefixLift 6140700
  have htrace : WordTrace (prefixWord ++ tailWord_6140700) baseStart_6140700 baseEnd_6140700 := by
    simpa [prefixWord, tailWord_6140700, baseEnd_6140700] using wordTrace_append hprefix tailTrace_6140700
  have hstable : (prefixWord ++ tailWord_6140700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6140700).length < 2 ^ (prefixWord ++ tailWord_6140700).sum := by decide
  have hdescent : baseEnd_6140700 < baseStart_6140700 := by decide
  rcases family_descends (prefixWord ++ tailWord_6140700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6140706 : List Nat := [3, 3, 1, 1, 2, 2, 1, 2, 2, 6]
def baseStart_6140706 : Nat := 118140960795 + 6140706 * 2 ^ 59
def prefixEnd_6140706 : Nat := 4983230072969 + 3 ^ 40 * 6140706 * 2
def baseEnd_6140706 : Nat := 1051044578649385564411471

theorem tailTrace_6140706 : CollatzResearch.WordTrace tailWord_6140706 prefixEnd_6140706 1051044578649385564411471 := by
  unfold tailWord_6140706
  simp only [CollatzResearch.WordTrace]
  refine ⟨55992486922819596483682493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149313298460852257289819981 55992486922819596483682493)
  ·
    refine ⟨20997182596057348681380935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55992486922819596483682493 20997182596057348681380935)
    ·
      refine ⟨31495773894086023022071403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20997182596057348681380935 31495773894086023022071403)
      ·
        refine ⟨47243660841129034533107105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31495773894086023022071403 47243660841129034533107105)
        ·
          refine ⟨35432745630846775899830329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47243660841129034533107105 35432745630846775899830329)
          ·
            refine ⟨26574559223135081924872747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35432745630846775899830329 26574559223135081924872747)
            ·
              refine ⟨39861838834702622887309121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26574559223135081924872747 39861838834702622887309121)
              ·
                refine ⟨29896379126026967165481841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39861838834702622887309121 29896379126026967165481841)
                ·
                  refine ⟨22422284344520225374111381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29896379126026967165481841 22422284344520225374111381)
                  ·
                    refine ⟨1051044578649385564411471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22422284344520225374111381 1051044578649385564411471)
                    ·
                      rfl

theorem cell23_6140706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 2, 2, 6].length) (baseStart_6140706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6140706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6140706 prefixEnd_6140706 := by exact prefixLift 6140706
  have htrace : WordTrace (prefixWord ++ tailWord_6140706) baseStart_6140706 baseEnd_6140706 := by
    simpa [prefixWord, tailWord_6140706, baseEnd_6140706] using wordTrace_append hprefix tailTrace_6140706
  have hstable : (prefixWord ++ tailWord_6140706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6140706).length < 2 ^ (prefixWord ++ tailWord_6140706).sum := by decide
  have hdescent : baseEnd_6140706 < baseStart_6140706 := by decide
  rcases family_descends (prefixWord ++ tailWord_6140706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6140713 : List Nat := [1, 2, 1, 1, 1, 1, 1, 7, 4, 2, 2]
def baseStart_6140713 : Nat := 118140960795 + 6140713 * 2 ^ 59
def prefixEnd_6140713 : Nat := 4983230072969 + 3 ^ 40 * 6140713 * 2
def baseEnd_6140713 : Nat := 3153137330312738165846881

theorem tailTrace_6140713 : CollatzResearch.WordTrace tailWord_6140713 prefixEnd_6140713 3153137330312738165846881 := by
  unfold tailWord_6140713
  simp only [CollatzResearch.WordTrace]
  refine ⟨223970203002253026130234793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149313468668168684086823195 223970203002253026130234793)
  ·
    refine ⟨167977652251689769597676095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223970203002253026130234793 167977652251689769597676095)
    ·
      refine ⟨251966478377534654396514143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167977652251689769597676095 251966478377534654396514143)
      ·
        refine ⟨377949717566301981594771215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251966478377534654396514143 377949717566301981594771215)
        ·
          refine ⟨566924576349452972392156823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 377949717566301981594771215 566924576349452972392156823)
          ·
            refine ⟨850386864524179458588235235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 566924576349452972392156823 850386864524179458588235235)
            ·
              refine ⟨1275580296786269187882352853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 850386864524179458588235235 1275580296786269187882352853)
              ·
                refine ⟨29896413205928184090992645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1275580296786269187882352853 29896413205928184090992645)
                ·
                  refine ⟨5605577476111534517061121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29896413205928184090992645 5605577476111534517061121)
                  ·
                    refine ⟨4204183107083650887795841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5605577476111534517061121 4204183107083650887795841)
                    ·
                      refine ⟨3153137330312738165846881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4204183107083650887795841 3153137330312738165846881)
                      ·
                        rfl

theorem cell23_6140713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 7, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 7, 4, 2, 2].length) (baseStart_6140713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6140713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6140713 prefixEnd_6140713 := by exact prefixLift 6140713
  have htrace : WordTrace (prefixWord ++ tailWord_6140713) baseStart_6140713 baseEnd_6140713 := by
    simpa [prefixWord, tailWord_6140713, baseEnd_6140713] using wordTrace_append hprefix tailTrace_6140713
  have hstable : (prefixWord ++ tailWord_6140713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6140713).length < 2 ^ (prefixWord ++ tailWord_6140713).sum := by decide
  have hdescent : baseEnd_6140713 < baseStart_6140713 := by decide
  rcases family_descends (prefixWord ++ tailWord_6140713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6140724 : List Nat := [2, 5, 1, 1, 3, 1, 3, 1, 2, 1, 3]
def baseStart_6140724 : Nat := 118140960795 + 6140724 * 2 ^ 59
def prefixEnd_6140724 : Nat := 4983230072969 + 3 ^ 40 * 6140724 * 2
def baseEnd_6140724 : Nat := 3153142978599937622809331

theorem tailTrace_6140724 : CollatzResearch.WordTrace tailWord_6140724 prefixEnd_6140724 3153142978599937622809331 := by
  unfold tailWord_6140724
  simp only [CollatzResearch.WordTrace]
  refine ⟨111985302102606587504442613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149313736136808783339256817 111985302102606587504442613)
  ·
    refine ⟨10498622072119367578541495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 111985302102606587504442613 10498622072119367578541495)
    ·
      refine ⟨15747933108179051367812243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10498622072119367578541495 15747933108179051367812243)
      ·
        refine ⟨23621899662268577051718365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15747933108179051367812243 23621899662268577051718365)
        ·
          refine ⟨8858212373350716394394387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23621899662268577051718365 8858212373350716394394387)
          ·
            refine ⟨13287318560026074591591581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8858212373350716394394387 13287318560026074591591581)
            ·
              refine ⟨4982744460009777971846843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13287318560026074591591581 4982744460009777971846843)
              ·
                refine ⟨7474116690014666957770265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4982744460009777971846843 7474116690014666957770265)
                ·
                  refine ⟨5605587517511000218327699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7474116690014666957770265 5605587517511000218327699)
                  ·
                    refine ⟨8408381276266500327491549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5605587517511000218327699 8408381276266500327491549)
                    ·
                      refine ⟨3153142978599937622809331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8408381276266500327491549 3153142978599937622809331)
                      ·
                        rfl

theorem cell23_6140724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 3, 1, 2, 1, 3].length) (baseStart_6140724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6140724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6140724 prefixEnd_6140724 := by exact prefixLift 6140724
  have htrace : WordTrace (prefixWord ++ tailWord_6140724) baseStart_6140724 baseEnd_6140724 := by
    simpa [prefixWord, tailWord_6140724, baseEnd_6140724] using wordTrace_append hprefix tailTrace_6140724
  have hstable : (prefixWord ++ tailWord_6140724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6140724).length < 2 ^ (prefixWord ++ tailWord_6140724).sum := by decide
  have hdescent : baseEnd_6140724 < baseStart_6140724 := by decide
  rcases family_descends (prefixWord ++ tailWord_6140724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6140746 : List Nat := [3, 1, 2, 1, 1, 1, 2, 2, 4, 3, 3]
def baseStart_6140746 : Nat := 118140960795 + 6140746 * 2 ^ 59
def prefixEnd_6140746 : Nat := 4983230072969 + 3 ^ 40 * 6140746 * 2
def baseEnd_6140746 : Nat := 3153154275174336536734229

theorem tailTrace_6140746 : CollatzResearch.WordTrace tailWord_6140746 prefixEnd_6140746 3153154275174336536734229 := by
  unfold tailWord_6140746
  simp only [CollatzResearch.WordTrace]
  refine ⟨55992851652783368191546523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149314271074088981844124061 55992851652783368191546523)
  ·
    refine ⟨83989277479175052287319785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55992851652783368191546523 83989277479175052287319785)
    ·
      refine ⟨62991958109381289215489839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83989277479175052287319785 62991958109381289215489839)
      ·
        refine ⟨94487937164071933823234759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62991958109381289215489839 94487937164071933823234759)
        ·
          refine ⟨141731905746107900734852139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94487937164071933823234759 141731905746107900734852139)
          ·
            refine ⟨212597858619161851102278209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141731905746107900734852139 212597858619161851102278209)
            ·
              refine ⟨159448393964371388326708657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 212597858619161851102278209 159448393964371388326708657)
              ·
                refine ⟨119586295473278541245031493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 159448393964371388326708657 119586295473278541245031493)
                ·
                  refine ⟨22422430401239726483443405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 119586295473278541245031493 22422430401239726483443405)
                  ·
                    refine ⟨8408411400464897431291277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22422430401239726483443405 8408411400464897431291277)
                    ·
                      refine ⟨3153154275174336536734229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8408411400464897431291277 3153154275174336536734229)
                      ·
                        rfl

theorem cell23_6140746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 4, 3, 3].length) (baseStart_6140746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6140746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6140746 prefixEnd_6140746 := by exact prefixLift 6140746
  have htrace : WordTrace (prefixWord ++ tailWord_6140746) baseStart_6140746 baseEnd_6140746 := by
    simpa [prefixWord, tailWord_6140746, baseEnd_6140746] using wordTrace_append hprefix tailTrace_6140746
  have hstable : (prefixWord ++ tailWord_6140746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6140746).length < 2 ^ (prefixWord ++ tailWord_6140746).sum := by decide
  have hdescent : baseEnd_6140746 < baseStart_6140746 := by decide
  rcases family_descends (prefixWord ++ tailWord_6140746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6140770 : List Nat := [3, 3, 2, 1, 3, 2, 1, 1, 7]
def baseStart_6140770 : Nat := 118140960795 + 6140770 * 2 ^ 59
def prefixEnd_6140770 : Nat := 4983230072969 + 3 ^ 40 * 6140770 * 2
def baseEnd_6140770 : Nat := 350351844301116049203791

theorem tailTrace_6140770 : CollatzResearch.WordTrace tailWord_6140770 prefixEnd_6140770 350351844301116049203791 := by
  unfold tailWord_6140770
  simp only [CollatzResearch.WordTrace]
  refine ⟨55993070490761631216264941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149314854642031016576706509 55993070490761631216264941)
  ·
    refine ⟨20997401434035611706099353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55993070490761631216264941 20997401434035611706099353)
    ·
      refine ⟨15748051075526708779574515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20997401434035611706099353 15748051075526708779574515)
      ·
        refine ⟨23622076613290063169361773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15748051075526708779574515 23622076613290063169361773)
        ·
          refine ⟨8858278729983773688510665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23622076613290063169361773 8858278729983773688510665)
          ·
            refine ⟨6643709047487830266382999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8858278729983773688510665 6643709047487830266382999)
            ·
              refine ⟨9965563571231745399574499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6643709047487830266382999 9965563571231745399574499)
              ·
                refine ⟨14948345356847618099361749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9965563571231745399574499 14948345356847618099361749)
                ·
                  refine ⟨350351844301116049203791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14948345356847618099361749 350351844301116049203791)
                  ·
                    rfl

theorem cell23_6140770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 1, 1, 7].length) (baseStart_6140770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6140770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6140770 prefixEnd_6140770 := by exact prefixLift 6140770
  have htrace : WordTrace (prefixWord ++ tailWord_6140770) baseStart_6140770 baseEnd_6140770 := by
    simpa [prefixWord, tailWord_6140770, baseEnd_6140770] using wordTrace_append hprefix tailTrace_6140770
  have hstable : (prefixWord ++ tailWord_6140770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6140770).length < 2 ^ (prefixWord ++ tailWord_6140770).sum := by decide
  have hdescent : baseEnd_6140770 < baseStart_6140770 := by decide
  rcases family_descends (prefixWord ++ tailWord_6140770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6140776 : List Nat := [2, 1, 4, 2, 1, 2, 1, 1, 1, 1, 7]
def baseStart_6140776 : Nat := 118140960795 + 6140776 * 2 ^ 59
def prefixEnd_6140776 : Nat := 4983230072969 + 3 ^ 40 * 6140776 * 2
def baseEnd_6140776 : Nat := 3153169679593971419359091

theorem tailTrace_6140776 : CollatzResearch.WordTrace tailWord_6140776 prefixEnd_6140776 3153169679593971419359091 := by
  unfold tailWord_6140776
  simp only [CollatzResearch.WordTrace]
  refine ⟨111986250400512393944889091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149315000534016525259852121 111986250400512393944889091)
  ·
    refine ⟨167979375600768590917333637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111986250400512393944889091 167979375600768590917333637)
    ·
      refine ⟨31496132925144110797000057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 167979375600768590917333637 31496132925144110797000057)
      ·
        refine ⟨23622099693858083097750043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31496132925144110797000057 23622099693858083097750043)
        ·
          refine ⟨35433149540787124646625065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23622099693858083097750043 35433149540787124646625065)
          ·
            refine ⟨26574862155590343484968799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35433149540787124646625065 26574862155590343484968799)
            ·
              refine ⟨39862293233385515227453199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26574862155590343484968799 39862293233385515227453199)
              ·
                refine ⟨59793439850078272841179799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39862293233385515227453199 59793439850078272841179799)
                ·
                  refine ⟨89690159775117409261769699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59793439850078272841179799 89690159775117409261769699)
                  ·
                    refine ⟨134535239662676113892654549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 89690159775117409261769699 134535239662676113892654549)
                    ·
                      refine ⟨3153169679593971419359091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 134535239662676113892654549 3153169679593971419359091)
                      ·
                        rfl

theorem cell23_6140776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_6140776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6140776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6140776 prefixEnd_6140776 := by exact prefixLift 6140776
  have htrace : WordTrace (prefixWord ++ tailWord_6140776) baseStart_6140776 baseEnd_6140776 := by
    simpa [prefixWord, tailWord_6140776, baseEnd_6140776] using wordTrace_append hprefix tailTrace_6140776
  have hstable : (prefixWord ++ tailWord_6140776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6140776).length < 2 ^ (prefixWord ++ tailWord_6140776).sum := by decide
  have hdescent : baseEnd_6140776 < baseStart_6140776 := by decide
  rcases family_descends (prefixWord ++ tailWord_6140776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6140786 : List Nat := [3, 2, 1, 2, 1, 1, 2, 1, 3, 3, 4]
def baseStart_6140786 : Nat := 118140960795 + 6140786 * 2 ^ 59
def prefixEnd_6140786 : Nat := 4983230072969 + 3 ^ 40 * 6140786 * 2
def baseEnd_6140786 : Nat := 3153174814400516380234045

theorem tailTrace_6140786 : CollatzResearch.WordTrace tailWord_6140786 prefixEnd_6140786 3153174814400516380234045 := by
  unfold tailWord_6140786
  simp only [CollatzResearch.WordTrace]
  refine ⟨55993216382747139899410553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149315243687325706398428141 55993216382747139899410553)
  ·
    refine ⟨41994912287060354924557915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55993216382747139899410553 41994912287060354924557915)
    ·
      refine ⟨62992368430590532386836873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41994912287060354924557915 62992368430590532386836873)
      ·
        refine ⟨47244276322942899290127655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62992368430590532386836873 47244276322942899290127655)
        ·
          refine ⟨70866414484414348935191483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47244276322942899290127655 70866414484414348935191483)
          ·
            refine ⟨106299621726621523402787225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70866414484414348935191483 106299621726621523402787225)
            ·
              refine ⟨79724716294966142552090419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106299621726621523402787225 79724716294966142552090419)
              ·
                refine ⟨119587074442449213828135629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79724716294966142552090419 119587074442449213828135629)
                ·
                  refine ⟨44845152915918455185550861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 119587074442449213828135629 44845152915918455185550861)
                  ·
                    refine ⟨16816932343469420694581573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44845152915918455185550861 16816932343469420694581573)
                    ·
                      refine ⟨3153174814400516380234045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16816932343469420694581573 3153174814400516380234045)
                      ·
                        rfl

theorem cell23_6140786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 3, 3, 4].length) (baseStart_6140786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6140786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6140786 prefixEnd_6140786 := by exact prefixLift 6140786
  have htrace : WordTrace (prefixWord ++ tailWord_6140786) baseStart_6140786 baseEnd_6140786 := by
    simpa [prefixWord, tailWord_6140786, baseEnd_6140786] using wordTrace_append hprefix tailTrace_6140786
  have hstable : (prefixWord ++ tailWord_6140786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6140786).length < 2 ^ (prefixWord ++ tailWord_6140786).sum := by decide
  have hdescent : baseEnd_6140786 < baseStart_6140786 := by decide
  rcases family_descends (prefixWord ++ tailWord_6140786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6140803 : List Nat := [1, 1, 1, 3, 4, 1, 4, 1, 2, 1, 4]
def baseStart_6140803 : Nat := 118140960795 + 6140803 * 2 ^ 59
def prefixEnd_6140803 : Nat := 4983230072969 + 3 ^ 40 * 6140803 * 2
def baseEnd_6140803 : Nat := 3153183543571642813721467

theorem tailTrace_6140803 : CollatzResearch.WordTrace tailWord_6140803 prefixEnd_6140803 3153183543571642813721467 := by
  unfold tailWord_6140803
  simp only [CollatzResearch.WordTrace]
  refine ⟨223973485571926971501011063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149315657047951314334007375 223973485571926971501011063)
  ·
    refine ⟨335960228357890457251516595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223973485571926971501011063 335960228357890457251516595)
    ·
      refine ⟨503940342536835685877274893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 335960228357890457251516595 503940342536835685877274893)
      ·
        refine ⟨188977628451313382203978085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 503940342536835685877274893 188977628451313382203978085)
        ·
          refine ⟨35433305334621259163245891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 188977628451313382203978085 35433305334621259163245891)
          ·
            refine ⟨53149958001931888744868837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35433305334621259163245891 53149958001931888744868837)
            ·
              refine ⟨9965617125362229139662907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53149958001931888744868837 9965617125362229139662907)
              ·
                refine ⟨14948425688043343709494361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9965617125362229139662907 14948425688043343709494361)
                ·
                  refine ⟨11211319266032507782120771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14948425688043343709494361 11211319266032507782120771)
                  ·
                    refine ⟨16816978899048761673181157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11211319266032507782120771 16816978899048761673181157)
                    ·
                      refine ⟨3153183543571642813721467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16816978899048761673181157 3153183543571642813721467)
                      ·
                        rfl

theorem cell23_6140803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 4, 1, 2, 1, 4].length) (baseStart_6140803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6140803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6140803 prefixEnd_6140803 := by exact prefixLift 6140803
  have htrace : WordTrace (prefixWord ++ tailWord_6140803) baseStart_6140803 baseEnd_6140803 := by
    simpa [prefixWord, tailWord_6140803, baseEnd_6140803] using wordTrace_append hprefix tailTrace_6140803
  have hstable : (prefixWord ++ tailWord_6140803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6140803).length < 2 ^ (prefixWord ++ tailWord_6140803).sum := by decide
  have hdescent : baseEnd_6140803 < baseStart_6140803 := by decide
  rcases family_descends (prefixWord ++ tailWord_6140803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6140820 : List Nat := [2, 4, 2, 1, 1, 1, 2, 2, 2, 4, 2]
def baseStart_6140820 : Nat := 118140960795 + 6140820 * 2 ^ 59
def prefixEnd_6140820 : Nat := 4983230072969 + 3 ^ 40 * 6140820 * 2
def baseEnd_6140820 : Nat := 3153192272742769247208889

theorem tailTrace_6140820 : CollatzResearch.WordTrace tailWord_6140820 prefixEnd_6140820 3153192272742769247208889 := by
  unfold tailWord_6140820
  simp only [CollatzResearch.WordTrace]
  refine ⟨111987052806432691702189957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149316070408576922269586609 111987052806432691702189957)
  ·
    refine ⟨20997572401206129694160617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 111987052806432691702189957 20997572401206129694160617)
    ·
      refine ⟨15748179300904597270620463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20997572401206129694160617 15748179300904597270620463)
      ·
        refine ⟨23622268951356895905930695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15748179300904597270620463 23622268951356895905930695)
        ·
          refine ⟨35433403427035343858896043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23622268951356895905930695 35433403427035343858896043)
          ·
            refine ⟨53150105140553015788344065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35433403427035343858896043 53150105140553015788344065)
            ·
              refine ⟨39862578855414761841258049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53150105140553015788344065 39862578855414761841258049)
              ·
                refine ⟨29896934141561071380943537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39862578855414761841258049 29896934141561071380943537)
                ·
                  refine ⟨22422700606170803535707653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29896934141561071380943537 22422700606170803535707653)
                  ·
                    refine ⟨4204256363657025662945185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22422700606170803535707653 4204256363657025662945185)
                    ·
                      refine ⟨3153192272742769247208889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4204256363657025662945185 3153192272742769247208889)
                      ·
                        rfl

theorem cell23_6140820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 2, 2, 4, 2].length) (baseStart_6140820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6140820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6140820 prefixEnd_6140820 := by exact prefixLift 6140820
  have htrace : WordTrace (prefixWord ++ tailWord_6140820) baseStart_6140820 baseEnd_6140820 := by
    simpa [prefixWord, tailWord_6140820, baseEnd_6140820] using wordTrace_append hprefix tailTrace_6140820
  have hstable : (prefixWord ++ tailWord_6140820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6140820).length < 2 ^ (prefixWord ++ tailWord_6140820).sum := by decide
  have hdescent : baseEnd_6140820 < baseStart_6140820 := by decide
  rcases family_descends (prefixWord ++ tailWord_6140820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6140823 : List Nat := [1, 1, 3, 3, 1, 2, 1, 4, 2, 2, 3]
def baseStart_6140823 : Nat := 118140960795 + 6140823 * 2 ^ 59
def prefixEnd_6140823 : Nat := 4983230072969 + 3 ^ 40 * 6140823 * 2
def baseEnd_6140823 : Nat := 3153193813184732735471375

theorem tailTrace_6140823 : CollatzResearch.WordTrace tailWord_6140823 prefixEnd_6140823 3153193813184732735471375 := by
  unfold tailWord_6140823
  simp only [CollatzResearch.WordTrace]
  refine ⟨223974215031854514916739123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149316143354569676611159415 223974215031854514916739123)
  ·
    refine ⟨335961322547781772375108685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223974215031854514916739123 335961322547781772375108685)
    ·
      refine ⟨125985495955418164640665757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 335961322547781772375108685 125985495955418164640665757)
      ·
        refine ⟨47244560983281811740249659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 125985495955418164640665757 47244560983281811740249659)
        ·
          refine ⟨70866841474922717610374489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47244560983281811740249659 70866841474922717610374489)
          ·
            refine ⟨53150131106192038207780867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70866841474922717610374489 53150131106192038207780867)
            ·
              refine ⟨79725196659288057311671301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53150131106192038207780867 79725196659288057311671301)
              ·
                refine ⟨14948474373616510745938369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 79725196659288057311671301 14948474373616510745938369)
                ·
                  refine ⟨11211355780212383059453777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14948474373616510745938369 11211355780212383059453777)
                  ·
                    refine ⟨8408516835159287294590333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11211355780212383059453777 8408516835159287294590333)
                    ·
                      refine ⟨3153193813184732735471375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8408516835159287294590333 3153193813184732735471375)
                      ·
                        rfl

theorem cell23_6140823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 4, 2, 2, 3].length) (baseStart_6140823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6140823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6140823 prefixEnd_6140823 := by exact prefixLift 6140823
  have htrace : WordTrace (prefixWord ++ tailWord_6140823) baseStart_6140823 baseEnd_6140823 := by
    simpa [prefixWord, tailWord_6140823, baseEnd_6140823] using wordTrace_append hprefix tailTrace_6140823
  have hstable : (prefixWord ++ tailWord_6140823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6140823).length < 2 ^ (prefixWord ++ tailWord_6140823).sum := by decide
  have hdescent : baseEnd_6140823 < baseStart_6140823 := by decide
  rcases family_descends (prefixWord ++ tailWord_6140823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6140854 : List Nat := [5, 1, 4, 1, 1, 1, 1, 1, 1, 3, 4]
def baseStart_6140854 : Nat := 118140960795 + 6140854 * 2 ^ 59
def prefixEnd_6140854 : Nat := 4983230072969 + 3 ^ 40 * 6140854 * 2
def baseEnd_6140854 : Nat := 3153209731085022114183733

theorem tailTrace_6140854 : CollatzResearch.WordTrace tailWord_6140854 prefixEnd_6140854 3153209731085022114183733 := by
  unfold tailWord_6140854
  simp only [CollatzResearch.WordTrace]
  refine ⟨13998459105921387950694851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 149316897129828138140745077 13998459105921387950694851)
  ·
    refine ⟨20997688658882081926042277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13998459105921387950694851 20997688658882081926042277)
    ·
      refine ⟨3937066623540390361132927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20997688658882081926042277 3937066623540390361132927)
      ·
        refine ⟨5905599935310585541699391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3937066623540390361132927 5905599935310585541699391)
        ·
          refine ⟨8858399902965878312549087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5905599935310585541699391 8858399902965878312549087)
          ·
            refine ⟨13287599854448817468823631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8858399902965878312549087 13287599854448817468823631)
            ·
              refine ⟨19931399781673226203235447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13287599854448817468823631 19931399781673226203235447)
              ·
                refine ⟨29897099672509839304853171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19931399781673226203235447 29897099672509839304853171)
                ·
                  refine ⟨44845649508764758957279757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29897099672509839304853171 44845649508764758957279757)
                  ·
                    refine ⟨16817118565786784608979909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44845649508764758957279757 16817118565786784608979909)
                    ·
                      refine ⟨3153209731085022114183733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16817118565786784608979909 3153209731085022114183733)
                      ·
                        rfl

theorem cell23_6140854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_6140854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6140854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6140854 prefixEnd_6140854 := by exact prefixLift 6140854
  have htrace : WordTrace (prefixWord ++ tailWord_6140854) baseStart_6140854 baseEnd_6140854 := by
    simpa [prefixWord, tailWord_6140854, baseEnd_6140854] using wordTrace_append hprefix tailTrace_6140854
  have hstable : (prefixWord ++ tailWord_6140854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6140854).length < 2 ^ (prefixWord ++ tailWord_6140854).sum := by decide
  have hdescent : baseEnd_6140854 < baseStart_6140854 := by decide
  rcases family_descends (prefixWord ++ tailWord_6140854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6140964 : List Nat := [2, 3, 1, 4, 1, 3, 1, 2, 1, 2, 3]
def baseStart_6140964 : Nat := 118140960795 + 6140964 * 2 ^ 59
def prefixEnd_6140964 : Nat := 4983230072969 + 3 ^ 40 * 6140964 * 2
def baseEnd_6140964 : Nat := 3153266213957016683808227

theorem tailTrace_6140964 : CollatzResearch.WordTrace tailWord_6140964 prefixEnd_6140964 3153266213957016683808227 := by
  unfold tailWord_6140964
  simp only [CollatzResearch.WordTrace]
  refine ⟨111989678862171847998810973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149319571816229130665081297 111989678862171847998810973)
  ·
    refine ⟨41996129573314442999554115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111989678862171847998810973 41996129573314442999554115)
    ·
      refine ⟨62994194359971664499331173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41996129573314442999554115 62994194359971664499331173)
      ·
        refine ⟨11811411442494687093624595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 62994194359971664499331173 11811411442494687093624595)
        ·
          refine ⟨17717117163742030640436893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11811411442494687093624595 17717117163742030640436893)
          ·
            refine ⟨6643918936403261490163835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17717117163742030640436893 6643918936403261490163835)
            ·
              refine ⟨9965878404604892235245753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6643918936403261490163835 9965878404604892235245753)
              ·
                refine ⟨7474408803453669176434315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9965878404604892235245753 7474408803453669176434315)
                ·
                  refine ⟨11211613205180503764651473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7474408803453669176434315 11211613205180503764651473)
                  ·
                    refine ⟨8408709903885377823488605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11211613205180503764651473 8408709903885377823488605)
                    ·
                      refine ⟨3153266213957016683808227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8408709903885377823488605 3153266213957016683808227)
                      ·
                        rfl

theorem cell23_6140964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_6140964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6140964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6140964 prefixEnd_6140964 := by exact prefixLift 6140964
  have htrace : WordTrace (prefixWord ++ tailWord_6140964) baseStart_6140964 baseEnd_6140964 := by
    simpa [prefixWord, tailWord_6140964, baseEnd_6140964] using wordTrace_append hprefix tailTrace_6140964
  have hstable : (prefixWord ++ tailWord_6140964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6140964).length < 2 ^ (prefixWord ++ tailWord_6140964).sum := by decide
  have hdescent : baseEnd_6140964 < baseStart_6140964 := by decide
  rcases family_descends (prefixWord ++ tailWord_6140964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6141000 : List Nat := [2, 1, 3, 1, 1, 1, 3, 2, 3, 4, 2]
def baseStart_6141000 : Nat := 118140960795 + 6141000 * 2 ^ 59
def prefixEnd_6141000 : Nat := 4983230072969 + 3 ^ 40 * 6141000 * 2
def baseEnd_6141000 : Nat := 3153284699260578542958061

theorem tailTrace_6141000 : CollatzResearch.WordTrace tailWord_6141000 prefixEnd_6141000 3153284699260578542958061 := by
  unfold tailWord_6141000
  simp only [CollatzResearch.WordTrace]
  refine ⟨111990335376106637072966227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149320447168142182763954969 111990335376106637072966227)
  ·
    refine ⟨167985503064159955609449341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111990335376106637072966227 167985503064159955609449341)
    ·
      refine ⟨62994563649059983353543503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 167985503064159955609449341 62994563649059983353543503)
      ·
        refine ⟨94491845473589975030315255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62994563649059983353543503 94491845473589975030315255)
        ·
          refine ⟨141737768210384962545472883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94491845473589975030315255 141737768210384962545472883)
          ·
            refine ⟨212606652315577443818209325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141737768210384962545472883 212606652315577443818209325)
            ·
              refine ⟨79727494618341541431828497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 212606652315577443818209325 79727494618341541431828497)
              ·
                refine ⟨59795620963756156073871373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79727494618341541431828497 59795620963756156073871373)
                ·
                  refine ⟨22423357861408558527701765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59795620963756156073871373 22423357861408558527701765)
                  ·
                    refine ⟨4204379599014104723944081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22423357861408558527701765 4204379599014104723944081)
                    ·
                      refine ⟨3153284699260578542958061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4204379599014104723944081 3153284699260578542958061)
                      ·
                        rfl

theorem cell23_6141000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 2, 3, 4, 2].length) (baseStart_6141000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6141000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6141000 prefixEnd_6141000 := by exact prefixLift 6141000
  have htrace : WordTrace (prefixWord ++ tailWord_6141000) baseStart_6141000 baseEnd_6141000 := by
    simpa [prefixWord, tailWord_6141000, baseEnd_6141000] using wordTrace_append hprefix tailTrace_6141000
  have hstable : (prefixWord ++ tailWord_6141000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6141000).length < 2 ^ (prefixWord ++ tailWord_6141000).sum := by decide
  have hdescent : baseEnd_6141000 < baseStart_6141000 := by decide
  rcases family_descends (prefixWord ++ tailWord_6141000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6141010 : List Nat := [3, 2, 2, 1, 3, 2, 1, 1, 2, 6]
def baseStart_6141010 : Nat := 118140960795 + 6141010 * 2 ^ 59
def prefixEnd_6141010 : Nat := 4983230072969 + 3 ^ 40 * 6141010 * 2
def baseEnd_6141010 : Nat := 1051096611355707834611005

theorem tailTrace_6141010 : CollatzResearch.WordTrace tailWord_6141010 prefixEnd_6141010 1051096611355707834611005 := by
  unfold tailWord_6141010
  simp only [CollatzResearch.WordTrace]
  refine ⟨55995258870544261463449121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149320690321451363902530989 55995258870544261463449121)
  ·
    refine ⟨41996444152908196097586841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55995258870544261463449121 41996444152908196097586841)
    ·
      refine ⟨31497333114681147073190131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41996444152908196097586841 31497333114681147073190131)
      ·
        refine ⟨47245999672021720609785197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31497333114681147073190131 47245999672021720609785197)
        ·
          refine ⟨17717249877008145228669449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47245999672021720609785197 17717249877008145228669449)
          ·
            refine ⟨13287937407756108921502087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17717249877008145228669449 13287937407756108921502087)
            ·
              refine ⟨19931906111634163382253131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13287937407756108921502087 19931906111634163382253131)
              ·
                refine ⟨29897859167451245073379697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19931906111634163382253131 29897859167451245073379697)
                ·
                  refine ⟨22423394375588433805034773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29897859167451245073379697 22423394375588433805034773)
                  ·
                    refine ⟨1051096611355707834611005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22423394375588433805034773 1051096611355707834611005)
                    ·
                      rfl

theorem cell23_6141010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 1, 2, 6].length) (baseStart_6141010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6141010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6141010 prefixEnd_6141010 := by exact prefixLift 6141010
  have htrace : WordTrace (prefixWord ++ tailWord_6141010) baseStart_6141010 baseEnd_6141010 := by
    simpa [prefixWord, tailWord_6141010, baseEnd_6141010] using wordTrace_append hprefix tailTrace_6141010
  have hstable : (prefixWord ++ tailWord_6141010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6141010).length < 2 ^ (prefixWord ++ tailWord_6141010).sum := by decide
  have hdescent : baseEnd_6141010 < baseStart_6141010 := by decide
  rcases family_descends (prefixWord ++ tailWord_6141010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6141020 : List Nat := [2, 2, 4, 1, 1, 1, 1, 2, 2, 4, 3]
def baseStart_6141020 : Nat := 118140960795 + 6141020 * 2 ^ 59
def prefixEnd_6141020 : Nat := 4983230072969 + 3 ^ 40 * 6141020 * 2
def baseEnd_6141020 : Nat := 3153294968873668464707969

theorem tailTrace_6141020 : CollatzResearch.WordTrace tailWord_6141020 prefixEnd_6141020 3153294968873668464707969 := by
  unfold tailWord_6141020
  simp only [CollatzResearch.WordTrace]
  refine ⟨111990700106070408780830257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149320933474760545041107009 111990700106070408780830257)
  ·
    refine ⟨83993025079552806585622693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111990700106070408780830257 83993025079552806585622693)
    ·
      refine ⟨15748692202416151234804255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 83993025079552806585622693 15748692202416151234804255)
      ·
        refine ⟨23623038303624226852206383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15748692202416151234804255 23623038303624226852206383)
        ·
          refine ⟨35434557455436340278309575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23623038303624226852206383 35434557455436340278309575)
          ·
            refine ⟨53151836183154510417464363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35434557455436340278309575 53151836183154510417464363)
            ·
              refine ⟨79727754274731765626196545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53151836183154510417464363 79727754274731765626196545)
              ·
                refine ⟨59795815706048824219647409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79727754274731765626196545 59795815706048824219647409)
                ·
                  refine ⟨44846861779536618164735557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59795815706048824219647409 44846861779536618164735557)
                  ·
                    refine ⟨8408786583663115905887917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44846861779536618164735557 8408786583663115905887917)
                    ·
                      refine ⟨3153294968873668464707969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8408786583663115905887917 3153294968873668464707969)
                      ·
                        rfl

theorem cell23_6141020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 2, 2, 4, 3].length) (baseStart_6141020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6141020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6141020 prefixEnd_6141020 := by exact prefixLift 6141020
  have htrace : WordTrace (prefixWord ++ tailWord_6141020) baseStart_6141020 baseEnd_6141020 := by
    simpa [prefixWord, tailWord_6141020, baseEnd_6141020] using wordTrace_append hprefix tailTrace_6141020
  have hstable : (prefixWord ++ tailWord_6141020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6141020).length < 2 ^ (prefixWord ++ tailWord_6141020).sum := by decide
  have hdescent : baseEnd_6141020 < baseStart_6141020 := by decide
  rcases family_descends (prefixWord ++ tailWord_6141020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6141023 : List Nat := [1, 1, 2, 3, 1, 1, 5, 2, 7]
def baseStart_6141023 : Nat := 118140960795 + 6141023 * 2 ^ 59
def prefixEnd_6141023 : Nat := 4983230072969 + 3 ^ 40 * 6141023 * 2
def baseEnd_6141023 : Nat := 350366278812847994774495

theorem tailTrace_6141023 : CollatzResearch.WordTrace tailWord_6141023 prefixEnd_6141023 350366278812847994774495 := by
  unfold tailWord_6141023
  simp only [CollatzResearch.WordTrace]
  refine ⟨223981509631129949074019723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149321006420753299382679815 223981509631129949074019723)
  ·
    refine ⟨335972264446694923611029585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223981509631129949074019723 335972264446694923611029585)
    ·
      refine ⟨251979198335021192708272189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 335972264446694923611029585 251979198335021192708272189)
      ·
        refine ⟨94492199375632947265602071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 251979198335021192708272189 94492199375632947265602071)
        ·
          refine ⟨141738299063449420898403107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94492199375632947265602071 141738299063449420898403107)
          ·
            refine ⟨212607448595174131347604661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141738299063449420898403107 212607448595174131347604661)
            ·
              refine ⟨19931948305797574813837937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 212607448595174131347604661 19931948305797574813837937)
              ·
                refine ⟨14948961229348181110378453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19931948305797574813837937 14948961229348181110378453)
                ·
                  refine ⟨350366278812847994774495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14948961229348181110378453 350366278812847994774495)
                  ·
                    rfl

theorem cell23_6141023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 2, 7].length) (baseStart_6141023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6141023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6141023 prefixEnd_6141023 := by exact prefixLift 6141023
  have htrace : WordTrace (prefixWord ++ tailWord_6141023) baseStart_6141023 baseEnd_6141023 := by
    simpa [prefixWord, tailWord_6141023, baseEnd_6141023] using wordTrace_append hprefix tailTrace_6141023
  have hstable : (prefixWord ++ tailWord_6141023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6141023).length < 2 ^ (prefixWord ++ tailWord_6141023).sum := by decide
  have hdescent : baseEnd_6141023 < baseStart_6141023 := by decide
  rcases family_descends (prefixWord ++ tailWord_6141023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6141057 : List Nat := [1, 2, 4, 2, 2, 1, 2, 4, 5]
def baseStart_6141057 : Nat := 118140960795 + 6141057 * 2 ^ 59
def prefixEnd_6141057 : Nat := 4983230072969 + 3 ^ 40 * 6141057 * 2
def baseEnd_6141057 : Nat := 350368218628653868882811

theorem tailTrace_6141057 : CollatzResearch.WordTrace tailWord_6141057 prefixEnd_6141057 350368218628653868882811 := by
  unfold tailWord_6141057
  simp only [CollatzResearch.WordTrace]
  refine ⟨223982749713006772880757425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149321833142004515253838283 223982749713006772880757425)
  ·
    refine ⟨167987062284755079660568069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223982749713006772880757425 167987062284755079660568069)
    ·
      refine ⟨31497574178391577436356513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 167987062284755079660568069 31497574178391577436356513)
      ·
        refine ⟨23623180633793683077267385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31497574178391577436356513 23623180633793683077267385)
        ·
          refine ⟨17717385475345262307950539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23623180633793683077267385 17717385475345262307950539)
          ·
            refine ⟨26576078213017893461925809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17717385475345262307950539 26576078213017893461925809)
            ·
              refine ⟨19932058659763420096444357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26576078213017893461925809 19932058659763420096444357)
              ·
                refine ⟨3737260998705641268083317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19932058659763420096444357 3737260998705641268083317)
                ·
                  refine ⟨350368218628653868882811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3737260998705641268083317 350368218628653868882811)
                  ·
                    rfl

theorem cell23_6141057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 4, 5].length) (baseStart_6141057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6141057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6141057 prefixEnd_6141057 := by exact prefixLift 6141057
  have htrace : WordTrace (prefixWord ++ tailWord_6141057) baseStart_6141057 baseEnd_6141057 := by
    simpa [prefixWord, tailWord_6141057, baseEnd_6141057] using wordTrace_append hprefix tailTrace_6141057
  have hstable : (prefixWord ++ tailWord_6141057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6141057).length < 2 ^ (prefixWord ++ tailWord_6141057).sum := by decide
  have hdescent : baseEnd_6141057 < baseStart_6141057 := by decide
  rcases family_descends (prefixWord ++ tailWord_6141057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6141063 : List Nat := [1, 1, 4, 2, 1, 1, 1, 3, 1, 1, 7]
def baseStart_6141063 : Nat := 118140960795 + 6141063 * 2 ^ 59
def prefixEnd_6141063 : Nat := 4983230072969 + 3 ^ 40 * 6141063 * 2
def baseEnd_6141063 : Nat := 3153317048541811796470271

theorem tailTrace_6141063 : CollatzResearch.WordTrace tailWord_6141063 prefixEnd_6141063 3153317048541811796470271 := by
  unfold tailWord_6141063
  simp only [CollatzResearch.WordTrace]
  refine ⟨223982968550985035905475843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149321979033990023936983895 223982968550985035905475843)
  ·
    refine ⟨335974452826477553858213765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223982968550985035905475843 335974452826477553858213765)
    ·
      refine ⟨62995209904964541348415081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 335974452826477553858213765 62995209904964541348415081)
      ·
        refine ⟨47246407428723406011311311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62995209904964541348415081 47246407428723406011311311)
        ·
          refine ⟨70869611143085109016966967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47246407428723406011311311 70869611143085109016966967)
          ·
            refine ⟨106304416714627663525450451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70869611143085109016966967 106304416714627663525450451)
            ·
              refine ⟨159456625071941495288175677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106304416714627663525450451 159456625071941495288175677)
              ·
                refine ⟨59796234401978060733065879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 159456625071941495288175677 59796234401978060733065879)
                ·
                  refine ⟨89694351602967091099598819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59796234401978060733065879 89694351602967091099598819)
                  ·
                    refine ⟨134541527404450636649398229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 89694351602967091099598819 134541527404450636649398229)
                    ·
                      refine ⟨3153317048541811796470271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 134541527404450636649398229 3153317048541811796470271)
                      ·
                        rfl

theorem cell23_6141063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 3, 1, 1, 7].length) (baseStart_6141063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6141063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6141063 prefixEnd_6141063 := by exact prefixLift 6141063
  have htrace : WordTrace (prefixWord ++ tailWord_6141063) baseStart_6141063 baseEnd_6141063 := by
    simpa [prefixWord, tailWord_6141063, baseEnd_6141063] using wordTrace_append hprefix tailTrace_6141063
  have hstable : (prefixWord ++ tailWord_6141063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6141063).length < 2 ^ (prefixWord ++ tailWord_6141063).sum := by decide
  have hdescent : baseEnd_6141063 < baseStart_6141063 := by decide
  rcases family_descends (prefixWord ++ tailWord_6141063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6141070 : List Nat := [4, 1, 1, 3, 2, 1, 1, 2, 1, 7]
def baseStart_6141070 : Nat := 118140960795 + 6141070 * 2 ^ 59
def prefixEnd_6141070 : Nat := 4983230072969 + 3 ^ 40 * 6141070 * 2
def baseEnd_6141070 : Nat := 1051106880968797756360913

theorem tailTrace_6141070 : CollatzResearch.WordTrace tailWord_6141070 prefixEnd_6141070 1051106880968797756360913 := by
  unfold tailWord_6141070
  simp only [CollatzResearch.WordTrace]
  refine ⟨27997902982744959512622583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149322149241306450733987109 27997902982744959512622583)
  ·
    refine ⟨41996854474117439268933875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27997902982744959512622583 41996854474117439268933875)
    ·
      refine ⟨62995281711176158903400813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41996854474117439268933875 62995281711176158903400813)
      ·
        refine ⟨23623230641691059588775305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62995281711176158903400813 23623230641691059588775305)
        ·
          refine ⟨17717422981268294691581479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23623230641691059588775305 17717422981268294691581479)
          ·
            refine ⟨26576134471902442037372219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17717422981268294691581479 26576134471902442037372219)
            ·
              refine ⟨39864201707853663056058329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26576134471902442037372219 39864201707853663056058329)
              ·
                refine ⟨29898151280890247292043747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39864201707853663056058329 29898151280890247292043747)
                ·
                  refine ⟨44847226921335370938065621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29898151280890247292043747 44847226921335370938065621)
                  ·
                    refine ⟨1051106880968797756360913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44847226921335370938065621 1051106880968797756360913)
                    ·
                      rfl

theorem cell23_6141070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 2, 1, 7].length) (baseStart_6141070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6141070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6141070 prefixEnd_6141070 := by exact prefixLift 6141070
  have htrace : WordTrace (prefixWord ++ tailWord_6141070) baseStart_6141070 baseEnd_6141070 := by
    simpa [prefixWord, tailWord_6141070, baseEnd_6141070] using wordTrace_append hprefix tailTrace_6141070
  have hstable : (prefixWord ++ tailWord_6141070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6141070).length < 2 ^ (prefixWord ++ tailWord_6141070).sum := by decide
  have hdescent : baseEnd_6141070 < baseStart_6141070 := by decide
  rcases family_descends (prefixWord ++ tailWord_6141070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6141103 : List Nat := [1, 1, 2, 1, 2, 3, 2, 1, 1, 3, 6]
def baseStart_6141103 : Nat := 118140960795 + 6141103 * 2 ^ 59
def prefixEnd_6141103 : Nat := 4983230072969 + 3 ^ 40 * 6141103 * 2
def baseEnd_6141103 : Nat := 3153337587767991639970087

theorem tailTrace_6141103 : CollatzResearch.WordTrace tailWord_6141103 prefixEnd_6141103 3153337587767991639970087 := by
  unfold tailWord_6141103
  simp only [CollatzResearch.WordTrace]
  refine ⟨223984427470840122736931963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149322951647226748491287975 223984427470840122736931963)
  ·
    refine ⟨335976641206260184105397945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223984427470840122736931963 335976641206260184105397945)
    ·
      refine ⟨251982480904695138079048459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 335976641206260184105397945 251982480904695138079048459)
      ·
        refine ⟨377973721357042707118572689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251982480904695138079048459 377973721357042707118572689)
        ·
          refine ⟨283480291017782030338929517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 377973721357042707118572689 283480291017782030338929517)
          ·
            refine ⟨106305109131668261377098569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 283480291017782030338929517 106305109131668261377098569)
            ·
              refine ⟨79728831848751196032823927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106305109131668261377098569 79728831848751196032823927)
              ·
                refine ⟨119593247773126794049235891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79728831848751196032823927 119593247773126794049235891)
                ·
                  refine ⟨179389871659690191073853837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 119593247773126794049235891 179389871659690191073853837)
                  ·
                    refine ⟨67271201872383821652695189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 179389871659690191073853837 67271201872383821652695189)
                    ·
                      refine ⟨3153337587767991639970087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67271201872383821652695189 3153337587767991639970087)
                      ·
                        rfl

theorem cell23_6141103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 3, 6].length) (baseStart_6141103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6141103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6141103 prefixEnd_6141103 := by exact prefixLift 6141103
  have htrace : WordTrace (prefixWord ++ tailWord_6141103) baseStart_6141103 baseEnd_6141103 := by
    simpa [prefixWord, tailWord_6141103, baseEnd_6141103] using wordTrace_append hprefix tailTrace_6141103
  have hstable : (prefixWord ++ tailWord_6141103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6141103).length < 2 ^ (prefixWord ++ tailWord_6141103).sum := by decide
  have hdescent : baseEnd_6141103 < baseStart_6141103 := by decide
  rcases family_descends (prefixWord ++ tailWord_6141103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6141117 : List Nat := [1, 4, 1, 2, 1, 1, 5, 1, 3, 4]
def baseStart_6141117 : Nat := 118140960795 + 6141117 * 2 ^ 59
def prefixEnd_6141117 : Nat := 4983230072969 + 3 ^ 40 * 6141117 * 2
def baseEnd_6141117 : Nat := 1051114925499051528398341

theorem tailTrace_6141117 : CollatzResearch.WordTrace tailWord_6141117 prefixEnd_6141117 1051114925499051528398341 := by
  unfold tailWord_6141117
  simp only [CollatzResearch.WordTrace]
  refine ⟨223984938092789403127941605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149323292061859602085294403 223984938092789403127941605)
  ·
    refine ⟨41997175892398013086489051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 223984938092789403127941605 41997175892398013086489051)
    ·
      refine ⟨62995763838597019629733577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41997175892398013086489051 62995763838597019629733577)
      ·
        refine ⟨47246822878947764722300183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62995763838597019629733577 47246822878947764722300183)
        ·
          refine ⟨70870234318421647083450275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47246822878947764722300183 70870234318421647083450275)
          ·
            refine ⟨106305351477632470625175413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70870234318421647083450275 106305351477632470625175413)
            ·
              refine ⟨9966126701028044121110195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 106305351477632470625175413 9966126701028044121110195)
              ·
                refine ⟨14949190051542066181665293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9966126701028044121110195 14949190051542066181665293)
                ·
                  refine ⟨5605946269328274818124485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14949190051542066181665293 5605946269328274818124485)
                  ·
                    refine ⟨1051114925499051528398341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5605946269328274818124485 1051114925499051528398341)
                    ·
                      rfl

theorem cell23_6141117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 5, 1, 3, 4].length) (baseStart_6141117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6141117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6141117 prefixEnd_6141117 := by exact prefixLift 6141117
  have htrace : WordTrace (prefixWord ++ tailWord_6141117) baseStart_6141117 baseEnd_6141117 := by
    simpa [prefixWord, tailWord_6141117, baseEnd_6141117] using wordTrace_append hprefix tailTrace_6141117
  have hstable : (prefixWord ++ tailWord_6141117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6141117).length < 2 ^ (prefixWord ++ tailWord_6141117).sum := by decide
  have hdescent : baseEnd_6141117 < baseStart_6141117 := by decide
  rcases family_descends (prefixWord ++ tailWord_6141117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6141144 : List Nat := [2, 1, 2, 2, 5, 1, 2, 1, 2, 2, 3]
def baseStart_6141144 : Nat := 118140960795 + 6141144 * 2 ^ 59
def prefixEnd_6141144 : Nat := 4983230072969 + 3 ^ 40 * 6141144 * 2
def baseEnd_6141144 : Nat := 3153358640474825979557399

theorem tailTrace_6141144 : CollatzResearch.WordTrace tailWord_6141144 prefixEnd_6141144 3153358640474825979557399 := by
  unfold tailWord_6141144
  simp only [CollatzResearch.WordTrace]
  refine ⟨111992961431845793369587243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149323948575794391159449657 111992961431845793369587243)
  ·
    refine ⟨167989442147768690054380865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111992961431845793369587243 167989442147768690054380865)
    ·
      refine ⟨125992081610826517540785649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 167989442147768690054380865 125992081610826517540785649)
      ·
        refine ⟨94494061208119888155589237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 125992081610826517540785649 94494061208119888155589237)
        ·
          refine ⟨8858818238261239514586491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 94494061208119888155589237 8858818238261239514586491)
          ·
            refine ⟨13288227357391859271879737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8858818238261239514586491 13288227357391859271879737)
            ·
              refine ⟨9966170518043894453909803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13288227357391859271879737 9966170518043894453909803)
              ·
                refine ⟨14949255777065841680864705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9966170518043894453909803 14949255777065841680864705)
                ·
                  refine ⟨11211941832799381260648529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14949255777065841680864705 11211941832799381260648529)
                  ·
                    refine ⟨8408956374599535945486397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11211941832799381260648529 8408956374599535945486397)
                    ·
                      refine ⟨3153358640474825979557399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8408956374599535945486397 3153358640474825979557399)
                      ·
                        rfl

theorem cell23_6141144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 2, 1, 2, 2, 3].length) (baseStart_6141144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6141144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6141144 prefixEnd_6141144 := by exact prefixLift 6141144
  have htrace : WordTrace (prefixWord ++ tailWord_6141144) baseStart_6141144 baseEnd_6141144 := by
    simpa [prefixWord, tailWord_6141144, baseEnd_6141144] using wordTrace_append hprefix tailTrace_6141144
  have hstable : (prefixWord ++ tailWord_6141144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6141144).length < 2 ^ (prefixWord ++ tailWord_6141144).sum := by decide
  have hdescent : baseEnd_6141144 < baseStart_6141144 := by decide
  rcases family_descends (prefixWord ++ tailWord_6141144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6141174 : List Nat := [5, 1, 1, 1, 1, 1, 1, 5, 3, 1, 3]
def baseStart_6141174 : Nat := 118140960795 + 6141174 * 2 ^ 59
def prefixEnd_6141174 : Nat := 4983230072969 + 3 ^ 40 * 6141174 * 2
def baseEnd_6141174 : Nat := 3153374044894460862182261

theorem tailTrace_6141174 : CollatzResearch.WordTrace tailWord_6141174 prefixEnd_6141174 3153374044894460862182261 := by
  unfold tailWord_6141174
  simp only [CollatzResearch.WordTrace]
  refine ⟨13999188565848931366422911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 149324678035721934575177717 13999188565848931366422911)
  ·
    refine ⟨20998782848773397049634367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13999188565848931366422911 20998782848773397049634367)
    ·
      refine ⟨31498174273160095574451551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20998782848773397049634367 31498174273160095574451551)
      ·
        refine ⟨47247261409740143361677327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31498174273160095574451551 47247261409740143361677327)
        ·
          refine ⟨70870892114610215042515991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47247261409740143361677327 70870892114610215042515991)
          ·
            refine ⟨106306338171915322563773987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70870892114610215042515991 106306338171915322563773987)
            ·
              refine ⟨159459507257872983845660981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106306338171915322563773987 159459507257872983845660981)
              ·
                refine ⟨14949328805425592235530717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 159459507257872983845660981 14949328805425592235530717)
                ·
                  refine ⟨5605998302034597088324019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14949328805425592235530717 5605998302034597088324019)
                  ·
                    refine ⟨8408997453051895632486029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5605998302034597088324019 8408997453051895632486029)
                    ·
                      refine ⟨3153374044894460862182261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8408997453051895632486029 3153374044894460862182261)
                      ·
                        rfl

theorem cell23_6141174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 5, 3, 1, 3].length) (baseStart_6141174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6141174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6141174 prefixEnd_6141174 := by exact prefixLift 6141174
  have htrace : WordTrace (prefixWord ++ tailWord_6141174) baseStart_6141174 baseEnd_6141174 := by
    simpa [prefixWord, tailWord_6141174, baseEnd_6141174] using wordTrace_append hprefix tailTrace_6141174
  have hstable : (prefixWord ++ tailWord_6141174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6141174).length < 2 ^ (prefixWord ++ tailWord_6141174).sum := by decide
  have hdescent : baseEnd_6141174 < baseStart_6141174 := by decide
  rcases family_descends (prefixWord ++ tailWord_6141174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6141207 : List Nat := [1, 1, 3, 4, 1, 1, 2, 2, 4, 4]
def baseStart_6141207 : Nat := 118140960795 + 6141207 * 2 ^ 59
def prefixEnd_6141207 : Nat := 4983230072969 + 3 ^ 40 * 6141207 * 2
def baseEnd_6141207 : Nat := 1051130329918686411023203

theorem tailTrace_6141207 : CollatzResearch.WordTrace tailWord_6141207 prefixEnd_6141207 1051130329918686411023203 := by
  unfold tailWord_6141207
  simp only [CollatzResearch.WordTrace]
  refine ⟨223988220662463348498717875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149325480441642232332478583 223988220662463348498717875)
  ·
    refine ⟨335982330993695022748076813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223988220662463348498717875 335982330993695022748076813)
    ·
      refine ⟨125993374122635633530528805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 335982330993695022748076813 125993374122635633530528805)
      ·
        refine ⟨23623757647994181286974151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 125993374122635633530528805 23623757647994181286974151)
        ·
          refine ⟨35435636471991271930461227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23623757647994181286974151 35435636471991271930461227)
          ·
            refine ⟨53153454707986907895691841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35435636471991271930461227 53153454707986907895691841)
            ·
              refine ⟨39865091030990180921768881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53153454707986907895691841 39865091030990180921768881)
              ·
                refine ⟨29898818273242635691326661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39865091030990180921768881 29898818273242635691326661)
                ·
                  refine ⟨5606028426232994192123749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29898818273242635691326661 5606028426232994192123749)
                  ·
                    refine ⟨1051130329918686411023203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5606028426232994192123749 1051130329918686411023203)
                    ·
                      rfl

theorem cell23_6141207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 2, 4, 4].length) (baseStart_6141207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6141207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6141207 prefixEnd_6141207 := by exact prefixLift 6141207
  have htrace : WordTrace (prefixWord ++ tailWord_6141207) baseStart_6141207 baseEnd_6141207 := by
    simpa [prefixWord, tailWord_6141207, baseEnd_6141207] using wordTrace_append hprefix tailTrace_6141207
  have hstable : (prefixWord ++ tailWord_6141207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6141207).length < 2 ^ (prefixWord ++ tailWord_6141207).sum := by decide
  have hdescent : baseEnd_6141207 < baseStart_6141207 := by decide
  rcases family_descends (prefixWord ++ tailWord_6141207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6141220 : List Nat := [2, 3, 1, 3, 1, 1, 12]
def baseStart_6141220 : Nat := 118140960795 + 6141220 * 2 ^ 59
def prefixEnd_6141220 : Nat := 4983230072969 + 3 ^ 40 * 6141220 * 2
def baseEnd_6141220 : Nat := 38930835370426761508729

theorem tailTrace_6141220 : CollatzResearch.WordTrace tailWord_6141220 prefixEnd_6141220 38930835370426761508729 := by
  unfold tailWord_6141220
  simp only [CollatzResearch.WordTrace]
  refine ⟨111994347405708125859470557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149325796540944167812627409 111994347405708125859470557)
  ·
    refine ⟨41997880277140547197301459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 111994347405708125859470557 41997880277140547197301459)
    ·
      refine ⟨62996820415710820795952189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41997880277140547197301459 62996820415710820795952189)
      ·
        refine ⟨23623807655891557798482071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62996820415710820795952189 23623807655891557798482071)
        ·
          refine ⟨35435711483837336697723107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23623807655891557798482071 35435711483837336697723107)
          ·
            refine ⟨53153567225756005046584661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35435711483837336697723107 53153567225756005046584661)
            ·
              refine ⟨38930835370426761508729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 53153567225756005046584661 38930835370426761508729)
              ·
                rfl

theorem cell23_6141220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 12].length) (baseStart_6141220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6141220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6141220 prefixEnd_6141220 := by exact prefixLift 6141220
  have htrace : WordTrace (prefixWord ++ tailWord_6141220) baseStart_6141220 baseEnd_6141220 := by
    simpa [prefixWord, tailWord_6141220, baseEnd_6141220] using wordTrace_append hprefix tailTrace_6141220
  have hstable : (prefixWord ++ tailWord_6141220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6141220).length < 2 ^ (prefixWord ++ tailWord_6141220).sum := by decide
  have hdescent : baseEnd_6141220 < baseStart_6141220 := by decide
  rcases family_descends (prefixWord ++ tailWord_6141220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6141224 : List Nat := [2, 1, 5, 1, 2, 2, 1, 1, 4, 4]
def baseStart_6141224 : Nat := 118140960795 + 6141224 * 2 ^ 59
def prefixEnd_6141224 : Nat := 4983230072969 + 3 ^ 40 * 6141224 * 2
def baseEnd_6141224 : Nat := 1051133239642395222185677

theorem tailTrace_6141224 : CollatzResearch.WordTrace tailWord_6141224 prefixEnd_6141224 1051133239642395222185677 := by
  unfold tailWord_6141224
  simp only [CollatzResearch.WordTrace]
  refine ⟨111994420351700880201043363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149325893802267840268057817 111994420351700880201043363)
  ·
    refine ⟨167991630527551320301565045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111994420351700880201043363 167991630527551320301565045)
    ·
      refine ⟨15749215361957936278271723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 167991630527551320301565045 15749215361957936278271723)
      ·
        refine ⟨23623823042936904417407585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15749215361957936278271723 23623823042936904417407585)
        ·
          refine ⟨17717867282202678313055689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23623823042936904417407585 17717867282202678313055689)
          ·
            refine ⟨13288400461652008734791767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17717867282202678313055689 13288400461652008734791767)
            ·
              refine ⟨19932600692478013102187651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13288400461652008734791767 19932600692478013102187651)
              ·
                refine ⟨29898901038717019653281477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19932600692478013102187651 29898901038717019653281477)
                ·
                  refine ⟨5606043944759441184990277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29898901038717019653281477 5606043944759441184990277)
                  ·
                    refine ⟨1051133239642395222185677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5606043944759441184990277 1051133239642395222185677)
                    ·
                      rfl

theorem cell23_6141224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 1, 4, 4].length) (baseStart_6141224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6141224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6141224 prefixEnd_6141224 := by exact prefixLift 6141224
  have htrace : WordTrace (prefixWord ++ tailWord_6141224) baseStart_6141224 baseEnd_6141224 := by
    simpa [prefixWord, tailWord_6141224, baseEnd_6141224] using wordTrace_append hprefix tailTrace_6141224
  have hstable : (prefixWord ++ tailWord_6141224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6141224).length < 2 ^ (prefixWord ++ tailWord_6141224).sum := by decide
  have hdescent : baseEnd_6141224 < baseStart_6141224 := by decide
  rcases family_descends (prefixWord ++ tailWord_6141224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6141241 : List Nat := [1, 2, 1, 6, 3, 1, 1, 1, 1, 6]
def baseStart_6141241 : Nat := 118140960795 + 6141241 * 2 ^ 59
def prefixEnd_6141241 : Nat := 4983230072969 + 3 ^ 40 * 6141241 * 2
def baseEnd_6141241 : Nat := 1051136149366104033348151

theorem tailTrace_6141241 : CollatzResearch.WordTrace tailWord_6141241 prefixEnd_6141241 1051136149366104033348151 := by
  unfold tailWord_6141241
  simp only [CollatzResearch.WordTrace]
  refine ⟨223989460744340172305455577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149326307162893448203637051 223989460744340172305455577)
  ·
    refine ⟨167992095558255129229091683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223989460744340172305455577 167992095558255129229091683)
    ·
      refine ⟨251988143337382693843637525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167992095558255129229091683 251988143337382693843637525)
      ·
        refine ⟨11811944218939813773920509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 251988143337382693843637525 11811944218939813773920509)
        ·
          refine ⟨4429479082102430165220191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11811944218939813773920509 4429479082102430165220191)
          ·
            refine ⟨6644218623153645247830287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4429479082102430165220191 6644218623153645247830287)
            ·
              refine ⟨9966327934730467871745431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6644218623153645247830287 9966327934730467871745431)
              ·
                refine ⟨14949491902095701807618147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9966327934730467871745431 14949491902095701807618147)
                ·
                  refine ⟨22424237853143552711427221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14949491902095701807618147 22424237853143552711427221)
                  ·
                    refine ⟨1051136149366104033348151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22424237853143552711427221 1051136149366104033348151)
                    ·
                      rfl

theorem cell23_6141241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 1, 1, 1, 6].length) (baseStart_6141241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6141241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6141241 prefixEnd_6141241 := by exact prefixLift 6141241
  have htrace : WordTrace (prefixWord ++ tailWord_6141241) baseStart_6141241 baseEnd_6141241 := by
    simpa [prefixWord, tailWord_6141241, baseEnd_6141241] using wordTrace_append hprefix tailTrace_6141241
  have hstable : (prefixWord ++ tailWord_6141241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6141241).length < 2 ^ (prefixWord ++ tailWord_6141241).sum := by decide
  have hdescent : baseEnd_6141241 < baseStart_6141241 := by decide
  rcases family_descends (prefixWord ++ tailWord_6141241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6141244 : List Nat := [2, 2, 2, 2, 1, 5, 1, 1, 1, 2, 4]
def baseStart_6141244 : Nat := 118140960795 + 6141244 * 2 ^ 59
def prefixEnd_6141244 : Nat := 4983230072969 + 3 ^ 40 * 6141244 * 2
def baseEnd_6141244 : Nat := 3153409988540275588306939

theorem tailTrace_6141244 : CollatzResearch.WordTrace tailWord_6141244 prefixEnd_6141244 3153409988540275588306939 := by
  unfold tailWord_6141244
  simp only [CollatzResearch.WordTrace]
  refine ⟨111994785081664651908907393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149326380108886202545209857 111994785081664651908907393)
  ·
    refine ⟨83996088811248488931680545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 111994785081664651908907393 83996088811248488931680545)
    ·
      refine ⟨62997066608436366698760409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83996088811248488931680545 62997066608436366698760409)
      ·
        refine ⟨47247799956327275024070307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62997066608436366698760409 47247799956327275024070307)
        ·
          refine ⟨70871699934490912536105461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47247799956327275024070307 70871699934490912536105461)
          ·
            refine ⟨6644221868858523050259887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 70871699934490912536105461 6644221868858523050259887)
            ·
              refine ⟨9966332803287784575389831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6644221868858523050259887 9966332803287784575389831)
              ·
                refine ⟨14949499204931676863084747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9966332803287784575389831 14949499204931676863084747)
                ·
                  refine ⟨22424248807397515294627121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14949499204931676863084747 22424248807397515294627121)
                  ·
                    refine ⟨16818186605548136470970341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22424248807397515294627121 16818186605548136470970341)
                    ·
                      refine ⟨3153409988540275588306939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16818186605548136470970341 3153409988540275588306939)
                      ·
                        rfl

theorem cell23_6141244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 1, 1, 1, 2, 4].length) (baseStart_6141244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6141244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6141244 prefixEnd_6141244 := by exact prefixLift 6141244
  have htrace : WordTrace (prefixWord ++ tailWord_6141244) baseStart_6141244 baseEnd_6141244 := by
    simpa [prefixWord, tailWord_6141244, baseEnd_6141244] using wordTrace_append hprefix tailTrace_6141244
  have hstable : (prefixWord ++ tailWord_6141244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6141244).length < 2 ^ (prefixWord ++ tailWord_6141244).sum := by decide
  have hdescent : baseEnd_6141244 < baseStart_6141244 := by decide
  rcases family_descends (prefixWord ++ tailWord_6141244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6141321 : List Nat := [1, 2, 1, 1, 7, 1, 1, 2, 1, 4, 2]
def baseStart_6141321 : Nat := 118140960795 + 6141321 * 2 ^ 59
def prefixEnd_6141321 : Nat := 4983230072969 + 3 ^ 40 * 6141321 * 2
def baseEnd_6141321 : Nat := 3153449526550671787044085

theorem tailTrace_6141321 : CollatzResearch.WordTrace tailWord_6141321 prefixEnd_6141321 3153449526550671787044085 := by
  unfold tailWord_6141321
  simp only [CollatzResearch.WordTrace]
  refine ⟨223992378584050345968367817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149328252389366897312245211 223992378584050345968367817)
  ·
    refine ⟨167994283938037759476275863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 223992378584050345968367817 167994283938037759476275863)
    ·
      refine ⟨251991425907056639214413795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167994283938037759476275863 251991425907056639214413795)
      ·
        refine ⟨377987138860584958821620693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251991425907056639214413795 377987138860584958821620693)
        ·
          refine ⟨8859073567044959972381735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 377987138860584958821620693 8859073567044959972381735)
          ·
            refine ⟨13288610350567439958572603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8859073567044959972381735 13288610350567439958572603)
            ·
              refine ⟨19932915525851159937858905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13288610350567439958572603 19932915525851159937858905)
              ·
                refine ⟨14949686644388369953394179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19932915525851159937858905 14949686644388369953394179)
                ·
                  refine ⟨22424529966582554930091269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14949686644388369953394179 22424529966582554930091269)
                  ·
                    refine ⟨4204599368734229049392113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22424529966582554930091269 4204599368734229049392113)
                    ·
                      refine ⟨3153449526550671787044085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4204599368734229049392113 3153449526550671787044085)
                      ·
                        rfl

theorem cell23_6141321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 2, 1, 4, 2].length) (baseStart_6141321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6141321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6141321 prefixEnd_6141321 := by exact prefixLift 6141321
  have htrace : WordTrace (prefixWord ++ tailWord_6141321) baseStart_6141321 baseEnd_6141321 := by
    simpa [prefixWord, tailWord_6141321, baseEnd_6141321] using wordTrace_append hprefix tailTrace_6141321
  have hstable : (prefixWord ++ tailWord_6141321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6141321).length < 2 ^ (prefixWord ++ tailWord_6141321).sum := by decide
  have hdescent : baseEnd_6141321 < baseStart_6141321 := by decide
  rcases family_descends (prefixWord ++ tailWord_6141321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6141338 : List Nat := [3, 1, 1, 4, 1, 1, 4, 2, 2, 2, 2]
def baseStart_6141338 : Nat := 118140960795 + 6141338 * 2 ^ 59
def prefixEnd_6141338 : Nat := 4983230072969 + 3 ^ 40 * 6141338 * 2
def baseEnd_6141338 : Nat := 3153458255721798220531507

theorem tailTrace_6141338 : CollatzResearch.WordTrace tailWord_6141338 prefixEnd_6141338 3153458255721798220531507 := by
  unfold tailWord_6141338
  simp only [CollatzResearch.WordTrace]
  refine ⟨55998249656247189467934167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149328665749992505247824445 55998249656247189467934167)
  ·
    refine ⟨83997374484370784201901251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55998249656247189467934167 83997374484370784201901251)
    ·
      refine ⟨125996061726556176302851877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 83997374484370784201901251 125996061726556176302851877)
      ·
        refine ⟨23624261573729283056784727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 125996061726556176302851877 23624261573729283056784727)
        ·
          refine ⟨35436392360593924585177091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23624261573729283056784727 35436392360593924585177091)
          ·
            refine ⟨53154588540890886877765637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35436392360593924585177091 53154588540890886877765637)
            ·
              refine ⟨9966485351417041289581057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53154588540890886877765637 9966485351417041289581057)
              ·
                refine ⟨7474864013562780967185793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9966485351417041289581057 7474864013562780967185793)
                ·
                  refine ⟨5606148010172085725389345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7474864013562780967185793 5606148010172085725389345)
                  ·
                    refine ⟨4204611007629064294042009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5606148010172085725389345 4204611007629064294042009)
                    ·
                      refine ⟨3153458255721798220531507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4204611007629064294042009 3153458255721798220531507)
                      ·
                        rfl

theorem cell23_6141338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 4, 2, 2, 2, 2].length) (baseStart_6141338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6141338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6141338 prefixEnd_6141338 := by exact prefixLift 6141338
  have htrace : WordTrace (prefixWord ++ tailWord_6141338) baseStart_6141338 baseEnd_6141338 := by
    simpa [prefixWord, tailWord_6141338, baseEnd_6141338] using wordTrace_append hprefix tailTrace_6141338
  have hstable : (prefixWord ++ tailWord_6141338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6141338).length < 2 ^ (prefixWord ++ tailWord_6141338).sum := by decide
  have hdescent : baseEnd_6141338 < baseStart_6141338 := by decide
  rcases family_descends (prefixWord ++ tailWord_6141338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6141344 : List Nat := [2, 1, 1, 4, 1, 2, 3, 4, 5]
def baseStart_6141344 : Nat := 118140960795 + 6141344 * 2 ^ 59
def prefixEnd_6141344 : Nat := 4983230072969 + 3 ^ 40 * 6141344 * 2
def baseEnd_6141344 : Nat := 350384592956191688561831

theorem tailTrace_6141344 : CollatzResearch.WordTrace tailWord_6141344 prefixEnd_6141344 350384592956191688561831 := by
  unfold tailWord_6141344
  simp only [CollatzResearch.WordTrace]
  refine ⟨111996608731483510448227543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149328811641978013930970057 111996608731483510448227543)
  ·
    refine ⟨167994913097225265672341315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 111996608731483510448227543 167994913097225265672341315)
    ·
      refine ⟨251992369645837898508511973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 167994913097225265672341315 251992369645837898508511973)
      ·
        refine ⟨47248569308594605970345995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 251992369645837898508511973 47248569308594605970345995)
        ·
          refine ⟨70872853962891908955518993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47248569308594605970345995 70872853962891908955518993)
          ·
            refine ⟨53154640472168931716639245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70872853962891908955518993 53154640472168931716639245)
            ·
              refine ⟨19932990177063349393739717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53154640472168931716639245 19932990177063349393739717)
              ·
                refine ⟨3737435658199378011326197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19932990177063349393739717 3737435658199378011326197)
                ·
                  refine ⟨350384592956191688561831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3737435658199378011326197 350384592956191688561831)
                  ·
                    rfl

theorem cell23_6141344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 4, 5].length) (baseStart_6141344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6141344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6141344 prefixEnd_6141344 := by exact prefixLift 6141344
  have htrace : WordTrace (prefixWord ++ tailWord_6141344) baseStart_6141344 baseEnd_6141344 := by
    simpa [prefixWord, tailWord_6141344, baseEnd_6141344] using wordTrace_append hprefix tailTrace_6141344
  have hstable : (prefixWord ++ tailWord_6141344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6141344).length < 2 ^ (prefixWord ++ tailWord_6141344).sum := by decide
  have hdescent : baseEnd_6141344 < baseStart_6141344 := by decide
  rcases family_descends (prefixWord ++ tailWord_6141344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6141407 : List Nat := [1, 1, 2, 3, 3, 1, 1, 2, 2, 1, 6]
def baseStart_6141407 : Nat := 118140960795 + 6141407 * 2 ^ 59
def prefixEnd_6141407 : Nat := 4983230072969 + 3 ^ 40 * 6141407 * 2
def baseEnd_6141407 : Nat := 3153493685886958450568689

theorem tailTrace_6141407 : CollatzResearch.WordTrace tailWord_6141407 prefixEnd_6141407 3153493685886958450568689 := by
  unfold tailWord_6141407
  simp only [CollatzResearch.WordTrace]
  refine ⟨223995515261738782655998475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149330343507825855103998983 223995515261738782655998475)
  ·
    refine ⟨335993272892608173983997713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223995515261738782655998475 335993272892608173983997713)
    ·
      refine ⟨251994954669456130487998285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 335993272892608173983997713 251994954669456130487998285)
      ·
        refine ⟨94498108001046048932999357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 251994954669456130487998285 94498108001046048932999357)
        ·
          refine ⟨35436790500392268349874759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94498108001046048932999357 35436790500392268349874759)
          ·
            refine ⟨53155185750588402524812139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35436790500392268349874759 53155185750588402524812139)
            ·
              refine ⟨79732778625882603787218209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53155185750588402524812139 79732778625882603787218209)
              ·
                refine ⟨59799583969411952840413657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79732778625882603787218209 59799583969411952840413657)
                ·
                  refine ⟨44849687977058964630310243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59799583969411952840413657 44849687977058964630310243)
                  ·
                    refine ⟨67274531965588446945465365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44849687977058964630310243 67274531965588446945465365)
                    ·
                      refine ⟨3153493685886958450568689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67274531965588446945465365 3153493685886958450568689)
                      ·
                        rfl

theorem cell23_6141407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 2, 2, 1, 6].length) (baseStart_6141407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6141407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6141407 prefixEnd_6141407 := by exact prefixLift 6141407
  have htrace : WordTrace (prefixWord ++ tailWord_6141407) baseStart_6141407 baseEnd_6141407 := by
    simpa [prefixWord, tailWord_6141407, baseEnd_6141407] using wordTrace_append hprefix tailTrace_6141407
  have hstable : (prefixWord ++ tailWord_6141407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6141407).length < 2 ^ (prefixWord ++ tailWord_6141407).sum := by decide
  have hdescent : baseEnd_6141407 < baseStart_6141407 := by decide
  rcases family_descends (prefixWord ++ tailWord_6141407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6141411 : List Nat := [1, 1, 1, 6, 2, 1, 2, 1, 2, 4, 2]
def baseStart_6141411 : Nat := 118140960795 + 6141411 * 2 ^ 59
def prefixEnd_6141411 : Nat := 4983230072969 + 3 ^ 40 * 6141411 * 2
def baseEnd_6141411 : Nat := 3153495739809576434918671

theorem tailTrace_6141411 : CollatzResearch.WordTrace tailWord_6141411 prefixEnd_6141411 3153495739809576434918671 := by
  unfold tailWord_6141411
  simp only [CollatzResearch.WordTrace]
  refine ⟨223995661153724291339144087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149330440769149527559429391 223995661153724291339144087)
  ·
    refine ⟨335993491730586437008716131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223995661153724291339144087 335993491730586437008716131)
    ·
      refine ⟨503990237595879655513074197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 335993491730586437008716131 503990237595879655513074197)
      ·
        refine ⟨23624542387306858852175353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 503990237595879655513074197 23624542387306858852175353)
        ·
          refine ⟨17718406790480144139131515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23624542387306858852175353 17718406790480144139131515)
          ·
            refine ⟨26577610185720216208697273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17718406790480144139131515 26577610185720216208697273)
            ·
              refine ⟨19933207639290162156522955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26577610185720216208697273 19933207639290162156522955)
              ·
                refine ⟨29899811458935243234784433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19933207639290162156522955 29899811458935243234784433)
                ·
                  refine ⟨22424858594201432426088325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29899811458935243234784433 22424858594201432426088325)
                  ·
                    refine ⟨4204660986412768579891561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22424858594201432426088325 4204660986412768579891561)
                    ·
                      refine ⟨3153495739809576434918671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4204660986412768579891561 3153495739809576434918671)
                      ·
                        rfl

theorem cell23_6141411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 1, 2, 4, 2].length) (baseStart_6141411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6141411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6141411 prefixEnd_6141411 := by exact prefixLift 6141411
  have htrace : WordTrace (prefixWord ++ tailWord_6141411) baseStart_6141411 baseEnd_6141411 := by
    simpa [prefixWord, tailWord_6141411, baseEnd_6141411] using wordTrace_append hprefix tailTrace_6141411
  have hstable : (prefixWord ++ tailWord_6141411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6141411).length < 2 ^ (prefixWord ++ tailWord_6141411).sum := by decide
  have hdescent : baseEnd_6141411 < baseStart_6141411 := by decide
  rcases family_descends (prefixWord ++ tailWord_6141411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6141487 : List Nat := [1, 1, 2, 1, 2, 1, 1, 1, 1, 7, 5]
def baseStart_6141487 : Nat := 118140960795 + 6141487 * 2 ^ 59
def prefixEnd_6141487 : Nat := 4983230072969 + 3 ^ 40 * 6141487 * 2
def baseEnd_6141487 : Nat := 3153534764339318137568321

theorem tailTrace_6141487 : CollatzResearch.WordTrace tailWord_6141487 prefixEnd_6141487 3153534764339318137568321 := by
  unfold tailWord_6141487
  simp only [CollatzResearch.WordTrace]
  refine ⟨223998433101448956318910715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149332288734299304212607143 223998433101448956318910715)
  ·
    refine ⟨335997649652173434478366073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 223998433101448956318910715 335997649652173434478366073)
    ·
      refine ⟨251998237239130075858774555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 335997649652173434478366073 251998237239130075858774555)
      ·
        refine ⟨377997355858695113788161833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251998237239130075858774555 377997355858695113788161833)
        ·
          refine ⟨283498016894021335341121375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 377997355858695113788161833 283498016894021335341121375)
          ·
            refine ⟨425247025341032003011682063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 283498016894021335341121375 425247025341032003011682063)
            ·
              refine ⟨637870538011548004517523095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 425247025341032003011682063 637870538011548004517523095)
              ·
                refine ⟨956805807017322006776284643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 637870538011548004517523095 956805807017322006776284643)
                ·
                  refine ⟨1435208710525983010164426965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 956805807017322006776284643 1435208710525983010164426965)
                  ·
                    refine ⟨33637704152952726800728757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1435208710525983010164426965 33637704152952726800728757)
                    ·
                      refine ⟨3153534764339318137568321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33637704152952726800728757 3153534764339318137568321)
                      ·
                        rfl

theorem cell23_6141487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 7, 5].length) (baseStart_6141487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6141487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6141487 prefixEnd_6141487 := by exact prefixLift 6141487
  have htrace : WordTrace (prefixWord ++ tailWord_6141487) baseStart_6141487 baseEnd_6141487 := by
    simpa [prefixWord, tailWord_6141487, baseEnd_6141487] using wordTrace_append hprefix tailTrace_6141487
  have hstable : (prefixWord ++ tailWord_6141487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6141487).length < 2 ^ (prefixWord ++ tailWord_6141487).sum := by decide
  have hdescent : baseEnd_6141487 < baseStart_6141487 := by decide
  rcases family_descends (prefixWord ++ tailWord_6141487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6141514 : List Nat := [3, 1, 2, 1, 1, 3, 1, 2, 3, 2, 4]
def baseStart_6141514 : Nat := 118140960795 + 6141514 * 2 ^ 59
def prefixEnd_6141514 : Nat := 4983230072969 + 3 ^ 40 * 6141514 * 2
def baseEnd_6141514 : Nat := 3153548628316989531930697

theorem tailTrace_6141514 : CollatzResearch.WordTrace tailWord_6141514 prefixEnd_6141514 3153548628316989531930697 := by
  unfold tailWord_6141514
  simp only [CollatzResearch.WordTrace]
  refine ⟨55999854468087784982535899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149332945248234093286762397 55999854468087784982535899)
  ·
    refine ⟨83999781702131677473803849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55999854468087784982535899 83999781702131677473803849)
    ·
      refine ⟨62999836276598758105352887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 83999781702131677473803849 62999836276598758105352887)
      ·
        refine ⟨94499754414898137158029331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62999836276598758105352887 94499754414898137158029331)
        ·
          refine ⟨141749631622347205737043997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94499754414898137158029331 141749631622347205737043997)
          ·
            refine ⟨53156111858380202151391499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 141749631622347205737043997 53156111858380202151391499)
            ·
              refine ⟨79734167787570303227087249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53156111858380202151391499 79734167787570303227087249)
              ·
                refine ⟨59800625840677727420315437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79734167787570303227087249 59800625840677727420315437)
                ·
                  refine ⟨22425234690254147782618289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59800625840677727420315437 22425234690254147782618289)
                  ·
                    refine ⟨16818926017690610836963717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22425234690254147782618289 16818926017690610836963717)
                    ·
                      refine ⟨3153548628316989531930697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16818926017690610836963717 3153548628316989531930697)
                      ·
                        rfl

theorem cell23_6141514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 2, 3, 2, 4].length) (baseStart_6141514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6141514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6141514 prefixEnd_6141514 := by exact prefixLift 6141514
  have htrace : WordTrace (prefixWord ++ tailWord_6141514) baseStart_6141514 baseEnd_6141514 := by
    simpa [prefixWord, tailWord_6141514, baseEnd_6141514] using wordTrace_append hprefix tailTrace_6141514
  have hstable : (prefixWord ++ tailWord_6141514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6141514).length < 2 ^ (prefixWord ++ tailWord_6141514).sum := by decide
  have hdescent : baseEnd_6141514 < baseStart_6141514 := by decide
  rcases family_descends (prefixWord ++ tailWord_6141514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6141518 : List Nat := [4, 1, 1, 1, 1, 2, 1, 5, 3, 2, 2]
def baseStart_6141518 : Nat := 118140960795 + 6141518 * 2 ^ 59
def prefixEnd_6141518 : Nat := 4983230072969 + 3 ^ 40 * 6141518 * 2
def baseEnd_6141518 : Nat := 3153550682239607516280679

theorem tailTrace_6141518 : CollatzResearch.WordTrace tailWord_6141518 prefixEnd_6141518 3153550682239607516280679 := by
  unfold tailWord_6141518
  simp only [CollatzResearch.WordTrace]
  refine ⟨27999945470542081076661151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149333042509557765742192805 27999945470542081076661151)
  ·
    refine ⟨41999918205813121614991727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27999945470542081076661151 41999918205813121614991727)
    ·
      refine ⟨62999877308719682422487591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41999918205813121614991727 62999877308719682422487591)
      ·
        refine ⟨94499815963079523633731387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62999877308719682422487591 94499815963079523633731387)
        ·
          refine ⟨141749723944619285450597081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94499815963079523633731387 141749723944619285450597081)
          ·
            refine ⟨106312292958464464087947811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141749723944619285450597081 106312292958464464087947811)
            ·
              refine ⟨159468439437696696131921717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106312292958464464087947811 159468439437696696131921717)
              ·
                refine ⟨14950166197284065262367661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 159468439437696696131921717 14950166197284065262367661)
                ·
                  refine ⟨5606312323981524473387873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14950166197284065262367661 5606312323981524473387873)
                  ·
                    refine ⟨4204734242986143355040905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5606312323981524473387873 4204734242986143355040905)
                    ·
                      refine ⟨3153550682239607516280679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4204734242986143355040905 3153550682239607516280679)
                      ·
                        rfl

theorem cell23_6141518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 5, 3, 2, 2].length) (baseStart_6141518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6141518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6141518 prefixEnd_6141518 := by exact prefixLift 6141518
  have htrace : WordTrace (prefixWord ++ tailWord_6141518) baseStart_6141518 baseEnd_6141518 := by
    simpa [prefixWord, tailWord_6141518, baseEnd_6141518] using wordTrace_append hprefix tailTrace_6141518
  have hstable : (prefixWord ++ tailWord_6141518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6141518).length < 2 ^ (prefixWord ++ tailWord_6141518).sum := by decide
  have hdescent : baseEnd_6141518 < baseStart_6141518 := by decide
  rcases family_descends (prefixWord ++ tailWord_6141518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6141541 : List Nat := [1, 3, 1, 3, 3, 2, 3, 7]
def baseStart_6141541 : Nat := 118140960795 + 6141541 * 2 ^ 59
def prefixEnd_6141541 : Nat := 4983230072969 + 3 ^ 40 * 6141541 * 2
def baseEnd_6141541 : Nat := 116798610825728182455299

theorem tailTrace_6141541 : CollatzResearch.WordTrace tailWord_6141541 prefixEnd_6141541 116798610825728182455299 := by
  unfold tailWord_6141541
  simp only [CollatzResearch.WordTrace]
  refine ⟨224000402643253323541376477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149333601762168882360917651 224000402643253323541376477)
  ·
    refine ⟨84000150991219996328016179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 224000402643253323541376477 84000150991219996328016179)
    ·
      refine ⟨126000226486829994492024269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84000150991219996328016179 126000226486829994492024269)
      ·
        refine ⟨47250084932561247934509101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126000226486829994492024269 47250084932561247934509101)
        ·
          refine ⟨17718781849710467975440913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47250084932561247934509101 17718781849710467975440913)
          ·
            refine ⟨13289086387282850981580685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17718781849710467975440913 13289086387282850981580685)
            ·
              refine ⟨4983407395231069118092757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13289086387282850981580685 4983407395231069118092757)
              ·
                refine ⟨116798610825728182455299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4983407395231069118092757 116798610825728182455299)
                ·
                  rfl

theorem cell23_6141541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 3, 7].length) (baseStart_6141541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6141541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6141541 prefixEnd_6141541 := by exact prefixLift 6141541
  have htrace : WordTrace (prefixWord ++ tailWord_6141541) baseStart_6141541 baseEnd_6141541 := by
    simpa [prefixWord, tailWord_6141541, baseEnd_6141541] using wordTrace_append hprefix tailTrace_6141541
  have hstable : (prefixWord ++ tailWord_6141541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6141541).length < 2 ^ (prefixWord ++ tailWord_6141541).sum := by decide
  have hdescent : baseEnd_6141541 < baseStart_6141541 := by decide
  rcases family_descends (prefixWord ++ tailWord_6141541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6141551 : List Nat := [1, 1, 2, 1, 3, 2, 1, 4, 4, 1, 3]
def baseStart_6141551 : Nat := 118140960795 + 6141551 * 2 ^ 59
def prefixEnd_6141551 : Nat := 4983230072969 + 3 ^ 40 * 6141551 * 2
def baseEnd_6141551 : Nat := 3153567627101205887168027

theorem tailTrace_6141551 : CollatzResearch.WordTrace tailWord_6141551 prefixEnd_6141551 3153567627101205887168027 := by
  unfold tailWord_6141551
  simp only [CollatzResearch.WordTrace]
  refine ⟨224000767373217095249240507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149333844915478063499493671 224000767373217095249240507)
  ·
    refine ⟨336001151059825642873860761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224000767373217095249240507 336001151059825642873860761)
    ·
      refine ⟨252000863294869232155395571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 336001151059825642873860761 252000863294869232155395571)
      ·
        refine ⟨378001294942303848233093357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252000863294869232155395571 378001294942303848233093357)
        ·
          refine ⟨141750485603363943087410009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 378001294942303848233093357 141750485603363943087410009)
          ·
            refine ⟨106312864202522957315557507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141750485603363943087410009 106312864202522957315557507)
            ·
              refine ⟨159469296303784435973336261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106312864202522957315557507 159469296303784435973336261)
              ·
                refine ⟨29900493056959581745000549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 159469296303784435973336261 29900493056959581745000549)
                ·
                  refine ⟨5606342448179921577187603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29900493056959581745000549 5606342448179921577187603)
                  ·
                    refine ⟨8409513672269882365781405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5606342448179921577187603 8409513672269882365781405)
                    ·
                      refine ⟨3153567627101205887168027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8409513672269882365781405 3153567627101205887168027)
                      ·
                        rfl

theorem cell23_6141551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 4, 4, 1, 3].length) (baseStart_6141551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6141551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6141551 prefixEnd_6141551 := by exact prefixLift 6141551
  have htrace : WordTrace (prefixWord ++ tailWord_6141551) baseStart_6141551 baseEnd_6141551 := by
    simpa [prefixWord, tailWord_6141551, baseEnd_6141551] using wordTrace_append hprefix tailTrace_6141551
  have hstable : (prefixWord ++ tailWord_6141551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6141551).length < 2 ^ (prefixWord ++ tailWord_6141551).sum := by decide
  have hdescent : baseEnd_6141551 < baseStart_6141551 := by decide
  rcases family_descends (prefixWord ++ tailWord_6141551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6141552 : List Nat := [2, 1, 1, 1, 6, 2, 2, 3, 1, 2, 2]
def baseStart_6141552 : Nat := 118140960795 + 6141552 * 2 ^ 59
def prefixEnd_6141552 : Nat := 4983230072969 + 3 ^ 40 * 6141552 * 2
def baseEnd_6141552 : Nat := 3153568140581860383255523

theorem tailTrace_6141552 : CollatzResearch.WordTrace tailWord_6141552 prefixEnd_6141552 3153568140581860383255523 := by
  unfold tailWord_6141552
  simp only [CollatzResearch.WordTrace]
  refine ⟨112000401923106736210013455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149333869230808981613351273 112000401923106736210013455)
  ·
    refine ⟨168000602884660104315020183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112000401923106736210013455 168000602884660104315020183)
    ·
      refine ⟨252000904326990156472530275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168000602884660104315020183 252000904326990156472530275)
      ·
        refine ⟨378001356490485234708795413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252000904326990156472530275 378001356490485234708795413)
        ·
          refine ⟨17718813585491495376974785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 378001356490485234708795413 17718813585491495376974785)
          ·
            refine ⟨13289110189118621532731089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17718813585491495376974785 13289110189118621532731089)
            ·
              refine ⟨9966832641838966149548317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13289110189118621532731089 9966832641838966149548317)
              ·
                refine ⟨3737562240689612306080619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9966832641838966149548317 3737562240689612306080619)
                ·
                  refine ⟨5606343361034418459120929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3737562240689612306080619 5606343361034418459120929)
                  ·
                    refine ⟨4204757520775813844340697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5606343361034418459120929 4204757520775813844340697)
                    ·
                      refine ⟨3153568140581860383255523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4204757520775813844340697 3153568140581860383255523)
                      ·
                        rfl

theorem cell23_6141552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 2, 3, 1, 2, 2].length) (baseStart_6141552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6141552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6141552 prefixEnd_6141552 := by exact prefixLift 6141552
  have htrace : WordTrace (prefixWord ++ tailWord_6141552) baseStart_6141552 baseEnd_6141552 := by
    simpa [prefixWord, tailWord_6141552, baseEnd_6141552] using wordTrace_append hprefix tailTrace_6141552
  have hstable : (prefixWord ++ tailWord_6141552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6141552).length < 2 ^ (prefixWord ++ tailWord_6141552).sum := by decide
  have hdescent : baseEnd_6141552 < baseStart_6141552 := by decide
  rcases family_descends (prefixWord ++ tailWord_6141552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6141642 : List Nat := [3, 1, 2, 1, 5, 1, 1, 3, 2, 2, 2]
def baseStart_6141642 : Nat := 118140960795 + 6141642 * 2 ^ 59
def prefixEnd_6141642 : Nat := 4983230072969 + 3 ^ 40 * 6141642 * 2
def baseEnd_6141642 : Nat := 3153614353840765031130109

theorem tailTrace_6141642 : CollatzResearch.WordTrace tailWord_6141642 prefixEnd_6141642 3153614353840765031130109 := by
  unfold tailWord_6141642
  simp only [CollatzResearch.WordTrace]
  refine ⟨56001021603971854447700795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149336057610591611860535453 56001021603971854447700795)
  ·
    refine ⟨84001532405957781671551193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56001021603971854447700795 84001532405957781671551193)
    ·
      refine ⟨63001149304468336253663395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84001532405957781671551193 63001149304468336253663395)
      ·
        refine ⟨94501723956702504380495093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63001149304468336253663395 94501723956702504380495093)
        ·
          refine ⟨8859536620940859785671415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 94501723956702504380495093 8859536620940859785671415)
          ·
            refine ⟨13289304931411289678507123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8859536620940859785671415 13289304931411289678507123)
            ·
              refine ⟨19933957397116934517760685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13289304931411289678507123 19933957397116934517760685)
              ·
                refine ⟨7475234023918850444160257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19933957397116934517760685 7475234023918850444160257)
                ·
                  refine ⟨5606425517939137833120193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7475234023918850444160257 5606425517939137833120193)
                  ·
                    refine ⟨4204819138454353374840145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5606425517939137833120193 4204819138454353374840145)
                    ·
                      refine ⟨3153614353840765031130109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4204819138454353374840145 3153614353840765031130109)
                      ·
                        rfl

theorem cell23_6141642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 3, 2, 2, 2].length) (baseStart_6141642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6141642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6141642 prefixEnd_6141642 := by exact prefixLift 6141642
  have htrace : WordTrace (prefixWord ++ tailWord_6141642) baseStart_6141642 baseEnd_6141642 := by
    simpa [prefixWord, tailWord_6141642, baseEnd_6141642] using wordTrace_append hprefix tailTrace_6141642
  have hstable : (prefixWord ++ tailWord_6141642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6141642).length < 2 ^ (prefixWord ++ tailWord_6141642).sum := by decide
  have hdescent : baseEnd_6141642 < baseStart_6141642 := by decide
  rcases family_descends (prefixWord ++ tailWord_6141642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6141698 : List Nat := [3, 4, 1, 1, 1, 1, 2, 2, 1, 3, 4]
def baseStart_6141698 : Nat := 118140960795 + 6141698 * 2 ^ 59
def prefixEnd_6141698 : Nat := 4983230072969 + 3 ^ 40 * 6141698 * 2
def baseEnd_6141698 : Nat := 3153643108757416812029851

theorem tailTrace_6141698 : CollatzResearch.WordTrace tailWord_6141698 prefixEnd_6141698 3153643108757416812029851 := by
  unfold tailWord_6141698
  simp only [CollatzResearch.WordTrace]
  refine ⟨56001532225921134838710437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149337419269123026236561165 56001532225921134838710437)
  ·
    refine ⟨10500287292360212782258207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56001532225921134838710437 10500287292360212782258207)
    ·
      refine ⟨15750430938540319173387311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10500287292360212782258207 15750430938540319173387311)
      ·
        refine ⟨23625646407810478760080967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15750430938540319173387311 23625646407810478760080967)
        ·
          refine ⟨35438469611715718140121451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23625646407810478760080967 35438469611715718140121451)
          ·
            refine ⟨53157704417573577210182177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35438469611715718140121451 53157704417573577210182177)
            ·
              refine ⟨39868278313180182907636633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53157704417573577210182177 39868278313180182907636633)
              ·
                refine ⟨29901208734885137180727475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39868278313180182907636633 29901208734885137180727475)
                ·
                  refine ⟨44851813102327705771091213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29901208734885137180727475 44851813102327705771091213)
                  ·
                    refine ⟨16819429913372889664159205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44851813102327705771091213 16819429913372889664159205)
                    ·
                      refine ⟨3153643108757416812029851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16819429913372889664159205 3153643108757416812029851)
                      ·
                        rfl

theorem cell23_6141698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_6141698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6141698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6141698 prefixEnd_6141698 := by exact prefixLift 6141698
  have htrace : WordTrace (prefixWord ++ tailWord_6141698) baseStart_6141698 baseEnd_6141698 := by
    simpa [prefixWord, tailWord_6141698, baseEnd_6141698] using wordTrace_append hprefix tailTrace_6141698
  have hstable : (prefixWord ++ tailWord_6141698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6141698).length < 2 ^ (prefixWord ++ tailWord_6141698).sum := by decide
  have hdescent : baseEnd_6141698 < baseStart_6141698 := by decide
  rcases family_descends (prefixWord ++ tailWord_6141698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6141742 : List Nat := [4, 1, 3, 2, 2, 1, 2, 1, 3, 4]
def baseStart_6141742 : Nat := 118140960795 + 6141742 * 2 ^ 59
def prefixEnd_6141742 : Nat := 4983230072969 + 3 ^ 40 * 6141742 * 2
def baseEnd_6141742 : Nat := 1051221900635404879959883

theorem tailTrace_6141742 : CollatzResearch.WordTrace tailWord_6141742 prefixEnd_6141742 1051221900635404879959883 := by
  unfold tailWord_6141742
  simp only [CollatzResearch.WordTrace]
  refine ⟨28000966714440641858680435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149338489143683423246295653 28000966714440641858680435)
  ·
    refine ⟨42001450071660962788020653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28000966714440641858680435 42001450071660962788020653)
    ·
      refine ⟨15750543776872861045507745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42001450071660962788020653 15750543776872861045507745)
      ·
        refine ⟨11812907832654645784130809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15750543776872861045507745 11812907832654645784130809)
        ·
          refine ⟨8859680874490984338098107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11812907832654645784130809 8859680874490984338098107)
          ·
            refine ⟨13289521311736476507147161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8859680874490984338098107 13289521311736476507147161)
            ·
              refine ⟨9967140983802357380360371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13289521311736476507147161 9967140983802357380360371)
              ·
                refine ⟨14950711475703536070540557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9967140983802357380360371 14950711475703536070540557)
                ·
                  refine ⟨5606516803388826026452709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14950711475703536070540557 5606516803388826026452709)
                  ·
                    refine ⟨1051221900635404879959883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5606516803388826026452709 1051221900635404879959883)
                    ·
                      rfl

theorem cell23_6141742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 2, 1, 3, 4].length) (baseStart_6141742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6141742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6141742 prefixEnd_6141742 := by exact prefixLift 6141742
  have htrace : WordTrace (prefixWord ++ tailWord_6141742) baseStart_6141742 baseEnd_6141742 := by
    simpa [prefixWord, tailWord_6141742, baseEnd_6141742] using wordTrace_append hprefix tailTrace_6141742
  have hstable : (prefixWord ++ tailWord_6141742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6141742).length < 2 ^ (prefixWord ++ tailWord_6141742).sum := by decide
  have hdescent : baseEnd_6141742 < baseStart_6141742 := by decide
  rcases family_descends (prefixWord ++ tailWord_6141742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6141751 : List Nat := [1, 1, 3, 1, 2, 1, 2, 4, 3, 5]
def baseStart_6141751 : Nat := 118140960795 + 6141751 * 2 ^ 59
def prefixEnd_6141751 : Nat := 4983230072969 + 3 ^ 40 * 6141751 * 2
def baseEnd_6141751 : Nat := 1051223441077368368222369

theorem tailTrace_6141751 : CollatzResearch.WordTrace tailWord_6141751 prefixEnd_6141751 1051223441077368368222369 := by
  unfold tailWord_6141751
  simp only [CollatzResearch.WordTrace]
  refine ⟨224008061972492529406521107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149338707981661686271014071 224008061972492529406521107)
  ·
    refine ⟨336012092958738794109781661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224008061972492529406521107 336012092958738794109781661)
    ·
      refine ⟨126004534859527047791168123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 336012092958738794109781661 126004534859527047791168123)
      ·
        refine ⟨189006802289290571686752185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126004534859527047791168123 189006802289290571686752185)
        ·
          refine ⟨141755101716967928765064139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189006802289290571686752185 141755101716967928765064139)
          ·
            refine ⟨212632652575451893147596209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141755101716967928765064139 212632652575451893147596209)
            ·
              refine ⟨159474489431588919860697157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 212632652575451893147596209 159474489431588919860697157)
              ·
                refine ⟨29901466768422922473880717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 159474489431588919860697157 29901466768422922473880717)
                ·
                  refine ⟨11213050038158595927705269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29901466768422922473880717 11213050038158595927705269)
                  ·
                    refine ⟨1051223441077368368222369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11213050038158595927705269 1051223441077368368222369)
                    ·
                      rfl

theorem cell23_6141751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 4, 3, 5].length) (baseStart_6141751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6141751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6141751 prefixEnd_6141751 := by exact prefixLift 6141751
  have htrace : WordTrace (prefixWord ++ tailWord_6141751) baseStart_6141751 baseEnd_6141751 := by
    simpa [prefixWord, tailWord_6141751, baseEnd_6141751] using wordTrace_append hprefix tailTrace_6141751
  have hstable : (prefixWord ++ tailWord_6141751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6141751).length < 2 ^ (prefixWord ++ tailWord_6141751).sum := by decide
  have hdescent : baseEnd_6141751 < baseStart_6141751 := by decide
  rcases family_descends (prefixWord ++ tailWord_6141751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6141768 : List Nat := [2, 1, 3, 1, 1, 4, 1, 4, 1, 5]
def baseStart_6141768 : Nat := 118140960795 + 6141768 * 2 ^ 59
def prefixEnd_6141768 : Nat := 4983230072969 + 3 ^ 40 * 6141768 * 2
def baseEnd_6141768 : Nat := 1051226350801077179384843

theorem tailTrace_6141768 : CollatzResearch.WordTrace tailWord_6141768 prefixEnd_6141768 1051226350801077179384843 := by
  unfold tailWord_6141768
  simp only [CollatzResearch.WordTrace]
  refine ⟨112004341006715470654944979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149339121342287294206593305 112004341006715470654944979)
  ·
    refine ⟨168006511510073205982417469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112004341006715470654944979 168006511510073205982417469)
    ·
      refine ⟨63002441816277452243406551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168006511510073205982417469 63002441816277452243406551)
      ·
        refine ⟨94503662724416178365109827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63002441816277452243406551 94503662724416178365109827)
        ·
          refine ⟨141755494086624267547664741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94503662724416178365109827 141755494086624267547664741)
          ·
            refine ⟨26579155141242050165187139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 141755494086624267547664741 26579155141242050165187139)
            ·
              refine ⟨39868732711863075247780709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26579155141242050165187139 39868732711863075247780709)
              ·
                refine ⟨7475387383474326608958883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39868732711863075247780709 7475387383474326608958883)
                ·
                  refine ⟨11213081075211489913438325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7475387383474326608958883 11213081075211489913438325)
                  ·
                    refine ⟨1051226350801077179384843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11213081075211489913438325 1051226350801077179384843)
                    ·
                      rfl

theorem cell23_6141768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 4, 1, 5].length) (baseStart_6141768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6141768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6141768 prefixEnd_6141768 := by exact prefixLift 6141768
  have htrace : WordTrace (prefixWord ++ tailWord_6141768) baseStart_6141768 baseEnd_6141768 := by
    simpa [prefixWord, tailWord_6141768, baseEnd_6141768] using wordTrace_append hprefix tailTrace_6141768
  have hstable : (prefixWord ++ tailWord_6141768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6141768).length < 2 ^ (prefixWord ++ tailWord_6141768).sum := by decide
  have hdescent : baseEnd_6141768 < baseStart_6141768 := by decide
  rcases family_descends (prefixWord ++ tailWord_6141768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6141799 : List Nat := [1, 1, 5, 1, 2, 1, 5, 2, 1, 1, 3]
def baseStart_6141799 : Nat := 118140960795 + 6141799 * 2 ^ 59
def prefixEnd_6141799 : Nat := 4983230072969 + 3 ^ 40 * 6141799 * 2
def baseEnd_6141799 : Nat := 3153694970303520916866887

theorem tailTrace_6141799 : CollatzResearch.WordTrace tailWord_6141799 prefixEnd_6141799 3153694970303520916866887 := by
  unfold tailWord_6141799
  simp only [CollatzResearch.WordTrace]
  refine ⟨224009812676318633604268451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149339875117545755736178967 224009812676318633604268451)
  ·
    refine ⟨336014719014477950406402677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224009812676318633604268451 336014719014477950406402677)
    ·
      refine ⟨31501379907607307850600251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 336014719014477950406402677 31501379907607307850600251)
      ·
        refine ⟨47252069861410961775900377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31501379907607307850600251 47252069861410961775900377)
        ·
          refine ⟨35439052396058221331925283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47252069861410961775900377 35439052396058221331925283)
          ·
            refine ⟨53158578594087331997887925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35439052396058221331925283 53158578594087331997887925)
            ·
              refine ⟨4983616743195687374801993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 53158578594087331997887925 4983616743195687374801993)
              ·
                refine ⟨3737712557396765531101495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4983616743195687374801993 3737712557396765531101495)
                ·
                  refine ⟨5606568836095148296652243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3737712557396765531101495 5606568836095148296652243)
                  ·
                    refine ⟨8409853254142722444978365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5606568836095148296652243 8409853254142722444978365)
                    ·
                      refine ⟨3153694970303520916866887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8409853254142722444978365 3153694970303520916866887)
                      ·
                        rfl

theorem cell23_6141799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 5, 2, 1, 1, 3].length) (baseStart_6141799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6141799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6141799 prefixEnd_6141799 := by exact prefixLift 6141799
  have htrace : WordTrace (prefixWord ++ tailWord_6141799) baseStart_6141799 baseEnd_6141799 := by
    simpa [prefixWord, tailWord_6141799, baseEnd_6141799] using wordTrace_append hprefix tailTrace_6141799
  have hstable : (prefixWord ++ tailWord_6141799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6141799).length < 2 ^ (prefixWord ++ tailWord_6141799).sum := by decide
  have hdescent : baseEnd_6141799 < baseStart_6141799 := by decide
  rcases family_descends (prefixWord ++ tailWord_6141799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6141808 : List Nat := [2, 1, 1, 1, 4, 1, 1, 4, 3, 2, 3]
def baseStart_6141808 : Nat := 118140960795 + 6141808 * 2 ^ 59
def prefixEnd_6141808 : Nat := 4983230072969 + 3 ^ 40 * 6141808 * 2
def baseEnd_6141808 : Nat := 3153699591629411381654345

theorem tailTrace_6141808 : CollatzResearch.WordTrace tailWord_6141808 prefixEnd_6141808 3153699591629411381654345 := by
  unfold tailWord_6141808
  simp only [CollatzResearch.WordTrace]
  refine ⟨112005070466643014070673039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149340093955524018760897385 112005070466643014070673039)
  ·
    refine ⟨168007605699964521106009559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112005070466643014070673039 168007605699964521106009559)
    ·
      refine ⟨252011408549946781659014339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168007605699964521106009559 252011408549946781659014339)
      ·
        refine ⟨378017112824920172488521509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252011408549946781659014339 378017112824920172488521509)
        ·
          refine ⟨70878208654672532341597783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 378017112824920172488521509 70878208654672532341597783)
          ·
            refine ⟨106317312982008798512396675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70878208654672532341597783 106317312982008798512396675)
            ·
              refine ⟨159475969473013197768595013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106317312982008798512396675 159475969473013197768595013)
              ·
                refine ⟨29901744276189974581611565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 159475969473013197768595013 29901744276189974581611565)
                ·
                  refine ⟨11213154103571240468104337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29901744276189974581611565 11213154103571240468104337)
                  ·
                    refine ⟨8409865577678430351078253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11213154103571240468104337 8409865577678430351078253)
                    ·
                      refine ⟨3153699591629411381654345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8409865577678430351078253 3153699591629411381654345)
                      ·
                        rfl

theorem cell23_6141808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 4, 3, 2, 3].length) (baseStart_6141808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6141808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6141808 prefixEnd_6141808 := by exact prefixLift 6141808
  have htrace : WordTrace (prefixWord ++ tailWord_6141808) baseStart_6141808 baseEnd_6141808 := by
    simpa [prefixWord, tailWord_6141808, baseEnd_6141808] using wordTrace_append hprefix tailTrace_6141808
  have hstable : (prefixWord ++ tailWord_6141808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6141808).length < 2 ^ (prefixWord ++ tailWord_6141808).sum := by decide
  have hdescent : baseEnd_6141808 < baseStart_6141808 := by decide
  rcases family_descends (prefixWord ++ tailWord_6141808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6141822 : List Nat := [4, 2, 3, 1, 1, 2, 1, 1, 3, 1, 4]
def baseStart_6141822 : Nat := 118140960795 + 6141822 * 2 ^ 59
def prefixEnd_6141822 : Nat := 4983230072969 + 3 ^ 40 * 6141822 * 2
def baseEnd_6141822 : Nat := 3153706780358574326879281

theorem tailTrace_6141822 : CollatzResearch.WordTrace tailWord_6141822 prefixEnd_6141822 3153706780358574326879281 := by
  unfold tailWord_6141822
  simp only [CollatzResearch.WordTrace]
  refine ⟨28001331444404413566544465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149340434370156872354903813 28001331444404413566544465)
  ·
    refine ⟨21000998583303310174908349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28001331444404413566544465 21000998583303310174908349)
    ·
      refine ⟨7875374468738741315590631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21000998583303310174908349 7875374468738741315590631)
      ·
        refine ⟨11813061703108111973385947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7875374468738741315590631 11813061703108111973385947)
        ·
          refine ⟨17719592554662167960078921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11813061703108111973385947 17719592554662167960078921)
          ·
            refine ⟨13289694415996625970059191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17719592554662167960078921 13289694415996625970059191)
            ·
              refine ⟨19934541623994938955088787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13289694415996625970059191 19934541623994938955088787)
              ·
                refine ⟨29901812435992408432633181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19934541623994938955088787 29901812435992408432633181)
                ·
                  refine ⟨11213179663497153162237443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29901812435992408432633181 11213179663497153162237443)
                  ·
                    refine ⟨16819769495245729743356165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11213179663497153162237443 16819769495245729743356165)
                    ·
                      refine ⟨3153706780358574326879281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16819769495245729743356165 3153706780358574326879281)
                      ·
                        rfl

theorem cell23_6141822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_6141822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6141822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6141822 prefixEnd_6141822 := by exact prefixLift 6141822
  have htrace : WordTrace (prefixWord ++ tailWord_6141822) baseStart_6141822 baseEnd_6141822 := by
    simpa [prefixWord, tailWord_6141822, baseEnd_6141822] using wordTrace_append hprefix tailTrace_6141822
  have hstable : (prefixWord ++ tailWord_6141822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6141822).length < 2 ^ (prefixWord ++ tailWord_6141822).sum := by decide
  have hdescent : baseEnd_6141822 < baseStart_6141822 := by decide
  rcases family_descends (prefixWord ++ tailWord_6141822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6141842 : List Nat := [3, 2, 3, 2, 1, 3, 1, 1, 1, 1, 5]
def baseStart_6141842 : Nat := 118140960795 + 6141842 * 2 ^ 59
def prefixEnd_6141842 : Nat := 4983230072969 + 3 ^ 40 * 6141842 * 2
def baseEnd_6141842 : Nat := 3153717049971664248629189

theorem tailTrace_6141842 : CollatzResearch.WordTrace tailWord_6141842 prefixEnd_6141842 3153717049971664248629189 := by
  unfold tailWord_6141842
  simp only [CollatzResearch.WordTrace]
  refine ⟨56002845253790712987020945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149340920676775234632055853 56002845253790712987020945)
  ·
    refine ⟨42002133940343034740265709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56002845253790712987020945 42002133940343034740265709)
    ·
      refine ⟨15750800227628638027599641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42002133940343034740265709 15750800227628638027599641)
      ·
        refine ⟨11813100170721478520699731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15750800227628638027599641 11813100170721478520699731)
        ·
          refine ⟨17719650256082217781049597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11813100170721478520699731 17719650256082217781049597)
          ·
            refine ⟨6644868846030831667893599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17719650256082217781049597 6644868846030831667893599)
            ·
              refine ⟨9967303269046247501840399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6644868846030831667893599 9967303269046247501840399)
              ·
                refine ⟨14950954903569371252760599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9967303269046247501840399 14950954903569371252760599)
                ·
                  refine ⟨22426432355354056879140899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14950954903569371252760599 22426432355354056879140899)
                  ·
                    refine ⟨33639648533031085318711349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22426432355354056879140899 33639648533031085318711349)
                    ·
                      refine ⟨3153717049971664248629189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33639648533031085318711349 3153717049971664248629189)
                      ·
                        rfl

theorem cell23_6141842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_6141842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6141842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6141842 prefixEnd_6141842 := by exact prefixLift 6141842
  have htrace : WordTrace (prefixWord ++ tailWord_6141842) baseStart_6141842 baseEnd_6141842 := by
    simpa [prefixWord, tailWord_6141842, baseEnd_6141842] using wordTrace_append hprefix tailTrace_6141842
  have hstable : (prefixWord ++ tailWord_6141842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6141842).length < 2 ^ (prefixWord ++ tailWord_6141842).sum := by decide
  have hdescent : baseEnd_6141842 < baseStart_6141842 := by decide
  rcases family_descends (prefixWord ++ tailWord_6141842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6141898 : List Nat := [3, 1, 2, 1, 2, 1, 2, 3, 2, 1, 5]
def baseStart_6141898 : Nat := 118140960795 + 6141898 * 2 ^ 59
def prefixEnd_6141898 : Nat := 4983230072969 + 3 ^ 40 * 6141898 * 2
def baseEnd_6141898 : Nat := 3153745804888316029528931

theorem tailTrace_6141898 : CollatzResearch.WordTrace tailWord_6141898 prefixEnd_6141898 3153745804888316029528931 := by
  unfold tailWord_6141898
  simp only [CollatzResearch.WordTrace]
  refine ⟨56003355875739993378030587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149342282335306649008081565 56003355875739993378030587)
  ·
    refine ⟨84005033813609990067045881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56003355875739993378030587 84005033813609990067045881)
    ·
      refine ⟨63003775360207492550284411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84005033813609990067045881 63003775360207492550284411)
      ·
        refine ⟨94505663040311238825426617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63003775360207492550284411 94505663040311238825426617)
        ·
          refine ⟨70879247280233429119069963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94505663040311238825426617 70879247280233429119069963)
          ·
            refine ⟨106318870920350143678604945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70879247280233429119069963 106318870920350143678604945)
            ·
              refine ⟨79739153190262607758953709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106318870920350143678604945 79739153190262607758953709)
              ·
                refine ⟨29902182446348477909607641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79739153190262607758953709 29902182446348477909607641)
                ·
                  refine ⟨22426636834761358432205731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29902182446348477909607641 22426636834761358432205731)
                  ·
                    refine ⟨33639955252142037648308597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22426636834761358432205731 33639955252142037648308597)
                    ·
                      refine ⟨3153745804888316029528931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33639955252142037648308597 3153745804888316029528931)
                      ·
                        rfl

theorem cell23_6141898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 3, 2, 1, 5].length) (baseStart_6141898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6141898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6141898 prefixEnd_6141898 := by exact prefixLift 6141898
  have htrace : WordTrace (prefixWord ++ tailWord_6141898) baseStart_6141898 baseEnd_6141898 := by
    simpa [prefixWord, tailWord_6141898, baseEnd_6141898] using wordTrace_append hprefix tailTrace_6141898
  have hstable : (prefixWord ++ tailWord_6141898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6141898).length < 2 ^ (prefixWord ++ tailWord_6141898).sum := by decide
  have hdescent : baseEnd_6141898 < baseStart_6141898 := by decide
  rcases family_descends (prefixWord ++ tailWord_6141898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6141906 : List Nat := [3, 2, 2, 3, 2, 2, 1, 2, 2, 1, 3]
def baseStart_6141906 : Nat := 118140960795 + 6141906 * 2 ^ 59
def prefixEnd_6141906 : Nat := 4983230072969 + 3 ^ 40 * 6141906 * 2
def baseEnd_6141906 : Nat := 3153749912733551998228895

theorem tailTrace_6141906 : CollatzResearch.WordTrace tailWord_6141906 prefixEnd_6141906 3153749912733551998228895 := by
  unfold tailWord_6141906
  simp only [CollatzResearch.WordTrace]
  refine ⟨56003428821732747719603393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149342476857953993918942381 56003428821732747719603393)
  ·
    refine ⟨42002571616299560789702545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56003428821732747719603393 42002571616299560789702545)
    ·
      refine ⟨31501928712224670592276909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42002571616299560789702545 31501928712224670592276909)
      ·
        refine ⟨11813223267084251472103841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31501928712224670592276909 11813223267084251472103841)
        ·
          refine ⟨8859917450313188604077881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11813223267084251472103841 8859917450313188604077881)
          ·
            refine ⟨6644938087734891453058411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8859917450313188604077881 6644938087734891453058411)
            ·
              refine ⟨9967407131602337179587617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6644938087734891453058411 9967407131602337179587617)
              ·
                refine ⟨7475555348701752884690713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9967407131602337179587617 7475555348701752884690713)
                ·
                  refine ⟨5606666511526314663518035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7475555348701752884690713 5606666511526314663518035)
                  ·
                    refine ⟨8409999767289471995277053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5606666511526314663518035 8409999767289471995277053)
                    ·
                      refine ⟨3153749912733551998228895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8409999767289471995277053 3153749912733551998228895)
                      ·
                        rfl

theorem cell23_6141906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_6141906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6141906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6141906 prefixEnd_6141906 := by exact prefixLift 6141906
  have htrace : WordTrace (prefixWord ++ tailWord_6141906) baseStart_6141906 baseEnd_6141906 := by
    simpa [prefixWord, tailWord_6141906, baseEnd_6141906] using wordTrace_append hprefix tailTrace_6141906
  have hstable : (prefixWord ++ tailWord_6141906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6141906).length < 2 ^ (prefixWord ++ tailWord_6141906).sum := by decide
  have hdescent : baseEnd_6141906 < baseStart_6141906 := by decide
  rcases family_descends (prefixWord ++ tailWord_6141906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6141912 : List Nat := [2, 1, 2, 2, 2, 2, 3, 1, 4, 2, 2]
def baseStart_6141912 : Nat := 118140960795 + 6141912 * 2 ^ 59
def prefixEnd_6141912 : Nat := 4983230072969 + 3 ^ 40 * 6141912 * 2
def baseEnd_6141912 : Nat := 3153752993617478974753867

theorem tailTrace_6141912 : CollatzResearch.WordTrace tailWord_6141912 prefixEnd_6141912 3153752993617478974753867 := by
  unfold tailWord_6141912
  simp only [CollatzResearch.WordTrace]
  refine ⟨112006967062454626951565995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149342622749939502602087993 112006967062454626951565995)
  ·
    refine ⟨168010450593681940427348993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112006967062454626951565995 168010450593681940427348993)
    ·
      refine ⟨126007837945261455320511745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168010450593681940427348993 126007837945261455320511745)
      ·
        refine ⟨94505878458946091490383809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126007837945261455320511745 94505878458946091490383809)
        ·
          refine ⟨70879408844209568617787857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94505878458946091490383809 70879408844209568617787857)
          ·
            refine ⟨53159556633157176463340893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70879408844209568617787857 53159556633157176463340893)
            ·
              refine ⟨19934833737433941173752835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53159556633157176463340893 19934833737433941173752835)
              ·
                refine ⟨29902250606150911760629253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19934833737433941173752835 29902250606150911760629253)
                ·
                  refine ⟨5606671988653295955117985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29902250606150911760629253 5606671988653295955117985)
                  ·
                    refine ⟨4205003991489971966338489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5606671988653295955117985 4205003991489971966338489)
                    ·
                      refine ⟨3153752993617478974753867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4205003991489971966338489 3153752993617478974753867)
                      ·
                        rfl

theorem cell23_6141912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 1, 4, 2, 2].length) (baseStart_6141912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6141912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6141912 prefixEnd_6141912 := by exact prefixLift 6141912
  have htrace : WordTrace (prefixWord ++ tailWord_6141912) baseStart_6141912 baseEnd_6141912 := by
    simpa [prefixWord, tailWord_6141912, baseEnd_6141912] using wordTrace_append hprefix tailTrace_6141912
  have hstable : (prefixWord ++ tailWord_6141912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6141912).length < 2 ^ (prefixWord ++ tailWord_6141912).sum := by decide
  have hdescent : baseEnd_6141912 < baseStart_6141912 := by decide
  rcases family_descends (prefixWord ++ tailWord_6141912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6141948 : List Nat := [2, 2, 2, 1, 2, 2, 1, 3, 1, 7]
def baseStart_6141948 : Nat := 118140960795 + 6141948 * 2 ^ 59
def prefixEnd_6141948 : Nat := 4983230072969 + 3 ^ 40 * 6141948 * 2
def baseEnd_6141948 : Nat := 1051257159640346944634567

theorem tailTrace_6141948 : CollatzResearch.WordTrace tailWord_6141948 prefixEnd_6141948 1051257159640346944634567 := by
  unfold tailWord_6141948
  simp only [CollatzResearch.WordTrace]
  refine ⟨112007623576389416025721249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149343498101852554700961665 112007623576389416025721249)
  ·
    refine ⟨84005717682292062019290937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112007623576389416025721249 84005717682292062019290937)
    ·
      refine ⟨63004288261719046514468203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84005717682292062019290937 63004288261719046514468203)
      ·
        refine ⟨94506432392578569771702305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63004288261719046514468203 94506432392578569771702305)
        ·
          refine ⟨70879824294433927328776729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94506432392578569771702305 70879824294433927328776729)
          ·
            refine ⟨53159868220825445496582547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70879824294433927328776729 53159868220825445496582547)
            ·
              refine ⟨79739802331238168244873821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53159868220825445496582547 79739802331238168244873821)
              ·
                refine ⟨29902425874214313091827683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79739802331238168244873821 29902425874214313091827683)
                ·
                  refine ⟨44853638811321469637741525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29902425874214313091827683 44853638811321469637741525)
                  ·
                    refine ⟨1051257159640346944634567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44853638811321469637741525 1051257159640346944634567)
                    ·
                      rfl

theorem cell23_6141948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 3, 1, 7].length) (baseStart_6141948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6141948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6141948 prefixEnd_6141948 := by exact prefixLift 6141948
  have htrace : WordTrace (prefixWord ++ tailWord_6141948) baseStart_6141948 baseEnd_6141948 := by
    simpa [prefixWord, tailWord_6141948, baseEnd_6141948] using wordTrace_append hprefix tailTrace_6141948
  have hstable : (prefixWord ++ tailWord_6141948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6141948).length < 2 ^ (prefixWord ++ tailWord_6141948).sum := by decide
  have hdescent : baseEnd_6141948 < baseStart_6141948 := by decide
  rcases family_descends (prefixWord ++ tailWord_6141948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6142002 : List Nat := [3, 2, 1, 1, 2, 4, 2, 1, 2, 1, 4]
def baseStart_6142002 : Nat := 118140960795 + 6142002 * 2 ^ 59
def prefixEnd_6142002 : Nat := 4983230072969 + 3 ^ 40 * 6142002 * 2
def baseEnd_6142002 : Nat := 3153799206876383622628453

theorem tailTrace_6142002 : CollatzResearch.WordTrace tailWord_6142002 prefixEnd_6142002 3153799206876383622628453 := by
  unfold tailWord_6142002
  simp only [CollatzResearch.WordTrace]
  refine ⟨56004304173645799818477065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149344811129722132849272173 56004304173645799818477065)
  ·
    refine ⟨42003228130234349863857799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56004304173645799818477065 42003228130234349863857799)
    ·
      refine ⟨63004842195351524795786699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42003228130234349863857799 63004842195351524795786699)
      ·
        refine ⟨94507263293027287193680049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63004842195351524795786699 94507263293027287193680049)
        ·
          refine ⟨70880447469770465395260037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94507263293027287193680049 70880447469770465395260037)
          ·
            refine ⟨13290083900581962261611257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70880447469770465395260037 13290083900581962261611257)
            ·
              refine ⟨9967562925436471696208443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13290083900581962261611257 9967562925436471696208443)
              ·
                refine ⟨14951344388154707544312665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9967562925436471696208443 14951344388154707544312665)
                ·
                  refine ⟨11213508291116030658234499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14951344388154707544312665 11213508291116030658234499)
                  ·
                    refine ⟨16820262436674045987351749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11213508291116030658234499 16820262436674045987351749)
                    ·
                      refine ⟨3153799206876383622628453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16820262436674045987351749 3153799206876383622628453)
                      ·
                        rfl

theorem cell23_6142002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 2, 1, 2, 1, 4].length) (baseStart_6142002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6142002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6142002 prefixEnd_6142002 := by exact prefixLift 6142002
  have htrace : WordTrace (prefixWord ++ tailWord_6142002) baseStart_6142002 baseEnd_6142002 := by
    simpa [prefixWord, tailWord_6142002, baseEnd_6142002] using wordTrace_append hprefix tailTrace_6142002
  have hstable : (prefixWord ++ tailWord_6142002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6142002).length < 2 ^ (prefixWord ++ tailWord_6142002).sum := by decide
  have hdescent : baseEnd_6142002 < baseStart_6142002 := by decide
  rcases family_descends (prefixWord ++ tailWord_6142002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6142005 : List Nat := [1, 3, 3, 1, 1, 1, 2, 3, 1, 4, 3]
def baseStart_6142005 : Nat := 118140960795 + 6142005 * 2 ^ 59
def prefixEnd_6142005 : Nat := 4983230072969 + 3 ^ 40 * 6142005 * 2
def baseEnd_6142005 : Nat := 3153800747318347110890939

theorem tailTrace_6142005 : CollatzResearch.WordTrace tailWord_6142005 prefixEnd_6142005 3153800747318347110890939 := by
  unfold tailWord_6142005
  simp only [CollatzResearch.WordTrace]
  refine ⟨224017326113572330786267469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149344884075714887190844979 224017326113572330786267469)
  ·
    refine ⟨84006497292589624044850301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 224017326113572330786267469 84006497292589624044850301)
    ·
      refine ⟨31502436484721109016818863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84006497292589624044850301 31502436484721109016818863)
      ·
        refine ⟨47253654727081663525228295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31502436484721109016818863 47253654727081663525228295)
        ·
          refine ⟨70880482090622495287842443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47253654727081663525228295 70880482090622495287842443)
          ·
            refine ⟨106320723135933742931763665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70880482090622495287842443 106320723135933742931763665)
            ·
              refine ⟨79740542351950307198822749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106320723135933742931763665 79740542351950307198822749)
              ·
                refine ⟨29902703381981365199558531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79740542351950307198822749 29902703381981365199558531)
                ·
                  refine ⟨44854055072972047799337797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29902703381981365199558531 44854055072972047799337797)
                  ·
                    refine ⟨8410135326182258962375837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44854055072972047799337797 8410135326182258962375837)
                    ·
                      refine ⟨3153800747318347110890939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8410135326182258962375837 3153800747318347110890939)
                      ·
                        rfl

theorem cell23_6142005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 3, 1, 4, 3].length) (baseStart_6142005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6142005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6142005 prefixEnd_6142005 := by exact prefixLift 6142005
  have htrace : WordTrace (prefixWord ++ tailWord_6142005) baseStart_6142005 baseEnd_6142005 := by
    simpa [prefixWord, tailWord_6142005, baseEnd_6142005] using wordTrace_append hprefix tailTrace_6142005
  have hstable : (prefixWord ++ tailWord_6142005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6142005).length < 2 ^ (prefixWord ++ tailWord_6142005).sum := by decide
  have hdescent : baseEnd_6142005 < baseStart_6142005 := by decide
  rcases family_descends (prefixWord ++ tailWord_6142005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6142022 : List Nat := [6, 1, 1, 1, 1, 1, 1, 1, 2, 3, 5]
def baseStart_6142022 : Nat := 118140960795 + 6142022 * 2 ^ 59
def prefixEnd_6142022 : Nat := 4983230072969 + 3 ^ 40 * 6142022 * 2
def baseEnd_6142022 : Nat := 3153809476489473544378361

theorem tailTrace_6142022 : CollatzResearch.WordTrace tailWord_6142022 prefixEnd_6142022 3153809476489473544378361 := by
  unfold tailWord_6142022
  simp only [CollatzResearch.WordTrace]
  refine ⟨7000560817328460709051135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 149345297436340495126424213 7000560817328460709051135)
  ·
    refine ⟨10500841225992691063576703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7000560817328460709051135 10500841225992691063576703)
    ·
      refine ⟨15751261838989036595365055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10500841225992691063576703 15751261838989036595365055)
      ·
        refine ⟨23626892758483554893047583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15751261838989036595365055 23626892758483554893047583)
        ·
          refine ⟨35440339137725332339571375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23626892758483554893047583 35440339137725332339571375)
          ·
            refine ⟨53160508706587998509357063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35440339137725332339571375 53160508706587998509357063)
            ·
              refine ⟨79740763059881997764035595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53160508706587998509357063 79740763059881997764035595)
              ·
                refine ⟨119611144589822996646053393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79740763059881997764035595 119611144589822996646053393)
                ·
                  refine ⟨89708358442367247484540045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 119611144589822996646053393 89708358442367247484540045)
                  ·
                    refine ⟨33640634415887717806702517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 89708358442367247484540045 33640634415887717806702517)
                    ·
                      refine ⟨3153809476489473544378361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33640634415887717806702517 3153809476489473544378361)
                      ·
                        rfl

theorem cell23_6142022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_6142022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6142022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6142022 prefixEnd_6142022 := by exact prefixLift 6142022
  have htrace : WordTrace (prefixWord ++ tailWord_6142022) baseStart_6142022 baseEnd_6142022 := by
    simpa [prefixWord, tailWord_6142022, baseEnd_6142022] using wordTrace_append hprefix tailTrace_6142022
  have hstable : (prefixWord ++ tailWord_6142022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6142022).length < 2 ^ (prefixWord ++ tailWord_6142022).sum := by decide
  have hdescent : baseEnd_6142022 < baseStart_6142022 := by decide
  rcases family_descends (prefixWord ++ tailWord_6142022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6142025 : List Nat := [1, 2, 1, 1, 2, 2, 6, 2, 6]
def baseStart_6142025 : Nat := 118140960795 + 6142025 * 2 ^ 59
def prefixEnd_6142025 : Nat := 4983230072969 + 3 ^ 40 * 6142025 * 2
def baseEnd_6142025 : Nat := 350423446325715225848983

theorem tailTrace_6142025 : CollatzResearch.WordTrace tailWord_6142025 prefixEnd_6142025 350423446325715225848983 := by
  unfold tailWord_6142025
  simp only [CollatzResearch.WordTrace]
  refine ⟨224018055573499874201995529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149345370382333249467997019 224018055573499874201995529)
  ·
    refine ⟨168013541680124905651496647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224018055573499874201995529 168013541680124905651496647)
    ·
      refine ⟨252020312520187358477244971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168013541680124905651496647 252020312520187358477244971)
      ·
        refine ⟨378030468780281037715867457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252020312520187358477244971 378030468780281037715867457)
        ·
          refine ⟨283522851585210778286900593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 378030468780281037715867457 283522851585210778286900593)
          ·
            refine ⟨212642138688908083715175445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 283522851585210778286900593 212642138688908083715175445)
            ·
              refine ⟨9967600251042566424148849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 212642138688908083715175445 9967600251042566424148849)
              ·
                refine ⟨7475700188281924818111637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9967600251042566424148849 7475700188281924818111637)
                ·
                  refine ⟨350423446325715225848983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7475700188281924818111637 350423446325715225848983)
                  ·
                    rfl

theorem cell23_6142025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 6, 2, 6].length) (baseStart_6142025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6142025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6142025 prefixEnd_6142025 := by exact prefixLift 6142025
  have htrace : WordTrace (prefixWord ++ tailWord_6142025) baseStart_6142025 baseEnd_6142025 := by
    simpa [prefixWord, tailWord_6142025, baseEnd_6142025] using wordTrace_append hprefix tailTrace_6142025
  have hstable : (prefixWord ++ tailWord_6142025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6142025).length < 2 ^ (prefixWord ++ tailWord_6142025).sum := by decide
  have hdescent : baseEnd_6142025 < baseStart_6142025 := by decide
  rcases family_descends (prefixWord ++ tailWord_6142025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6142052 : List Nat := [2, 3, 1, 1, 2, 1, 3, 1, 5, 1, 3]
def baseStart_6142052 : Nat := 118140960795 + 6142052 * 2 ^ 59
def prefixEnd_6142052 : Nat := 4983230072969 + 3 ^ 40 * 6142052 * 2
def baseEnd_6142052 : Nat := 3153824880909108427003223

theorem tailTrace_6142052 : CollatzResearch.WordTrace tailWord_6142052 prefixEnd_6142052 3153824880909108427003223 := by
  unfold tailWord_6142052
  simp only [CollatzResearch.WordTrace]
  refine ⟨112009520172201028906614205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149346026896268038542152273 112009520172201028906614205)
  ·
    refine ⟨42003570064575385839980327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112009520172201028906614205 42003570064575385839980327)
    ·
      refine ⟨63005355096863078759970491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42003570064575385839980327 63005355096863078759970491)
      ·
        refine ⟨94508032645294618139955737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63005355096863078759970491 94508032645294618139955737)
        ·
          refine ⟨70881024483970963604966803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94508032645294618139955737 70881024483970963604966803)
          ·
            refine ⟨106321536725956445407450205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70881024483970963604966803 106321536725956445407450205)
            ·
              refine ⟨39870576272233667027793827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 106321536725956445407450205 39870576272233667027793827)
              ·
                refine ⟨59805864408350500541690741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39870576272233667027793827 59805864408350500541690741)
                ·
                  refine ⟨5606799788282859425783507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59805864408350500541690741 5606799788282859425783507)
                  ·
                    refine ⟨8410199682424289138675261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5606799788282859425783507 8410199682424289138675261)
                    ·
                      refine ⟨3153824880909108427003223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8410199682424289138675261 3153824880909108427003223)
                      ·
                        rfl

theorem cell23_6142052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 1, 5, 1, 3].length) (baseStart_6142052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6142052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6142052 prefixEnd_6142052 := by exact prefixLift 6142052
  have htrace : WordTrace (prefixWord ++ tailWord_6142052) baseStart_6142052 baseEnd_6142052 := by
    simpa [prefixWord, tailWord_6142052, baseEnd_6142052] using wordTrace_append hprefix tailTrace_6142052
  have hstable : (prefixWord ++ tailWord_6142052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6142052).length < 2 ^ (prefixWord ++ tailWord_6142052).sum := by decide
  have hdescent : baseEnd_6142052 < baseStart_6142052 := by decide
  rcases family_descends (prefixWord ++ tailWord_6142052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6142055 : List Nat := [1, 1, 5, 1, 1, 2, 1, 3, 3, 5]
def baseStart_6142055 : Nat := 118140960795 + 6142055 * 2 ^ 59
def prefixEnd_6142055 : Nat := 4983230072969 + 3 ^ 40 * 6142055 * 2
def baseEnd_6142055 : Nat := 1051275473783690638421903

theorem tailTrace_6142055 : CollatzResearch.WordTrace tailWord_6142055 prefixEnd_6142055 1051275473783690638421903 := by
  unfold tailWord_6142055
  simp only [CollatzResearch.WordTrace]
  refine ⟨224019149763391189325587619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149346099842260792883725079 224019149763391189325587619)
  ·
    refine ⟨336028724645086783988381429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224019149763391189325587619 336028724645086783988381429)
    ·
      refine ⟨31502692935476885998910759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 336028724645086783988381429 31502692935476885998910759)
      ·
        refine ⟨47254039403215328998366139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31502692935476885998910759 47254039403215328998366139)
        ·
          refine ⟨70881059104822993497549209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47254039403215328998366139 70881059104822993497549209)
          ·
            refine ⟨53160794328617245123161907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70881059104822993497549209 53160794328617245123161907)
            ·
              refine ⟨79741191492925867684742861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53160794328617245123161907 79741191492925867684742861)
              ·
                refine ⟨29902946809847200381778573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79741191492925867684742861 29902946809847200381778573)
                ·
                  refine ⟨11213605053692700143166965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29902946809847200381778573 11213605053692700143166965)
                  ·
                    refine ⟨1051275473783690638421903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11213605053692700143166965 1051275473783690638421903)
                    ·
                      rfl

theorem cell23_6142055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 3, 3, 5].length) (baseStart_6142055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6142055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6142055 prefixEnd_6142055 := by exact prefixLift 6142055
  have htrace : WordTrace (prefixWord ++ tailWord_6142055) baseStart_6142055 baseEnd_6142055 := by
    simpa [prefixWord, tailWord_6142055, baseEnd_6142055] using wordTrace_append hprefix tailTrace_6142055
  have hstable : (prefixWord ++ tailWord_6142055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6142055).length < 2 ^ (prefixWord ++ tailWord_6142055).sum := by decide
  have hdescent : baseEnd_6142055 < baseStart_6142055 := by decide
  rcases family_descends (prefixWord ++ tailWord_6142055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6142109 : List Nat := [1, 4, 2, 1, 1, 4, 2, 2, 1, 1, 4]
def baseStart_6142109 : Nat := 118140960795 + 6142109 * 2 ^ 59
def prefixEnd_6142109 : Nat := 4983230072969 + 3 ^ 40 * 6142109 * 2
def baseEnd_6142109 : Nat := 3153854149306414703990461

theorem tailTrace_6142109 : CollatzResearch.WordTrace tailWord_6142109 prefixEnd_6142109 3153854149306414703990461 := by
  unfold tailWord_6142109
  simp only [CollatzResearch.WordTrace]
  refine ⟨224021119305195556548053381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149347412870130371032035587 224021119305195556548053381)
  ·
    refine ⟨42003959869724166852760009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 224021119305195556548053381 42003959869724166852760009)
    ·
      refine ⟨31502969902293125139570007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42003959869724166852760009 31502969902293125139570007)
      ·
        refine ⟨47254454853439687709355011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31502969902293125139570007 47254454853439687709355011)
        ·
          refine ⟨70881682280159531564032517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47254454853439687709355011 70881682280159531564032517)
          ·
            refine ⟨13290315427529912168256097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70881682280159531564032517 13290315427529912168256097)
            ·
              refine ⟨9967736570647434126192073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13290315427529912168256097 9967736570647434126192073)
              ·
                refine ⟨7475802427985575594644055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9967736570647434126192073 7475802427985575594644055)
                ·
                  refine ⟨11213703641978363391966083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7475802427985575594644055 11213703641978363391966083)
                  ·
                    refine ⟨16820555462967545087949125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11213703641978363391966083 16820555462967545087949125)
                    ·
                      refine ⟨3153854149306414703990461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16820555462967545087949125 3153854149306414703990461)
                      ·
                        rfl

theorem cell23_6142109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 2, 2, 1, 1, 4].length) (baseStart_6142109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6142109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6142109 prefixEnd_6142109 := by exact prefixLift 6142109
  have htrace : WordTrace (prefixWord ++ tailWord_6142109) baseStart_6142109 baseEnd_6142109 := by
    simpa [prefixWord, tailWord_6142109, baseEnd_6142109] using wordTrace_append hprefix tailTrace_6142109
  have hstable : (prefixWord ++ tailWord_6142109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6142109).length < 2 ^ (prefixWord ++ tailWord_6142109).sum := by decide
  have hdescent : baseEnd_6142109 < baseStart_6142109 := by decide
  rcases family_descends (prefixWord ++ tailWord_6142109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6142129 : List Nat := [1, 2, 2, 5, 2, 1, 2, 1, 1, 1, 5]
def baseStart_6142129 : Nat := 118140960795 + 6142129 * 2 ^ 59
def prefixEnd_6142129 : Nat := 4983230072969 + 3 ^ 40 * 6142129 * 2
def baseEnd_6142129 : Nat := 3153864418919504625740369

theorem tailTrace_6142129 : CollatzResearch.WordTrace tailWord_6142129 prefixEnd_6142129 3153864418919504625740369 := by
  unfold tailWord_6142129
  simp only [CollatzResearch.WordTrace]
  refine ⟨224021848765123099963781441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149347899176748733309187627 224021848765123099963781441)
  ·
    refine ⟨168016386573842324972836081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224021848765123099963781441 168016386573842324972836081)
    ·
      refine ⟨126012289930381743729627061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168016386573842324972836081 126012289930381743729627061)
      ·
        refine ⟨11813652180973288474652537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 126012289930381743729627061 11813652180973288474652537)
        ·
          refine ⟨8860239135729966355989403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11813652180973288474652537 8860239135729966355989403)
          ·
            refine ⟨13290358703594949533984105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8860239135729966355989403 13290358703594949533984105)
            ·
              refine ⟨9967769027696212150488079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13290358703594949533984105 9967769027696212150488079)
              ·
                refine ⟨14951653541544318225732119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9967769027696212150488079 14951653541544318225732119)
                ·
                  refine ⟨22427480312316477338598179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14951653541544318225732119 22427480312316477338598179)
                  ·
                    refine ⟨33641220468474716007897269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22427480312316477338598179 33641220468474716007897269)
                    ·
                      refine ⟨3153864418919504625740369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33641220468474716007897269 3153864418919504625740369)
                      ·
                        rfl

theorem cell23_6142129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_6142129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6142129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6142129 prefixEnd_6142129 := by exact prefixLift 6142129
  have htrace : WordTrace (prefixWord ++ tailWord_6142129) baseStart_6142129 baseEnd_6142129 := by
    simpa [prefixWord, tailWord_6142129, baseEnd_6142129] using wordTrace_append hprefix tailTrace_6142129
  have hstable : (prefixWord ++ tailWord_6142129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6142129).length < 2 ^ (prefixWord ++ tailWord_6142129).sum := by decide
  have hdescent : baseEnd_6142129 < baseStart_6142129 := by decide
  rcases family_descends (prefixWord ++ tailWord_6142129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6142146 : List Nat := [3, 5, 1, 1, 1, 1, 2, 2, 1, 1, 5]
def baseStart_6142146 : Nat := 118140960795 + 6142146 * 2 ^ 59
def prefixEnd_6142146 : Nat := 4983230072969 + 3 ^ 40 * 6142146 * 2
def baseEnd_6142146 : Nat := 3153873148090631059227791

theorem tailTrace_6142146 : CollatzResearch.WordTrace tailWord_6142146 prefixEnd_6142146 3153873148090631059227791 := by
  unfold tailWord_6142146
  simp only [CollatzResearch.WordTrace]
  refine ⟨56005617201515377966787573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149348312537374341244766861 56005617201515377966787573)
  ·
    refine ⟨5250526612642066684386335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 56005617201515377966787573 5250526612642066684386335)
    ·
      refine ⟨7875789918963100026579503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5250526612642066684386335 7875789918963100026579503)
      ·
        refine ⟨11813684878444650039869255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7875789918963100026579503 11813684878444650039869255)
        ·
          refine ⟨17720527317666975059803883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11813684878444650039869255 17720527317666975059803883)
          ·
            refine ⟨26580790976500462589705825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17720527317666975059803883 26580790976500462589705825)
            ·
              refine ⟨19935593232375346942279369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26580790976500462589705825 19935593232375346942279369)
              ·
                refine ⟨14951694924281510206709527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19935593232375346942279369 14951694924281510206709527)
                ·
                  refine ⟨22427542386422265310064291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14951694924281510206709527 22427542386422265310064291)
                  ·
                    refine ⟨33641313579633397965096437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22427542386422265310064291 33641313579633397965096437)
                    ·
                      refine ⟨3153873148090631059227791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33641313579633397965096437 3153873148090631059227791)
                      ·
                        rfl

theorem cell23_6142146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_6142146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6142146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6142146 prefixEnd_6142146 := by exact prefixLift 6142146
  have htrace : WordTrace (prefixWord ++ tailWord_6142146) baseStart_6142146 baseEnd_6142146 := by
    simpa [prefixWord, tailWord_6142146, baseEnd_6142146] using wordTrace_append hprefix tailTrace_6142146
  have hstable : (prefixWord ++ tailWord_6142146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6142146).length < 2 ^ (prefixWord ++ tailWord_6142146).sum := by decide
  have hdescent : baseEnd_6142146 < baseStart_6142146 := by decide
  rcases family_descends (prefixWord ++ tailWord_6142146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6142152 : List Nat := [2, 1, 3, 1, 2, 1, 1, 1, 2, 7, 2]
def baseStart_6142152 : Nat := 118140960795 + 6142152 * 2 ^ 59
def prefixEnd_6142152 : Nat := 4983230072969 + 3 ^ 40 * 6142152 * 2
def baseEnd_6142152 : Nat := 3153876228974558035752763

theorem tailTrace_6142152 : CollatzResearch.WordTrace tailWord_6142152 prefixEnd_6142152 3153876228974558035752763 := by
  unfold tailWord_6142152
  simp only [CollatzResearch.WordTrace]
  refine ⟨112011343822019887445934355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149348458429359849927912473 112011343822019887445934355)
  ·
    refine ⟨168017015733029831168901533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112011343822019887445934355 168017015733029831168901533)
    ·
      refine ⟨63006380899886186688338075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168017015733029831168901533 63006380899886186688338075)
      ·
        refine ⟨94509571349829280032507113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63006380899886186688338075 94509571349829280032507113)
        ·
          refine ⟨70882178512371960024380335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94509571349829280032507113 70882178512371960024380335)
          ·
            refine ⟨106323267768557940036570503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70882178512371960024380335 106323267768557940036570503)
            ·
              refine ⟨159484901652836910054855755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106323267768557940036570503 159484901652836910054855755)
              ·
                refine ⟨239227352479255365082283633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 159484901652836910054855755 239227352479255365082283633)
                ·
                  refine ⟨179420514359441523811712725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 239227352479255365082283633 179420514359441523811712725)
                  ·
                    refine ⟨4205168305299410714337017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 179420514359441523811712725 4205168305299410714337017)
                    ·
                      refine ⟨3153876228974558035752763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4205168305299410714337017 3153876228974558035752763)
                      ·
                        rfl

theorem cell23_6142152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 2, 7, 2].length) (baseStart_6142152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6142152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6142152 prefixEnd_6142152 := by exact prefixLift 6142152
  have htrace : WordTrace (prefixWord ++ tailWord_6142152) baseStart_6142152 baseEnd_6142152 := by
    simpa [prefixWord, tailWord_6142152, baseEnd_6142152] using wordTrace_append hprefix tailTrace_6142152
  have hstable : (prefixWord ++ tailWord_6142152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6142152).length < 2 ^ (prefixWord ++ tailWord_6142152).sum := by decide
  have hdescent : baseEnd_6142152 < baseStart_6142152 := by decide
  rcases family_descends (prefixWord ++ tailWord_6142152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6142159 : List Nat := [1, 1, 2, 1, 1, 3, 5, 3, 2, 1, 3]
def baseStart_6142159 : Nat := 118140960795 + 6142159 * 2 ^ 59
def prefixEnd_6142159 : Nat := 4983230072969 + 3 ^ 40 * 6142159 * 2
def baseEnd_6142159 : Nat := 3153879823339139508365231

theorem tailTrace_6142159 : CollatzResearch.WordTrace tailWord_6142159 prefixEnd_6142159 3153879823339139508365231 := by
  unfold tailWord_6142159
  simp only [CollatzResearch.WordTrace]
  refine ⟨224022942955014415087373531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149348628636676276724915687 224022942955014415087373531)
  ·
    refine ⟨336034414432521622631060297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224022942955014415087373531 336034414432521622631060297)
    ·
      refine ⟨252025810824391216973295223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 336034414432521622631060297 252025810824391216973295223)
      ·
        refine ⟨378038716236586825459942835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252025810824391216973295223 378038716236586825459942835)
        ·
          refine ⟨567058074354880238189914253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 378038716236586825459942835 567058074354880238189914253)
          ·
            refine ⟨212646777883080089321217845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 567058074354880238189914253 212646777883080089321217845)
            ·
              refine ⟨19935635426538758373864173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 212646777883080089321217845 19935635426538758373864173)
              ·
                refine ⟨7475863284952034390199065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19935635426538758373864173 7475863284952034390199065)
                ·
                  refine ⟨5606897463714025792649299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7475863284952034390199065 5606897463714025792649299)
                  ·
                    refine ⟨8410346195571038688973949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5606897463714025792649299 8410346195571038688973949)
                    ·
                      refine ⟨3153879823339139508365231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8410346195571038688973949 3153879823339139508365231)
                      ·
                        rfl

theorem cell23_6142159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 3, 2, 1, 3].length) (baseStart_6142159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6142159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6142159 prefixEnd_6142159 := by exact prefixLift 6142159
  have htrace : WordTrace (prefixWord ++ tailWord_6142159) baseStart_6142159 baseEnd_6142159 := by
    simpa [prefixWord, tailWord_6142159, baseEnd_6142159] using wordTrace_append hprefix tailTrace_6142159
  have hstable : (prefixWord ++ tailWord_6142159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6142159).length < 2 ^ (prefixWord ++ tailWord_6142159).sum := by decide
  have hdescent : baseEnd_6142159 < baseStart_6142159 := by decide
  rcases family_descends (prefixWord ++ tailWord_6142159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6142175 : List Nat := [1, 1, 2, 3, 2, 1, 1, 2, 4, 6]
def baseStart_6142175 : Nat := 118140960795 + 6142175 * 2 ^ 59
def prefixEnd_6142175 : Nat := 4983230072969 + 3 ^ 40 * 6142175 * 2
def baseEnd_6142175 : Nat := 1051296013009870481921719

theorem tailTrace_6142175 : CollatzResearch.WordTrace tailWord_6142175 prefixEnd_6142175 1051296013009870481921719 := by
  unfold tailWord_6142175
  simp only [CollatzResearch.WordTrace]
  refine ⟨224023526522956449819955979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149349017681970966546637319 224023526522956449819955979)
  ·
    refine ⟨336035289784434674729933969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224023526522956449819955979 336035289784434674729933969)
    ·
      refine ⟨252026467338326006047450477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 336035289784434674729933969 252026467338326006047450477)
      ·
        refine ⟨94509925251872252267793929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 252026467338326006047450477 94509925251872252267793929)
        ·
          refine ⟨70882443938904189200845447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94509925251872252267793929 70882443938904189200845447)
          ·
            refine ⟨106323665908356283801268171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70882443938904189200845447 106323665908356283801268171)
            ·
              refine ⟨159485498862534425701902257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106323665908356283801268171 159485498862534425701902257)
              ·
                refine ⟨119614124146900819276426693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 159485498862534425701902257 119614124146900819276426693)
                ·
                  refine ⟨22427648277543903614330005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 119614124146900819276426693 22427648277543903614330005)
                  ·
                    refine ⟨1051296013009870481921719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22427648277543903614330005 1051296013009870481921719)
                    ·
                      rfl

theorem cell23_6142175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 4, 6].length) (baseStart_6142175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6142175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6142175 prefixEnd_6142175 := by exact prefixLift 6142175
  have htrace : WordTrace (prefixWord ++ tailWord_6142175) baseStart_6142175 baseEnd_6142175 := by
    simpa [prefixWord, tailWord_6142175, baseEnd_6142175] using wordTrace_append hprefix tailTrace_6142175
  have hstable : (prefixWord ++ tailWord_6142175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6142175).length < 2 ^ (prefixWord ++ tailWord_6142175).sum := by decide
  have hdescent : baseEnd_6142175 < baseStart_6142175 := by decide
  rcases family_descends (prefixWord ++ tailWord_6142175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6142202 : List Nat := [3, 1, 1, 1, 1, 5, 1, 1, 2, 4, 3]
def baseStart_6142202 : Nat := 118140960795 + 6142202 * 2 ^ 59
def prefixEnd_6142202 : Nat := 4983230072969 + 3 ^ 40 * 6142202 * 2
def baseEnd_6142202 : Nat := 3153901903007282840127533

theorem tailTrace_6142202 : CollatzResearch.WordTrace tailWord_6142202 prefixEnd_6142202 3153901903007282840127533 := by
  unfold tailWord_6142202
  simp only [CollatzResearch.WordTrace]
  refine ⟨56006127823464658357797215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149349674195905755620792573 56006127823464658357797215)
  ·
    refine ⟨84009191735196987536695823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56006127823464658357797215 84009191735196987536695823)
    ·
      refine ⟨126013787602795481305043735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84009191735196987536695823 126013787602795481305043735)
      ·
        refine ⟨189020681404193221957565603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126013787602795481305043735 189020681404193221957565603)
        ·
          refine ⟨283531022106289832936348405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189020681404193221957565603 283531022106289832936348405)
          ·
            refine ⟨26581033322464671837782663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 283531022106289832936348405 26581033322464671837782663)
            ·
              refine ⟨39871549983697007756673995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26581033322464671837782663 39871549983697007756673995)
              ·
                refine ⟨59807324975545511635010993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39871549983697007756673995 59807324975545511635010993)
                ·
                  refine ⟨44855493731659133726258245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59807324975545511635010993 44855493731659133726258245)
                  ·
                    refine ⟨8410405074686087573673421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44855493731659133726258245 8410405074686087573673421)
                    ·
                      refine ⟨3153901903007282840127533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8410405074686087573673421 3153901903007282840127533)
                      ·
                        rfl

theorem cell23_6142202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 1, 2, 4, 3].length) (baseStart_6142202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6142202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6142202 prefixEnd_6142202 := by exact prefixLift 6142202
  have htrace : WordTrace (prefixWord ++ tailWord_6142202) baseStart_6142202 baseEnd_6142202 := by
    simpa [prefixWord, tailWord_6142202, baseEnd_6142202] using wordTrace_append hprefix tailTrace_6142202
  have hstable : (prefixWord ++ tailWord_6142202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6142202).length < 2 ^ (prefixWord ++ tailWord_6142202).sum := by decide
  have hdescent : baseEnd_6142202 < baseStart_6142202 := by decide
  rcases family_descends (prefixWord ++ tailWord_6142202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6142205 : List Nat := [1, 4, 1, 1, 1, 1, 1, 2, 11]
def baseStart_6142205 : Nat := 118140960795 + 6142205 * 2 ^ 59
def prefixEnd_6142205 : Nat := 4983230072969 + 3 ^ 40 * 6142205 * 2
def baseEnd_6142205 : Nat := 350433715938805147598891

theorem tailTrace_6142205 : CollatzResearch.WordTrace tailWord_6142205 prefixEnd_6142205 350433715938805147598891 := by
  unfold tailWord_6142205
  simp only [CollatzResearch.WordTrace]
  refine ⟨224024620712847764943548069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149349747141898509962365379 224024620712847764943548069)
  ·
    refine ⟨42004616383658955926915263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 224024620712847764943548069 42004616383658955926915263)
    ·
      refine ⟨63006924575488433890372895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42004616383658955926915263 63006924575488433890372895)
      ·
        refine ⟨94510386863232650835559343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63006924575488433890372895 94510386863232650835559343)
        ·
          refine ⟨141765580294848976253339015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94510386863232650835559343 141765580294848976253339015)
          ·
            refine ⟨212648370442273464380008523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141765580294848976253339015 212648370442273464380008523)
            ·
              refine ⟨318972555663410196570012785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 212648370442273464380008523 318972555663410196570012785)
              ·
                refine ⟨239229416747557647427509589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 318972555663410196570012785 239229416747557647427509589)
                ·
                  refine ⟨350433715938805147598891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 239229416747557647427509589 350433715938805147598891)
                  ·
                    rfl

theorem cell23_6142205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 11].length) (baseStart_6142205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6142205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6142205 prefixEnd_6142205 := by exact prefixLift 6142205
  have htrace : WordTrace (prefixWord ++ tailWord_6142205) baseStart_6142205 baseEnd_6142205 := by
    simpa [prefixWord, tailWord_6142205, baseEnd_6142205] using wordTrace_append hprefix tailTrace_6142205
  have hstable : (prefixWord ++ tailWord_6142205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6142205).length < 2 ^ (prefixWord ++ tailWord_6142205).sum := by decide
  have hdescent : baseEnd_6142205 < baseStart_6142205 := by decide
  rcases family_descends (prefixWord ++ tailWord_6142205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6142216 : List Nat := [2, 1, 3, 2, 3, 2, 2, 1, 1, 4, 2]
def baseStart_6142216 : Nat := 118140960795 + 6142216 * 2 ^ 59
def prefixEnd_6142216 : Nat := 4983230072969 + 3 ^ 40 * 6142216 * 2
def baseEnd_6142216 : Nat := 3153909091736445785352469

theorem tailTrace_6142216 : CollatzResearch.WordTrace tailWord_6142216 prefixEnd_6142216 3153909091736445785352469 := by
  unfold tailWord_6142216
  simp only [CollatzResearch.WordTrace]
  refine ⟨112012510957903956911099251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149350014610538609214799001 112012510957903956911099251)
  ·
    refine ⟨168018766436855935366648877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112012510957903956911099251 168018766436855935366648877)
    ·
      refine ⟨63007037413820975762493329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168018766436855935366648877 63007037413820975762493329)
      ·
        refine ⟨47255278060365731821869997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63007037413820975762493329 47255278060365731821869997)
        ·
          refine ⟨17720729272637149433201249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47255278060365731821869997 17720729272637149433201249)
          ·
            refine ⟨13290546954477862074900937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17720729272637149433201249 13290546954477862074900937)
            ·
              refine ⟨9967910215858396556175703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13290546954477862074900937 9967910215858396556175703)
              ·
                refine ⟨14951865323787594834263555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9967910215858396556175703 14951865323787594834263555)
                ·
                  refine ⟨22427797985681392251395333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14951865323787594834263555 22427797985681392251395333)
                  ·
                    refine ⟨4205212122315261047136625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22427797985681392251395333 4205212122315261047136625)
                    ·
                      refine ⟨3153909091736445785352469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4205212122315261047136625 3153909091736445785352469)
                      ·
                        rfl

theorem cell23_6142216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 2, 1, 1, 4, 2].length) (baseStart_6142216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6142216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6142216 prefixEnd_6142216 := by exact prefixLift 6142216
  have htrace : WordTrace (prefixWord ++ tailWord_6142216) baseStart_6142216 baseEnd_6142216 := by
    simpa [prefixWord, tailWord_6142216, baseEnd_6142216] using wordTrace_append hprefix tailTrace_6142216
  have hstable : (prefixWord ++ tailWord_6142216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6142216).length < 2 ^ (prefixWord ++ tailWord_6142216).sum := by decide
  have hdescent : baseEnd_6142216 < baseStart_6142216 := by decide
  rcases family_descends (prefixWord ++ tailWord_6142216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6142222 : List Nat := [4, 1, 1, 2, 1, 2, 3, 2, 7]
def baseStart_6142222 : Nat := 118140960795 + 6142222 * 2 ^ 59
def prefixEnd_6142222 : Nat := 4983230072969 + 3 ^ 40 * 6142222 * 2
def baseEnd_6142222 : Nat := 350434685846708084653049

theorem tailTrace_6142222 : CollatzResearch.WordTrace tailWord_6142222 prefixEnd_6142222 350434685846708084653049 := by
  unfold tailWord_6142222
  simp only [CollatzResearch.WordTrace]
  refine ⟨28003155094223272105864615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149350160502524117897944613 28003155094223272105864615)
  ·
    refine ⟨42004732641334908158796923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28003155094223272105864615 42004732641334908158796923)
    ·
      refine ⟨63007098962002362238195385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42004732641334908158796923 63007098962002362238195385)
      ·
        refine ⟨47255324221501771678646539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63007098962002362238195385 47255324221501771678646539)
        ·
          refine ⟨70882986332252657517969809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47255324221501771678646539 70882986332252657517969809)
          ·
            refine ⟨53162239749189493138477357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70882986332252657517969809 53162239749189493138477357)
            ·
              refine ⟨19935839905946059926929009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53162239749189493138477357 19935839905946059926929009)
              ·
                refine ⟨14951879929459544945196757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19935839905946059926929009 14951879929459544945196757)
                ·
                  refine ⟨350434685846708084653049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14951879929459544945196757 350434685846708084653049)
                  ·
                    rfl

theorem cell23_6142222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 3, 2, 7].length) (baseStart_6142222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6142222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6142222 prefixEnd_6142222 := by exact prefixLift 6142222
  have htrace : WordTrace (prefixWord ++ tailWord_6142222) baseStart_6142222 baseEnd_6142222 := by
    simpa [prefixWord, tailWord_6142222, baseEnd_6142222] using wordTrace_append hprefix tailTrace_6142222
  have hstable : (prefixWord ++ tailWord_6142222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6142222).length < 2 ^ (prefixWord ++ tailWord_6142222).sum := by decide
  have hdescent : baseEnd_6142222 < baseStart_6142222 := by decide
  rcases family_descends (prefixWord ++ tailWord_6142222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6142232 : List Nat := [2, 1, 2, 3, 1, 2, 1, 2, 1, 5, 3]
def baseStart_6142232 : Nat := 118140960795 + 6142232 * 2 ^ 59
def prefixEnd_6142232 : Nat := 4983230072969 + 3 ^ 40 * 6142232 * 2
def baseEnd_6142232 : Nat := 3153917307426917722752395

theorem tailTrace_6142232 : CollatzResearch.WordTrace tailWord_6142232 prefixEnd_6142232 3153917307426917722752395 := by
  unfold tailWord_6142232
  simp only [CollatzResearch.WordTrace]
  refine ⟨112012802741874974277390475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149350403655833299036520633 112012802741874974277390475)
  ·
    refine ⟨168019204112812461416085713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112012802741874974277390475 168019204112812461416085713)
    ·
      refine ⟨126014403084609346062064285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168019204112812461416085713 126014403084609346062064285)
      ·
        refine ⟨47255401156728504773274107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126014403084609346062064285 47255401156728504773274107)
        ·
          refine ⟨70883101735092757159911161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47255401156728504773274107 70883101735092757159911161)
          ·
            refine ⟨53162326301319567869933371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70883101735092757159911161 53162326301319567869933371)
            ·
              refine ⟨79743489451979351804900057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53162326301319567869933371 79743489451979351804900057)
              ·
                refine ⟨59807617088984513853675043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79743489451979351804900057 59807617088984513853675043)
                ·
                  refine ⟨89711425633476770780512565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59807617088984513853675043 89711425633476770780512565)
                  ·
                    refine ⟨8410446153138447260673053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 89711425633476770780512565 8410446153138447260673053)
                    ·
                      refine ⟨3153917307426917722752395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8410446153138447260673053 3153917307426917722752395)
                      ·
                        rfl

theorem cell23_6142232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 2, 1, 5, 3].length) (baseStart_6142232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6142232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6142232 prefixEnd_6142232 := by exact prefixLift 6142232
  have htrace : WordTrace (prefixWord ++ tailWord_6142232) baseStart_6142232 baseEnd_6142232 := by
    simpa [prefixWord, tailWord_6142232, baseEnd_6142232] using wordTrace_append hprefix tailTrace_6142232
  have hstable : (prefixWord ++ tailWord_6142232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6142232).length < 2 ^ (prefixWord ++ tailWord_6142232).sum := by decide
  have hdescent : baseEnd_6142232 < baseStart_6142232 := by decide
  rcases family_descends (prefixWord ++ tailWord_6142232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6142237 : List Nat := [1, 4, 2, 3, 3, 1, 2, 1, 1, 3, 2]
def baseStart_6142237 : Nat := 118140960795 + 6142237 * 2 ^ 59
def prefixEnd_6142237 : Nat := 4983230072969 + 3 ^ 40 * 6142237 * 2
def baseEnd_6142237 : Nat := 3153919874830190203189873

theorem tailTrace_6142237 : CollatzResearch.WordTrace tailWord_6142237 prefixEnd_6142237 3153919874830190203189873 := by
  unfold tailWord_6142237
  simp only [CollatzResearch.WordTrace]
  refine ⟨224025787848731834408712965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149350525232487889605808643 224025787848731834408712965)
  ·
    refine ⟨42004835221637218951633681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 224025787848731834408712965 42004835221637218951633681)
    ·
      refine ⟨31503626416227914213725261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42004835221637218951633681 31503626416227914213725261)
      ·
        refine ⟨11813859906085467830146973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31503626416227914213725261 11813859906085467830146973)
        ·
          refine ⟨4430197464782050436305115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11813859906085467830146973 4430197464782050436305115)
          ·
            refine ⟨6645296197173075654457673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4430197464782050436305115 6645296197173075654457673)
            ·
              refine ⟨4983972147879806740843255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6645296197173075654457673 4983972147879806740843255)
              ·
                refine ⟨7475958221819710111264883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4983972147879806740843255 7475958221819710111264883)
                ·
                  refine ⟨11213937332729565166897325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7475958221819710111264883 11213937332729565166897325)
                  ·
                    refine ⟨4205226499773586937586497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11213937332729565166897325 4205226499773586937586497)
                    ·
                      refine ⟨3153919874830190203189873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4205226499773586937586497 3153919874830190203189873)
                      ·
                        rfl

theorem cell23_6142237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 2, 1, 1, 3, 2].length) (baseStart_6142237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6142237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6142237 prefixEnd_6142237 := by exact prefixLift 6142237
  have htrace : WordTrace (prefixWord ++ tailWord_6142237) baseStart_6142237 baseEnd_6142237 := by
    simpa [prefixWord, tailWord_6142237, baseEnd_6142237] using wordTrace_append hprefix tailTrace_6142237
  have hstable : (prefixWord ++ tailWord_6142237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6142237).length < 2 ^ (prefixWord ++ tailWord_6142237).sum := by decide
  have hdescent : baseEnd_6142237 < baseStart_6142237 := by decide
  rcases family_descends (prefixWord ++ tailWord_6142237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6142239 : List Nat := [1, 1, 2, 4, 3, 1, 1, 5, 5]
def baseStart_6142239 : Nat := 118140960795 + 6142239 * 2 ^ 59
def prefixEnd_6142239 : Nat := 4983230072969 + 3 ^ 40 * 6142239 * 2
def baseEnd_6142239 : Nat := 350435655754611021707207

theorem tailTrace_6142239 : CollatzResearch.WordTrace tailWord_6142239 prefixEnd_6142239 350435655754611021707207 := by
  unfold tailWord_6142239
  simp only [CollatzResearch.WordTrace]
  refine ⟨224025860794724588750285771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149350573863149725833523847 224025860794724588750285771)
  ·
    refine ⟨336038791192086883125428657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224025860794724588750285771 336038791192086883125428657)
    ·
      refine ⟨252029093394065162344071493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 336038791192086883125428657 252029093394065162344071493)
      ·
        refine ⟨47255455011387217939513405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 252029093394065162344071493 47255455011387217939513405)
        ·
          refine ⟨17720795629270206727317527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47255455011387217939513405 17720795629270206727317527)
          ·
            refine ⟨26581193443905310090976291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17720795629270206727317527 26581193443905310090976291)
            ·
              refine ⟨39871790165857965136464437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26581193443905310090976291 39871790165857965136464437)
              ·
                refine ⟨3737980328049184231543541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39871790165857965136464437 3737980328049184231543541)
                ·
                  refine ⟨350435655754611021707207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3737980328049184231543541 350435655754611021707207)
                  ·
                    rfl

theorem cell23_6142239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 5, 5].length) (baseStart_6142239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6142239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6142239 prefixEnd_6142239 := by exact prefixLift 6142239
  have htrace : WordTrace (prefixWord ++ tailWord_6142239) baseStart_6142239 baseEnd_6142239 := by
    simpa [prefixWord, tailWord_6142239, baseEnd_6142239] using wordTrace_append hprefix tailTrace_6142239
  have hstable : (prefixWord ++ tailWord_6142239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6142239).length < 2 ^ (prefixWord ++ tailWord_6142239).sum := by decide
  have hdescent : baseEnd_6142239 < baseStart_6142239 := by decide
  rcases family_descends (prefixWord ++ tailWord_6142239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6142252 : List Nat := [2, 2, 1, 1, 1, 3, 2, 4, 2, 5]
def baseStart_6142252 : Nat := 118140960795 + 6142252 * 2 ^ 59
def prefixEnd_6142252 : Nat := 4983230072969 + 3 ^ 40 * 6142252 * 2
def baseEnd_6142252 : Nat := 1051309192346669214834101

theorem tailTrace_6142252 : CollatzResearch.WordTrace tailWord_6142252 prefixEnd_6142252 1051309192346669214834101 := by
  unfold tailWord_6142252
  simp only [CollatzResearch.WordTrace]
  refine ⟨112013167471838745985254505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149350889962451661313672673 112013167471838745985254505)
  ·
    refine ⟨84009875603879059488940879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112013167471838745985254505 84009875603879059488940879)
    ·
      refine ⟨126014813405818589233411319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84009875603879059488940879 126014813405818589233411319)
      ·
        refine ⟨189022220108727883850116979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126014813405818589233411319 189022220108727883850116979)
        ·
          refine ⟨283533330163091825775175469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189022220108727883850116979 283533330163091825775175469)
          ·
            refine ⟨106324998811159434665690801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 283533330163091825775175469 106324998811159434665690801)
            ·
              refine ⟨79743749108369575999268101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106324998811159434665690801 79743749108369575999268101)
              ·
                refine ⟨14951952957819295499862769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 79743749108369575999268101 14951952957819295499862769)
                ·
                  refine ⟨11213964718364471624897077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14951952957819295499862769 11213964718364471624897077)
                  ·
                    refine ⟨1051309192346669214834101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11213964718364471624897077 1051309192346669214834101)
                    ·
                      rfl

theorem cell23_6142252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 5].length) (baseStart_6142252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6142252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6142252 prefixEnd_6142252 := by exact prefixLift 6142252
  have htrace : WordTrace (prefixWord ++ tailWord_6142252) baseStart_6142252 baseEnd_6142252 := by
    simpa [prefixWord, tailWord_6142252, baseEnd_6142252] using wordTrace_append hprefix tailTrace_6142252
  have hstable : (prefixWord ++ tailWord_6142252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6142252).length < 2 ^ (prefixWord ++ tailWord_6142252).sum := by decide
  have hdescent : baseEnd_6142252 < baseStart_6142252 := by decide
  rcases family_descends (prefixWord ++ tailWord_6142252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6142272 : List Nat := [2, 1, 1, 2, 2, 1, 2, 1, 6, 1, 4]
def baseStart_6142272 : Nat := 118140960795 + 6142272 * 2 ^ 59
def prefixEnd_6142272 : Nat := 4983230072969 + 3 ^ 40 * 6142272 * 2
def baseEnd_6142272 : Nat := 3153937846653097566252211

theorem tailTrace_6142272 : CollatzResearch.WordTrace tailWord_6142272 prefixEnd_6142272 3153937846653097566252211 := by
  unfold tailWord_6142272
  simp only [CollatzResearch.WordTrace]
  refine ⟨112013532201802517693118535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149351376269070023590824713 112013532201802517693118535)
  ·
    refine ⟨168020298302703776539677803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112013532201802517693118535 168020298302703776539677803)
    ·
      refine ⟨252030447454055664809516705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168020298302703776539677803 252030447454055664809516705)
      ·
        refine ⟨189022835590541748607137529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 252030447454055664809516705 189022835590541748607137529)
        ·
          refine ⟨141767126692906311455353147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189022835590541748607137529 141767126692906311455353147)
          ·
            refine ⟨212650690039359467183029721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141767126692906311455353147 212650690039359467183029721)
            ·
              refine ⟨159488017529519600387272291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 212650690039359467183029721 159488017529519600387272291)
              ·
                refine ⟨239232026294279400580908437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 159488017529519600387272291 239232026294279400580908437)
                ·
                  refine ⟨11214001232544346902230083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 239232026294279400580908437 11214001232544346902230083)
                  ·
                    refine ⟨16821001848816520353345125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11214001232544346902230083 16821001848816520353345125)
                    ·
                      refine ⟨3153937846653097566252211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16821001848816520353345125 3153937846653097566252211)
                      ·
                        rfl

theorem cell23_6142272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 6, 1, 4].length) (baseStart_6142272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6142272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6142272 prefixEnd_6142272 := by exact prefixLift 6142272
  have htrace : WordTrace (prefixWord ++ tailWord_6142272) baseStart_6142272 baseEnd_6142272 := by
    simpa [prefixWord, tailWord_6142272, baseEnd_6142272] using wordTrace_append hprefix tailTrace_6142272
  have hstable : (prefixWord ++ tailWord_6142272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6142272).length < 2 ^ (prefixWord ++ tailWord_6142272).sum := by decide
  have hdescent : baseEnd_6142272 < baseStart_6142272 := by decide
  rcases family_descends (prefixWord ++ tailWord_6142272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6142306 : List Nat := [3, 3, 2, 1, 1, 3, 1, 2, 2, 1, 4]
def baseStart_6142306 : Nat := 118140960795 + 6142306 * 2 ^ 59
def prefixEnd_6142306 : Nat := 4983230072969 + 3 ^ 40 * 6142306 * 2
def baseEnd_6142306 : Nat := 3153955304995350433227055

theorem tailTrace_6142306 : CollatzResearch.WordTrace tailWord_6142306 prefixEnd_6142306 3153955304995350433227055 := by
  unfold tailWord_6142306
  simp only [CollatzResearch.WordTrace]
  refine ⟨56007076121370464798243693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149352202990321239461983181 56007076121370464798243693)
  ·
    refine ⟨21002653545513924299341385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56007076121370464798243693 21002653545513924299341385)
    ·
      refine ⟨15751990159135443224506039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21002653545513924299341385 15751990159135443224506039)
      ·
        refine ⟨23627985238703164836759059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15751990159135443224506039 23627985238703164836759059)
        ·
          refine ⟨35441977858054747255138589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23627985238703164836759059 35441977858054747255138589)
          ·
            refine ⟨13290741696770530220676971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35441977858054747255138589 13290741696770530220676971)
            ·
              refine ⟨19936112545155795331015457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13290741696770530220676971 19936112545155795331015457)
              ·
                refine ⟨14952084408866846498261593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19936112545155795331015457 14952084408866846498261593)
                ·
                  refine ⟨11214063306650134873696195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14952084408866846498261593 11214063306650134873696195)
                  ·
                    refine ⟨16821094959975202310544293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11214063306650134873696195 16821094959975202310544293)
                    ·
                      refine ⟨3153955304995350433227055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16821094959975202310544293 3153955304995350433227055)
                      ·
                        rfl

theorem cell23_6142306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_6142306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6142306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6142306 prefixEnd_6142306 := by exact prefixLift 6142306
  have htrace : WordTrace (prefixWord ++ tailWord_6142306) baseStart_6142306 baseEnd_6142306 := by
    simpa [prefixWord, tailWord_6142306, baseEnd_6142306] using wordTrace_append hprefix tailTrace_6142306
  have hstable : (prefixWord ++ tailWord_6142306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6142306).length < 2 ^ (prefixWord ++ tailWord_6142306).sum := by decide
  have hdescent : baseEnd_6142306 < baseStart_6142306 := by decide
  rcases family_descends (prefixWord ++ tailWord_6142306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6142309 : List Nat := [1, 3, 1, 3, 1, 3, 1, 1, 4, 2, 3]
def baseStart_6142309 : Nat := 118140960795 + 6142309 * 2 ^ 59
def prefixEnd_6142309 : Nat := 4983230072969 + 3 ^ 40 * 6142309 * 2
def baseEnd_6142309 : Nat := 3153956845437313921489541

theorem tailTrace_6142309 : CollatzResearch.WordTrace tailWord_6142309 prefixEnd_6142309 3153956845437313921489541 := by
  unfold tailWord_6142309
  simp only [CollatzResearch.WordTrace]
  refine ⟨224028413904470990705333981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149352275936313993803555987 224028413904470990705333981)
  ·
    refine ⟨84010655214176621514500243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 224028413904470990705333981 84010655214176621514500243)
    ·
      refine ⟨126015982821264932271750365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84010655214176621514500243 126015982821264932271750365)
      ·
        refine ⟨47255993557974349601906387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126015982821264932271750365 47255993557974349601906387)
        ·
          refine ⟨70883990336961524402859581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47255993557974349601906387 70883990336961524402859581)
          ·
            refine ⟨26581496376360571651072343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70883990336961524402859581 26581496376360571651072343)
            ·
              refine ⟨39872244564540857476608515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26581496376360571651072343 39872244564540857476608515)
              ·
                refine ⟨59808366846811286214912773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39872244564540857476608515 59808366846811286214912773)
                ·
                  refine ⟨11214068783777116165296145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59808366846811286214912773 11214068783777116165296145)
                  ·
                    refine ⟨8410551587832837123972109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11214068783777116165296145 8410551587832837123972109)
                    ·
                      refine ⟨3153956845437313921489541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8410551587832837123972109 3153956845437313921489541)
                      ·
                        rfl

theorem cell23_6142309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 4, 2, 3].length) (baseStart_6142309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6142309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6142309 prefixEnd_6142309 := by exact prefixLift 6142309
  have htrace : WordTrace (prefixWord ++ tailWord_6142309) baseStart_6142309 baseEnd_6142309 := by
    simpa [prefixWord, tailWord_6142309, baseEnd_6142309] using wordTrace_append hprefix tailTrace_6142309
  have hstable : (prefixWord ++ tailWord_6142309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6142309).length < 2 ^ (prefixWord ++ tailWord_6142309).sum := by decide
  have hdescent : baseEnd_6142309 < baseStart_6142309 := by decide
  rcases family_descends (prefixWord ++ tailWord_6142309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6142359 : List Nat := [1, 1, 3, 3, 1, 1, 2, 5, 1, 5]
def baseStart_6142359 : Nat := 118140960795 + 6142359 * 2 ^ 59
def prefixEnd_6142359 : Nat := 4983230072969 + 3 ^ 40 * 6142359 * 2
def baseEnd_6142359 : Nat := 1051327506490012908621437

theorem tailTrace_6142359 : CollatzResearch.WordTrace tailWord_6142359 prefixEnd_6142359 1051327506490012908621437 := by
  unfold tailWord_6142359
  simp only [CollatzResearch.WordTrace]
  refine ⟨224030237554289849244654131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149353491702859899496436087 224030237554289849244654131)
  ·
    refine ⟨336045356331434773866981197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224030237554289849244654131 336045356331434773866981197)
    ·
      refine ⟨126017008624288040200117949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 336045356331434773866981197 126017008624288040200117949)
      ·
        refine ⟨47256378234108015075044231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126017008624288040200117949 47256378234108015075044231)
        ·
          refine ⟨70884567351162022612566347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47256378234108015075044231 70884567351162022612566347)
          ·
            refine ⟨106326851026743033918849521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70884567351162022612566347 106326851026743033918849521)
            ·
              refine ⟨79745138270057275439137141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106326851026743033918849521 79745138270057275439137141)
              ·
                refine ⟨7476106712817869572419107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 79745138270057275439137141 7476106712817869572419107)
                ·
                  refine ⟨11214160069226804358628661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7476106712817869572419107 11214160069226804358628661)
                  ·
                    refine ⟨1051327506490012908621437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11214160069226804358628661 1051327506490012908621437)
                    ·
                      rfl

theorem cell23_6142359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 5, 1, 5].length) (baseStart_6142359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6142359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6142359 prefixEnd_6142359 := by exact prefixLift 6142359
  have htrace : WordTrace (prefixWord ++ tailWord_6142359) baseStart_6142359 baseEnd_6142359 := by
    simpa [prefixWord, tailWord_6142359, baseEnd_6142359] using wordTrace_append hprefix tailTrace_6142359
  have hstable : (prefixWord ++ tailWord_6142359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6142359).length < 2 ^ (prefixWord ++ tailWord_6142359).sum := by decide
  have hdescent : baseEnd_6142359 < baseStart_6142359 := by decide
  rcases family_descends (prefixWord ++ tailWord_6142359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6142373 : List Nat := [1, 3, 1, 2, 1, 1, 5, 4, 1, 1, 3]
def baseStart_6142373 : Nat := 118140960795 + 6142373 * 2 ^ 59
def prefixEnd_6142373 : Nat := 4983230072969 + 3 ^ 40 * 6142373 * 2
def baseEnd_6142373 : Nat := 3153989708199201671089247

theorem tailTrace_6142373 : CollatzResearch.WordTrace tailWord_6142373 prefixEnd_6142373 3153989708199201671089247 := by
  unfold tailWord_6142373
  simp only [CollatzResearch.WordTrace]
  refine ⟨224030748176239129635663773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149353832117492753090442515 224030748176239129635663773)
  ·
    refine ⟨84011530566089673613373915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 224030748176239129635663773 84011530566089673613373915)
    ·
      refine ⟨126017295849134510420060873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84011530566089673613373915 126017295849134510420060873)
      ·
        refine ⟨94512971886850882815045655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126017295849134510420060873 94512971886850882815045655)
        ·
          refine ⟨141769457830276324222568483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94512971886850882815045655 141769457830276324222568483)
          ·
            refine ⟨212654186745414486333852725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141769457830276324222568483 212654186745414486333852725)
            ·
              refine ⟨19936330007382608093798693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 212654186745414486333852725 19936330007382608093798693)
              ·
                refine ⟨3738061876384239017587255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19936330007382608093798693 3738061876384239017587255)
                ·
                  refine ⟨5607092814576358526380883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3738061876384239017587255 5607092814576358526380883)
                  ·
                    refine ⟨8410639221864537789571325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5607092814576358526380883 8410639221864537789571325)
                    ·
                      refine ⟨3153989708199201671089247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8410639221864537789571325 3153989708199201671089247)
                      ·
                        rfl

theorem cell23_6142373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 4, 1, 1, 3].length) (baseStart_6142373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6142373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6142373 prefixEnd_6142373 := by exact prefixLift 6142373
  have htrace : WordTrace (prefixWord ++ tailWord_6142373) baseStart_6142373 baseEnd_6142373 := by
    simpa [prefixWord, tailWord_6142373, baseEnd_6142373] using wordTrace_append hprefix tailTrace_6142373
  have hstable : (prefixWord ++ tailWord_6142373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6142373).length < 2 ^ (prefixWord ++ tailWord_6142373).sum := by decide
  have hdescent : baseEnd_6142373 < baseStart_6142373 := by decide
  rcases family_descends (prefixWord ++ tailWord_6142373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6142376 : List Nat := [2, 1, 6, 1, 1, 1, 1, 2, 3, 5]
def baseStart_6142376 : Nat := 118140960795 + 6142376 * 2 ^ 59
def prefixEnd_6142376 : Nat := 4983230072969 + 3 ^ 40 * 6142376 * 2
def baseEnd_6142376 : Nat := 1051330416213721719783911

theorem tailTrace_6142376 : CollatzResearch.WordTrace tailWord_6142376 prefixEnd_6142376 1051330416213721719783911 := by
  unfold tailWord_6142376
  simp only [CollatzResearch.WordTrace]
  refine ⟨112015428797614130574011491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149353905063485507432015321 112015428797614130574011491)
  ·
    refine ⟨168023143196421195861017237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112015428797614130574011491 168023143196421195861017237)
    ·
      refine ⟨7876084837332243555985183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 168023143196421195861017237 7876084837332243555985183)
      ·
        refine ⟨11814127255998365333977775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7876084837332243555985183 11814127255998365333977775)
        ·
          refine ⟨17721190883997548000966663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11814127255998365333977775 17721190883997548000966663)
          ·
            refine ⟨26581786325996322001449995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17721190883997548000966663 26581786325996322001449995)
            ·
              refine ⟨39872679488994483002174993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26581786325996322001449995 39872679488994483002174993)
              ·
                refine ⟨29904509616745862251631245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39872679488994483002174993 29904509616745862251631245)
                ·
                  refine ⟨11214191106279698344361717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29904509616745862251631245 11214191106279698344361717)
                  ·
                    refine ⟨1051330416213721719783911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11214191106279698344361717 1051330416213721719783911)
                    ·
                      rfl

theorem cell23_6142376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_6142376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6142376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6142376 prefixEnd_6142376 := by exact prefixLift 6142376
  have htrace : WordTrace (prefixWord ++ tailWord_6142376) baseStart_6142376 baseEnd_6142376 := by
    simpa [prefixWord, tailWord_6142376, baseEnd_6142376] using wordTrace_append hprefix tailTrace_6142376
  have hstable : (prefixWord ++ tailWord_6142376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6142376).length < 2 ^ (prefixWord ++ tailWord_6142376).sum := by decide
  have hdescent : baseEnd_6142376 < baseStart_6142376 := by decide
  rcases family_descends (prefixWord ++ tailWord_6142376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6142396 : List Nat := [2, 2, 2, 4, 1, 1, 2, 1, 3, 1, 4]
def baseStart_6142396 : Nat := 118140960795 + 6142396 * 2 ^ 59
def prefixEnd_6142396 : Nat := 4983230072969 + 3 ^ 40 * 6142396 * 2
def baseEnd_6142396 : Nat := 3154001518254255081101641

theorem tailTrace_6142396 : CollatzResearch.WordTrace tailWord_6142396 prefixEnd_6142396 3154001518254255081101641 := by
  unfold tailWord_6142396
  simp only [CollatzResearch.WordTrace]
  refine ⟨112015793527577902281875521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149354391370103869709167361 112015793527577902281875521)
  ·
    refine ⟨84011845145683426711406641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112015793527577902281875521 84011845145683426711406641)
    ·
      refine ⟨63008883859262570033554981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84011845145683426711406641 63008883859262570033554981)
      ·
        refine ⟨11814165723611731881291559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63008883859262570033554981 11814165723611731881291559)
        ·
          refine ⟨17721248585417597821937339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11814165723611731881291559 17721248585417597821937339)
          ·
            refine ⟨26581872878126396732906009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17721248585417597821937339 26581872878126396732906009)
            ·
              refine ⟨19936404658594797549679507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26581872878126396732906009 19936404658594797549679507)
              ·
                refine ⟨29904606987892196324519261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19936404658594797549679507 29904606987892196324519261)
                ·
                  refine ⟨11214227620459573621694723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29904606987892196324519261 11214227620459573621694723)
                  ·
                    refine ⟨16821341430689360432542085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11214227620459573621694723 16821341430689360432542085)
                    ·
                      refine ⟨3154001518254255081101641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16821341430689360432542085 3154001518254255081101641)
                      ·
                        rfl

theorem cell23_6142396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_6142396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6142396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6142396 prefixEnd_6142396 := by exact prefixLift 6142396
  have htrace : WordTrace (prefixWord ++ tailWord_6142396) baseStart_6142396 baseEnd_6142396 := by
    simpa [prefixWord, tailWord_6142396, baseEnd_6142396] using wordTrace_append hprefix tailTrace_6142396
  have hstable : (prefixWord ++ tailWord_6142396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6142396).length < 2 ^ (prefixWord ++ tailWord_6142396).sum := by decide
  have hdescent : baseEnd_6142396 < baseStart_6142396 := by decide
  rcases family_descends (prefixWord ++ tailWord_6142396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6142409 : List Nat := [1, 2, 1, 1, 2, 1, 6, 2, 1, 2, 4]
def baseStart_6142409 : Nat := 118140960795 + 6142409 * 2 ^ 59
def prefixEnd_6142409 : Nat := 4983230072969 + 3 ^ 40 * 6142409 * 2
def baseEnd_6142409 : Nat := 3154008193502763530239081

theorem tailTrace_6142409 : CollatzResearch.WordTrace tailWord_6142409 prefixEnd_6142409 3154008193502763530239081 := by
  unfold tailWord_6142409
  simp only [CollatzResearch.WordTrace]
  refine ⟨224032061204108707783974281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149354707469405805189316187 224032061204108707783974281)
  ·
    refine ⟨168024045903081530837980711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224032061204108707783974281 168024045903081530837980711)
    ·
      refine ⟨252036068854622296256971067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168024045903081530837980711 252036068854622296256971067)
      ·
        refine ⟨378054103281933444385456601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252036068854622296256971067 378054103281933444385456601)
        ·
          refine ⟨283540577461450083289092451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 378054103281933444385456601 283540577461450083289092451)
          ·
            refine ⟨425310866192175124933638677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 283540577461450083289092451 425310866192175124933638677)
            ·
              refine ⟨19936446852758208981264313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 425310866192175124933638677 19936446852758208981264313)
              ·
                refine ⟨14952335139568656735948235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19936446852758208981264313 14952335139568656735948235)
                ·
                  refine ⟨22428502709352985103922353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14952335139568656735948235 22428502709352985103922353)
                  ·
                    refine ⟨16821377032014738827941765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22428502709352985103922353 16821377032014738827941765)
                    ·
                      refine ⟨3154008193502763530239081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16821377032014738827941765 3154008193502763530239081)
                      ·
                        rfl

theorem cell23_6142409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 2, 1, 2, 4].length) (baseStart_6142409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6142409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6142409 prefixEnd_6142409 := by exact prefixLift 6142409
  have htrace : WordTrace (prefixWord ++ tailWord_6142409) baseStart_6142409 baseEnd_6142409 := by
    simpa [prefixWord, tailWord_6142409, baseEnd_6142409] using wordTrace_append hprefix tailTrace_6142409
  have hstable : (prefixWord ++ tailWord_6142409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6142409).length < 2 ^ (prefixWord ++ tailWord_6142409).sum := by decide
  have hdescent : baseEnd_6142409 < baseStart_6142409 := by decide
  rcases family_descends (prefixWord ++ tailWord_6142409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6142450 : List Nat := [3, 2, 1, 4, 2, 1, 2, 2, 1, 2, 3]
def baseStart_6142450 : Nat := 118140960795 + 6142450 * 2 ^ 59
def prefixEnd_6142450 : Nat := 4983230072969 + 3 ^ 40 * 6142450 * 2
def baseEnd_6142450 : Nat := 3154029246209597869826393

theorem tailTrace_6142450 : CollatzResearch.WordTrace tailWord_6142450 prefixEnd_6142450 3154029246209597869826393 := by
  unfold tailWord_6142450
  simp only [CollatzResearch.WordTrace]
  refine ⟨56008389149240042946554201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149355704397973447857477869 56008389149240042946554201)
  ·
    refine ⟨42006291861930032209915651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56008389149240042946554201 42006291861930032209915651)
    ·
      refine ⟨63009437792895048314873477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42006291861930032209915651 63009437792895048314873477)
      ·
        refine ⟨11814269586167821559038777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63009437792895048314873477 11814269586167821559038777)
        ·
          refine ⟨8860702189625866169279083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11814269586167821559038777 8860702189625866169279083)
          ·
            refine ⟨13291053284438799253918625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8860702189625866169279083 13291053284438799253918625)
            ·
              refine ⟨9968289963329099440438969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13291053284438799253918625 9968289963329099440438969)
              ·
                refine ⟨7476217472496824580329227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9968289963329099440438969 7476217472496824580329227)
                ·
                  refine ⟨11214326208745236870493841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7476217472496824580329227 11214326208745236870493841)
                  ·
                    refine ⟨8410744656558927652870381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11214326208745236870493841 8410744656558927652870381)
                    ·
                      refine ⟨3154029246209597869826393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8410744656558927652870381 3154029246209597869826393)
                      ·
                        rfl

theorem cell23_6142450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_6142450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6142450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6142450 prefixEnd_6142450 := by exact prefixLift 6142450
  have htrace : WordTrace (prefixWord ++ tailWord_6142450) baseStart_6142450 baseEnd_6142450 := by
    simpa [prefixWord, tailWord_6142450, baseEnd_6142450] using wordTrace_append hprefix tailTrace_6142450
  have hstable : (prefixWord ++ tailWord_6142450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6142450).length < 2 ^ (prefixWord ++ tailWord_6142450).sum := by decide
  have hdescent : baseEnd_6142450 < baseStart_6142450 := by decide
  rcases family_descends (prefixWord ++ tailWord_6142450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6142470 : List Nat := [6, 2, 1, 1, 1, 3, 9]
def baseStart_6142470 : Nat := 118140960795 + 6142470 * 2 ^ 59
def prefixEnd_6142470 : Nat := 4983230072969 + 3 ^ 40 * 6142470 * 2
def baseEnd_6142470 : Nat := 38938759454601083846621

theorem tailTrace_6142470 : CollatzResearch.WordTrace tailWord_6142470 prefixEnd_6142470 38938759454601083846621 := by
  unfold tailWord_6142470
  simp only [CollatzResearch.WordTrace]
  refine ⟨7001071439277741100060777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 149356190704591810134629909 7001071439277741100060777)
  ·
    refine ⟨5250803579458305825045583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7001071439277741100060777 5250803579458305825045583)
    ·
      refine ⟨7876205369187458737568375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5250803579458305825045583 7876205369187458737568375)
      ·
        refine ⟨11814308053781188106352563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7876205369187458737568375 11814308053781188106352563)
        ·
          refine ⟨17721462080671782159528845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11814308053781188106352563 17721462080671782159528845)
          ·
            refine ⟨6645548280251918309823317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17721462080671782159528845 6645548280251918309823317)
            ·
              refine ⟨38938759454601083846621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6645548280251918309823317 38938759454601083846621)
              ·
                rfl

theorem cell23_6142470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 9].length) (baseStart_6142470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6142470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6142470 prefixEnd_6142470 := by exact prefixLift 6142470
  have htrace : WordTrace (prefixWord ++ tailWord_6142470) baseStart_6142470 baseEnd_6142470 := by
    simpa [prefixWord, tailWord_6142470, baseEnd_6142470] using wordTrace_append hprefix tailTrace_6142470
  have hstable : (prefixWord ++ tailWord_6142470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6142470).length < 2 ^ (prefixWord ++ tailWord_6142470).sum := by decide
  have hdescent : baseEnd_6142470 < baseStart_6142470 := by decide
  rcases family_descends (prefixWord ++ tailWord_6142470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6142489 : List Nat := [1, 2, 1, 2, 1, 1, 2, 3, 1, 6, 3]
def baseStart_6142489 : Nat := 118140960795 + 6142489 * 2 ^ 59
def prefixEnd_6142489 : Nat := 4983230072969 + 3 ^ 40 * 6142489 * 2
def baseEnd_6142489 : Nat := 3154049271955123217238713

theorem tailTrace_6142489 : CollatzResearch.WordTrace tailWord_6142489 prefixEnd_6142489 3154049271955123217238713 := by
  unfold tailWord_6142489
  simp only [CollatzResearch.WordTrace]
  refine ⟨224034979043818881446886521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149356652695879254297924347 224034979043818881446886521)
  ·
    refine ⟨168026234282864161085164891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224034979043818881446886521 168026234282864161085164891)
    ·
      refine ⟨252039351424296241627747337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168026234282864161085164891 252039351424296241627747337)
      ·
        refine ⟨189029513568222181220810503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 252039351424296241627747337 189029513568222181220810503)
        ·
          refine ⟨283544270352333271831215755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189029513568222181220810503 283544270352333271831215755)
          ·
            refine ⟨425316405528499907746823633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 283544270352333271831215755 425316405528499907746823633)
            ·
              refine ⟨318987304146374930810117725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 425316405528499907746823633 318987304146374930810117725)
              ·
                refine ⟨119620239054890599053794147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 318987304146374930810117725 119620239054890599053794147)
                ·
                  refine ⟨179430358582335898580691221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 119620239054890599053794147 179430358582335898580691221)
                  ·
                    refine ⟨8410798058546995245969901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 179430358582335898580691221 8410798058546995245969901)
                    ·
                      refine ⟨3154049271955123217238713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8410798058546995245969901 3154049271955123217238713)
                      ·
                        rfl

theorem cell23_6142489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 6, 3].length) (baseStart_6142489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6142489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6142489 prefixEnd_6142489 := by exact prefixLift 6142489
  have htrace : WordTrace (prefixWord ++ tailWord_6142489) baseStart_6142489 baseEnd_6142489 := by
    simpa [prefixWord, tailWord_6142489, baseEnd_6142489] using wordTrace_append hprefix tailTrace_6142489
  have hstable : (prefixWord ++ tailWord_6142489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6142489).length < 2 ^ (prefixWord ++ tailWord_6142489).sum := by decide
  have hdescent : baseEnd_6142489 < baseStart_6142489 := by decide
  rcases family_descends (prefixWord ++ tailWord_6142489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6142506 : List Nat := [3, 1, 4, 1, 1, 2, 1, 2, 2, 1, 5]
def baseStart_6142506 : Nat := 118140960795 + 6142506 * 2 ^ 59
def prefixEnd_6142506 : Nat := 4983230072969 + 3 ^ 40 * 6142506 * 2
def baseEnd_6142506 : Nat := 3154058001126249650726135

theorem tailTrace_6142506 : CollatzResearch.WordTrace tailWord_6142506 prefixEnd_6142506 3154058001126249650726135 := by
  unfold tailWord_6142506
  simp only [CollatzResearch.WordTrace]
  refine ⟨56008899771189323337563843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149357066056504862233503581 56008899771189323337563843)
  ·
    refine ⟨84013349656783985006345765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56008899771189323337563843 84013349656783985006345765)
    ·
      refine ⟨15752503060646997188689831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84013349656783985006345765 15752503060646997188689831)
      ·
        refine ⟨23628754590970495783034747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15752503060646997188689831 23628754590970495783034747)
        ·
          refine ⟨35443131886455743674552121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23628754590970495783034747 35443131886455743674552121)
          ·
            refine ⟨26582348914841807755914091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35443131886455743674552121 26582348914841807755914091)
            ·
              refine ⟨39873523372262711633871137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26582348914841807755914091 39873523372262711633871137)
              ·
                refine ⟨29905142529197033725403353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39873523372262711633871137 29905142529197033725403353)
                ·
                  refine ⟨22428856896897775294052515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29905142529197033725403353 22428856896897775294052515)
                  ·
                    refine ⟨33643285345346662941078773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22428856896897775294052515 33643285345346662941078773)
                    ·
                      refine ⟨3154058001126249650726135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33643285345346662941078773 3154058001126249650726135)
                      ·
                        rfl

theorem cell23_6142506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_6142506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6142506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6142506 prefixEnd_6142506 := by exact prefixLift 6142506
  have htrace : WordTrace (prefixWord ++ tailWord_6142506) baseStart_6142506 baseEnd_6142506 := by
    simpa [prefixWord, tailWord_6142506, baseEnd_6142506] using wordTrace_append hprefix tailTrace_6142506
  have hstable : (prefixWord ++ tailWord_6142506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6142506).length < 2 ^ (prefixWord ++ tailWord_6142506).sum := by decide
  have hdescent : baseEnd_6142506 < baseStart_6142506 := by decide
  rcases family_descends (prefixWord ++ tailWord_6142506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6142543 : List Nat := [1, 1, 2, 1, 1, 2, 8, 2, 5]
def baseStart_6142543 : Nat := 118140960795 + 6142543 * 2 ^ 59
def prefixEnd_6142543 : Nat := 4983230072969 + 3 ^ 40 * 6142543 * 2
def baseEnd_6142543 : Nat := 350452999990051778440385

theorem tailTrace_6142543 : CollatzResearch.WordTrace tailWord_6142543 prefixEnd_6142543 350452999990051778440385 := by
  unfold tailWord_6142543
  simp only [CollatzResearch.WordTrace]
  refine ⟨224036948585623248669352283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149357965723748832446234855 224036948585623248669352283)
  ·
    refine ⟨336055422878434873004028425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224036948585623248669352283 336055422878434873004028425)
    ·
      refine ⟨252041567158826154753021319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 336055422878434873004028425 252041567158826154753021319)
      ·
        refine ⟨378062350738239232129531979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252041567158826154753021319 378062350738239232129531979)
        ·
          refine ⟨567093526107358848194297969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 378062350738239232129531979 567093526107358848194297969)
          ·
            refine ⟨425320144580519136145723477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 567093526107358848194297969 425320144580519136145723477)
            ·
              refine ⟨4984220444302958626707697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 425320144580519136145723477 4984220444302958626707697)
              ·
                refine ⟨3738165333227218970030773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4984220444302958626707697 3738165333227218970030773)
                ·
                  refine ⟨350452999990051778440385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3738165333227218970030773 350452999990051778440385)
                  ·
                    rfl

theorem cell23_6142543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 8, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 8, 2, 5].length) (baseStart_6142543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6142543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6142543 prefixEnd_6142543 := by exact prefixLift 6142543
  have htrace : WordTrace (prefixWord ++ tailWord_6142543) baseStart_6142543 baseEnd_6142543 := by
    simpa [prefixWord, tailWord_6142543, baseEnd_6142543] using wordTrace_append hprefix tailTrace_6142543
  have hstable : (prefixWord ++ tailWord_6142543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6142543).length < 2 ^ (prefixWord ++ tailWord_6142543).sum := by decide
  have hdescent : baseEnd_6142543 < baseStart_6142543 := by decide
  rcases family_descends (prefixWord ++ tailWord_6142543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6142573 : List Nat := [1, 5, 1, 1, 3, 1, 3, 1, 2, 5]
def baseStart_6142573 : Nat := 118140960795 + 6142573 * 2 ^ 59
def prefixEnd_6142573 : Nat := 4983230072969 + 3 ^ 40 * 6142573 * 2
def baseEnd_6142573 : Nat := 1051364134776700296196109

theorem tailTrace_6142573 : CollatzResearch.WordTrace tailWord_6142573 prefixEnd_6142573 1051364134776700296196109 := by
  unfold tailWord_6142573
  simp only [CollatzResearch.WordTrace]
  refine ⟨224038042775514563792944373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149358695183676375861962915 224038042775514563792944373)
  ·
    refine ⟨21003566510204490355588535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 224038042775514563792944373 21003566510204490355588535)
    ·
      refine ⟨31505349765306735533382803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21003566510204490355588535 31505349765306735533382803)
      ·
        refine ⟨47258024647960103300074205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31505349765306735533382803 47258024647960103300074205)
        ·
          refine ⟨17721759242985038737527827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47258024647960103300074205 17721759242985038737527827)
          ·
            refine ⟨26582638864477558106291741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17721759242985038737527827 26582638864477558106291741)
            ·
              refine ⟨9968489574179084289859403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26582638864477558106291741 9968489574179084289859403)
              ·
                refine ⟨14952734361268626434789105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9968489574179084289859403 14952734361268626434789105)
                ·
                  refine ⟨11214550770951469826091829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14952734361268626434789105 11214550770951469826091829)
                  ·
                    refine ⟨1051364134776700296196109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11214550770951469826091829 1051364134776700296196109)
                    ·
                      rfl

theorem cell23_6142573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 3, 1, 2, 5].length) (baseStart_6142573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6142573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6142573 prefixEnd_6142573 := by exact prefixLift 6142573
  have htrace : WordTrace (prefixWord ++ tailWord_6142573) baseStart_6142573 baseEnd_6142573 := by
    simpa [prefixWord, tailWord_6142573, baseEnd_6142573] using wordTrace_append hprefix tailTrace_6142573
  have hstable : (prefixWord ++ tailWord_6142573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6142573).length < 2 ^ (prefixWord ++ tailWord_6142573).sum := by decide
  have hdescent : baseEnd_6142573 < baseStart_6142573 := by decide
  rcases family_descends (prefixWord ++ tailWord_6142573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6142579 : List Nat := [1, 1, 1, 2, 2, 1, 1, 4, 2, 3, 5]
def baseStart_6142579 : Nat := 118140960795 + 6142579 * 2 ^ 59
def prefixEnd_6142579 : Nat := 4983230072969 + 3 ^ 40 * 6142579 * 2
def baseEnd_6142579 : Nat := 3154095485214027865113299

theorem tailTrace_6142579 : CollatzResearch.WordTrace tailWord_6142579 prefixEnd_6142579 3154095485214027865113299 := by
  unfold tailWord_6142579
  simp only [CollatzResearch.WordTrace]
  refine ⟨224038261613492826817662791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149358841075661884545108527 224038261613492826817662791)
  ·
    refine ⟨336057392420239240226494187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224038261613492826817662791 336057392420239240226494187)
    ·
      refine ⟨504086088630358860339741281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 336057392420239240226494187 504086088630358860339741281)
      ·
        refine ⟨378064566472769145254805961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 504086088630358860339741281 378064566472769145254805961)
        ·
          refine ⟨283548424854576858941104471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 378064566472769145254805961 283548424854576858941104471)
          ·
            refine ⟨425322637281865288411656707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 283548424854576858941104471 425322637281865288411656707)
            ·
              refine ⟨637983955922797932617485061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 425322637281865288411656707 637983955922797932617485061)
              ·
                refine ⟨119621991735524612365778449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 637983955922797932617485061 119621991735524612365778449)
                ·
                  refine ⟨89716493801643459274333837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 119621991735524612365778449 89716493801643459274333837)
                  ·
                    refine ⟨33643685175616297227875189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 89716493801643459274333837 33643685175616297227875189)
                    ·
                      refine ⟨3154095485214027865113299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33643685175616297227875189 3154095485214027865113299)
                      ·
                        rfl

theorem cell23_6142579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 2, 3, 5].length) (baseStart_6142579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6142579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6142579 prefixEnd_6142579 := by exact prefixLift 6142579
  have htrace : WordTrace (prefixWord ++ tailWord_6142579) baseStart_6142579 baseEnd_6142579 := by
    simpa [prefixWord, tailWord_6142579, baseEnd_6142579] using wordTrace_append hprefix tailTrace_6142579
  have hstable : (prefixWord ++ tailWord_6142579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6142579).length < 2 ^ (prefixWord ++ tailWord_6142579).sum := by decide
  have hdescent : baseEnd_6142579 < baseStart_6142579 := by decide
  rcases family_descends (prefixWord ++ tailWord_6142579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6142593 : List Nat := [1, 2, 4, 2, 1, 1, 1, 1, 4, 4, 2]
def baseStart_6142593 : Nat := 118140960795 + 6142593 * 2 ^ 59
def prefixEnd_6142593 : Nat := 4983230072969 + 3 ^ 40 * 6142593 * 2
def baseEnd_6142593 : Nat := 3154102673943190810338235

theorem tailTrace_6142593 : CollatzResearch.WordTrace tailWord_6142593 prefixEnd_6142593 3154102673943190810338235 := by
  unfold tailWord_6142593
  simp only [CollatzResearch.WordTrace]
  refine ⟨224038772235442107208672433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149359181490294738139114955 224038772235442107208672433)
  ·
    refine ⟨168029079176581580406504325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224038772235442107208672433 168029079176581580406504325)
    ·
      refine ⟨31505452345609046326219561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 168029079176581580406504325 31505452345609046326219561)
      ·
        refine ⟨23629089259206784744664671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31505452345609046326219561 23629089259206784744664671)
        ·
          refine ⟨35443633888810177116997007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23629089259206784744664671 35443633888810177116997007)
          ·
            refine ⟨53165450833215265675495511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35443633888810177116997007 53165450833215265675495511)
            ·
              refine ⟨79748176249822898513243267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53165450833215265675495511 79748176249822898513243267)
              ·
                refine ⟨119622264374734347769864901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79748176249822898513243267 119622264374734347769864901)
                ·
                  refine ⟨22429174570262690206849669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 119622264374734347769864901 22429174570262690206849669)
                  ·
                    refine ⟨4205470231924254413784313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22429174570262690206849669 4205470231924254413784313)
                    ·
                      refine ⟨3154102673943190810338235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4205470231924254413784313 3154102673943190810338235)
                      ·
                        rfl

theorem cell23_6142593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 1, 4, 4, 2].length) (baseStart_6142593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6142593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6142593 prefixEnd_6142593 := by exact prefixLift 6142593
  have htrace : WordTrace (prefixWord ++ tailWord_6142593) baseStart_6142593 baseEnd_6142593 := by
    simpa [prefixWord, tailWord_6142593, baseEnd_6142593] using wordTrace_append hprefix tailTrace_6142593
  have hstable : (prefixWord ++ tailWord_6142593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6142593).length < 2 ^ (prefixWord ++ tailWord_6142593).sum := by decide
  have hdescent : baseEnd_6142593 < baseStart_6142593 := by decide
  rcases family_descends (prefixWord ++ tailWord_6142593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6142606 : List Nat := [4, 1, 1, 3, 1, 1, 1, 2, 2, 1, 6]
def baseStart_6142606 : Nat := 118140960795 + 6142606 * 2 ^ 59
def prefixEnd_6142606 : Nat := 4983230072969 + 3 ^ 40 * 6142606 * 2
def baseEnd_6142606 : Nat := 3154109349191699259475675

theorem tailTrace_6142606 : CollatzResearch.WordTrace tailWord_6142606 prefixEnd_6142606 3154109349191699259475675 := by
  unfold tailWord_6142606
  simp only [CollatzResearch.WordTrace]
  refine ⟨28004905798049376303611959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149359497589596673619263781 28004905798049376303611959)
  ·
    refine ⟨42007358697074064455417939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28004905798049376303611959 42007358697074064455417939)
    ·
      refine ⟨63011038045611096683126909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42007358697074064455417939 63011038045611096683126909)
      ·
        refine ⟨23629139267104161256172591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63011038045611096683126909 23629139267104161256172591)
        ·
          refine ⟨35443708900656241884258887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23629139267104161256172591 35443708900656241884258887)
          ·
            refine ⟨53165563350984362826388331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35443708900656241884258887 53165563350984362826388331)
            ·
              refine ⟨79748345026476544239582497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53165563350984362826388331 79748345026476544239582497)
              ·
                refine ⟨59811258769857408179686873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79748345026476544239582497 59811258769857408179686873)
                ·
                  refine ⟨44858444077393056134765155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59811258769857408179686873 44858444077393056134765155)
                  ·
                    refine ⟨67287666116089584202147733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44858444077393056134765155 67287666116089584202147733)
                    ·
                      refine ⟨3154109349191699259475675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67287666116089584202147733 3154109349191699259475675)
                      ·
                        rfl

theorem cell23_6142606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_6142606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6142606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6142606 prefixEnd_6142606 := by exact prefixLift 6142606
  have htrace : WordTrace (prefixWord ++ tailWord_6142606) baseStart_6142606 baseEnd_6142606 := by
    simpa [prefixWord, tailWord_6142606, baseEnd_6142606] using wordTrace_append hprefix tailTrace_6142606
  have hstable : (prefixWord ++ tailWord_6142606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6142606).length < 2 ^ (prefixWord ++ tailWord_6142606).sum := by decide
  have hdescent : baseEnd_6142606 < baseStart_6142606 := by decide
  rcases family_descends (prefixWord ++ tailWord_6142606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6142609 : List Nat := [1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 9]
def baseStart_6142609 : Nat := 118140960795 + 6142609 * 2 ^ 59
def prefixEnd_6142609 : Nat := 4983230072969 + 3 ^ 40 * 6142609 * 2
def baseEnd_6142609 : Nat := 3154110889633662747738161

theorem tailTrace_6142609 : CollatzResearch.WordTrace tailWord_6142609 prefixEnd_6142609 3154110889633662747738161 := by
  unfold tailWord_6142609
  simp only [CollatzResearch.WordTrace]
  refine ⟨224039355803384141941254881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149359570535589427960836587 224039355803384141941254881)
  ·
    refine ⟨168029516852538106455941161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224039355803384141941254881 168029516852538106455941161)
    ·
      refine ⟨126022137639403579841955871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168029516852538106455941161 126022137639403579841955871)
      ·
        refine ⟨189033206459105369762933807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126022137639403579841955871 189033206459105369762933807)
        ·
          refine ⟨283549809688658054644400711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189033206459105369762933807 283549809688658054644400711)
          ·
            refine ⟨425324714532987081966601067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 283549809688658054644400711 425324714532987081966601067)
            ·
              refine ⟨637987071799480622949901601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 425324714532987081966601067 637987071799480622949901601)
              ·
                refine ⟨478490303849610467212426201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 637987071799480622949901601 478490303849610467212426201)
                ·
                  refine ⟨358867727887207850409319651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 478490303849610467212426201 358867727887207850409319651)
                  ·
                    refine ⟨538301591830811775613979477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 358867727887207850409319651 538301591830811775613979477)
                    ·
                      refine ⟨3154110889633662747738161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 538301591830811775613979477 3154110889633662747738161)
                      ·
                        rfl

theorem cell23_6142609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 9].length) (baseStart_6142609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6142609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6142609 prefixEnd_6142609 := by exact prefixLift 6142609
  have htrace : WordTrace (prefixWord ++ tailWord_6142609) baseStart_6142609 baseEnd_6142609 := by
    simpa [prefixWord, tailWord_6142609, baseEnd_6142609] using wordTrace_append hprefix tailTrace_6142609
  have hstable : (prefixWord ++ tailWord_6142609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6142609).length < 2 ^ (prefixWord ++ tailWord_6142609).sum := by decide
  have hdescent : baseEnd_6142609 < baseStart_6142609 := by decide
  rcases family_descends (prefixWord ++ tailWord_6142609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6142610 : List Nat := [3, 2, 3, 1, 2, 1, 2, 1, 2, 4, 2]
def baseStart_6142610 : Nat := 118140960795 + 6142610 * 2 ^ 59
def prefixEnd_6142610 : Nat := 4983230072969 + 3 ^ 40 * 6142610 * 2
def baseEnd_6142610 : Nat := 3154111403114317243825657

theorem tailTrace_6142610 : CollatzResearch.WordTrace tailWord_6142610 prefixEnd_6142610 3154111403114317243825657 := by
  unfold tailWord_6142610
  simp only [CollatzResearch.WordTrace]
  refine ⟨56009848069095129778010321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149359594850920346074694189 56009848069095129778010321)
  ·
    refine ⟨42007386051821347333507741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56009848069095129778010321 42007386051821347333507741)
    ·
      refine ⟨15752769769433005250065403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42007386051821347333507741 15752769769433005250065403)
      ·
        refine ⟨23629154654149507875098105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15752769769433005250065403 23629154654149507875098105)
        ·
          refine ⟨17721865990612130906323579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23629154654149507875098105 17721865990612130906323579)
          ·
            refine ⟨26582798985918196359485369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17721865990612130906323579 26582798985918196359485369)
            ·
              refine ⟨19937099239438647269614027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26582798985918196359485369 19937099239438647269614027)
              ·
                refine ⟨29905648859157970904421041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19937099239438647269614027 29905648859157970904421041)
                ·
                  refine ⟨22429236644368478178315781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29905648859157970904421041 22429236644368478178315781)
                  ·
                    refine ⟨4205481870819089658434209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22429236644368478178315781 4205481870819089658434209)
                    ·
                      refine ⟨3154111403114317243825657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4205481870819089658434209 3154111403114317243825657)
                      ·
                        rfl

theorem cell23_6142610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 1, 2, 4, 2].length) (baseStart_6142610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6142610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6142610 prefixEnd_6142610 := by exact prefixLift 6142610
  have htrace : WordTrace (prefixWord ++ tailWord_6142610) baseStart_6142610 baseEnd_6142610 := by
    simpa [prefixWord, tailWord_6142610, baseEnd_6142610] using wordTrace_append hprefix tailTrace_6142610
  have hstable : (prefixWord ++ tailWord_6142610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6142610).length < 2 ^ (prefixWord ++ tailWord_6142610).sum := by decide
  have hdescent : baseEnd_6142610 < baseStart_6142610 := by decide
  rcases family_descends (prefixWord ++ tailWord_6142610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6142637 : List Nat := [1, 5, 2, 1, 1, 2, 3, 3, 1, 4]
def baseStart_6142637 : Nat := 118140960795 + 6142637 * 2 ^ 59
def prefixEnd_6142637 : Nat := 4983230072969 + 3 ^ 40 * 6142637 * 2
def baseEnd_6142637 : Nat := 1051375089030662879396011

theorem tailTrace_6142637 : CollatzResearch.WordTrace tailWord_6142637 prefixEnd_6142637 1051375089030662879396011 := by
  unfold tailWord_6142637
  simp only [CollatzResearch.WordTrace]
  refine ⟨224040377047282702723274165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149360251364855135148849443 224040377047282702723274165)
  ·
    refine ⟨21003785348182753380306953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 224040377047282702723274165 21003785348182753380306953)
    ·
      refine ⟨15752839011137065035230215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21003785348182753380306953 15752839011137065035230215)
      ·
        refine ⟨23629258516705597552845323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15752839011137065035230215 23629258516705597552845323)
        ·
          refine ⟨35443887775058396329267985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23629258516705597552845323 35443887775058396329267985)
          ·
            refine ⟨26582915831293797246950989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35443887775058396329267985 26582915831293797246950989)
            ·
              refine ⟨9968593436735173967606621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26582915831293797246950989 9968593436735173967606621)
              ·
                refine ⟨3738222538775690237852483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9968593436735173967606621 3738222538775690237852483)
                ·
                  refine ⟨5607333808163535356778725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3738222538775690237852483 5607333808163535356778725)
                  ·
                    refine ⟨1051375089030662879396011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5607333808163535356778725 1051375089030662879396011)
                    ·
                      rfl

theorem cell23_6142637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 3, 3, 1, 4].length) (baseStart_6142637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6142637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6142637 prefixEnd_6142637 := by exact prefixLift 6142637
  have htrace : WordTrace (prefixWord ++ tailWord_6142637) baseStart_6142637 baseEnd_6142637 := by
    simpa [prefixWord, tailWord_6142637, baseEnd_6142637] using wordTrace_append hprefix tailTrace_6142637
  have hstable : (prefixWord ++ tailWord_6142637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6142637).length < 2 ^ (prefixWord ++ tailWord_6142637).sum := by decide
  have hdescent : baseEnd_6142637 < baseStart_6142637 := by decide
  rcases family_descends (prefixWord ++ tailWord_6142637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6142680 : List Nat := [2, 1, 2, 2, 3, 4, 1, 2, 1, 5]
def baseStart_6142680 : Nat := 118140960795 + 6142680 * 2 ^ 59
def prefixEnd_6142680 : Nat := 4983230072969 + 3 ^ 40 * 6142680 * 2
def baseEnd_6142680 : Nat := 1051382448920043989983445

theorem tailTrace_6142680 : CollatzResearch.WordTrace tailWord_6142680 prefixEnd_6142680 1051382448920043989983445 := by
  unfold tailWord_6142680
  simp only [CollatzResearch.WordTrace]
  refine ⟨112020972693063460533544747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149361296924084614044726329 112020972693063460533544747)
  ·
    refine ⟨168031459039595190800317121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112020972693063460533544747 168031459039595190800317121)
    ·
      refine ⟨126023594279696393100237841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168031459039595190800317121 126023594279696393100237841)
      ·
        refine ⟨94517695709772294825178381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126023594279696393100237841 94517695709772294825178381)
        ·
          refine ⟨35444135891164610559441893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94517695709772294825178381 35444135891164610559441893)
          ·
            refine ⟨6645775479593364479895355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35444135891164610559441893 6645775479593364479895355)
            ·
              refine ⟨9968663219390046719843033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6645775479593364479895355 9968663219390046719843033)
              ·
                refine ⟨7476497414542535039882275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9968663219390046719843033 7476497414542535039882275)
                ·
                  refine ⟨11214746121813802559823413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7476497414542535039882275 11214746121813802559823413)
                  ·
                    refine ⟨1051382448920043989983445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11214746121813802559823413 1051382448920043989983445)
                    ·
                      rfl

theorem cell23_6142680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 1, 2, 1, 5].length) (baseStart_6142680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6142680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6142680 prefixEnd_6142680 := by exact prefixLift 6142680
  have htrace : WordTrace (prefixWord ++ tailWord_6142680) baseStart_6142680 baseEnd_6142680 := by
    simpa [prefixWord, tailWord_6142680, baseEnd_6142680] using wordTrace_append hprefix tailTrace_6142680
  have hstable : (prefixWord ++ tailWord_6142680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6142680).length < 2 ^ (prefixWord ++ tailWord_6142680).sum := by decide
  have hdescent : baseEnd_6142680 < baseStart_6142680 := by decide
  rcases family_descends (prefixWord ++ tailWord_6142680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6142693 : List Nat := [1, 3, 1, 4, 1, 3, 1, 2, 1, 6]
def baseStart_6142693 : Nat := 118140960795 + 6142693 * 2 ^ 59
def prefixEnd_6142693 : Nat := 4983230072969 + 3 ^ 40 * 6142693 * 2
def baseEnd_6142693 : Nat := 1051384674002880139695925

theorem tailTrace_6142693 : CollatzResearch.WordTrace tailWord_6142693 prefixEnd_6142693 1051384674002880139695925 := by
  unfold tailWord_6142693
  simp only [CollatzResearch.WordTrace]
  refine ⟨224042419535079824287312733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149361613023386549524875155 224042419535079824287312733)
  ·
    refine ⟨84015907325654934107742275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 224042419535079824287312733 84015907325654934107742275)
    ·
      refine ⟨126023860988482401161613413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84015907325654934107742275 126023860988482401161613413)
      ·
        refine ⟨23629473935340450217802515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 126023860988482401161613413 23629473935340450217802515)
        ·
          refine ⟨35444210903010675326703773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23629473935340450217802515 35444210903010675326703773)
          ·
            refine ⟨13291579088629003247513915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35444210903010675326703773 13291579088629003247513915)
            ·
              refine ⟨19937368632943504871270873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13291579088629003247513915 19937368632943504871270873)
              ·
                refine ⟨14953026474707628653453155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19937368632943504871270873 14953026474707628653453155)
                ·
                  refine ⟨22429539712061442980179733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14953026474707628653453155 22429539712061442980179733)
                  ·
                    refine ⟨1051384674002880139695925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22429539712061442980179733 1051384674002880139695925)
                    ·
                      rfl

theorem cell23_6142693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 2, 1, 6].length) (baseStart_6142693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6142693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6142693 prefixEnd_6142693 := by exact prefixLift 6142693
  have htrace : WordTrace (prefixWord ++ tailWord_6142693) baseStart_6142693 baseEnd_6142693 := by
    simpa [prefixWord, tailWord_6142693, baseEnd_6142693] using wordTrace_append hprefix tailTrace_6142693
  have hstable : (prefixWord ++ tailWord_6142693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6142693).length < 2 ^ (prefixWord ++ tailWord_6142693).sum := by decide
  have hdescent : baseEnd_6142693 < baseStart_6142693 := by decide
  rcases family_descends (prefixWord ++ tailWord_6142693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6142703 : List Nat := [1, 1, 2, 1, 5, 2, 3, 1, 1, 1, 5]
def baseStart_6142703 : Nat := 118140960795 + 6142703 * 2 ^ 59
def prefixEnd_6142703 : Nat := 4983230072969 + 3 ^ 40 * 6142703 * 2
def baseEnd_6142703 : Nat := 3154159156815185379962729

theorem tailTrace_6142703 : CollatzResearch.WordTrace tailWord_6142703 prefixEnd_6142703 3154159156815185379962729 := by
  unfold tailWord_6142703
  simp only [CollatzResearch.WordTrace]
  refine ⟨224042784265043595995176763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149361856176695730663451175 224042784265043595995176763)
  ·
    refine ⟨336064176397565393992765145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224042784265043595995176763 336064176397565393992765145)
    ·
      refine ⟨252048132298174045494573859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 336064176397565393992765145 252048132298174045494573859)
      ·
        refine ⟨378072198447261068241860789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252048132298174045494573859 378072198447261068241860789)
        ·
          refine ⟨35444268604430725147674449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 378072198447261068241860789 35444268604430725147674449)
          ·
            refine ⟨26583201453323043860755837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35444268604430725147674449 26583201453323043860755837)
            ·
              refine ⟨9968700544996141447783439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26583201453323043860755837 9968700544996141447783439)
              ·
                refine ⟨14953050817494212171675159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9968700544996141447783439 14953050817494212171675159)
                ·
                  refine ⟨22429576226241318257512739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14953050817494212171675159 22429576226241318257512739)
                  ·
                    refine ⟨33644364339361977386269109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22429576226241318257512739 33644364339361977386269109)
                    ·
                      refine ⟨3154159156815185379962729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33644364339361977386269109 3154159156815185379962729)
                      ·
                        rfl

theorem cell23_6142703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 3, 1, 1, 1, 5].length) (baseStart_6142703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6142703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6142703 prefixEnd_6142703 := by exact prefixLift 6142703
  have htrace : WordTrace (prefixWord ++ tailWord_6142703) baseStart_6142703 baseEnd_6142703 := by
    simpa [prefixWord, tailWord_6142703, baseEnd_6142703] using wordTrace_append hprefix tailTrace_6142703
  have hstable : (prefixWord ++ tailWord_6142703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6142703).length < 2 ^ (prefixWord ++ tailWord_6142703).sum := by decide
  have hdescent : baseEnd_6142703 < baseStart_6142703 := by decide
  rcases family_descends (prefixWord ++ tailWord_6142703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6142706 : List Nat := [3, 2, 1, 3, 1, 13]
def baseStart_6142706 : Nat := 118140960795 + 6142706 * 2 ^ 59
def prefixEnd_6142706 : Nat := 4983230072969 + 3 ^ 40 * 6142706 * 2
def baseEnd_6142706 : Nat := 12980085173897731968005

theorem tailTrace_6142706 : CollatzResearch.WordTrace tailWord_6142706 prefixEnd_6142706 12980085173897731968005 := by
  unfold tailWord_6142706
  simp only [CollatzResearch.WordTrace]
  refine ⟨56010723421008181876883993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149361929122688485005023981 56010723421008181876883993)
  ·
    refine ⟨42008042565756136407662995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56010723421008181876883993 42008042565756136407662995)
    ·
      refine ⟨63012063848634204611494493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42008042565756136407662995 63012063848634204611494493)
      ·
        refine ⟨23629523943237826729310435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63012063848634204611494493 23629523943237826729310435)
        ·
          refine ⟨35444285914856740093965653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23629523943237826729310435 35444285914856740093965653)
          ·
            refine ⟨12980085173897731968005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 35444285914856740093965653 12980085173897731968005)
            ·
              rfl

theorem cell23_6142706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 13].length) (baseStart_6142706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6142706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6142706 prefixEnd_6142706 := by exact prefixLift 6142706
  have htrace : WordTrace (prefixWord ++ tailWord_6142706) baseStart_6142706 baseEnd_6142706 := by
    simpa [prefixWord, tailWord_6142706, baseEnd_6142706] using wordTrace_append hprefix tailTrace_6142706
  have hstable : (prefixWord ++ tailWord_6142706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6142706).length < 2 ^ (prefixWord ++ tailWord_6142706).sum := by decide
  have hdescent : baseEnd_6142706 < baseStart_6142706 := by decide
  rcases family_descends (prefixWord ++ tailWord_6142706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6142754 : List Nat := [3, 3, 1, 1, 2, 4, 2, 1, 1, 2, 3]
def baseStart_6142754 : Nat := 118140960795 + 6142754 * 2 ^ 59
def prefixEnd_6142754 : Nat := 4983230072969 + 3 ^ 40 * 6142754 * 2
def baseEnd_6142754 : Nat := 3154185344328564680424995

theorem tailTrace_6142754 : CollatzResearch.WordTrace tailWord_6142754 prefixEnd_6142754 3154185344328564680424995 := by
  unfold tailWord_6142754
  simp only [CollatzResearch.WordTrace]
  refine ⟨56011161096964707926320829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149363096258572554470188877 56011161096964707926320829)
  ·
    refine ⟨21004185411361765472370311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56011161096964707926320829 21004185411361765472370311)
    ·
      refine ⟨31506278117042648208555467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21004185411361765472370311 31506278117042648208555467)
      ·
        refine ⟨47259417175563972312833201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31506278117042648208555467 47259417175563972312833201)
        ·
          refine ⟨35444562881672979234624901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47259417175563972312833201 35444562881672979234624901)
          ·
            refine ⟨6645855540313683606492169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35444562881672979234624901 6645855540313683606492169)
            ·
              refine ⟨4984391655235262704869127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6645855540313683606492169 4984391655235262704869127)
              ·
                refine ⟨7476587482852894057303691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4984391655235262704869127 7476587482852894057303691)
                ·
                  refine ⟨11214881224279341085955537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7476587482852894057303691 11214881224279341085955537)
                  ·
                    refine ⟨8411160918209505814466653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11214881224279341085955537 8411160918209505814466653)
                    ·
                      refine ⟨3154185344328564680424995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8411160918209505814466653 3154185344328564680424995)
                      ·
                        rfl

theorem cell23_6142754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 2, 1, 1, 2, 3].length) (baseStart_6142754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6142754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6142754 prefixEnd_6142754 := by exact prefixLift 6142754
  have htrace : WordTrace (prefixWord ++ tailWord_6142754) baseStart_6142754 baseEnd_6142754 := by
    simpa [prefixWord, tailWord_6142754, baseEnd_6142754] using wordTrace_append hprefix tailTrace_6142754
  have hstable : (prefixWord ++ tailWord_6142754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6142754).length < 2 ^ (prefixWord ++ tailWord_6142754).sum := by decide
  have hdescent : baseEnd_6142754 < baseStart_6142754 := by decide
  rcases family_descends (prefixWord ++ tailWord_6142754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6142783 : List Nat := [1, 1, 2, 2, 5, 1, 2, 1, 2, 6]
def baseStart_6142783 : Nat := 118140960795 + 6142783 * 2 ^ 59
def prefixEnd_6142783 : Nat := 4983230072969 + 3 ^ 40 * 6142783 * 2
def baseEnd_6142783 : Nat := 1051400078422515022320787

theorem tailTrace_6142783 : CollatzResearch.WordTrace tailWord_6142783 prefixEnd_6142783 1051400078422515022320787 := by
  unfold tailWord_6142783
  simp only [CollatzResearch.WordTrace]
  refine ⟨224045702104753769658089003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149363801403169179772059335 224045702104753769658089003)
  ·
    refine ⟨336068553157130654487133505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224045702104753769658089003 336068553157130654487133505)
    ·
      refine ⟨252051414867847990865350129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 336068553157130654487133505 252051414867847990865350129)
      ·
        refine ⟨189038561150885993149012597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 252051414867847990865350129 189038561150885993149012597)
        ·
          refine ⟨17722365107895561857719931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 189038561150885993149012597 17722365107895561857719931)
          ·
            refine ⟨26583547661843342786579897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17722365107895561857719931 26583547661843342786579897)
            ·
              refine ⟨19937660746382507089934923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26583547661843342786579897 19937660746382507089934923)
              ·
                refine ⟨29906491119573760634902385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19937660746382507089934923 29906491119573760634902385)
                ·
                  refine ⟨22429868339680320476176789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29906491119573760634902385 22429868339680320476176789)
                  ·
                    refine ⟨1051400078422515022320787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22429868339680320476176789 1051400078422515022320787)
                    ·
                      rfl

theorem cell23_6142783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 1, 2, 6].length) (baseStart_6142783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6142783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6142783 prefixEnd_6142783 := by exact prefixLift 6142783
  have htrace : WordTrace (prefixWord ++ tailWord_6142783) baseStart_6142783 baseEnd_6142783 := by
    simpa [prefixWord, tailWord_6142783, baseEnd_6142783] using wordTrace_append hprefix tailTrace_6142783
  have hstable : (prefixWord ++ tailWord_6142783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6142783).length < 2 ^ (prefixWord ++ tailWord_6142783).sum := by decide
  have hdescent : baseEnd_6142783 < baseStart_6142783 := by decide
  rcases family_descends (prefixWord ++ tailWord_6142783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6142807 : List Nat := [1, 1, 3, 2, 4, 1, 1, 2, 4, 2, 2]
def baseStart_6142807 : Nat := 118140960795 + 6142807 * 2 ^ 59
def prefixEnd_6142807 : Nat := 4983230072969 + 3 ^ 40 * 6142807 * 2
def baseEnd_6142807 : Nat := 3154212558803252973062251

theorem tailTrace_6142807 : CollatzResearch.WordTrace tailWord_6142807 prefixEnd_6142807 3154212558803252973062251 := by
  unfold tailWord_6142807
  simp only [CollatzResearch.WordTrace]
  refine ⟨224046577456666821756962675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149364384971111214504641783 224046577456666821756962675)
  ·
    refine ⟨336069866185000232635444013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224046577456666821756962675 336069866185000232635444013)
    ·
      refine ⟨126026199819375087238291505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 336069866185000232635444013 126026199819375087238291505)
      ·
        refine ⟨94519649864531315428718629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126026199819375087238291505 94519649864531315428718629)
        ·
          refine ⟨17722434349599621642884743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 94519649864531315428718629 17722434349599621642884743)
          ·
            refine ⟨26583651524399432464327115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17722434349599621642884743 26583651524399432464327115)
            ·
              refine ⟨39875477286599148696490673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26583651524399432464327115 39875477286599148696490673)
              ·
                refine ⟨29906607964949361522368005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39875477286599148696490673 29906607964949361522368005)
                ·
                  refine ⟨5607488993428005285444001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29906607964949361522368005 5607488993428005285444001)
                  ·
                    refine ⟨4205616745071003964083001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5607488993428005285444001 4205616745071003964083001)
                    ·
                      refine ⟨3154212558803252973062251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4205616745071003964083001 3154212558803252973062251)
                      ·
                        rfl

theorem cell23_6142807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 2, 4, 2, 2].length) (baseStart_6142807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6142807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6142807 prefixEnd_6142807 := by exact prefixLift 6142807
  have htrace : WordTrace (prefixWord ++ tailWord_6142807) baseStart_6142807 baseEnd_6142807 := by
    simpa [prefixWord, tailWord_6142807, baseEnd_6142807] using wordTrace_append hprefix tailTrace_6142807
  have hstable : (prefixWord ++ tailWord_6142807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6142807).length < 2 ^ (prefixWord ++ tailWord_6142807).sum := by decide
  have hdescent : baseEnd_6142807 < baseStart_6142807 := by decide
  rcases family_descends (prefixWord ++ tailWord_6142807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6142841 : List Nat := [1, 2, 1, 3, 2, 5, 2, 1, 2, 2, 2]
def baseStart_6142841 : Nat := 118140960795 + 6142841 * 2 ^ 59
def prefixEnd_6142841 : Nat := 4983230072969 + 3 ^ 40 * 6142841 * 2
def baseEnd_6142841 : Nat := 3154230017145505840037095

theorem tailTrace_6142841 : CollatzResearch.WordTrace tailWord_6142841 prefixEnd_6142841 3154230017145505840037095 := by
  unfold tailWord_6142841
  simp only [CollatzResearch.WordTrace]
  refine ⟨224047817538543645563700377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149365211692362430375800251 224047817538543645563700377)
  ·
    refine ⟨168035863153907734172775283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224047817538543645563700377 168035863153907734172775283)
    ·
      refine ⟨252053794730861601259162925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168035863153907734172775283 252053794730861601259162925)
      ·
        refine ⟨94520173024073100472186097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 252053794730861601259162925 94520173024073100472186097)
        ·
          refine ⟨70890129768054825354139573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94520173024073100472186097 70890129768054825354139573)
          ·
            refine ⟨6645949665755139876950585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 70890129768054825354139573 6645949665755139876950585)
            ·
              refine ⟨4984462249316354907712939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6645949665755139876950585 4984462249316354907712939)
              ·
                refine ⟨7476693373974532361569409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4984462249316354907712939 7476693373974532361569409)
                ·
                  refine ⟨5607520030480899271177057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7476693373974532361569409 5607520030480899271177057)
                  ·
                    refine ⟨4205640022860674453382793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5607520030480899271177057 4205640022860674453382793)
                    ·
                      refine ⟨3154230017145505840037095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4205640022860674453382793 3154230017145505840037095)
                      ·
                        rfl

theorem cell23_6142841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 2, 1, 2, 2, 2].length) (baseStart_6142841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6142841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6142841 prefixEnd_6142841 := by exact prefixLift 6142841
  have htrace : WordTrace (prefixWord ++ tailWord_6142841) baseStart_6142841 baseEnd_6142841 := by
    simpa [prefixWord, tailWord_6142841, baseEnd_6142841] using wordTrace_append hprefix tailTrace_6142841
  have hstable : (prefixWord ++ tailWord_6142841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6142841).length < 2 ^ (prefixWord ++ tailWord_6142841).sum := by decide
  have hdescent : baseEnd_6142841 < baseStart_6142841 := by decide
  rcases family_descends (prefixWord ++ tailWord_6142841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6142880 : List Nat := [2, 1, 1, 4, 1, 1, 4, 2, 2, 1, 4]
def baseStart_6142880 : Nat := 118140960795 + 6142880 * 2 ^ 59
def prefixEnd_6142880 : Nat := 4983230072969 + 3 ^ 40 * 6142880 * 2
def baseEnd_6142880 : Nat := 3154250042891031187449415

theorem tailTrace_6142880 : CollatzResearch.WordTrace tailWord_6142880 prefixEnd_6142880 3154250042891031187449415 := by
  unfold tailWord_6142880
  simp only [CollatzResearch.WordTrace]
  refine ⟨112024619992701177612185047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149366159990268236816246729 112024619992701177612185047)
  ·
    refine ⟨168036929989051766418277571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112024619992701177612185047 168036929989051766418277571)
    ·
      refine ⟨252055394983577649627416357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168036929989051766418277571 252055394983577649627416357)
      ·
        refine ⟨47260386559420809305140567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 252055394983577649627416357 47260386559420809305140567)
        ·
          refine ⟨70890579839131213957710851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47260386559420809305140567 70890579839131213957710851)
          ·
            refine ⟨106335869758696820936566277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70890579839131213957710851 106335869758696820936566277)
            ·
              refine ⟨19937975579755653925606177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 106335869758696820936566277 19937975579755653925606177)
              ·
                refine ⟨14953481684816740444204633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19937975579755653925606177 14953481684816740444204633)
                ·
                  refine ⟨11215111263612555333153475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14953481684816740444204633 11215111263612555333153475)
                  ·
                    refine ⟨16822666895418832999730213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11215111263612555333153475 16822666895418832999730213)
                    ·
                      refine ⟨3154250042891031187449415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16822666895418832999730213 3154250042891031187449415)
                      ·
                        rfl

theorem cell23_6142880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 2, 2, 1, 4].length) (baseStart_6142880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6142880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6142880 prefixEnd_6142880 := by exact prefixLift 6142880
  have htrace : WordTrace (prefixWord ++ tailWord_6142880) baseStart_6142880 baseEnd_6142880 := by
    simpa [prefixWord, tailWord_6142880, baseEnd_6142880] using wordTrace_append hprefix tailTrace_6142880
  have hstable : (prefixWord ++ tailWord_6142880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6142880).length < 2 ^ (prefixWord ++ tailWord_6142880).sum := by decide
  have hdescent : baseEnd_6142880 < baseStart_6142880 := by decide
  rcases family_descends (prefixWord ++ tailWord_6142880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6142924 : List Nat := [2, 2, 1, 4, 1, 1, 4, 3, 1, 4]
def baseStart_6142924 : Nat := 118140960795 + 6142924 * 2 ^ 59
def prefixEnd_6142924 : Nat := 4983230072969 + 3 ^ 40 * 6142924 * 2
def baseEnd_6142924 : Nat := 1051424212013276338433071

theorem tailTrace_6142924 : CollatzResearch.WordTrace tailWord_6142924 prefixEnd_6142924 1051424212013276338433071 := by
  unfold tailWord_6142924
  simp only [CollatzResearch.WordTrace]
  refine ⟨112025422398621475369485913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149367229864828633825981217 112025422398621475369485913)
  ·
    refine ⟨84019066798966106527114435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112025422398621475369485913 84019066798966106527114435)
    ·
      refine ⟨126028600198449159790671653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84019066798966106527114435 126028600198449159790671653)
      ·
        refine ⟨23630362537209217460750935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 126028600198449159790671653 23630362537209217460750935)
        ·
          refine ⟨35445543805813826191126403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23630362537209217460750935 35445543805813826191126403)
          ·
            refine ⟨53168315708720739286689605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35445543805813826191126403 53168315708720739286689605)
            ·
              refine ⟨9969059195385138616254301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53168315708720739286689605 9969059195385138616254301)
              ·
                refine ⟨3738397198269426981095363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9969059195385138616254301 3738397198269426981095363)
                ·
                  refine ⟨5607595797404140471643045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3738397198269426981095363 5607595797404140471643045)
                  ·
                    refine ⟨1051424212013276338433071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5607595797404140471643045 1051424212013276338433071)
                    ·
                      rfl

theorem cell23_6142924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 4, 3, 1, 4].length) (baseStart_6142924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6142924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6142924 prefixEnd_6142924 := by exact prefixLift 6142924
  have htrace : WordTrace (prefixWord ++ tailWord_6142924) baseStart_6142924 baseEnd_6142924 := by
    simpa [prefixWord, tailWord_6142924, baseEnd_6142924] using wordTrace_append hprefix tailTrace_6142924
  have hstable : (prefixWord ++ tailWord_6142924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6142924).length < 2 ^ (prefixWord ++ tailWord_6142924).sum := by decide
  have hdescent : baseEnd_6142924 < baseStart_6142924 := by decide
  rcases family_descends (prefixWord ++ tailWord_6142924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6142937 : List Nat := [1, 2, 1, 2, 5, 3, 1, 2, 6]
def baseStart_6142937 : Nat := 118140960795 + 6142937 * 2 ^ 59
def prefixEnd_6142937 : Nat := 4983230072969 + 3 ^ 40 * 6142937 * 2
def baseEnd_6142937 : Nat := 350475479032037496048517

theorem tailTrace_6142937 : CollatzResearch.WordTrace tailWord_6142937 prefixEnd_6142937 350475479032037496048517 := by
  unfold tailWord_6142937
  simp only [CollatzResearch.WordTrace]
  refine ⟨224051318946195853959195065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149367545964130569306130043 224051318946195853959195065)
  ·
    refine ⟨168038489209646890469396299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224051318946195853959195065 168038489209646890469396299)
    ·
      refine ⟨252057733814470335704094449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168038489209646890469396299 252057733814470335704094449)
      ·
        refine ⟨189043300360852751778070837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 252057733814470335704094449 189043300360852751778070837)
        ·
          refine ⟨17722809408829945479194141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 189043300360852751778070837 17722809408829945479194141)
          ·
            refine ⟨6646053528311229554697803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17722809408829945479194141 6646053528311229554697803)
            ·
              refine ⟨9969080292466844332046705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6646053528311229554697803 9969080292466844332046705)
              ·
                refine ⟨7476810219350133249035029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9969080292466844332046705 7476810219350133249035029)
                ·
                  refine ⟨350475479032037496048517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7476810219350133249035029 350475479032037496048517)
                  ·
                    rfl

theorem cell23_6142937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 1, 2, 6].length) (baseStart_6142937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6142937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6142937 prefixEnd_6142937 := by exact prefixLift 6142937
  have htrace : WordTrace (prefixWord ++ tailWord_6142937) baseStart_6142937 baseEnd_6142937 := by
    simpa [prefixWord, tailWord_6142937, baseEnd_6142937] using wordTrace_append hprefix tailTrace_6142937
  have hstable : (prefixWord ++ tailWord_6142937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6142937).length < 2 ^ (prefixWord ++ tailWord_6142937).sum := by decide
  have hdescent : baseEnd_6142937 < baseStart_6142937 := by decide
  rcases family_descends (prefixWord ++ tailWord_6142937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6142970 : List Nat := [3, 1, 1, 1, 1, 2, 1, 5, 3, 1, 4]
def baseStart_6142970 : Nat := 118140960795 + 6142970 * 2 ^ 59
def prefixEnd_6142970 : Nat := 4983230072969 + 3 ^ 40 * 6142970 * 2
def baseEnd_6142970 : Nat := 3154296256149935835324001

theorem tailTrace_6142970 : CollatzResearch.WordTrace tailWord_6142970 prefixEnd_6142970 3154296256149935835324001 := by
  unfold tailWord_6142970
  simp only [CollatzResearch.WordTrace]
  refine ⟨56013130638769075148786591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149368348370050867063430909 56013130638769075148786591)
  ·
    refine ⟨84019695958153612723179887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56013130638769075148786591 84019695958153612723179887)
    ·
      refine ⟨126029543937230419084769831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84019695958153612723179887 126029543937230419084769831)
      ·
        refine ⟨189044315905845628627154747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126029543937230419084769831 189044315905845628627154747)
        ·
          refine ⟨283566473858768442940732121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189044315905845628627154747 283566473858768442940732121)
          ·
            refine ⟨212674855394076332205549091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 283566473858768442940732121 212674855394076332205549091)
            ·
              refine ⟨319012283091114498308323637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 212674855394076332205549091 319012283091114498308323637)
              ·
                refine ⟨29907401539791984216405341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 319012283091114498308323637 29907401539791984216405341)
                ·
                  refine ⟨11215275577421994081152003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29907401539791984216405341 11215275577421994081152003)
                  ·
                    refine ⟨16822913366132991121728005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11215275577421994081152003 16822913366132991121728005)
                    ·
                      refine ⟨3154296256149935835324001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16822913366132991121728005 3154296256149935835324001)
                      ·
                        rfl

theorem cell23_6142970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 5, 3, 1, 4].length) (baseStart_6142970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6142970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6142970 prefixEnd_6142970 := by exact prefixLift 6142970
  have htrace : WordTrace (prefixWord ++ tailWord_6142970) baseStart_6142970 baseEnd_6142970 := by
    simpa [prefixWord, tailWord_6142970, baseEnd_6142970] using wordTrace_append hprefix tailTrace_6142970
  have hstable : (prefixWord ++ tailWord_6142970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6142970).length < 2 ^ (prefixWord ++ tailWord_6142970).sum := by decide
  have hdescent : baseEnd_6142970 < baseStart_6142970 := by decide
  rcases family_descends (prefixWord ++ tailWord_6142970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6142987 : List Nat := [1, 1, 1, 1, 6, 2, 2, 3, 1, 1, 4]
def baseStart_6142987 : Nat := 118140960795 + 6142987 * 2 ^ 59
def prefixEnd_6142987 : Nat := 4983230072969 + 3 ^ 40 * 6142987 * 2
def baseEnd_6142987 : Nat := 3154304985321062268811423

theorem tailTrace_6142987 : CollatzResearch.WordTrace tailWord_6142987 prefixEnd_6142987 3154304985321062268811423 := by
  unfold tailWord_6142987
  simp only [CollatzResearch.WordTrace]
  refine ⟨224053142596014712498515215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149368761730676474999010143 224053142596014712498515215)
  ·
    refine ⟨336079713894022068747772823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224053142596014712498515215 336079713894022068747772823)
    ·
      refine ⟨504119570841033103121659235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 336079713894022068747772823 504119570841033103121659235)
      ·
        refine ⟨756179356261549654682488853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 504119570841033103121659235 756179356261549654682488853)
        ·
          refine ⟨35445907324760140063241665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 756179356261549654682488853 35445907324760140063241665)
          ·
            refine ⟨26584430493570105047431249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35445907324760140063241665 26584430493570105047431249)
            ·
              refine ⟨19938322870177578785573437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26584430493570105047431249 19938322870177578785573437)
              ·
                refine ⟨7476871076316592044590039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19938322870177578785573437 7476871076316592044590039)
                ·
                  refine ⟨11215306614474888066885059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7476871076316592044590039 11215306614474888066885059)
                  ·
                    refine ⟨16822959921712332100327589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11215306614474888066885059 16822959921712332100327589)
                    ·
                      refine ⟨3154304985321062268811423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16822959921712332100327589 3154304985321062268811423)
                      ·
                        rfl

theorem cell23_6142987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 3, 1, 1, 4].length) (baseStart_6142987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6142987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6142987 prefixEnd_6142987 := by exact prefixLift 6142987
  have htrace : WordTrace (prefixWord ++ tailWord_6142987) baseStart_6142987 baseEnd_6142987 := by
    simpa [prefixWord, tailWord_6142987, baseEnd_6142987] using wordTrace_append hprefix tailTrace_6142987
  have hstable : (prefixWord ++ tailWord_6142987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6142987).length < 2 ^ (prefixWord ++ tailWord_6142987).sum := by decide
  have hdescent : baseEnd_6142987 < baseStart_6142987 := by decide
  rcases family_descends (prefixWord ++ tailWord_6142987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6142997 : List Nat := [1, 3, 2, 1, 4, 1, 2, 1, 4, 4]
def baseStart_6142997 : Nat := 118140960795 + 6142997 * 2 ^ 59
def prefixEnd_6142997 : Nat := 4983230072969 + 3 ^ 40 * 6142997 * 2
def baseEnd_6142997 : Nat := 1051436706709202409895459

theorem tailTrace_6142997 : CollatzResearch.WordTrace tailWord_6142997 prefixEnd_6142997 1051436706709202409895459 := by
  unfold tailWord_6142997
  simp only [CollatzResearch.WordTrace]
  refine ⟨224053507325978484206379245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149369004883985656137586163 224053507325978484206379245)
  ·
    refine ⟨84020065247241931577392217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 224053507325978484206379245 84020065247241931577392217)
    ·
      refine ⟨63015048935431448683044163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84020065247241931577392217 63015048935431448683044163)
      ·
        refine ⟨94522573403147173024566245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63015048935431448683044163 94522573403147173024566245)
        ·
          refine ⟨17722982513090094942106171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 94522573403147173024566245 17722982513090094942106171)
          ·
            refine ⟨26584473769635142413159257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17722982513090094942106171 26584473769635142413159257)
            ·
              refine ⟨19938355327226356809869443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26584473769635142413159257 19938355327226356809869443)
              ·
                refine ⟨29907532990839535214804165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19938355327226356809869443 29907532990839535214804165)
                ·
                  refine ⟨5607662435782412852775781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29907532990839535214804165 5607662435782412852775781)
                  ·
                    refine ⟨1051436706709202409895459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5607662435782412852775781 1051436706709202409895459)
                    ·
                      rfl

theorem cell23_6142997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 1, 4, 4].length) (baseStart_6142997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6142997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6142997 prefixEnd_6142997 := by exact prefixLift 6142997
  have htrace : WordTrace (prefixWord ++ tailWord_6142997) baseStart_6142997 baseEnd_6142997 := by
    simpa [prefixWord, tailWord_6142997, baseEnd_6142997] using wordTrace_append hprefix tailTrace_6142997
  have hstable : (prefixWord ++ tailWord_6142997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6142997).length < 2 ^ (prefixWord ++ tailWord_6142997).sum := by decide
  have hdescent : baseEnd_6142997 < baseStart_6142997 := by decide
  rcases family_descends (prefixWord ++ tailWord_6142997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6143000 : List Nat := [2, 1, 2, 3, 2, 2, 1, 2, 1, 1, 6]
def baseStart_6143000 : Nat := 118140960795 + 6143000 * 2 ^ 59
def prefixEnd_6143000 : Nat := 4983230072969 + 3 ^ 40 * 6143000 * 2
def baseEnd_6143000 : Nat := 3154311660569570717948863

theorem tailTrace_6143000 : CollatzResearch.WordTrace tailWord_6143000 prefixEnd_6143000 3154311660569570717948863 := by
  unfold tailWord_6143000
  simp only [CollatzResearch.WordTrace]
  refine ⟨112026808372483807859369227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149369077829978410479158969 112026808372483807859369227)
  ·
    refine ⟨168040212558725711789053841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112026808372483807859369227 168040212558725711789053841)
    ·
      refine ⟨126030159419044283841790381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168040212558725711789053841 126030159419044283841790381)
      ·
        refine ⟨47261309782141606440671393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126030159419044283841790381 47261309782141606440671393)
        ·
          refine ⟨35445982336606204830503545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47261309782141606440671393 35445982336606204830503545)
          ·
            refine ⟨26584486752454653622877659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35445982336606204830503545 26584486752454653622877659)
            ·
              refine ⟨39876730128681980434316489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26584486752454653622877659 39876730128681980434316489)
              ·
                refine ⟨29907547596511485325737367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39876730128681980434316489 29907547596511485325737367)
                ·
                  refine ⟨44861321394767227988606051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29907547596511485325737367 44861321394767227988606051)
                  ·
                    refine ⟨67291982092150841982909077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44861321394767227988606051 67291982092150841982909077)
                    ·
                      refine ⟨3154311660569570717948863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67291982092150841982909077 3154311660569570717948863)
                      ·
                        rfl

theorem cell23_6143000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 2, 1, 1, 6].length) (baseStart_6143000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6143000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6143000 prefixEnd_6143000 := by exact prefixLift 6143000
  have htrace : WordTrace (prefixWord ++ tailWord_6143000) baseStart_6143000 baseEnd_6143000 := by
    simpa [prefixWord, tailWord_6143000, baseEnd_6143000] using wordTrace_append hprefix tailTrace_6143000
  have hstable : (prefixWord ++ tailWord_6143000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6143000).length < 2 ^ (prefixWord ++ tailWord_6143000).sum := by decide
  have hdescent : baseEnd_6143000 < baseStart_6143000 := by decide
  rcases family_descends (prefixWord ++ tailWord_6143000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6143010 : List Nat := [3, 3, 1, 1, 1, 3, 1, 10]
def baseStart_6143010 : Nat := 118140960795 + 6143010 * 2 ^ 59
def prefixEnd_6143010 : Nat := 4983230072969 + 3 ^ 40 * 6143010 * 2
def baseEnd_6143010 : Nat := 116826547976893173289771

theorem tailTrace_6143010 : CollatzResearch.WordTrace tailWord_6143010 prefixEnd_6143010 116826547976893173289771 := by
  unfold tailWord_6143010
  simp only [CollatzResearch.WordTrace]
  refine ⟨56013495368732846856650621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149369320983287591617734989 56013495368732846856650621)
  ·
    refine ⟨21005060763274817571243983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56013495368732846856650621 21005060763274817571243983)
    ·
      refine ⟨31507591144912226356865975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21005060763274817571243983 31507591144912226356865975)
      ·
        refine ⟨47261386717368339535298963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31507591144912226356865975 47261386717368339535298963)
        ·
          refine ⟨70892080076052509302948445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47261386717368339535298963 70892080076052509302948445)
          ·
            refine ⟨26584530028519690988605667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70892080076052509302948445 26584530028519690988605667)
            ·
              refine ⟨39876795042779536482908501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26584530028519690988605667 39876795042779536482908501)
              ·
                refine ⟨116826547976893173289771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 39876795042779536482908501 116826547976893173289771)
                ·
                  rfl

theorem cell23_6143010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 10].length) (baseStart_6143010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6143010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6143010 prefixEnd_6143010 := by exact prefixLift 6143010
  have htrace : WordTrace (prefixWord ++ tailWord_6143010) baseStart_6143010 baseEnd_6143010 := by
    simpa [prefixWord, tailWord_6143010, baseEnd_6143010] using wordTrace_append hprefix tailTrace_6143010
  have hstable : (prefixWord ++ tailWord_6143010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6143010).length < 2 ^ (prefixWord ++ tailWord_6143010).sum := by decide
  have hdescent : baseEnd_6143010 < baseStart_6143010 := by decide
  rcases family_descends (prefixWord ++ tailWord_6143010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6143037 : List Nat := [1, 4, 1, 3, 1, 2, 1, 1, 3, 3, 3]
def baseStart_6143037 : Nat := 118140960795 + 6143037 * 2 ^ 59
def prefixEnd_6143037 : Nat := 4983230072969 + 3 ^ 40 * 6143037 * 2
def baseEnd_6143037 : Nat := 3154330659353787073186193

theorem tailTrace_6143037 : CollatzResearch.WordTrace tailWord_6143037 prefixEnd_6143037 3154330659353787073186193 := by
  unfold tailWord_6143037
  simp only [CollatzResearch.WordTrace]
  refine ⟨224054966245833571037835365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149369977497222380691890243 224054966245833571037835365)
  ·
    refine ⟨42010306171093794569594131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 224054966245833571037835365 42010306171093794569594131)
    ·
      refine ⟨63015459256640691854391197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42010306171093794569594131 63015459256640691854391197)
      ·
        refine ⟨23630797221240259445396699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63015459256640691854391197 23630797221240259445396699)
        ·
          refine ⟨35446195831860389168095049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23630797221240259445396699 35446195831860389168095049)
          ·
            refine ⟨26584646873895291876071287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35446195831860389168095049 26584646873895291876071287)
            ·
              refine ⟨39876970310842937814106931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26584646873895291876071287 39876970310842937814106931)
              ·
                refine ⟨59815455466264406721160397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39876970310842937814106931 59815455466264406721160397)
                ·
                  refine ⟨22430795799849152520435149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59815455466264406721160397 22430795799849152520435149)
                  ·
                    refine ⟨8411548424943432195163181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22430795799849152520435149 8411548424943432195163181)
                    ·
                      refine ⟨3154330659353787073186193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8411548424943432195163181 3154330659353787073186193)
                      ·
                        rfl

theorem cell23_6143037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 1, 3, 3, 3].length) (baseStart_6143037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6143037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6143037 prefixEnd_6143037 := by exact prefixLift 6143037
  have htrace : WordTrace (prefixWord ++ tailWord_6143037) baseStart_6143037 baseEnd_6143037 := by
    simpa [prefixWord, tailWord_6143037, baseEnd_6143037] using wordTrace_append hprefix tailTrace_6143037
  have hstable : (prefixWord ++ tailWord_6143037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6143037).length < 2 ^ (prefixWord ++ tailWord_6143037).sum := by decide
  have hdescent : baseEnd_6143037 < baseStart_6143037 := by decide
  rcases family_descends (prefixWord ++ tailWord_6143037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6143041 : List Nat := [1, 2, 5, 1, 4, 1, 1, 1, 1, 1, 5]
def baseStart_6143041 : Nat := 118140960795 + 6143041 * 2 ^ 59
def prefixEnd_6143041 : Nat := 4983230072969 + 3 ^ 40 * 6143041 * 2
def baseEnd_6143041 : Nat := 3154332713276405057536175

theorem tailTrace_6143041 : CollatzResearch.WordTrace tailWord_6143041 prefixEnd_6143041 3154332713276405057536175 := by
  unfold tailWord_6143041
  simp only [CollatzResearch.WordTrace]
  refine ⟨224055112137819079720980977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149370074758546053147320651 224055112137819079720980977)
  ·
    refine ⟨168041334103364309790735733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224055112137819079720980977 168041334103364309790735733)
    ·
      refine ⟨15753875072190404042881475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 168041334103364309790735733 15753875072190404042881475)
      ·
        refine ⟨23630812608285606064322213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15753875072190404042881475 23630812608285606064322213)
        ·
          refine ⟨4430777364053551137060415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23630812608285606064322213 4430777364053551137060415)
          ·
            refine ⟨6646166046080326705590623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4430777364053551137060415 6646166046080326705590623)
            ·
              refine ⟨9969249069120490058385935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6646166046080326705590623 9969249069120490058385935)
              ·
                refine ⟨14953873603680735087578903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9969249069120490058385935 14953873603680735087578903)
                ·
                  refine ⟨22430810405521102631368355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14953873603680735087578903 22430810405521102631368355)
                  ·
                    refine ⟨33646215608281653947052533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22430810405521102631368355 33646215608281653947052533)
                    ·
                      refine ⟨3154332713276405057536175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33646215608281653947052533 3154332713276405057536175)
                      ·
                        rfl

theorem cell23_6143041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 1, 1, 1, 1, 5].length) (baseStart_6143041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6143041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6143041 prefixEnd_6143041 := by exact prefixLift 6143041
  have htrace : WordTrace (prefixWord ++ tailWord_6143041) baseStart_6143041 baseEnd_6143041 := by
    simpa [prefixWord, tailWord_6143041, baseEnd_6143041] using wordTrace_append hprefix tailTrace_6143041
  have hstable : (prefixWord ++ tailWord_6143041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6143041).length < 2 ^ (prefixWord ++ tailWord_6143041).sum := by decide
  have hdescent : baseEnd_6143041 < baseStart_6143041 := by decide
  rcases family_descends (prefixWord ++ tailWord_6143041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6143050 : List Nat := [3, 1, 2, 1, 1, 2, 2, 2, 2, 2, 5]
def baseStart_6143050 : Nat := 118140960795 + 6143050 * 2 ^ 59
def prefixEnd_6143050 : Nat := 4983230072969 + 3 ^ 40 * 6143050 * 2
def baseEnd_6143050 : Nat := 3154337334602295522323633

theorem tailTrace_6143050 : CollatzResearch.WordTrace tailWord_6143050 prefixEnd_6143050 3154337334602295522323633 := by
  unfold tailWord_6143050
  simp only [CollatzResearch.WordTrace]
  refine ⟨56013860098696618564514651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149370293596524316172039069 56013860098696618564514651)
  ·
    refine ⟨84020790148044927846771977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56013860098696618564514651 84020790148044927846771977)
    ·
      refine ⟨63015592611033695885078983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84020790148044927846771977 63015592611033695885078983)
      ·
        refine ⟨94523388916550543827618475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63015592611033695885078983 94523388916550543827618475)
        ·
          refine ⟨141785083374825815741427713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94523388916550543827618475 141785083374825815741427713)
          ·
            refine ⟨106338812531119361806070785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141785083374825815741427713 106338812531119361806070785)
            ·
              refine ⟨79754109398339521354553089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106338812531119361806070785 79754109398339521354553089)
              ·
                refine ⟨59815582048754641015914817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79754109398339521354553089 59815582048754641015914817)
                ·
                  refine ⟨44861686536565980761936113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59815582048754641015914817 44861686536565980761936113)
                  ·
                    refine ⟨33646264902424485571452085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44861686536565980761936113 33646264902424485571452085)
                    ·
                      refine ⟨3154337334602295522323633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33646264902424485571452085 3154337334602295522323633)
                      ·
                        rfl

theorem cell23_6143050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 2, 2, 2, 5].length) (baseStart_6143050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6143050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6143050 prefixEnd_6143050 := by exact prefixLift 6143050
  have htrace : WordTrace (prefixWord ++ tailWord_6143050) baseStart_6143050 baseEnd_6143050 := by
    simpa [prefixWord, tailWord_6143050, baseEnd_6143050] using wordTrace_append hprefix tailTrace_6143050
  have hstable : (prefixWord ++ tailWord_6143050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6143050).length < 2 ^ (prefixWord ++ tailWord_6143050).sum := by decide
  have hdescent : baseEnd_6143050 < baseStart_6143050 := by decide
  rcases family_descends (prefixWord ++ tailWord_6143050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6143100 : List Nat := [2, 2, 2, 1, 1, 3, 1, 2, 9]
def baseStart_6143100 : Nat := 118140960795 + 6143100 * 2 ^ 59
def prefixEnd_6143100 : Nat := 4983230072969 + 3 ^ 40 * 6143100 * 2
def baseEnd_6143100 : Nat := 350484778737224480744267

theorem tailTrace_6143100 : CollatzResearch.WordTrace tailWord_6143100 prefixEnd_6143100 350484778737224480744267 := by
  unfold tailWord_6143100
  simp only [CollatzResearch.WordTrace]
  refine ⟨112028632022302666398689377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149371509363070221864919169 112028632022302666398689377)
  ·
    refine ⟨84021474016726999799017033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112028632022302666398689377 84021474016726999799017033)
    ·
      refine ⟨63016105512545249849262775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84021474016726999799017033 63016105512545249849262775)
      ·
        refine ⟨94524158268817874773894163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63016105512545249849262775 94524158268817874773894163)
        ·
          refine ⟨141786237403226812160841245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94524158268817874773894163 141786237403226812160841245)
          ·
            refine ⟨53169839026210054560315467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 141786237403226812160841245 53169839026210054560315467)
            ·
              refine ⟨79754758539315081840473201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53169839026210054560315467 79754758539315081840473201)
              ·
                refine ⟨59816068904486311380354901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79754758539315081840473201 59816068904486311380354901)
                ·
                  refine ⟨350484778737224480744267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 59816068904486311380354901 350484778737224480744267)
                  ·
                    rfl

theorem cell23_6143100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 2, 9].length) (baseStart_6143100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6143100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6143100 prefixEnd_6143100 := by exact prefixLift 6143100
  have htrace : WordTrace (prefixWord ++ tailWord_6143100) baseStart_6143100 baseEnd_6143100 := by
    simpa [prefixWord, tailWord_6143100, baseEnd_6143100] using wordTrace_append hprefix tailTrace_6143100
  have hstable : (prefixWord ++ tailWord_6143100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6143100).length < 2 ^ (prefixWord ++ tailWord_6143100).sum := by decide
  have hdescent : baseEnd_6143100 < baseStart_6143100 := by decide
  rcases family_descends (prefixWord ++ tailWord_6143100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6143134 : List Nat := [4, 3, 1, 1, 2, 1, 2, 2, 7]
def baseStart_6143134 : Nat := 118140960795 + 6143134 * 2 ^ 59
def prefixEnd_6143134 : Nat := 4983230072969 + 3 ^ 40 * 6143134 * 2
def baseEnd_6143134 : Nat := 350486718553030354852583

theorem tailTrace_6143134 : CollatzResearch.WordTrace tailWord_6143134 prefixEnd_6143134 350486718553030354852583 := by
  unfold tailWord_6143134
  simp only [CollatzResearch.WordTrace]
  refine ⟨28007313015810269575514557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149372336084321437736077637 28007313015810269575514557)
  ·
    refine ⟨10502742380928851090817959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28007313015810269575514557 10502742380928851090817959)
    ·
      refine ⟨15754113571393276636226939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10502742380928851090817959 15754113571393276636226939)
      ·
        refine ⟨23631170357089914954340409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15754113571393276636226939 23631170357089914954340409)
        ·
          refine ⟨17723377767817436215755307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23631170357089914954340409 17723377767817436215755307)
          ·
            refine ⟨26585066651726154323632961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17723377767817436215755307 26585066651726154323632961)
            ·
              refine ⟨19938799988794615742724721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26585066651726154323632961 19938799988794615742724721)
              ·
                refine ⟨14954099991595961807043541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19938799988794615742724721 14954099991595961807043541)
                ·
                  refine ⟨350486718553030354852583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14954099991595961807043541 350486718553030354852583)
                  ·
                    rfl

theorem cell23_6143134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 2, 2, 7].length) (baseStart_6143134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6143134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6143134 prefixEnd_6143134 := by exact prefixLift 6143134
  have htrace : WordTrace (prefixWord ++ tailWord_6143134) baseStart_6143134 baseEnd_6143134 := by
    simpa [prefixWord, tailWord_6143134, baseEnd_6143134] using wordTrace_append hprefix tailTrace_6143134
  have hstable : (prefixWord ++ tailWord_6143134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6143134).length < 2 ^ (prefixWord ++ tailWord_6143134).sum := by decide
  have hdescent : baseEnd_6143134 < baseStart_6143134 := by decide
  rcases family_descends (prefixWord ++ tailWord_6143134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6143164 : List Nat := [2, 2, 2, 3, 2, 2, 1, 2, 2, 5]
def baseStart_6143164 : Nat := 118140960795 + 6143164 * 2 ^ 59
def prefixEnd_6143164 : Nat := 4983230072969 + 3 ^ 40 * 6143164 * 2
def baseEnd_6143164 : Nat := 1051465290465636025432703

theorem tailTrace_6143164 : CollatzResearch.WordTrace tailWord_6143164 prefixEnd_6143164 1051465290465636025432703 := by
  unfold tailWord_6143164
  simp only [CollatzResearch.WordTrace]
  refine ⟨112029799158186735863854273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149373065544248981151805697 112029799158186735863854273)
  ·
    refine ⟨84022349368640051897890705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112029799158186735863854273 84022349368640051897890705)
    ·
      refine ⟨63016762026480038923418029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84022349368640051897890705 63016762026480038923418029)
      ·
        refine ⟨23631285759930014596281761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63016762026480038923418029 23631285759930014596281761)
        ·
          refine ⟨17723464319947510947211321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23631285759930014596281761 17723464319947510947211321)
          ·
            refine ⟨13292598239960633210408491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17723464319947510947211321 13292598239960633210408491)
            ·
              refine ⟨19938897359940949815612737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13292598239960633210408491 19938897359940949815612737)
              ·
                refine ⟨14954173019955712361709553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19938897359940949815612737 14954173019955712361709553)
                ·
                  refine ⟨11215629764966784271282165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14954173019955712361709553 11215629764966784271282165)
                  ·
                    refine ⟨1051465290465636025432703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11215629764966784271282165 1051465290465636025432703)
                    ·
                      rfl

theorem cell23_6143164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 2, 2, 5].length) (baseStart_6143164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6143164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6143164 prefixEnd_6143164 := by exact prefixLift 6143164
  have htrace : WordTrace (prefixWord ++ tailWord_6143164) baseStart_6143164 baseEnd_6143164 := by
    simpa [prefixWord, tailWord_6143164, baseEnd_6143164] using wordTrace_append hprefix tailTrace_6143164
  have hstable : (prefixWord ++ tailWord_6143164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6143164).length < 2 ^ (prefixWord ++ tailWord_6143164).sum := by decide
  have hdescent : baseEnd_6143164 < baseStart_6143164 := by decide
  rcases family_descends (prefixWord ++ tailWord_6143164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6143167 : List Nat := [1, 1, 2, 2, 2, 2, 3, 1, 4, 1, 4]
def baseStart_6143167 : Nat := 118140960795 + 6143167 * 2 ^ 59
def prefixEnd_6143167 : Nat := 4983230072969 + 3 ^ 40 * 6143167 * 2
def baseEnd_6143167 : Nat := 3154397411838871564560595

theorem tailTrace_6143167 : CollatzResearch.WordTrace tailWord_6143167 prefixEnd_6143167 3154397411838871564560595 := by
  unfold tailWord_6143167
  simp only [CollatzResearch.WordTrace]
  refine ⟨224059707735362603240067755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149373138490241735493378503 224059707735362603240067755)
  ·
    refine ⟨336089561603043904860101633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224059707735362603240067755 336089561603043904860101633)
    ·
      refine ⟨252067171202282928645076225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 336089561603043904860101633 252067171202282928645076225)
      ·
        refine ⟨189050378401712196483807169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 252067171202282928645076225 189050378401712196483807169)
        ·
          refine ⟨141787783801284147362855377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189050378401712196483807169 141787783801284147362855377)
          ·
            refine ⟨106340837850963110522141533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141787783801284147362855377 106340837850963110522141533)
            ·
              refine ⟨39877814194111166445803075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 106340837850963110522141533 39877814194111166445803075)
              ·
                refine ⟨59816721291166749668704613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39877814194111166445803075 59816721291166749668704613)
                ·
                  refine ⟨11215635242093765562882115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59816721291166749668704613 11215635242093765562882115)
                  ·
                    refine ⟨16823452863140648344323173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11215635242093765562882115 16823452863140648344323173)
                    ·
                      refine ⟨3154397411838871564560595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16823452863140648344323173 3154397411838871564560595)
                      ·
                        rfl

theorem cell23_6143167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 1, 4, 1, 4].length) (baseStart_6143167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6143167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6143167 prefixEnd_6143167 := by exact prefixLift 6143167
  have htrace : WordTrace (prefixWord ++ tailWord_6143167) baseStart_6143167 baseEnd_6143167 := by
    simpa [prefixWord, tailWord_6143167, baseEnd_6143167] using wordTrace_append hprefix tailTrace_6143167
  have hstable : (prefixWord ++ tailWord_6143167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6143167).length < 2 ^ (prefixWord ++ tailWord_6143167).sum := by decide
  have hdescent : baseEnd_6143167 < baseStart_6143167 := by decide
  rcases family_descends (prefixWord ++ tailWord_6143167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6143204 : List Nat := [2, 3, 1, 1, 1, 2, 3, 3, 2, 2, 3]
def baseStart_6143204 : Nat := 118140960795 + 6143204 * 2 ^ 59
def prefixEnd_6143204 : Nat := 4983230072969 + 3 ^ 40 * 6143204 * 2
def baseEnd_6143204 : Nat := 3154416410623087919797925

theorem tailTrace_6143204 : CollatzResearch.WordTrace tailWord_6143204 prefixEnd_6143204 3154416410623087919797925 := by
  unfold tailWord_6143204
  simp only [CollatzResearch.WordTrace]
  refine ⟨112030528618114279279582333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149374038157485705706109777 112030528618114279279582333)
  ·
    refine ⟨42011448231792854729843375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112030528618114279279582333 42011448231792854729843375)
    ·
      refine ⟨63017172347689282094765063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42011448231792854729843375 63017172347689282094765063)
      ·
        refine ⟨94525758521533923142147595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63017172347689282094765063 94525758521533923142147595)
        ·
          refine ⟨141788637782300884713221393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94525758521533923142147595 141788637782300884713221393)
          ·
            refine ⟨106341478336725663534916045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141788637782300884713221393 106341478336725663534916045)
            ·
              refine ⟨39878054376272123825593517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 106341478336725663534916045 39878054376272123825593517)
              ·
                refine ⟨14954270391102046434597569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39878054376272123825593517 14954270391102046434597569)
                ·
                  refine ⟨11215702793326534825948177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14954270391102046434597569 11215702793326534825948177)
                  ·
                    refine ⟨8411777094994901119461133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11215702793326534825948177 8411777094994901119461133)
                    ·
                      refine ⟨3154416410623087919797925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8411777094994901119461133 3154416410623087919797925)
                      ·
                        rfl

theorem cell23_6143204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 3, 2, 2, 3].length) (baseStart_6143204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6143204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6143204 prefixEnd_6143204 := by exact prefixLift 6143204
  have htrace : WordTrace (prefixWord ++ tailWord_6143204) baseStart_6143204 baseEnd_6143204 := by
    simpa [prefixWord, tailWord_6143204, baseEnd_6143204] using wordTrace_append hprefix tailTrace_6143204
  have hstable : (prefixWord ++ tailWord_6143204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6143204).length < 2 ^ (prefixWord ++ tailWord_6143204).sum := by decide
  have hdescent : baseEnd_6143204 < baseStart_6143204 := by decide
  rcases family_descends (prefixWord ++ tailWord_6143204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6143228 : List Nat := [2, 2, 2, 1, 5, 1, 1, 4, 1, 4]
def baseStart_6143228 : Nat := 118140960795 + 6143228 * 2 ^ 59
def prefixEnd_6143228 : Nat := 4983230072969 + 3 ^ 40 * 6143228 * 2
def baseEnd_6143228 : Nat := 1051476244719598608632605

theorem tailTrace_6143228 : CollatzResearch.WordTrace tailWord_6143228 prefixEnd_6143228 1051476244719598608632605 := by
  unfold tailWord_6143228
  simp only [CollatzResearch.WordTrace]
  refine ⟨112030966294070805329019169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149374621725427740438692225 112030966294070805329019169)
  ·
    refine ⟨84023224720553103996764377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112030966294070805329019169 84023224720553103996764377)
    ·
      refine ⟨63017418540414827997573283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84023224720553103996764377 63017418540414827997573283)
      ·
        refine ⟨94526127810622241996359925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63017418540414827997573283 94526127810622241996359925)
        ·
          refine ⟨8861824482245835187158743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 94526127810622241996359925 8861824482245835187158743)
          ·
            refine ⟨13292736723368752780738115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8861824482245835187158743 13292736723368752780738115)
            ·
              refine ⟨19939105085053129171107173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13292736723368752780738115 19939105085053129171107173)
              ·
                refine ⟨3738582203447461719582595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19939105085053129171107173 3738582203447461719582595)
                ·
                  refine ⟨5607873305171192579373893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3738582203447461719582595 5607873305171192579373893)
                  ·
                    refine ⟨1051476244719598608632605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5607873305171192579373893 1051476244719598608632605)
                    ·
                      rfl

theorem cell23_6143228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 4, 1, 4].length) (baseStart_6143228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6143228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6143228 prefixEnd_6143228 := by exact prefixLift 6143228
  have htrace : WordTrace (prefixWord ++ tailWord_6143228) baseStart_6143228 baseEnd_6143228 := by
    simpa [prefixWord, tailWord_6143228, baseEnd_6143228] using wordTrace_append hprefix tailTrace_6143228
  have hstable : (prefixWord ++ tailWord_6143228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6143228).length < 2 ^ (prefixWord ++ tailWord_6143228).sum := by decide
  have hdescent : baseEnd_6143228 < baseStart_6143228 := by decide
  rcases family_descends (prefixWord ++ tailWord_6143228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6143237 : List Nat := [1, 3, 1, 1, 2, 1, 3, 1, 5, 5]
def baseStart_6143237 : Nat := 118140960795 + 6143237 * 2 ^ 59
def prefixEnd_6143237 : Nat := 4983230072969 + 3 ^ 40 * 6143237 * 2
def baseEnd_6143237 : Nat := 1051477785161562096895091

theorem tailTrace_6143237 : CollatzResearch.WordTrace tailWord_6143237 prefixEnd_6143237 1051477785161562096895091 := by
  unfold tailWord_6143237
  simp only [CollatzResearch.WordTrace]
  refine ⟨224062260845109005195115965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149374840563406003463410643 224062260845109005195115965)
  ·
    refine ⟨84023347816915876948168487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 224062260845109005195115965 84023347816915876948168487)
    ·
      refine ⟨126035021725373815422252731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84023347816915876948168487 126035021725373815422252731)
      ·
        refine ⟨189052532588060723133379097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126035021725373815422252731 189052532588060723133379097)
        ·
          refine ⟨141789399441045542350034323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189052532588060723133379097 141789399441045542350034323)
          ·
            refine ⟨212684099161568313525051485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141789399441045542350034323 212684099161568313525051485)
            ·
              refine ⟨79756537185588117571894307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 212684099161568313525051485 79756537185588117571894307)
              ·
                refine ⟨119634805778382176357841461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79756537185588117571894307 119634805778382176357841461)
                ·
                  refine ⟨11215763041723329033547637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 119634805778382176357841461 11215763041723329033547637)
                  ·
                    refine ⟨1051477785161562096895091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11215763041723329033547637 1051477785161562096895091)
                    ·
                      rfl

theorem cell23_6143237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 5, 5].length) (baseStart_6143237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6143237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6143237 prefixEnd_6143237 := by exact prefixLift 6143237
  have htrace : WordTrace (prefixWord ++ tailWord_6143237) baseStart_6143237 baseEnd_6143237 := by
    simpa [prefixWord, tailWord_6143237, baseEnd_6143237] using wordTrace_append hprefix tailTrace_6143237
  have hstable : (prefixWord ++ tailWord_6143237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6143237).length < 2 ^ (prefixWord ++ tailWord_6143237).sum := by decide
  have hdescent : baseEnd_6143237 < baseStart_6143237 := by decide
  rcases family_descends (prefixWord ++ tailWord_6143237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6143262 : List Nat := [4, 3, 2, 1, 2, 1, 2, 3, 1, 4]
def baseStart_6143262 : Nat := 118140960795 + 6143262 * 2 ^ 59
def prefixEnd_6143262 : Nat := 4983230072969 + 3 ^ 40 * 6143262 * 2
def baseEnd_6143262 : Nat := 1051482064167016230957553

theorem tailTrace_6143262 : CollatzResearch.WordTrace tailWord_6143262 prefixEnd_6143262 1051482064167016230957553 := by
  unfold tailWord_6143262
  simp only [CollatzResearch.WordTrace]
  refine ⟨28007896583752304308097005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149375448446678956309850693 28007896583752304308097005)
  ·
    refine ⟨10502961218907114115536377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28007896583752304308097005 10502961218907114115536377)
    ·
      refine ⟨7877220914180335586652283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10502961218907114115536377 7877220914180335586652283)
      ·
        refine ⟨11815831371270503379978425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7877220914180335586652283 11815831371270503379978425)
        ·
          refine ⟨8861873528452877534983819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11815831371270503379978425 8861873528452877534983819)
          ·
            refine ⟨13292810292679316302475729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8861873528452877534983819 13292810292679316302475729)
            ·
              refine ⟨9969607719509487226856797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13292810292679316302475729 9969607719509487226856797)
              ·
                refine ⟨3738602894816057710071299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9969607719509487226856797 3738602894816057710071299)
                ·
                  refine ⟨5607904342224086565106949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3738602894816057710071299 5607904342224086565106949)
                  ·
                    refine ⟨1051482064167016230957553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5607904342224086565106949 1051482064167016230957553)
                    ·
                      rfl

theorem cell23_6143262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_6143262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6143262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6143262 prefixEnd_6143262 := by exact prefixLift 6143262
  have htrace : WordTrace (prefixWord ++ tailWord_6143262) baseStart_6143262 baseEnd_6143262 := by
    simpa [prefixWord, tailWord_6143262, baseEnd_6143262] using wordTrace_append hprefix tailTrace_6143262
  have hstable : (prefixWord ++ tailWord_6143262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6143262).length < 2 ^ (prefixWord ++ tailWord_6143262).sum := by decide
  have hdescent : baseEnd_6143262 < baseStart_6143262 := by decide
  rcases family_descends (prefixWord ++ tailWord_6143262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6143287 : List Nat := [1, 1, 3, 1, 2, 1, 1, 1, 2, 6, 4]
def baseStart_6143287 : Nat := 118140960795 + 6143287 * 2 ^ 59
def prefixEnd_6143287 : Nat := 4983230072969 + 3 ^ 40 * 6143287 * 2
def baseEnd_6143287 : Nat := 3154459029517411095060043

theorem tailTrace_6143287 : CollatzResearch.WordTrace tailWord_6143287 prefixEnd_6143287 3154459029517411095060043 := by
  unfold tailWord_6143287
  simp only [CollatzResearch.WordTrace]
  refine ⟨224064084494927863734436115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149376056329951909156290743 224064084494927863734436115)
  ·
    refine ⟨336096126742391795601654173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224064084494927863734436115 336096126742391795601654173)
    ·
      refine ⟨126036047528396923350620315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 336096126742391795601654173 126036047528396923350620315)
      ·
        refine ⟨189054071292595385025930473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126036047528396923350620315 189054071292595385025930473)
        ·
          refine ⟨141790553469446538769447855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189054071292595385025930473 141790553469446538769447855)
          ·
            refine ⟨212685830204169808154171783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141790553469446538769447855 212685830204169808154171783)
            ·
              refine ⟨319028745306254712231257675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 212685830204169808154171783 319028745306254712231257675)
              ·
                refine ⟨478543117959382068346886513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 319028745306254712231257675 478543117959382068346886513)
                ·
                  refine ⟨358907338469536551260164885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 478543117959382068346886513 358907338469536551260164885)
                  ·
                    refine ⟨16823781490759525840320229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 358907338469536551260164885 16823781490759525840320229)
                    ·
                      refine ⟨3154459029517411095060043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16823781490759525840320229 3154459029517411095060043)
                      ·
                        rfl

theorem cell23_6143287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 6, 4].length) (baseStart_6143287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6143287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6143287 prefixEnd_6143287 := by exact prefixLift 6143287
  have htrace : WordTrace (prefixWord ++ tailWord_6143287) baseStart_6143287 baseEnd_6143287 := by
    simpa [prefixWord, tailWord_6143287, baseEnd_6143287] using wordTrace_append hprefix tailTrace_6143287
  have hstable : (prefixWord ++ tailWord_6143287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6143287).length < 2 ^ (prefixWord ++ tailWord_6143287).sum := by decide
  have hdescent : baseEnd_6143287 < baseStart_6143287 := by decide
  rcases family_descends (prefixWord ++ tailWord_6143287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6143308 : List Nat := [2, 2, 1, 3, 2, 2, 2, 2, 3, 2, 2]
def baseStart_6143308 : Nat := 118140960795 + 6143308 * 2 ^ 59
def prefixEnd_6143308 : Nat := 4983230072969 + 3 ^ 40 * 6143308 * 2
def baseEnd_6143308 : Nat := 3154469812611155512897447

theorem tailTrace_6143308 : CollatzResearch.WordTrace tailWord_6143308 prefixEnd_6143308 3154469812611155512897447 := by
  unfold tailWord_6143308
  simp only [CollatzResearch.WordTrace]
  refine ⟨112032425213925892160475289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149376566951901189547300385 112032425213925892160475289)
  ·
    refine ⟨84024318910444419120356467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112032425213925892160475289 84024318910444419120356467)
    ·
      refine ⟨126036478365666628680534701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84024318910444419120356467 126036478365666628680534701)
      ·
        refine ⟨47263679387124985755200513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126036478365666628680534701 47263679387124985755200513)
        ·
          refine ⟨35447759540343739316400385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47263679387124985755200513 35447759540343739316400385)
          ·
            refine ⟨26585819655257804487300289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35447759540343739316400385 26585819655257804487300289)
            ·
              refine ⟨19939364741443353365475217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26585819655257804487300289 19939364741443353365475217)
              ·
                refine ⟨14954523556082515024106413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19939364741443353365475217 14954523556082515024106413)
                ·
                  refine ⟨5607946333530943134039905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14954523556082515024106413 5607946333530943134039905)
                  ·
                    refine ⟨4205959750148207350529929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5607946333530943134039905 4205959750148207350529929)
                    ·
                      refine ⟨3154469812611155512897447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4205959750148207350529929 3154469812611155512897447)
                      ·
                        rfl

theorem cell23_6143308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 2, 3, 2, 2].length) (baseStart_6143308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6143308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6143308 prefixEnd_6143308 := by exact prefixLift 6143308
  have htrace : WordTrace (prefixWord ++ tailWord_6143308) baseStart_6143308 baseEnd_6143308 := by
    simpa [prefixWord, tailWord_6143308, baseEnd_6143308] using wordTrace_append hprefix tailTrace_6143308
  have hstable : (prefixWord ++ tailWord_6143308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6143308).length < 2 ^ (prefixWord ++ tailWord_6143308).sum := by decide
  have hdescent : baseEnd_6143308 < baseStart_6143308 := by decide
  rcases family_descends (prefixWord ++ tailWord_6143308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6143327 : List Nat := [1, 1, 2, 3, 1, 2, 1, 2, 1, 9]
def baseStart_6143327 : Nat := 118140960795 + 6143327 * 2 ^ 59
def prefixEnd_6143327 : Nat := 4983230072969 + 3 ^ 40 * 6143327 * 2
def baseEnd_6143327 : Nat := 1051493189581196979519953

theorem tailTrace_6143327 : CollatzResearch.WordTrace tailWord_6143327 prefixEnd_6143327 1051493189581196979519953 := by
  unfold tailWord_6143327
  simp only [CollatzResearch.WordTrace]
  refine ⟨224065543414782950565892235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149377028943188633710594823 224065543414782950565892235)
  ·
    refine ⟨336098315122174425848838353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224065543414782950565892235 336098315122174425848838353)
    ·
      refine ⟨252073736341630819386628765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 336098315122174425848838353 252073736341630819386628765)
      ·
        refine ⟨94527651128111557269985787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 252073736341630819386628765 94527651128111557269985787)
        ·
          refine ⟨141791476692167335904978681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94527651128111557269985787 141791476692167335904978681)
          ·
            refine ⟨106343607519125501928734011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141791476692167335904978681 106343607519125501928734011)
            ·
              refine ⟨159515411278688252893101017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106343607519125501928734011 159515411278688252893101017)
              ·
                refine ⟨119636558459016189669825763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 159515411278688252893101017 119636558459016189669825763)
                ·
                  refine ⟨179454837688524284504738645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 119636558459016189669825763 179454837688524284504738645)
                  ·
                    refine ⟨1051493189581196979519953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 179454837688524284504738645 1051493189581196979519953)
                    ·
                      rfl

theorem cell23_6143327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 9].length) (baseStart_6143327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6143327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6143327 prefixEnd_6143327 := by exact prefixLift 6143327
  have htrace : WordTrace (prefixWord ++ tailWord_6143327) baseStart_6143327 baseEnd_6143327 := by
    simpa [prefixWord, tailWord_6143327, baseEnd_6143327] using wordTrace_append hprefix tailTrace_6143327
  have hstable : (prefixWord ++ tailWord_6143327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6143327).length < 2 ^ (prefixWord ++ tailWord_6143327).sum := by decide
  have hdescent : baseEnd_6143327 < baseStart_6143327 := by decide
  rcases family_descends (prefixWord ++ tailWord_6143327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6143351 : List Nat := [1, 1, 3, 1, 1, 2, 4, 2, 3, 3, 2]
def baseStart_6143351 : Nat := 118140960795 + 6143351 * 2 ^ 59
def prefixEnd_6143351 : Nat := 4983230072969 + 3 ^ 40 * 6143351 * 2
def baseEnd_6143351 : Nat := 3154491892279298844659749

theorem tailTrace_6143351 : CollatzResearch.WordTrace tailWord_6143351 prefixEnd_6143351 3154491892279298844659749 := by
  unfold tailWord_6143351
  simp only [CollatzResearch.WordTrace]
  refine ⟨224066418766696002664765907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149377612511130668443177271 224066418766696002664765907)
  ·
    refine ⟨336099628150044003997148861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224066418766696002664765907 336099628150044003997148861)
    ·
      refine ⟨126037360556266501498930823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 336099628150044003997148861 126037360556266501498930823)
      ·
        refine ⟨189056040834399752248396235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126037360556266501498930823 189056040834399752248396235)
        ·
          refine ⟨283584061251599628372594353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189056040834399752248396235 283584061251599628372594353)
          ·
            refine ⟨212688045938699721279445765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 283584061251599628372594353 212688045938699721279445765)
            ·
              refine ⟨39879008613506197739896081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 212688045938699721279445765 39879008613506197739896081)
              ·
                refine ⟨29909256460129648304922061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39879008613506197739896081 29909256460129648304922061)
                ·
                  refine ⟨11215971172548618114345773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29909256460129648304922061 11215971172548618114345773)
                  ·
                    refine ⟨4205989189705731792879665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11215971172548618114345773 4205989189705731792879665)
                    ·
                      refine ⟨3154491892279298844659749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4205989189705731792879665 3154491892279298844659749)
                      ·
                        rfl

theorem cell23_6143351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 2, 3, 3, 2].length) (baseStart_6143351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6143351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6143351 prefixEnd_6143351 := by exact prefixLift 6143351
  have htrace : WordTrace (prefixWord ++ tailWord_6143351) baseStart_6143351 baseEnd_6143351 := by
    simpa [prefixWord, tailWord_6143351, baseEnd_6143351] using wordTrace_append hprefix tailTrace_6143351
  have hstable : (prefixWord ++ tailWord_6143351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6143351).length < 2 ^ (prefixWord ++ tailWord_6143351).sum := by decide
  have hdescent : baseEnd_6143351 < baseStart_6143351 := by decide
  rcases family_descends (prefixWord ++ tailWord_6143351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6143362 : List Nat := [3, 4, 2, 1, 1, 3, 1, 2, 1, 2, 3]
def baseStart_6143362 : Nat := 118140960795 + 6143362 * 2 ^ 59
def prefixEnd_6143362 : Nat := 4983230072969 + 3 ^ 40 * 6143362 * 2
def baseEnd_6143362 : Nat := 3154497540566498301622199

theorem tailTrace_6143362 : CollatzResearch.WordTrace tailWord_6143362 prefixEnd_6143362 3154497540566498301622199 := by
  unfold tailWord_6143362
  simp only [CollatzResearch.WordTrace]
  refine ⟨56016704992414037885854085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149377879979770767695610893 56016704992414037885854085)
  ·
    refine ⟨10503132186077632103597641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56016704992414037885854085 10503132186077632103597641)
    ·
      refine ⟨7877349139558224077698231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10503132186077632103597641 7877349139558224077698231)
      ·
        refine ⟨11816023709337336116547347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7877349139558224077698231 11816023709337336116547347)
        ·
          refine ⟨17724035564006004174821021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11816023709337336116547347 17724035564006004174821021)
          ·
            refine ⟨6646513336502251565557883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17724035564006004174821021 6646513336502251565557883)
            ·
              refine ⟨9969770004753377348336825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6646513336502251565557883 9969770004753377348336825)
              ·
                refine ⟨7477327503565033011252619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9969770004753377348336825 7477327503565033011252619)
                ·
                  refine ⟨11215991255347549516878929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7477327503565033011252619 11215991255347549516878929)
                  ·
                    refine ⟨8411993441510662137659197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11215991255347549516878929 8411993441510662137659197)
                    ·
                      refine ⟨3154497540566498301622199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8411993441510662137659197 3154497540566498301622199)
                      ·
                        rfl

theorem cell23_6143362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_6143362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6143362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6143362 prefixEnd_6143362 := by exact prefixLift 6143362
  have htrace : WordTrace (prefixWord ++ tailWord_6143362) baseStart_6143362 baseEnd_6143362 := by
    simpa [prefixWord, tailWord_6143362, baseEnd_6143362] using wordTrace_append hprefix tailTrace_6143362
  have hstable : (prefixWord ++ tailWord_6143362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6143362).length < 2 ^ (prefixWord ++ tailWord_6143362).sum := by decide
  have hdescent : baseEnd_6143362 < baseStart_6143362 := by decide
  rcases family_descends (prefixWord ++ tailWord_6143362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6143368 : List Nat := [2, 1, 3, 3, 1, 3, 1, 1, 3, 3, 2]
def baseStart_6143368 : Nat := 118140960795 + 6143368 * 2 ^ 59
def prefixEnd_6143368 : Nat := 4983230072969 + 3 ^ 40 * 6143368 * 2
def baseEnd_6143368 : Nat := 3154500621450425278147171

theorem tailTrace_6143368 : CollatzResearch.WordTrace tailWord_6143368 prefixEnd_6143368 3154500621450425278147171 := by
  unfold tailWord_6143368
  simp only [CollatzResearch.WordTrace]
  refine ⟨112033519403817207284067379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149378025871756276378756505 112033519403817207284067379)
  ·
    refine ⟨168050279105725810926101069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112033519403817207284067379 168050279105725810926101069)
    ·
      refine ⟨63018854664647179097287901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168050279105725810926101069 63018854664647179097287901)
      ·
        refine ⟨23632070499242692161482963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63018854664647179097287901 23632070499242692161482963)
        ·
          refine ⟨35448105748864038242224445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23632070499242692161482963 35448105748864038242224445)
          ·
            refine ⟨13293039655824014340834167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35448105748864038242224445 13293039655824014340834167)
            ·
              refine ⟨19939559483736021511251251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13293039655824014340834167 19939559483736021511251251)
              ·
                refine ⟨29909339225604032266876877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19939559483736021511251251 29909339225604032266876877)
                ·
                  refine ⟨11216002209601512100078829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29909339225604032266876877 11216002209601512100078829)
                  ·
                    refine ⟨4206000828600567037529561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11216002209601512100078829 4206000828600567037529561)
                    ·
                      refine ⟨3154500621450425278147171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4206000828600567037529561 3154500621450425278147171)
                      ·
                        rfl

theorem cell23_6143368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 1, 3, 3, 2].length) (baseStart_6143368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6143368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6143368 prefixEnd_6143368 := by exact prefixLift 6143368
  have htrace : WordTrace (prefixWord ++ tailWord_6143368) baseStart_6143368 baseEnd_6143368 := by
    simpa [prefixWord, tailWord_6143368, baseEnd_6143368] using wordTrace_append hprefix tailTrace_6143368
  have hstable : (prefixWord ++ tailWord_6143368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6143368).length < 2 ^ (prefixWord ++ tailWord_6143368).sum := by decide
  have hdescent : baseEnd_6143368 < baseStart_6143368 := by decide
  rcases family_descends (prefixWord ++ tailWord_6143368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6143381 : List Nat := [1, 3, 2, 1, 1, 2, 3, 1, 3, 4, 2]
def baseStart_6143381 : Nat := 118140960795 + 6143381 * 2 ^ 59
def prefixEnd_6143381 : Nat := 4983230072969 + 3 ^ 40 * 6143381 * 2
def baseEnd_6143381 : Nat := 3154507296698933727284611

theorem tailTrace_6143381 : CollatzResearch.WordTrace tailWord_6143381 prefixEnd_6143381 3154507296698933727284611 := by
  unfold tailWord_6143381
  simp only [CollatzResearch.WordTrace]
  refine ⟨224067512956587317788357997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149378341971058211858905331 224067512956587317788357997)
  ·
    refine ⟨84025317358720244170634249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 224067512956587317788357997 84025317358720244170634249)
    ·
      refine ⟨63018988019040183127975687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84025317358720244170634249 63018988019040183127975687)
      ·
        refine ⟨94528482028560274691963531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63018988019040183127975687 94528482028560274691963531)
        ·
          refine ⟨141792723042840412037945297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94528482028560274691963531 141792723042840412037945297)
          ·
            refine ⟨106344542282130309028458973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141792723042840412037945297 106344542282130309028458973)
            ·
              refine ⟨39879203355798865885672115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 106344542282130309028458973 39879203355798865885672115)
              ·
                refine ⟨59818805033698298828508173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39879203355798865885672115 59818805033698298828508173)
                ·
                  refine ⟨22432051887636862060690565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59818805033698298828508173 22432051887636862060690565)
                  ·
                    refine ⟨4206009728931911636379481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22432051887636862060690565 4206009728931911636379481)
                    ·
                      refine ⟨3154507296698933727284611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4206009728931911636379481 3154507296698933727284611)
                      ·
                        rfl

theorem cell23_6143381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 1, 3, 4, 2].length) (baseStart_6143381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6143381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6143381 prefixEnd_6143381 := by exact prefixLift 6143381
  have htrace : WordTrace (prefixWord ++ tailWord_6143381) baseStart_6143381 baseEnd_6143381 := by
    simpa [prefixWord, tailWord_6143381, baseEnd_6143381] using wordTrace_append hprefix tailTrace_6143381
  have hstable : (prefixWord ++ tailWord_6143381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6143381).length < 2 ^ (prefixWord ++ tailWord_6143381).sum := by decide
  have hdescent : baseEnd_6143381 < baseStart_6143381 := by decide
  rcases family_descends (prefixWord ++ tailWord_6143381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6143385 : List Nat := [1, 2, 1, 2, 1, 6, 3, 1, 1, 3, 2]
def baseStart_6143385 : Nat := 118140960795 + 6143385 * 2 ^ 59
def prefixEnd_6143385 : Nat := 4983230072969 + 3 ^ 40 * 6143385 * 2
def baseEnd_6143385 : Nat := 3154509350621551711634593

theorem tailTrace_6143385 : CollatzResearch.WordTrace tailWord_6143385 prefixEnd_6143385 3154509350621551711634593 := by
  unfold tailWord_6143385
  simp only [CollatzResearch.WordTrace]
  refine ⟨224067658848572826471503609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149378439232381884314335739 224067658848572826471503609)
  ·
    refine ⟨168050744136429619853627707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224067658848572826471503609 168050744136429619853627707)
    ·
      refine ⟨252076116204644429780441561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168050744136429619853627707 252076116204644429780441561)
      ·
        refine ⟨189057087153483322335331171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 252076116204644429780441561 189057087153483322335331171)
        ·
          refine ⟨283585630730224983502996757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189057087153483322335331171 283585630730224983502996757)
          ·
            refine ⟨13293076440479296101702973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 283585630730224983502996757 13293076440479296101702973)
            ·
              refine ⟨4984903665179736038138615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13293076440479296101702973 4984903665179736038138615)
              ·
                refine ⟨7477355497769604057207923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4984903665179736038138615 7477355497769604057207923)
                ·
                  refine ⟨11216033246654406085811885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7477355497769604057207923 11216033246654406085811885)
                  ·
                    refine ⟨4206012467495402282179457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11216033246654406085811885 4206012467495402282179457)
                    ·
                      refine ⟨3154509350621551711634593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4206012467495402282179457 3154509350621551711634593)
                      ·
                        rfl

theorem cell23_6143385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 3, 1, 1, 3, 2].length) (baseStart_6143385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6143385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6143385 prefixEnd_6143385 := by exact prefixLift 6143385
  have htrace : WordTrace (prefixWord ++ tailWord_6143385) baseStart_6143385 baseEnd_6143385 := by
    simpa [prefixWord, tailWord_6143385, baseEnd_6143385] using wordTrace_append hprefix tailTrace_6143385
  have hstable : (prefixWord ++ tailWord_6143385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6143385).length < 2 ^ (prefixWord ++ tailWord_6143385).sum := by decide
  have hdescent : baseEnd_6143385 < baseStart_6143385 := by decide
  rcases family_descends (prefixWord ++ tailWord_6143385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6143538 : List Nat := [3, 2, 1, 1, 2, 1, 1, 3, 5, 1, 3]
def baseStart_6143538 : Nat := 118140960795 + 6143538 * 2 ^ 59
def prefixEnd_6143538 : Nat := 4983230072969 + 3 ^ 40 * 6143538 * 2
def baseEnd_6143538 : Nat := 3154587913161689613021389

theorem tailTrace_6143538 : CollatzResearch.WordTrace tailWord_6143538 prefixEnd_6143538 3154587913161689613021389 := by
  unfold tailWord_6143538
  simp only [CollatzResearch.WordTrace]
  refine ⟨56018309804254633400455817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149382159478012355734548845 56018309804254633400455817)
  ·
    refine ⟨42013732353190975050341863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56018309804254633400455817 42013732353190975050341863)
    ·
      refine ⟨63020598529786462575512795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42013732353190975050341863 63020598529786462575512795)
      ·
        refine ⟨94530897794679693863269193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63020598529786462575512795 94530897794679693863269193)
        ·
          refine ⟨70898173346009770397451895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94530897794679693863269193 70898173346009770397451895)
          ·
            refine ⟨106347260019014655596177843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70898173346009770397451895 106347260019014655596177843)
            ·
              refine ⟨159520890028521983394266765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106347260019014655596177843 159520890028521983394266765)
              ·
                refine ⟨59820333760695743772850037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 159520890028521983394266765 59820333760695743772850037)
                ·
                  refine ⟨5608156290065225978704691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59820333760695743772850037 5608156290065225978704691)
                  ·
                    refine ⟨8412234435097838968057037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5608156290065225978704691 8412234435097838968057037)
                    ·
                      refine ⟨3154587913161689613021389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8412234435097838968057037 3154587913161689613021389)
                      ·
                        rfl

theorem cell23_6143538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 3, 5, 1, 3].length) (baseStart_6143538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6143538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6143538 prefixEnd_6143538 := by exact prefixLift 6143538
  have htrace : WordTrace (prefixWord ++ tailWord_6143538) baseStart_6143538 baseEnd_6143538 := by
    simpa [prefixWord, tailWord_6143538, baseEnd_6143538] using wordTrace_append hprefix tailTrace_6143538
  have hstable : (prefixWord ++ tailWord_6143538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6143538).length < 2 ^ (prefixWord ++ tailWord_6143538).sum := by decide
  have hdescent : baseEnd_6143538 < baseStart_6143538 := by decide
  rcases family_descends (prefixWord ++ tailWord_6143538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6143542 : List Nat := [5, 1, 2, 1, 3, 1, 2, 1, 2, 2, 3]
def baseStart_6143542 : Nat := 118140960795 + 6143542 * 2 ^ 59
def prefixEnd_6143542 : Nat := 4983230072969 + 3 ^ 40 * 6143542 * 2
def baseEnd_6143542 : Nat := 3154589967084307597371371

theorem tailTrace_6143542 : CollatzResearch.WordTrace tailWord_6143542 prefixEnd_6143542 3154589967084307597371371 := by
  unfold tailWord_6143542
  simp only [CollatzResearch.WordTrace]
  refine ⟨14004586569312752642810555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 149382256739336028189979253 14004586569312752642810555)
  ·
    refine ⟨21006879853969128964215833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14004586569312752642810555 21006879853969128964215833)
    ·
      refine ⟨15755159890476846723161875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21006879853969128964215833 15755159890476846723161875)
      ·
        refine ⟨23632739835715270084742813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15755159890476846723161875 23632739835715270084742813)
        ·
          refine ⟨8862277438393226281778555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23632739835715270084742813 8862277438393226281778555)
          ·
            refine ⟨13293416157589839422667833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8862277438393226281778555 13293416157589839422667833)
            ·
              refine ⟨9970062118192379567000875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13293416157589839422667833 9970062118192379567000875)
              ·
                refine ⟨14955093177288569350501313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9970062118192379567000875 14955093177288569350501313)
                ·
                  refine ⟨11216319882966427012875985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14955093177288569350501313 11216319882966427012875985)
                  ·
                    refine ⟨8412239912224820259656989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11216319882966427012875985 8412239912224820259656989)
                    ·
                      refine ⟨3154589967084307597371371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8412239912224820259656989 3154589967084307597371371)
                      ·
                        rfl

theorem cell23_6143542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 2, 1, 2, 2, 3].length) (baseStart_6143542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6143542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6143542 prefixEnd_6143542 := by exact prefixLift 6143542
  have htrace : WordTrace (prefixWord ++ tailWord_6143542) baseStart_6143542 baseEnd_6143542 := by
    simpa [prefixWord, tailWord_6143542, baseEnd_6143542] using wordTrace_append hprefix tailTrace_6143542
  have hstable : (prefixWord ++ tailWord_6143542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6143542).length < 2 ^ (prefixWord ++ tailWord_6143542).sum := by decide
  have hdescent : baseEnd_6143542 < baseStart_6143542 := by decide
  rcases family_descends (prefixWord ++ tailWord_6143542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6143572 : List Nat := [2, 4, 1, 1, 1, 2, 3, 4, 1, 1, 3]
def baseStart_6143572 : Nat := 118140960795 + 6143572 * 2 ^ 59
def prefixEnd_6143572 : Nat := 4983230072969 + 3 ^ 40 * 6143572 * 2
def baseEnd_6143572 : Nat := 3154605371503942479996233

theorem tailTrace_6143572 : CollatzResearch.WordTrace tailWord_6143572 prefixEnd_6143572 3154605371503942479996233 := by
  unfold tailWord_6143572
  simp only [CollatzResearch.WordTrace]
  refine ⟨112037239649447678704280485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149382986199263571605707313 112037239649447678704280485)
  ·
    refine ⟨21006982434271439757052591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112037239649447678704280485 21006982434271439757052591)
    ·
      refine ⟨31510473651407159635578887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21006982434271439757052591 31510473651407159635578887)
      ·
        refine ⟨47265710477110739453368331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31510473651407159635578887 47265710477110739453368331)
        ·
          refine ⟨70898565715666109180052497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47265710477110739453368331 70898565715666109180052497)
          ·
            refine ⟨53173924286749581885039373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70898565715666109180052497 53173924286749581885039373)
            ·
              refine ⟨19940221607531093206889765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53173924286749581885039373 19940221607531093206889765)
              ·
                refine ⟨3738791551412079976291831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19940221607531093206889765 3738791551412079976291831)
                ·
                  refine ⟨5608187327118119964437747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3738791551412079976291831 5608187327118119964437747)
                  ·
                    refine ⟨8412280990677179946656621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5608187327118119964437747 8412280990677179946656621)
                    ·
                      refine ⟨3154605371503942479996233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8412280990677179946656621 3154605371503942479996233)
                      ·
                        rfl

theorem cell23_6143572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 4, 1, 1, 3].length) (baseStart_6143572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6143572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6143572 prefixEnd_6143572 := by exact prefixLift 6143572
  have htrace : WordTrace (prefixWord ++ tailWord_6143572) baseStart_6143572 baseEnd_6143572 := by
    simpa [prefixWord, tailWord_6143572, baseEnd_6143572] using wordTrace_append hprefix tailTrace_6143572
  have hstable : (prefixWord ++ tailWord_6143572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6143572).length < 2 ^ (prefixWord ++ tailWord_6143572).sum := by decide
  have hdescent : baseEnd_6143572 < baseStart_6143572 := by decide
  rcases family_descends (prefixWord ++ tailWord_6143572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6143588 : List Nat := [2, 3, 1, 1, 2, 4, 2, 1, 1, 6]
def baseStart_6143588 : Nat := 118140960795 + 6143588 * 2 ^ 59
def prefixEnd_6143588 : Nat := 4983230072969 + 3 ^ 40 * 6143588 * 2
def baseEnd_6143588 : Nat := 1051537862398138139132053

theorem tailTrace_6143588 : CollatzResearch.WordTrace tailWord_6143588 prefixEnd_6143588 1051537862398138139132053 := by
  unfold tailWord_6143588
  simp only [CollatzResearch.WordTrace]
  refine ⟨112037531433418696070571709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149383375244558261427428945 112037531433418696070571709)
  ·
    refine ⟨42014074287532011026464391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112037531433418696070571709 42014074287532011026464391)
    ·
      refine ⟨63021111431298016539696587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42014074287532011026464391 63021111431298016539696587)
      ·
        refine ⟨94531667146947024809544881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63021111431298016539696587 94531667146947024809544881)
        ·
          refine ⟨70898750360210268607158661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94531667146947024809544881 70898750360210268607158661)
          ·
            refine ⟨13293515692539425363842249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70898750360210268607158661 13293515692539425363842249)
            ·
              refine ⟨9970136769404569022881687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13293515692539425363842249 9970136769404569022881687)
              ·
                refine ⟨14955205154106853534322531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9970136769404569022881687 14955205154106853534322531)
                ·
                  refine ⟨22432807731160280301483797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14955205154106853534322531 22432807731160280301483797)
                  ·
                    refine ⟨1051537862398138139132053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22432807731160280301483797 1051537862398138139132053)
                    ·
                      rfl

theorem cell23_6143588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 2, 1, 1, 6].length) (baseStart_6143588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6143588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6143588 prefixEnd_6143588 := by exact prefixLift 6143588
  have htrace : WordTrace (prefixWord ++ tailWord_6143588) baseStart_6143588 baseEnd_6143588 := by
    simpa [prefixWord, tailWord_6143588, baseEnd_6143588] using wordTrace_append hprefix tailTrace_6143588
  have hstable : (prefixWord ++ tailWord_6143588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6143588).length < 2 ^ (prefixWord ++ tailWord_6143588).sum := by decide
  have hdescent : baseEnd_6143588 < baseStart_6143588 := by decide
  rcases family_descends (prefixWord ++ tailWord_6143588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6143591 : List Nat := [1, 1, 5, 1, 1, 1, 2, 3, 1, 1, 6]
def baseStart_6143591 : Nat := 118140960795 + 6143591 * 2 ^ 59
def prefixEnd_6143591 : Nat := 4983230072969 + 3 ^ 40 * 6143591 * 2
def baseEnd_6143591 : Nat := 3154615127636377905658645

theorem tailTrace_6143591 : CollatzResearch.WordTrace tailWord_6143591 prefixEnd_6143591 3154615127636377905658645 := by
  unfold tailWord_6143591
  simp only [CollatzResearch.WordTrace]
  refine ⟨224075172285826523653502627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149383448190551015769001751 224075172285826523653502627)
  ·
    refine ⟨336112758428739785480253941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224075172285826523653502627 336112758428739785480253941)
    ·
      refine ⟨31510571102694354888773807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 336112758428739785480253941 31510571102694354888773807)
      ·
        refine ⟨47265856654041532333160711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31510571102694354888773807 47265856654041532333160711)
        ·
          refine ⟨70898784981062298499741067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47265856654041532333160711 70898784981062298499741067)
          ·
            refine ⟨106348177471593447749611601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70898784981062298499741067 106348177471593447749611601)
            ·
              refine ⟨79761133103695085812208701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106348177471593447749611601 79761133103695085812208701)
              ·
                refine ⟨29910424913885657179578263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79761133103695085812208701 29910424913885657179578263)
                ·
                  refine ⟨44865637370828485769367395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29910424913885657179578263 44865637370828485769367395)
                  ·
                    refine ⟨67298456056242728654051093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44865637370828485769367395 67298456056242728654051093)
                    ·
                      refine ⟨3154615127636377905658645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67298456056242728654051093 3154615127636377905658645)
                      ·
                        rfl

theorem cell23_6143591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 3, 1, 1, 6].length) (baseStart_6143591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6143591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6143591 prefixEnd_6143591 := by exact prefixLift 6143591
  have htrace : WordTrace (prefixWord ++ tailWord_6143591) baseStart_6143591 baseEnd_6143591 := by
    simpa [prefixWord, tailWord_6143591, baseEnd_6143591] using wordTrace_append hprefix tailTrace_6143591
  have hstable : (prefixWord ++ tailWord_6143591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6143591).length < 2 ^ (prefixWord ++ tailWord_6143591).sum := by decide
  have hdescent : baseEnd_6143591 < baseStart_6143591 := by decide
  rcases family_descends (prefixWord ++ tailWord_6143591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6143688 : List Nat := [2, 1, 3, 1, 2, 2, 2, 1, 2, 4, 3]
def baseStart_6143688 : Nat := 118140960795 + 6143688 * 2 ^ 59
def prefixEnd_6143688 : Nat := 4983230072969 + 3 ^ 40 * 6143688 * 2
def baseEnd_6143688 : Nat := 3154664935259864026145699

theorem tailTrace_6143688 : CollatzResearch.WordTrace tailWord_6143688 prefixEnd_6143688 3154664935259864026145699 := by
  unfold tailWord_6143688
  simp only [CollatzResearch.WordTrace]
  refine ⟨112039355083237554609891859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149385806777650072813189145 112039355083237554609891859)
  ·
    refine ⟨168059032624856331914837789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112039355083237554609891859 168059032624856331914837789)
    ·
      refine ⟨63022137234321124468064171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168059032624856331914837789 63022137234321124468064171)
      ·
        refine ⟨94533205851481686702096257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63022137234321124468064171 94533205851481686702096257)
        ·
          refine ⟨70899904388611265026572193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94533205851481686702096257 70899904388611265026572193)
          ·
            refine ⟨53174928291458448769929145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70899904388611265026572193 53174928291458448769929145)
            ·
              refine ⟨39881196218593836577446859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53174928291458448769929145 39881196218593836577446859)
              ·
                refine ⟨59821794327890754866170289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39881196218593836577446859 59821794327890754866170289)
                ·
                  refine ⟨44866345745918066149627717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59821794327890754866170289 44866345745918066149627717)
                  ·
                    refine ⟨8412439827359637403055197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44866345745918066149627717 8412439827359637403055197)
                    ·
                      refine ⟨3154664935259864026145699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8412439827359637403055197 3154664935259864026145699)
                      ·
                        rfl

theorem cell23_6143688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 1, 2, 4, 3].length) (baseStart_6143688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6143688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6143688 prefixEnd_6143688 := by exact prefixLift 6143688
  have htrace : WordTrace (prefixWord ++ tailWord_6143688) baseStart_6143688 baseEnd_6143688 := by
    simpa [prefixWord, tailWord_6143688, baseEnd_6143688] using wordTrace_append hprefix tailTrace_6143688
  have hstable : (prefixWord ++ tailWord_6143688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6143688).length < 2 ^ (prefixWord ++ tailWord_6143688).sum := by decide
  have hdescent : baseEnd_6143688 < baseStart_6143688 := by decide
  rcases family_descends (prefixWord ++ tailWord_6143688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6143719 : List Nat := [1, 1, 5, 4, 1, 1, 1, 2, 1, 4, 2]
def baseStart_6143719 : Nat := 118140960795 + 6143719 * 2 ^ 59
def prefixEnd_6143719 : Nat := 4983230072969 + 3 ^ 40 * 6143719 * 2
def baseEnd_6143719 : Nat := 3154680853160153404858057

theorem tailTrace_6143719 : CollatzResearch.WordTrace tailWord_6143719 prefixEnd_6143719 3154680853160153404858057 := by
  unfold tailWord_6143719
  simp only [CollatzResearch.WordTrace]
  refine ⟨224079840829362801514162211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149386560552908534342774807 224079840829362801514162211)
  ·
    refine ⟨336119761244044202271243317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224079840829362801514162211 336119761244044202271243317)
    ·
      refine ⟨31511227616629143962929061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 336119761244044202271243317 31511227616629143962929061)
      ·
        refine ⟨5908355178117964493049199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31511227616629143962929061 5908355178117964493049199)
        ·
          refine ⟨8862532767176946739573799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5908355178117964493049199 8862532767176946739573799)
          ·
            refine ⟨13293799150765420109360699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8862532767176946739573799 13293799150765420109360699)
            ·
              refine ⟨19940698726148130164041049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13293799150765420109360699 19940698726148130164041049)
              ·
                refine ⟨14955524044611097623030787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19940698726148130164041049 14955524044611097623030787)
                ·
                  refine ⟨22433286066916646434546181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14955524044611097623030787 22433286066916646434546181)
                  ·
                    refine ⟨4206241137546871206477409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22433286066916646434546181 4206241137546871206477409)
                    ·
                      refine ⟨3154680853160153404858057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4206241137546871206477409 3154680853160153404858057)
                      ·
                        rfl

theorem cell23_6143719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_6143719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6143719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6143719 prefixEnd_6143719 := by exact prefixLift 6143719
  have htrace : WordTrace (prefixWord ++ tailWord_6143719) baseStart_6143719 baseEnd_6143719 := by
    simpa [prefixWord, tailWord_6143719, baseEnd_6143719] using wordTrace_append hprefix tailTrace_6143719
  have hstable : (prefixWord ++ tailWord_6143719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6143719).length < 2 ^ (prefixWord ++ tailWord_6143719).sum := by decide
  have hdescent : baseEnd_6143719 < baseStart_6143719 := by decide
  rcases family_descends (prefixWord ++ tailWord_6143719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6143745 : List Nat := [1, 2, 4, 1, 1, 1, 3, 1, 2, 5, 2]
def baseStart_6143745 : Nat := 118140960795 + 6143745 * 2 ^ 59
def prefixEnd_6143745 : Nat := 4983230072969 + 3 ^ 40 * 6143745 * 2
def baseEnd_6143745 : Nat := 3154694203657170303132937

theorem tailTrace_6143745 : CollatzResearch.WordTrace tailWord_6143745 prefixEnd_6143745 3154694203657170303132937 := by
  unfold tailWord_6143745
  simp only [CollatzResearch.WordTrace]
  refine ⟨224080789127268607954608689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149387192751512405303072459 224080789127268607954608689)
  ·
    refine ⟨168060591845451455965956517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224080789127268607954608689 168060591845451455965956517)
    ·
      refine ⟨31511360971022147993616847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 168060591845451455965956517 31511360971022147993616847)
      ·
        refine ⟨47267041456533221990425271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31511360971022147993616847 47267041456533221990425271)
        ·
          refine ⟨70900562184799832985637907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47267041456533221990425271 70900562184799832985637907)
          ·
            refine ⟨106350843277199749478456861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70900562184799832985637907 106350843277199749478456861)
            ·
              refine ⟨39881566228949906054421323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 106350843277199749478456861 39881566228949906054421323)
              ·
                refine ⟨59822349343424859081631985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39881566228949906054421323 59822349343424859081631985)
                ·
                  refine ⟨44866762007568644311223989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59822349343424859081631985 44866762007568644311223989)
                  ·
                    refine ⟨4206258938209560404177249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44866762007568644311223989 4206258938209560404177249)
                    ·
                      refine ⟨3154694203657170303132937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4206258938209560404177249 3154694203657170303132937)
                      ·
                        rfl

theorem cell23_6143745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 1, 2, 5, 2].length) (baseStart_6143745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6143745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6143745 prefixEnd_6143745 := by exact prefixLift 6143745
  have htrace : WordTrace (prefixWord ++ tailWord_6143745) baseStart_6143745 baseEnd_6143745 := by
    simpa [prefixWord, tailWord_6143745, baseEnd_6143745] using wordTrace_append hprefix tailTrace_6143745
  have hstable : (prefixWord ++ tailWord_6143745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6143745).length < 2 ^ (prefixWord ++ tailWord_6143745).sum := by decide
  have hdescent : baseEnd_6143745 < baseStart_6143745 := by decide
  rcases family_descends (prefixWord ++ tailWord_6143745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6143775 : List Nat := [1, 1, 2, 4, 2, 1, 1, 2, 1, 6, 2]
def baseStart_6143775 : Nat := 118140960795 + 6143775 * 2 ^ 59
def prefixEnd_6143775 : Nat := 4983230072969 + 3 ^ 40 * 6143775 * 2
def baseEnd_6143775 : Nat := 3154709608076805185757799

theorem tailTrace_6143775 : CollatzResearch.WordTrace tailWord_6143775 prefixEnd_6143775 3154709608076805185757799 := by
  unfold tailWord_6143775
  simp only [CollatzResearch.WordTrace]
  refine ⟨224081883317159923078200779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149387922211439948718800519 224081883317159923078200779)
  ·
    refine ⟨336122824975739884617301169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224081883317159923078200779 336122824975739884617301169)
    ·
      refine ⟨252092118731804913462975877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 336122824975739884617301169 252092118731804913462975877)
      ·
        refine ⟨47267272262213421274307977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 252092118731804913462975877 47267272262213421274307977)
        ·
          refine ⟨35450454196660065955730983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47267272262213421274307977 35450454196660065955730983)
          ·
            refine ⟨53175681294990098933596475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35450454196660065955730983 53175681294990098933596475)
            ·
              refine ⟨79763521942485148400394713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53175681294990098933596475 79763521942485148400394713)
              ·
                refine ⟨59822641456863861300296035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79763521942485148400394713 59822641456863861300296035)
                ·
                  refine ⟨89733962185295791950444053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59822641456863861300296035 89733962185295791950444053)
                  ·
                    refine ⟨4206279477435740247677065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 89733962185295791950444053 4206279477435740247677065)
                    ·
                      refine ⟨3154709608076805185757799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4206279477435740247677065 3154709608076805185757799)
                      ·
                        rfl

theorem cell23_6143775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 2, 1, 6, 2].length) (baseStart_6143775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6143775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6143775 prefixEnd_6143775 := by exact prefixLift 6143775
  have htrace : WordTrace (prefixWord ++ tailWord_6143775) baseStart_6143775 baseEnd_6143775 := by
    simpa [prefixWord, tailWord_6143775, baseEnd_6143775] using wordTrace_append hprefix tailTrace_6143775
  have hstable : (prefixWord ++ tailWord_6143775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6143775).length < 2 ^ (prefixWord ++ tailWord_6143775).sum := by decide
  have hdescent : baseEnd_6143775 < baseStart_6143775 := by decide
  rcases family_descends (prefixWord ++ tailWord_6143775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6143788 : List Nat := [2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 6]
def baseStart_6143788 : Nat := 118140960795 + 6143788 * 2 ^ 59
def prefixEnd_6143788 : Nat := 4983230072969 + 3 ^ 40 * 6143788 * 2
def baseEnd_6143788 : Nat := 3154716283325313634895239

theorem tailTrace_6143788 : CollatzResearch.WordTrace tailWord_6143788 prefixEnd_6143788 3154716283325313634895239 := by
  unfold tailWord_6143788
  simp only [CollatzResearch.WordTrace]
  refine ⟨112041178733056413149212009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149388238310741884198949345 112041178733056413149212009)
  ·
    refine ⟨84030884049792309861909007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112041178733056413149212009 84030884049792309861909007)
    ·
      refine ⟨126046326074688464792863511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84030884049792309861909007 126046326074688464792863511)
      ·
        refine ⟨189069489112032697189295267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126046326074688464792863511 189069489112032697189295267)
        ·
          refine ⟨283604233668049045783942901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189069489112032697189295267 283604233668049045783942901)
          ·
            refine ⟨26587896906379598042244647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 283604233668049045783942901 26587896906379598042244647)
            ·
              refine ⟨39881845359569397063366971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26587896906379598042244647 39881845359569397063366971)
              ·
                refine ⟨59822768039354095595050457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39881845359569397063366971 59822768039354095595050457)
                ·
                  refine ⟨44867076029515571696287843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59822768039354095595050457 44867076029515571696287843)
                  ·
                    refine ⟨67300614044273357544431765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44867076029515571696287843 67300614044273357544431765)
                    ·
                      refine ⟨3154716283325313634895239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67300614044273357544431765 3154716283325313634895239)
                      ·
                        rfl

theorem cell23_6143788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 6].length) (baseStart_6143788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6143788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6143788 prefixEnd_6143788 := by exact prefixLift 6143788
  have htrace : WordTrace (prefixWord ++ tailWord_6143788) baseStart_6143788 baseEnd_6143788 := by
    simpa [prefixWord, tailWord_6143788, baseEnd_6143788] using wordTrace_append hprefix tailTrace_6143788
  have hstable : (prefixWord ++ tailWord_6143788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6143788).length < 2 ^ (prefixWord ++ tailWord_6143788).sum := by decide
  have hdescent : baseEnd_6143788 < baseStart_6143788 := by decide
  rcases family_descends (prefixWord ++ tailWord_6143788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6143802 : List Nat := [3, 1, 1, 1, 5, 2, 2, 1, 3, 4]
def baseStart_6143802 : Nat := 118140960795 + 6143802 * 2 ^ 59
def prefixEnd_6143802 : Nat := 4983230072969 + 3 ^ 40 * 6143802 * 2
def baseEnd_6143802 : Nat := 1051574490684825526706725

theorem tailTrace_6143802 : CollatzResearch.WordTrace tailWord_6143802 prefixEnd_6143802 1051574490684825526706725 := by
  unfold tailWord_6143802
  simp only [CollatzResearch.WordTrace]
  refine ⟨56020717022015526672358415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149388578725374737792955773 56020717022015526672358415)
  ·
    refine ⟨84031075533023290008537623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56020717022015526672358415 84031075533023290008537623)
    ·
      refine ⟨126046613299534935012806435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84031075533023290008537623 126046613299534935012806435)
      ·
        refine ⟨189069919949302402519209653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126046613299534935012806435 189069919949302402519209653)
        ·
          refine ⟨17725304995247100236175905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 189069919949302402519209653 17725304995247100236175905)
          ·
            refine ⟨13293978746435325177131929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17725304995247100236175905 13293978746435325177131929)
            ·
              refine ⟨9970484059826493882848947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13293978746435325177131929 9970484059826493882848947)
              ·
                refine ⟨14955726089739740824273421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9970484059826493882848947 14955726089739740824273421)
                ·
                  refine ⟨5608397283652402809102533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14955726089739740824273421 5608397283652402809102533)
                  ·
                    refine ⟨1051574490684825526706725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5608397283652402809102533 1051574490684825526706725)
                    ·
                      rfl

theorem cell23_6143802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 2, 1, 3, 4].length) (baseStart_6143802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6143802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6143802 prefixEnd_6143802 := by exact prefixLift 6143802
  have htrace : WordTrace (prefixWord ++ tailWord_6143802) baseStart_6143802 baseEnd_6143802 := by
    simpa [prefixWord, tailWord_6143802, baseEnd_6143802] using wordTrace_append hprefix tailTrace_6143802
  have hstable : (prefixWord ++ tailWord_6143802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6143802).length < 2 ^ (prefixWord ++ tailWord_6143802).sum := by decide
  have hdescent : baseEnd_6143802 < baseStart_6143802 := by decide
  rcases family_descends (prefixWord ++ tailWord_6143802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6143818 : List Nat := [3, 1, 2, 1, 1, 1, 3, 2, 1, 2, 6]
def baseStart_6143818 : Nat := 118140960795 + 6143818 * 2 ^ 59
def prefixEnd_6143818 : Nat := 4983230072969 + 3 ^ 40 * 6143818 * 2
def baseEnd_6143818 : Nat := 3154731687744948517520101

theorem tailTrace_6143818 : CollatzResearch.WordTrace tailWord_6143818 prefixEnd_6143818 3154731687744948517520101 := by
  unfold tailWord_6143818
  simp only [CollatzResearch.WordTrace]
  refine ⟨56020862914001035355504027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149388967770669427614677405 56020862914001035355504027)
  ·
    refine ⟨84031294371001553033256041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56020862914001035355504027 84031294371001553033256041)
    ·
      refine ⟨63023470778251164774942031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84031294371001553033256041 63023470778251164774942031)
      ·
        refine ⟨94535206167376747162413047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63023470778251164774942031 94535206167376747162413047)
        ·
          refine ⟨141802809251065120743619571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94535206167376747162413047 141802809251065120743619571)
          ·
            refine ⟨212704213876597681115429357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141802809251065120743619571 212704213876597681115429357)
            ·
              refine ⟨79764080203724130418286009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 212704213876597681115429357 79764080203724130418286009)
              ·
                refine ⟨59823060152793097813714507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79764080203724130418286009 59823060152793097813714507)
                ·
                  refine ⟨89734590229189646720571761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 59823060152793097813714507 89734590229189646720571761)
                  ·
                    refine ⟨67300942671892235040428821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 89734590229189646720571761 67300942671892235040428821)
                    ·
                      refine ⟨3154731687744948517520101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67300942671892235040428821 3154731687744948517520101)
                      ·
                        rfl

theorem cell23_6143818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 2, 1, 2, 6].length) (baseStart_6143818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6143818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6143818 prefixEnd_6143818 := by exact prefixLift 6143818
  have htrace : WordTrace (prefixWord ++ tailWord_6143818) baseStart_6143818 baseEnd_6143818 := by
    simpa [prefixWord, tailWord_6143818, baseEnd_6143818] using wordTrace_append hprefix tailTrace_6143818
  have hstable : (prefixWord ++ tailWord_6143818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6143818).length < 2 ^ (prefixWord ++ tailWord_6143818).sum := by decide
  have hdescent : baseEnd_6143818 < baseStart_6143818 := by decide
  rcases family_descends (prefixWord ++ tailWord_6143818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6143852 : List Nat := [2, 2, 1, 1, 4, 2, 1, 1, 4, 3, 2]
def baseStart_6143852 : Nat := 118140960795 + 6143852 * 2 ^ 59
def prefixEnd_6143852 : Nat := 4983230072969 + 3 ^ 40 * 6143852 * 2
def baseEnd_6143852 : Nat := 3154749146087201384494945

theorem tailTrace_6143852 : CollatzResearch.WordTrace tailWord_6143852 prefixEnd_6143852 3154749146087201384494945 := by
  unfold tailWord_6143852
  simp only [CollatzResearch.WordTrace]
  refine ⟨112042345868940482614376905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149389794491920643485835873 112042345868940482614376905)
  ·
    refine ⟨84031759401705361960782679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112042345868940482614376905 84031759401705361960782679)
    ·
      refine ⟨126047639102558042941174019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84031759401705361960782679 126047639102558042941174019)
      ·
        refine ⟨189071458653837064411761029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126047639102558042941174019 189071458653837064411761029)
        ·
          refine ⟨35450898497594449577205193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 189071458653837064411761029 35450898497594449577205193)
          ·
            refine ⟨26588173873195837182903895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35450898497594449577205193 26588173873195837182903895)
            ·
              refine ⟨39882260809793755774355843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26588173873195837182903895 39882260809793755774355843)
              ·
                refine ⟨59823391214690633661533765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39882260809793755774355843 59823391214690633661533765)
                ·
                  refine ⟨11216885852754493811537581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59823391214690633661533765 11216885852754493811537581)
                  ·
                    refine ⟨4206332194782935179326593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11216885852754493811537581 4206332194782935179326593)
                    ·
                      refine ⟨3154749146087201384494945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4206332194782935179326593 3154749146087201384494945)
                      ·
                        rfl

theorem cell23_6143852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 3, 2].length) (baseStart_6143852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6143852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6143852 prefixEnd_6143852 := by exact prefixLift 6143852
  have htrace : WordTrace (prefixWord ++ tailWord_6143852) baseStart_6143852 baseEnd_6143852 := by
    simpa [prefixWord, tailWord_6143852, baseEnd_6143852] using wordTrace_append hprefix tailTrace_6143852
  have hstable : (prefixWord ++ tailWord_6143852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6143852).length < 2 ^ (prefixWord ++ tailWord_6143852).sum := by decide
  have hdescent : baseEnd_6143852 < baseStart_6143852 := by decide
  rcases family_descends (prefixWord ++ tailWord_6143852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6143865 : List Nat := [1, 2, 1, 3, 2, 2, 2, 2, 3, 1, 4]
def baseStart_6143865 : Nat := 118140960795 + 6143865 * 2 ^ 59
def prefixEnd_6143865 : Nat := 4983230072969 + 3 ^ 40 * 6143865 * 2
def baseEnd_6143865 : Nat := 3154755821335709833632385

theorem tailTrace_6143865 : CollatzResearch.WordTrace tailWord_6143865 prefixEnd_6143865 3154755821335709833632385 := by
  unfold tailWord_6143865
  simp only [CollatzResearch.WordTrace]
  refine ⟨224085165886833868448977049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149390110591222578965984699 224085165886833868448977049)
  ·
    refine ⟨168063874415125401336732787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224085165886833868448977049 168063874415125401336732787)
    ·
      refine ⟨252095811622688102005099181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168063874415125401336732787 252095811622688102005099181)
      ·
        refine ⟨94535929358508038251912193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 252095811622688102005099181 94535929358508038251912193)
        ·
          refine ⟨70901947018881028688934145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94535929358508038251912193 70901947018881028688934145)
          ·
            refine ⟨53176460264160771516700609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70901947018881028688934145 53176460264160771516700609)
            ·
              refine ⟨39882345198120578637525457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53176460264160771516700609 39882345198120578637525457)
              ·
                refine ⟨29911758898590433978144093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39882345198120578637525457 29911758898590433978144093)
                ·
                  refine ⟨11216909586971412741804035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29911758898590433978144093 11216909586971412741804035)
                  ·
                    refine ⟨16825364380457119112706053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11216909586971412741804035 16825364380457119112706053)
                    ·
                      refine ⟨3154755821335709833632385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16825364380457119112706053 3154755821335709833632385)
                      ·
                        rfl

theorem cell23_6143865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 2, 3, 1, 4].length) (baseStart_6143865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6143865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6143865 prefixEnd_6143865 := by exact prefixLift 6143865
  have htrace : WordTrace (prefixWord ++ tailWord_6143865) baseStart_6143865 baseEnd_6143865 := by
    simpa [prefixWord, tailWord_6143865, baseEnd_6143865] using wordTrace_append hprefix tailTrace_6143865
  have hstable : (prefixWord ++ tailWord_6143865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6143865).length < 2 ^ (prefixWord ++ tailWord_6143865).sum := by decide
  have hdescent : baseEnd_6143865 < baseStart_6143865 := by decide
  rcases family_descends (prefixWord ++ tailWord_6143865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6143879 : List Nat := [1, 1, 4, 2, 4, 2, 1, 2, 1, 5]
def baseStart_6143879 : Nat := 118140960795 + 6143879 * 2 ^ 59
def prefixEnd_6143879 : Nat := 4983230072969 + 3 ^ 40 * 6143879 * 2
def baseEnd_6143879 : Nat := 1051587670021624259619107

theorem tailTrace_6143879 : CollatzResearch.WordTrace tailWord_6143879 prefixEnd_6143879 1051587670021624259619107 := by
  unfold tailWord_6143879
  simp only [CollatzResearch.WordTrace]
  refine ⟨224085676508783148839986691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149390451005855432559991127 224085676508783148839986691)
  ·
    refine ⟨336128514763174723259980037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224085676508783148839986691 336128514763174723259980037)
    ·
      refine ⟨63024096518095260611246257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 336128514763174723259980037 63024096518095260611246257)
      ·
        refine ⟨47268072388571445458434693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63024096518095260611246257 47268072388571445458434693)
        ·
          refine ⟨8862763572857146023456505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47268072388571445458434693 8862763572857146023456505)
          ·
            refine ⟨6647072679642859517592379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8862763572857146023456505 6647072679642859517592379)
            ·
              refine ⟨9970609019464289276388569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6647072679642859517592379 9970609019464289276388569)
              ·
                refine ⟨7477956764598216957291427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9970609019464289276388569 7477956764598216957291427)
                ·
                  refine ⟨11216935146897325435937141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7477956764598216957291427 11216935146897325435937141)
                  ·
                    refine ⟨1051587670021624259619107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11216935146897325435937141 1051587670021624259619107)
                    ·
                      rfl

theorem cell23_6143879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 1, 2, 1, 5].length) (baseStart_6143879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6143879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6143879 prefixEnd_6143879 := by exact prefixLift 6143879
  have htrace : WordTrace (prefixWord ++ tailWord_6143879) baseStart_6143879 baseEnd_6143879 := by
    simpa [prefixWord, tailWord_6143879, baseEnd_6143879] using wordTrace_append hprefix tailTrace_6143879
  have hstable : (prefixWord ++ tailWord_6143879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6143879).length < 2 ^ (prefixWord ++ tailWord_6143879).sum := by decide
  have hdescent : baseEnd_6143879 < baseStart_6143879 := by decide
  rcases family_descends (prefixWord ++ tailWord_6143879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6143892 : List Nat := [2, 4, 2, 1, 1, 3, 1, 2, 1, 6]
def baseStart_6143892 : Nat := 118140960795 + 6143892 * 2 ^ 59
def prefixEnd_6143892 : Nat := 4983230072969 + 3 ^ 40 * 6143892 * 2
def baseEnd_6143892 : Nat := 1051589895104460409331587

theorem tailTrace_6143892 : CollatzResearch.WordTrace tailWord_6143892 prefixEnd_6143892 1051589895104460409331587 := by
  unfold tailWord_6143892
  simp only [CollatzResearch.WordTrace]
  refine ⟨112043075328868026030104965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149390767105157368040139953 112043075328868026030104965)
  ·
    refine ⟨21008076624162754880644681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 112043075328868026030104965 21008076624162754880644681)
    ·
      refine ⟨15756057468122066160483511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21008076624162754880644681 15756057468122066160483511)
      ·
        refine ⟨23634086202183099240725267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15756057468122066160483511 23634086202183099240725267)
        ·
          refine ⟨35451129303274648861087901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23634086202183099240725267 35451129303274648861087901)
          ·
            refine ⟨13294173488727993322907963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35451129303274648861087901 13294173488727993322907963)
            ·
              refine ⟨19941260233091989984361945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13294173488727993322907963 19941260233091989984361945)
              ·
                refine ⟨14955945174818992488271459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19941260233091989984361945 14955945174818992488271459)
                ·
                  refine ⟨22433917762228488732407189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14955945174818992488271459 22433917762228488732407189)
                  ·
                    refine ⟨1051589895104460409331587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22433917762228488732407189 1051589895104460409331587)
                    ·
                      rfl

theorem cell23_6143892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 2, 1, 6].length) (baseStart_6143892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6143892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6143892 prefixEnd_6143892 := by exact prefixLift 6143892
  have htrace : WordTrace (prefixWord ++ tailWord_6143892) baseStart_6143892 baseEnd_6143892 := by
    simpa [prefixWord, tailWord_6143892, baseEnd_6143892] using wordTrace_append hprefix tailTrace_6143892
  have hstable : (prefixWord ++ tailWord_6143892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6143892).length < 2 ^ (prefixWord ++ tailWord_6143892).sum := by decide
  have hdescent : baseEnd_6143892 < baseStart_6143892 := by decide
  rcases family_descends (prefixWord ++ tailWord_6143892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6143895 : List Nat := [1, 1, 3, 3, 1, 3, 1, 1, 3, 2, 4]
def baseStart_6143895 : Nat := 118140960795 + 6143895 * 2 ^ 59
def prefixEnd_6143895 : Nat := 4983230072969 + 3 ^ 40 * 6143895 * 2
def baseEnd_6143895 : Nat := 3154771225755344716257247

theorem tailTrace_6143895 : CollatzResearch.WordTrace tailWord_6143895 prefixEnd_6143895 3154771225755344716257247 := by
  unfold tailWord_6143895
  simp only [CollatzResearch.WordTrace]
  refine ⟨224086260076725183572569139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149390840051150122381712759 224086260076725183572569139)
  ·
    refine ⟨336129390115087775358853709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224086260076725183572569139 336129390115087775358853709)
    ·
      refine ⟨126048521293157915759570141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 336129390115087775358853709 126048521293157915759570141)
      ·
        refine ⟨47268195484934218409838803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126048521293157915759570141 47268195484934218409838803)
        ·
          refine ⟨70902293227401327614758205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47268195484934218409838803 70902293227401327614758205)
          ·
            refine ⟨26588359960275497855534327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70902293227401327614758205 26588359960275497855534327)
            ·
              refine ⟨39882539940413246783301491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26588359960275497855534327 39882539940413246783301491)
              ·
                refine ⟨59823809910619870174952237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39882539940413246783301491 59823809910619870174952237)
                ·
                  refine ⟨22433928716482451315607089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59823809910619870174952237 22433928716482451315607089)
                  ·
                    refine ⟨16825446537361838486705317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22433928716482451315607089 16825446537361838486705317)
                    ·
                      refine ⟨3154771225755344716257247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16825446537361838486705317 3154771225755344716257247)
                      ·
                        rfl

theorem cell23_6143895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 1, 3, 2, 4].length) (baseStart_6143895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6143895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6143895 prefixEnd_6143895 := by exact prefixLift 6143895
  have htrace : WordTrace (prefixWord ++ tailWord_6143895) baseStart_6143895 baseEnd_6143895 := by
    simpa [prefixWord, tailWord_6143895, baseEnd_6143895] using wordTrace_append hprefix tailTrace_6143895
  have hstable : (prefixWord ++ tailWord_6143895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6143895).length < 2 ^ (prefixWord ++ tailWord_6143895).sum := by decide
  have hdescent : baseEnd_6143895 < baseStart_6143895 := by decide
  rcases family_descends (prefixWord ++ tailWord_6143895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6143896 : List Nat := [2, 1, 2, 6, 1, 1, 3, 1, 1, 5]
def baseStart_6143896 : Nat := 118140960795 + 6143896 * 2 ^ 59
def prefixEnd_6143896 : Nat := 4983230072969 + 3 ^ 40 * 6143896 * 2
def baseEnd_6143896 : Nat := 1051590579745333070781581

theorem tailTrace_6143896 : CollatzResearch.WordTrace tailWord_6143896 prefixEnd_6143896 1051590579745333070781581 := by
  unfold tailWord_6143896
  simp only [CollatzResearch.WordTrace]
  refine ⟨112043148274860780371677771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149390864366481040495570361 112043148274860780371677771)
  ·
    refine ⟨168064722412291170557516657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112043148274860780371677771 168064722412291170557516657)
    ·
      refine ⟨126048541809218377918137493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168064722412291170557516657 126048541809218377918137493)
      ·
        refine ⟨5908525397307111464912695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 126048541809218377918137493 5908525397307111464912695)
        ·
          refine ⟨8862788095960667197369043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5908525397307111464912695 8862788095960667197369043)
          ·
            refine ⟨13294182143941000796053565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8862788095960667197369043 13294182143941000796053565)
            ·
              refine ⟨4985318303977875298520087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13294182143941000796053565 4985318303977875298520087)
              ·
                refine ⟨7477977455966812947780131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4985318303977875298520087 7477977455966812947780131)
                ·
                  refine ⟨11216966183950219421670197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7477977455966812947780131 11216966183950219421670197)
                  ·
                    refine ⟨1051590579745333070781581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11216966183950219421670197 1051590579745333070781581)
                    ·
                      rfl

theorem cell23_6143896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 3, 1, 1, 5].length) (baseStart_6143896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6143896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6143896 prefixEnd_6143896 := by exact prefixLift 6143896
  have htrace : WordTrace (prefixWord ++ tailWord_6143896) baseStart_6143896 baseEnd_6143896 := by
    simpa [prefixWord, tailWord_6143896, baseEnd_6143896] using wordTrace_append hprefix tailTrace_6143896
  have hstable : (prefixWord ++ tailWord_6143896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6143896).length < 2 ^ (prefixWord ++ tailWord_6143896).sum := by decide
  have hdescent : baseEnd_6143896 < baseStart_6143896 := by decide
  rcases family_descends (prefixWord ++ tailWord_6143896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6143905 : List Nat := [1, 2, 3, 4, 2, 11]
def baseStart_6143905 : Nat := 118140960795 + 6143905 * 2 ^ 59
def prefixEnd_6143905 : Nat := 4983230072969 + 3 ^ 40 * 6143905 * 2
def baseEnd_6143905 : Nat := 12982618767744401963507

theorem tailTrace_6143905 : CollatzResearch.WordTrace tailWord_6143905 prefixEnd_6143905 12982618767744401963507 := by
  unfold tailWord_6143905
  simp only [CollatzResearch.WordTrace]
  refine ⟨224086624806688955280433169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149391083204459303520288779 224086624806688955280433169)
  ·
    refine ⟨168064968605016716460324877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224086624806688955280433169 168064968605016716460324877)
    ·
      refine ⟨63024363226881268672621829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168064968605016716460324877 63024363226881268672621829)
      ·
        refine ⟨11817068105040237876116593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63024363226881268672621829 11817068105040237876116593)
        ·
          refine ⟨8862801078780178407087445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11817068105040237876116593 8862801078780178407087445)
          ·
            refine ⟨12982618767744401963507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 8862801078780178407087445 12982618767744401963507)
            ·
              rfl

theorem cell23_6143905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 11].length) (baseStart_6143905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6143905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6143905 prefixEnd_6143905 := by exact prefixLift 6143905
  have htrace : WordTrace (prefixWord ++ tailWord_6143905) baseStart_6143905 baseEnd_6143905 := by
    simpa [prefixWord, tailWord_6143905, baseEnd_6143905] using wordTrace_append hprefix tailTrace_6143905
  have hstable : (prefixWord ++ tailWord_6143905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6143905).length < 2 ^ (prefixWord ++ tailWord_6143905).sum := by decide
  have hdescent : baseEnd_6143905 < baseStart_6143905 := by decide
  rcases family_descends (prefixWord ++ tailWord_6143905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6143959 : List Nat := [1, 1, 3, 2, 1, 1, 5, 3, 1, 3, 2]
def baseStart_6143959 : Nat := 118140960795 + 6143959 * 2 ^ 59
def prefixEnd_6143959 : Nat := 4983230072969 + 3 ^ 40 * 6143959 * 2
def baseEnd_6143959 : Nat := 3154804088517232465856953

theorem tailTrace_6143959 : CollatzResearch.WordTrace tailWord_6143959 prefixEnd_6143959 3154804088517232465856953 := by
  unfold tailWord_6143959
  simp only [CollatzResearch.WordTrace]
  refine ⟨224088594348493322502898931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149392396232328881668599287 224088594348493322502898931)
  ·
    refine ⟨336132891522739983754348397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224088594348493322502898931 336132891522739983754348397)
    ·
      refine ⟨126049834321027493907880649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 336132891522739983754348397 126049834321027493907880649)
      ·
        refine ⟨94537375740770620430910487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126049834321027493907880649 94537375740770620430910487)
        ·
          refine ⟨141806063611155930646365731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94537375740770620430910487 141806063611155930646365731)
          ·
            refine ⟨212709095416733895969548597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141806063611155930646365731 212709095416733895969548597)
            ·
              refine ⟨19941477695318802747145181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 212709095416733895969548597 19941477695318802747145181)
              ·
                refine ⟨7478054135744551030179443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19941477695318802747145181 7478054135744551030179443)
                ·
                  refine ⟨11217081203616826545269165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7478054135744551030179443 11217081203616826545269165)
                  ·
                    refine ⟨4206405451356309954475937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11217081203616826545269165 4206405451356309954475937)
                    ·
                      refine ⟨3154804088517232465856953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4206405451356309954475937 3154804088517232465856953)
                      ·
                        rfl

theorem cell23_6143959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 3, 1, 3, 2].length) (baseStart_6143959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6143959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6143959 prefixEnd_6143959 := by exact prefixLift 6143959
  have htrace : WordTrace (prefixWord ++ tailWord_6143959) baseStart_6143959 baseEnd_6143959 := by
    simpa [prefixWord, tailWord_6143959, baseEnd_6143959] using wordTrace_append hprefix tailTrace_6143959
  have hstable : (prefixWord ++ tailWord_6143959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6143959).length < 2 ^ (prefixWord ++ tailWord_6143959).sum := by decide
  have hdescent : baseEnd_6143959 < baseStart_6143959 := by decide
  rcases family_descends (prefixWord ++ tailWord_6143959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6143982 : List Nat := [4, 1, 2, 1, 3, 1, 2, 1, 2, 6]
def baseStart_6143982 : Nat := 118140960795 + 6143982 * 2 ^ 59
def prefixEnd_6143982 : Nat := 4983230072969 + 3 ^ 40 * 6143982 * 2
def baseEnd_6143982 : Nat := 1051605299524095291956449

theorem tailTrace_6143982 : CollatzResearch.WordTrace tailWord_6143982 prefixEnd_6143982 1051605299524095291956449 := by
  unfold tailWord_6143982
  simp only [CollatzResearch.WordTrace]
  refine ⟨28011179153426249678873275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149392955484939998287324133 28011179153426249678873275)
  ·
    refine ⟨42016768730139374518309913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28011179153426249678873275 42016768730139374518309913)
    ·
      refine ⟨31512576547604530888732435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42016768730139374518309913 31512576547604530888732435)
      ·
        refine ⟨47268864821406796333098653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31512576547604530888732435 47268864821406796333098653)
        ·
          refine ⟨17725824308027548624911995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47268864821406796333098653 17725824308027548624911995)
          ·
            refine ⟨26588736462041322937367993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17725824308027548624911995 26588736462041322937367993)
            ·
              refine ⟨19941552346530992203025995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26588736462041322937367993 19941552346530992203025995)
              ·
                refine ⟨29912328519796488304538993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19941552346530992203025995 29912328519796488304538993)
                ·
                  refine ⟨22434246389847366228404245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29912328519796488304538993 22434246389847366228404245)
                  ·
                    refine ⟨1051605299524095291956449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22434246389847366228404245 1051605299524095291956449)
                    ·
                      rfl

theorem cell23_6143982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 1, 2, 6].length) (baseStart_6143982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6143982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6143982 prefixEnd_6143982 := by exact prefixLift 6143982
  have htrace : WordTrace (prefixWord ++ tailWord_6143982) baseStart_6143982 baseEnd_6143982 := by
    simpa [prefixWord, tailWord_6143982, baseEnd_6143982] using wordTrace_append hprefix tailTrace_6143982
  have hstable : (prefixWord ++ tailWord_6143982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6143982).length < 2 ^ (prefixWord ++ tailWord_6143982).sum := by decide
  have hdescent : baseEnd_6143982 < baseStart_6143982 := by decide
  rcases family_descends (prefixWord ++ tailWord_6143982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6143995 : List Nat := [1, 1, 1, 1, 1, 3, 6, 2, 7]
def baseStart_6143995 : Nat := 118140960795 + 6143995 * 2 ^ 59
def prefixEnd_6143995 : Nat := 4983230072969 + 3 ^ 40 * 6143995 * 2
def baseEnd_6143995 : Nat := 350535841535643813889643

theorem tailTrace_6143995 : CollatzResearch.WordTrace tailWord_6143995 prefixEnd_6143995 350535841535643813889643 := by
  unfold tailWord_6143995
  simp only [CollatzResearch.WordTrace]
  refine ⟨224089907376362900651209439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149393271584241933767472959 224089907376362900651209439)
  ·
    refine ⟨336134861064544350976814159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224089907376362900651209439 336134861064544350976814159)
    ·
      refine ⟨504202291596816526465221239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 336134861064544350976814159 504202291596816526465221239)
      ·
        refine ⟨756303437395224789697831859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 504202291596816526465221239 756303437395224789697831859)
        ·
          refine ⟨1134455156092837184546747789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 756303437395224789697831859 1134455156092837184546747789)
          ·
            refine ⟨425420683534813944205030421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1134455156092837184546747789 425420683534813944205030421)
            ·
              refine ⟨19941594540694403634610801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 425420683534813944205030421 19941594540694403634610801)
              ·
                refine ⟨14956195905520802725958101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19941594540694403634610801 14956195905520802725958101)
                ·
                  refine ⟨350535841535643813889643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14956195905520802725958101 350535841535643813889643)
                  ·
                    rfl

theorem cell23_6143995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 6, 2, 7].length) (baseStart_6143995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6143995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6143995 prefixEnd_6143995 := by exact prefixLift 6143995
  have htrace : WordTrace (prefixWord ++ tailWord_6143995) baseStart_6143995 baseEnd_6143995 := by
    simpa [prefixWord, tailWord_6143995, baseEnd_6143995] using wordTrace_append hprefix tailTrace_6143995
  have hstable : (prefixWord ++ tailWord_6143995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6143995).length < 2 ^ (prefixWord ++ tailWord_6143995).sum := by decide
  have hdescent : baseEnd_6143995 < baseStart_6143995 := by decide
  rcases family_descends (prefixWord ++ tailWord_6143995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6144029 : List Nat := [1, 4, 2, 2, 2, 3, 1, 1, 7]
def baseStart_6144029 : Nat := 118140960795 + 6144029 * 2 ^ 59
def prefixEnd_6144029 : Nat := 4983230072969 + 3 ^ 40 * 6144029 * 2
def baseEnd_6144029 : Nat := 350537781351449687997959

theorem tailTrace_6144029 : CollatzResearch.WordTrace tailWord_6144029 prefixEnd_6144029 350537781351449687997959 := by
  unfold tailWord_6144029
  simp only [CollatzResearch.WordTrace]
  refine ⟨224091147458239724457947141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149394098305493149638631427 224091147458239724457947141)
  ·
    refine ⟨42017090148419948335865089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 224091147458239724457947141 42017090148419948335865089)
    ·
      refine ⟨31512817611314961251898817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42017090148419948335865089 31512817611314961251898817)
      ·
        refine ⟨23634613208486220938924113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31512817611314961251898817 23634613208486220938924113)
        ·
          refine ⟨17725959906364665704193085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23634613208486220938924113 17725959906364665704193085)
          ·
            refine ⟨6647234964886749639072407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17725959906364665704193085 6647234964886749639072407)
            ·
              refine ⟨9970852447330124458608611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6647234964886749639072407 9970852447330124458608611)
              ·
                refine ⟨14956278670995186687912917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9970852447330124458608611 14956278670995186687912917)
                ·
                  refine ⟨350537781351449687997959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14956278670995186687912917 350537781351449687997959)
                  ·
                    rfl

theorem cell23_6144029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 1, 1, 7].length) (baseStart_6144029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6144029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6144029 prefixEnd_6144029 := by exact prefixLift 6144029
  have htrace : WordTrace (prefixWord ++ tailWord_6144029) baseStart_6144029 baseEnd_6144029 := by
    simpa [prefixWord, tailWord_6144029, baseEnd_6144029] using wordTrace_append hprefix tailTrace_6144029
  have hstable : (prefixWord ++ tailWord_6144029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6144029).length < 2 ^ (prefixWord ++ tailWord_6144029).sum := by decide
  have hdescent : baseEnd_6144029 < baseStart_6144029 := by decide
  rcases family_descends (prefixWord ++ tailWord_6144029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6144040 : List Nat := [2, 1, 5, 3, 1, 1, 1, 3, 2, 2, 2]
def baseStart_6144040 : Nat := 118140960795 + 6144040 * 2 ^ 59
def prefixEnd_6144040 : Nat := 4983230072969 + 3 ^ 40 * 6144040 * 2
def baseEnd_6144040 : Nat := 3154845680450246648944081

theorem tailTrace_6144040 : CollatzResearch.WordTrace tailWord_6144040 prefixEnd_6144040 3154845680450246648944081 := by
  unfold tailWord_6144040
  simp only [CollatzResearch.WordTrace]
  refine ⟨112045774330599936668298787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149394365774133248891065049 112045774330599936668298787)
  ·
    refine ⟨168068661495899905002448181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112045774330599936668298787 168068661495899905002448181)
    ·
      refine ⟨15756437015240616093979517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 168068661495899905002448181 15756437015240616093979517)
      ·
        refine ⟨5908663880715231035242319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15756437015240616093979517 5908663880715231035242319)
        ·
          refine ⟨8862995821072846552863479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5908663880715231035242319 8862995821072846552863479)
          ·
            refine ⟨13294493731609269829295219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8862995821072846552863479 13294493731609269829295219)
            ·
              refine ⟨19941740597413904743942829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13294493731609269829295219 19941740597413904743942829)
              ·
                refine ⟨7478152724030214278978561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19941740597413904743942829 7478152724030214278978561)
                ·
                  refine ⟨5608614543022660709233921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7478152724030214278978561 5608614543022660709233921)
                  ·
                    refine ⟨4206460907266995531925441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5608614543022660709233921 4206460907266995531925441)
                    ·
                      refine ⟨3154845680450246648944081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4206460907266995531925441 3154845680450246648944081)
                      ·
                        rfl

theorem cell23_6144040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_6144040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6144040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6144040 prefixEnd_6144040 := by exact prefixLift 6144040
  have htrace : WordTrace (prefixWord ++ tailWord_6144040) baseStart_6144040 baseEnd_6144040 := by
    simpa [prefixWord, tailWord_6144040, baseEnd_6144040] using wordTrace_append hprefix tailTrace_6144040
  have hstable : (prefixWord ++ tailWord_6144040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6144040).length < 2 ^ (prefixWord ++ tailWord_6144040).sum := by decide
  have hdescent : baseEnd_6144040 < baseStart_6144040 := by decide
  rcases family_descends (prefixWord ++ tailWord_6144040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6144055 : List Nat := [1, 1, 3, 1, 2, 2, 2, 1, 2, 8]
def baseStart_6144055 : Nat := 118140960795 + 6144055 * 2 ^ 59
def prefixEnd_6144055 : Nat := 4983230072969 + 3 ^ 40 * 6144055 * 2
def baseEnd_6144055 : Nat := 1051617794220021363418837

theorem tailTrace_6144055 : CollatzResearch.WordTrace tailWord_6144055 prefixEnd_6144055 1051617794220021363418837 := by
  unfold tailWord_6144055
  simp only [CollatzResearch.WordTrace]
  refine ⟨224092095756145530898393619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149394730504097020598929079 224092095756145530898393619)
  ·
    refine ⟨336138143634218296347590429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224092095756145530898393619 336138143634218296347590429)
    ·
      refine ⟨126051803862831861130346411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 336138143634218296347590429 126051803862831861130346411)
      ·
        refine ⟨189077705794247791695519617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126051803862831861130346411 189077705794247791695519617)
        ·
          refine ⟨141808279345685843771639713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189077705794247791695519617 141808279345685843771639713)
          ·
            refine ⟨106356209509264382828729785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141808279345685843771639713 106356209509264382828729785)
            ·
              refine ⟨79767157131948287121547339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106356209509264382828729785 79767157131948287121547339)
              ·
                refine ⟨119650735697922430682321009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79767157131948287121547339 119650735697922430682321009)
                ·
                  refine ⟨89738051773441823011740757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 119650735697922430682321009 89738051773441823011740757)
                  ·
                    refine ⟨1051617794220021363418837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 89738051773441823011740757 1051617794220021363418837)
                    ·
                      rfl

theorem cell23_6144055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 2, 8].length) (baseStart_6144055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6144055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6144055 prefixEnd_6144055 := by exact prefixLift 6144055
  have htrace : WordTrace (prefixWord ++ tailWord_6144055) baseStart_6144055 baseEnd_6144055 := by
    simpa [prefixWord, tailWord_6144055, baseEnd_6144055] using wordTrace_append hprefix tailTrace_6144055
  have hstable : (prefixWord ++ tailWord_6144055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6144055).length < 2 ^ (prefixWord ++ tailWord_6144055).sum := by decide
  have hdescent : baseEnd_6144055 < baseStart_6144055 := by decide
  rcases family_descends (prefixWord ++ tailWord_6144055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6144072 : List Nat := [2, 1, 3, 1, 1, 1, 2, 1, 7, 4]
def baseStart_6144072 : Nat := 118140960795 + 6144072 * 2 ^ 59
def prefixEnd_6144072 : Nat := 4983230072969 + 3 ^ 40 * 6144072 * 2
def baseEnd_6144072 : Nat := 1051620703943730174581311

theorem tailTrace_6144072 : CollatzResearch.WordTrace tailWord_6144072 prefixEnd_6144072 1051620703943730174581311 := by
  unfold tailWord_6144072
  simp only [CollatzResearch.WordTrace]
  refine ⟨112046357898541971400881235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149395143864722628534508313 112046357898541971400881235)
  ·
    refine ⟨168069536847812957101321853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112046357898541971400881235 168069536847812957101321853)
    ·
      refine ⟨63026076317929858912995695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168069536847812957101321853 63026076317929858912995695)
      ·
        refine ⟨94539114476894788369493543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63026076317929858912995695 94539114476894788369493543)
        ·
          refine ⟨141808671715342182554240315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94539114476894788369493543 141808671715342182554240315)
          ·
            refine ⟨212713007573013273831360473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141808671715342182554240315 212713007573013273831360473)
            ·
              refine ⟨159534755679759955373520355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 212713007573013273831360473 159534755679759955373520355)
              ·
                refine ⟨239302133519639933060280533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 159534755679759955373520355 239302133519639933060280533)
                ·
                  refine ⟨5608643754366560931100325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 239302133519639933060280533 5608643754366560931100325)
                  ·
                    refine ⟨1051620703943730174581311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5608643754366560931100325 1051620703943730174581311)
                    ·
                      rfl

theorem cell23_6144072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 7, 4].length) (baseStart_6144072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6144072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6144072 prefixEnd_6144072 := by exact prefixLift 6144072
  have htrace : WordTrace (prefixWord ++ tailWord_6144072) baseStart_6144072 baseEnd_6144072 := by
    simpa [prefixWord, tailWord_6144072, baseEnd_6144072] using wordTrace_append hprefix tailTrace_6144072
  have hstable : (prefixWord ++ tailWord_6144072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6144072).length < 2 ^ (prefixWord ++ tailWord_6144072).sum := by decide
  have hdescent : baseEnd_6144072 < baseStart_6144072 := by decide
  rcases family_descends (prefixWord ++ tailWord_6144072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6144075 : List Nat := [1, 1, 1, 1, 3, 1, 2, 3, 1, 3, 6]
def baseStart_6144075 : Nat := 118140960795 + 6144075 * 2 ^ 59
def prefixEnd_6144075 : Nat := 4983230072969 + 3 ^ 40 * 6144075 * 2
def baseEnd_6144075 : Nat := 3154863652273154012006419

theorem tailTrace_6144075 : CollatzResearch.WordTrace tailWord_6144075 prefixEnd_6144075 3154863652273154012006419 := by
  unfold tailWord_6144075
  simp only [CollatzResearch.WordTrace]
  refine ⟨224092825216073074314121679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149395216810715382876081119 224092825216073074314121679)
  ·
    refine ⟨336139237824109611471182519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224092825216073074314121679 336139237824109611471182519)
    ·
      refine ⟨504208856736164417206773779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 336139237824109611471182519 504208856736164417206773779)
      ·
        refine ⟨756313285104246625810160669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 504208856736164417206773779 756313285104246625810160669)
        ·
          refine ⟨283617481914092484678810251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 756313285104246625810160669 283617481914092484678810251)
          ·
            refine ⟨425426222871138727018215377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 283617481914092484678810251 425426222871138727018215377)
            ·
              refine ⟨319069667153354045263661533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 425426222871138727018215377 319069667153354045263661533)
              ·
                refine ⟨119651125182507766973873075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 319069667153354045263661533 119651125182507766973873075)
                ·
                  refine ⟨179476687773761650460809613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 119651125182507766973873075 179476687773761650460809613)
                  ·
                    refine ⟨67303757915160618922803605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 179476687773761650460809613 67303757915160618922803605)
                    ·
                      refine ⟨3154863652273154012006419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67303757915160618922803605 3154863652273154012006419)
                      ·
                        rfl

theorem cell23_6144075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 3, 6].length) (baseStart_6144075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6144075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6144075 prefixEnd_6144075 := by exact prefixLift 6144075
  have htrace : WordTrace (prefixWord ++ tailWord_6144075) baseStart_6144075 baseEnd_6144075 := by
    simpa [prefixWord, tailWord_6144075, baseEnd_6144075] using wordTrace_append hprefix tailTrace_6144075
  have hstable : (prefixWord ++ tailWord_6144075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6144075).length < 2 ^ (prefixWord ++ tailWord_6144075).sum := by decide
  have hdescent : baseEnd_6144075 < baseStart_6144075 := by decide
  rcases family_descends (prefixWord ++ tailWord_6144075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6144086 : List Nat := [5, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5]
def baseStart_6144086 : Nat := 118140960795 + 6144086 * 2 ^ 59
def prefixEnd_6144086 : Nat := 4983230072969 + 3 ^ 40 * 6144086 * 2
def baseEnd_6144086 : Nat := 3154869300560353468968869

theorem tailTrace_6144086 : CollatzResearch.WordTrace tailWord_6144086 prefixEnd_6144086 3154869300560353468968869 := by
  unfold tailWord_6144086
  simp only [CollatzResearch.WordTrace]
  refine ⟨14005826651189576449548257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 149395484279355482128514741 14005826651189576449548257)
  ·
    refine ⟨10504369988392182337161193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14005826651189576449548257 10504369988392182337161193)
    ·
      refine ⟨7878277491294136752870895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10504369988392182337161193 7878277491294136752870895)
      ·
        refine ⟨11817416236941205129306343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7878277491294136752870895 11817416236941205129306343)
        ·
          refine ⟨17726124355411807693959515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11817416236941205129306343 17726124355411807693959515)
          ·
            refine ⟨26589186533117711540939273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17726124355411807693959515 26589186533117711540939273)
            ·
              refine ⟨19941889899838283655704455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26589186533117711540939273 19941889899838283655704455)
              ·
                refine ⟨29912834849757425483556683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19941889899838283655704455 29912834849757425483556683)
                ·
                  refine ⟨44869252274636138225335025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29912834849757425483556683 44869252274636138225335025)
                  ·
                    refine ⟨33651939205977103669001269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44869252274636138225335025 33651939205977103669001269)
                    ·
                      refine ⟨3154869300560353468968869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33651939205977103669001269 3154869300560353468968869)
                      ·
                        rfl

theorem cell23_6144086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_6144086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6144086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6144086 prefixEnd_6144086 := by exact prefixLift 6144086
  have htrace : WordTrace (prefixWord ++ tailWord_6144086) baseStart_6144086 baseEnd_6144086 := by
    simpa [prefixWord, tailWord_6144086, baseEnd_6144086] using wordTrace_append hprefix tailTrace_6144086
  have hstable : (prefixWord ++ tailWord_6144086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6144086).length < 2 ^ (prefixWord ++ tailWord_6144086).sum := by decide
  have hdescent : baseEnd_6144086 < baseStart_6144086 := by decide
  rcases family_descends (prefixWord ++ tailWord_6144086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6144106 : List Nat := [3, 1, 3, 2, 3, 1, 1, 2, 3, 4]
def baseStart_6144106 : Nat := 118140960795 + 6144106 * 2 ^ 59
def prefixEnd_6144106 : Nat := 4983230072969 + 3 ^ 40 * 6144106 * 2
def baseEnd_6144106 : Nat := 1051626523391147796906259

theorem tailTrace_6144106 : CollatzResearch.WordTrace tailWord_6144106 prefixEnd_6144106 1051626523391147796906259 := by
  unfold tailWord_6144106
  simp only [CollatzResearch.WordTrace]
  refine ⟨56023488969740191652125043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149395970585973844405666781 56023488969740191652125043)
  ·
    refine ⟨84035233454610287478187565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56023488969740191652125043 84035233454610287478187565)
    ·
      refine ⟨31513212545478857804320337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84035233454610287478187565 31513212545478857804320337)
      ·
        refine ⟨23634909409109143353240253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31513212545478857804320337 23634909409109143353240253)
        ·
          refine ⟨8863091028415928757465095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23634909409109143353240253 8863091028415928757465095)
          ·
            refine ⟨13294636542623893136197643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8863091028415928757465095 13294636542623893136197643)
            ·
              refine ⟨19941954813935839704296465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13294636542623893136197643 19941954813935839704296465)
              ·
                refine ⟨14956466110451879778222349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19941954813935839704296465 14956466110451879778222349)
                ·
                  refine ⟨5608674791419454916833381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14956466110451879778222349 5608674791419454916833381)
                  ·
                    refine ⟨1051626523391147796906259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5608674791419454916833381 1051626523391147796906259)
                    ·
                      rfl

theorem cell23_6144106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 2, 3, 4].length) (baseStart_6144106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6144106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6144106 prefixEnd_6144106 := by exact prefixLift 6144106
  have htrace : WordTrace (prefixWord ++ tailWord_6144106) baseStart_6144106 baseEnd_6144106 := by
    simpa [prefixWord, tailWord_6144106, baseEnd_6144106] using wordTrace_append hprefix tailTrace_6144106
  have hstable : (prefixWord ++ tailWord_6144106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6144106).length < 2 ^ (prefixWord ++ tailWord_6144106).sum := by decide
  have hdescent : baseEnd_6144106 < baseStart_6144106 := by decide
  rcases family_descends (prefixWord ++ tailWord_6144106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6144136 : List Nat := [2, 1, 3, 4, 1, 3, 1, 2, 6]
def baseStart_6144136 : Nat := 118140960795 + 6144136 * 2 ^ 59
def prefixEnd_6144136 : Nat := 4983230072969 + 3 ^ 40 * 6144136 * 2
def baseEnd_6144136 : Nat := 350543886065897585927071

theorem tailTrace_6144136 : CollatzResearch.WordTrace tailWord_6144136 prefixEnd_6144136 350543886065897585927071 := by
  unfold tailWord_6144136
  simp only [CollatzResearch.WordTrace]
  refine ⟨112047525034426040866046131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149396700045901387821394841 112047525034426040866046131)
  ·
    refine ⟨168071287551639061299069197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112047525034426040866046131 168071287551639061299069197)
    ·
      refine ⟨63026732831864647987150949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168071287551639061299069197 63026732831864647987150949)
      ·
        refine ⟨11817512405974621497590803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63026732831864647987150949 11817512405974621497590803)
        ·
          refine ⟨17726268608961932246386205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11817512405974621497590803 17726268608961932246386205)
          ·
            refine ⟨6647350728360724592394827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17726268608961932246386205 6647350728360724592394827)
            ·
              refine ⟨9971026092541086888592241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6647350728360724592394827 9971026092541086888592241)
              ·
                refine ⟨7478269569405815166444181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9971026092541086888592241 7478269569405815166444181)
                ·
                  refine ⟨350543886065897585927071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7478269569405815166444181 350543886065897585927071)
                  ·
                    rfl

theorem cell23_6144136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 1, 2, 6].length) (baseStart_6144136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6144136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6144136 prefixEnd_6144136 := by exact prefixLift 6144136
  have htrace : WordTrace (prefixWord ++ tailWord_6144136) baseStart_6144136 baseEnd_6144136 := by
    simpa [prefixWord, tailWord_6144136, baseEnd_6144136] using wordTrace_append hprefix tailTrace_6144136
  have hstable : (prefixWord ++ tailWord_6144136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6144136).length < 2 ^ (prefixWord ++ tailWord_6144136).sum := by decide
  have hdescent : baseEnd_6144136 < baseStart_6144136 := by decide
  rcases family_descends (prefixWord ++ tailWord_6144136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6144174 : List Nat := [4, 1, 4, 2, 2, 1, 1, 3, 1, 4]
def baseStart_6144174 : Nat := 118140960795 + 6144174 * 2 ^ 59
def prefixEnd_6144174 : Nat := 4983230072969 + 3 ^ 40 * 6144174 * 2
def baseEnd_6144174 : Nat := 1051638162285983041556155

theorem tailTrace_6144174 : CollatzResearch.WordTrace tailWord_6144174 prefixEnd_6144174 1051638162285983041556155 := by
  unfold tailWord_6144174
  simp only [CollatzResearch.WordTrace]
  refine ⟨28012054505339301777746947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149397624028476276147983717 28012054505339301777746947)
  ·
    refine ⟨42018081758008952666620421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28012054505339301777746947 42018081758008952666620421)
    ·
      refine ⟨7878390329626678624991329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42018081758008952666620421 7878390329626678624991329)
      ·
        refine ⟨5908792747220008968743497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7878390329626678624991329 5908792747220008968743497)
        ·
          refine ⟨4431594560415006726557623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5908792747220008968743497 4431594560415006726557623)
          ·
            refine ⟨6647391840622510089836435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4431594560415006726557623 6647391840622510089836435)
            ·
              refine ⟨9971087760933765134754653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6647391840622510089836435 9971087760933765134754653)
              ·
                refine ⟨3739157910350161925532995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9971087760933765134754653 3739157910350161925532995)
                ·
                  refine ⟨5608736865525242888299493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3739157910350161925532995 5608736865525242888299493)
                  ·
                    refine ⟨1051638162285983041556155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5608736865525242888299493 1051638162285983041556155)
                    ·
                      rfl

theorem cell23_6144174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_6144174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6144174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6144174 prefixEnd_6144174 := by exact prefixLift 6144174
  have htrace : WordTrace (prefixWord ++ tailWord_6144174) baseStart_6144174 baseEnd_6144174 := by
    simpa [prefixWord, tailWord_6144174, baseEnd_6144174] using wordTrace_append hprefix tailTrace_6144174
  have hstable : (prefixWord ++ tailWord_6144174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6144174).length < 2 ^ (prefixWord ++ tailWord_6144174).sum := by decide
  have hdescent : baseEnd_6144174 < baseStart_6144174 := by decide
  rcases family_descends (prefixWord ++ tailWord_6144174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6144186 : List Nat := [3, 1, 1, 1, 2, 2, 2, 2, 5, 2, 2]
def baseStart_6144186 : Nat := 118140960795 + 6144186 * 2 ^ 59
def prefixEnd_6144186 : Nat := 4983230072969 + 3 ^ 40 * 6144186 * 2
def baseEnd_6144186 : Nat := 3154920648625803077718409

theorem tailTrace_6144186 : CollatzResearch.WordTrace tailWord_6144186 prefixEnd_6144186 3154920648625803077718409 := by
  unfold tailWord_6144186
  simp only [CollatzResearch.WordTrace]
  refine ⟨56024218429667735067853103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149397915812447293514274941 56024218429667735067853103)
  ·
    refine ⟨84036327644501602601779655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56024218429667735067853103 84036327644501602601779655)
    ·
      refine ⟨126054491466752403902669483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84036327644501602601779655 126054491466752403902669483)
      ·
        refine ⟨189081737200128605854004225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126054491466752403902669483 189081737200128605854004225)
        ·
          refine ⟨141811302900096454390503169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189081737200128605854004225 141811302900096454390503169)
          ·
            refine ⟨106358477175072340792877377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141811302900096454390503169 106358477175072340792877377)
            ·
              refine ⟨79768857881304255594658033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106358477175072340792877377 79768857881304255594658033)
              ·
                refine ⟨59826643410978191695993525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 79768857881304255594658033 59826643410978191695993525)
                ·
                  refine ⟨5608747819779205471499393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59826643410978191695993525 5608747819779205471499393)
                  ·
                    refine ⟨4206560864834404103624545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5608747819779205471499393 4206560864834404103624545)
                    ·
                      refine ⟨3154920648625803077718409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4206560864834404103624545 3154920648625803077718409)
                      ·
                        rfl

theorem cell23_6144186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 2, 5, 2, 2].length) (baseStart_6144186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6144186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6144186 prefixEnd_6144186 := by exact prefixLift 6144186
  have htrace : WordTrace (prefixWord ++ tailWord_6144186) baseStart_6144186 baseEnd_6144186 := by
    simpa [prefixWord, tailWord_6144186, baseEnd_6144186] using wordTrace_append hprefix tailTrace_6144186
  have hstable : (prefixWord ++ tailWord_6144186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6144186).length < 2 ^ (prefixWord ++ tailWord_6144186).sum := by decide
  have hdescent : baseEnd_6144186 < baseStart_6144186 := by decide
  rcases family_descends (prefixWord ++ tailWord_6144186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6144189 : List Nat := [1, 4, 1, 2, 1, 1, 1, 2, 5, 2, 3]
def baseStart_6144189 : Nat := 118140960795 + 6144189 * 2 ^ 59
def prefixEnd_6144189 : Nat := 4983230072969 + 3 ^ 40 * 6144189 * 2
def baseEnd_6144189 : Nat := 3154922189067766565980895

theorem tailTrace_6144189 : CollatzResearch.WordTrace tailWord_6144189 prefixEnd_6144189 3154922189067766565980895 := by
  unfold tailWord_6144189
  simp only [CollatzResearch.WordTrace]
  refine ⟨224096983137660071783771621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149397988758440047855847747 224096983137660071783771621)
  ·
    refine ⟨42018184338311263459457179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 224096983137660071783771621 42018184338311263459457179)
    ·
      refine ⟨63027276507466895189185769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42018184338311263459457179 63027276507466895189185769)
      ·
        refine ⟨47270457380600171391889327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63027276507466895189185769 47270457380600171391889327)
        ·
          refine ⟨70905686070900257087833991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47270457380600171391889327 70905686070900257087833991)
          ·
            refine ⟨106358529106350385631750987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70905686070900257087833991 106358529106350385631750987)
            ·
              refine ⟨159537793659525578447626481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106358529106350385631750987 159537793659525578447626481)
              ·
                refine ⟨119653345244644183835719861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 159537793659525578447626481 119653345244644183835719861)
                ·
                  refine ⟨11217501116685392234598737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 119653345244644183835719861 11217501116685392234598737)
                  ·
                    refine ⟨8413125837514044175949053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11217501116685392234598737 8413125837514044175949053)
                    ·
                      refine ⟨3154922189067766565980895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8413125837514044175949053 3154922189067766565980895)
                      ·
                        rfl

theorem cell23_6144189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 5, 2, 3].length) (baseStart_6144189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6144189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6144189 prefixEnd_6144189 := by exact prefixLift 6144189
  have htrace : WordTrace (prefixWord ++ tailWord_6144189) baseStart_6144189 baseEnd_6144189 := by
    simpa [prefixWord, tailWord_6144189, baseEnd_6144189] using wordTrace_append hprefix tailTrace_6144189
  have hstable : (prefixWord ++ tailWord_6144189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6144189).length < 2 ^ (prefixWord ++ tailWord_6144189).sum := by decide
  have hdescent : baseEnd_6144189 < baseStart_6144189 := by decide
  rcases family_descends (prefixWord ++ tailWord_6144189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6144192 : List Nat := [2, 1, 1, 2, 5, 1, 11]
def baseStart_6144192 : Nat := 118140960795 + 6144192 * 2 ^ 59
def prefixEnd_6144192 : Nat := 4983230072969 + 3 ^ 40 * 6144192 * 2
def baseEnd_6144192 : Nat := 38949675672959630299301

theorem tailTrace_6144192 : CollatzResearch.WordTrace tailWord_6144192 prefixEnd_6144192 38949675672959630299301 := by
  unfold tailWord_6144192
  simp only [CollatzResearch.WordTrace]
  refine ⟨112048546278324601648065415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149398061704432802197420553 112048546278324601648065415)
  ·
    refine ⟨168072819417486902472098123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112048546278324601648065415 168072819417486902472098123)
    ·
      refine ⟨252109229126230353708147185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168072819417486902472098123 252109229126230353708147185)
      ·
        refine ⟨189081921844672765281110389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 252109229126230353708147185 189081921844672765281110389)
        ·
          refine ⟨17726430172938071745104099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 189081921844672765281110389 17726430172938071745104099)
          ·
            refine ⟨26589645259407107617656149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17726430172938071745104099 26589645259407107617656149)
            ·
              refine ⟨38949675672959630299301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 26589645259407107617656149 38949675672959630299301)
              ·
                rfl

theorem cell23_6144192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 11].length) (baseStart_6144192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6144192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6144192 prefixEnd_6144192 := by exact prefixLift 6144192
  have htrace : WordTrace (prefixWord ++ tailWord_6144192) baseStart_6144192 baseEnd_6144192 := by
    simpa [prefixWord, tailWord_6144192, baseEnd_6144192] using wordTrace_append hprefix tailTrace_6144192
  have hstable : (prefixWord ++ tailWord_6144192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6144192).length < 2 ^ (prefixWord ++ tailWord_6144192).sum := by decide
  have hdescent : baseEnd_6144192 < baseStart_6144192 := by decide
  rcases family_descends (prefixWord ++ tailWord_6144192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6144196 : List Nat := [2, 3, 3, 1, 2, 1, 2, 1, 4, 4]
def baseStart_6144196 : Nat := 118140960795 + 6144196 * 2 ^ 59
def prefixEnd_6144196 : Nat := 4983230072969 + 3 ^ 40 * 6144196 * 2
def baseEnd_6144196 : Nat := 1051641927810782679531121

theorem tailTrace_6144196 : CollatzResearch.WordTrace tailWord_6144196 prefixEnd_6144196 1051641927810782679531121 := by
  unfold tailWord_6144196
  simp only [CollatzResearch.WordTrace]
  refine ⟨112048619224317355989638221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149398158965756474652850961 112048619224317355989638221)
  ·
    refine ⟨42018232209119008496114333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112048619224317355989638221 42018232209119008496114333)
    ·
      refine ⟨15756837078419628186042875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42018232209119008496114333 15756837078419628186042875)
      ·
        refine ⟨23635255617629442279064313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15756837078419628186042875 23635255617629442279064313)
        ·
          refine ⟨17726441713222081709298235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23635255617629442279064313 17726441713222081709298235)
          ·
            refine ⟨26589662569833122563947353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17726441713222081709298235 26589662569833122563947353)
            ·
              refine ⟨19942246927374841922960515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26589662569833122563947353 19942246927374841922960515)
              ·
                refine ⟨29913370391062262884440773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19942246927374841922960515 29913370391062262884440773)
                ·
                  refine ⟨5608756948324174290832645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29913370391062262884440773 5608756948324174290832645)
                  ·
                    refine ⟨1051641927810782679531121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5608756948324174290832645 1051641927810782679531121)
                    ·
                      rfl

theorem cell23_6144196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 1, 4, 4].length) (baseStart_6144196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6144196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6144196 prefixEnd_6144196 := by exact prefixLift 6144196
  have htrace : WordTrace (prefixWord ++ tailWord_6144196) baseStart_6144196 baseEnd_6144196 := by
    simpa [prefixWord, tailWord_6144196, baseEnd_6144196] using wordTrace_append hprefix tailTrace_6144196
  have hstable : (prefixWord ++ tailWord_6144196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6144196).length < 2 ^ (prefixWord ++ tailWord_6144196).sum := by decide
  have hdescent : baseEnd_6144196 < baseStart_6144196 := by decide
  rcases family_descends (prefixWord ++ tailWord_6144196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6144213 : List Nat := [1, 3, 2, 4, 2, 1, 1, 3, 2, 4]
def baseStart_6144213 : Nat := 118140960795 + 6144213 * 2 ^ 59
def prefixEnd_6144213 : Nat := 4983230072969 + 3 ^ 40 * 6144213 * 2
def baseEnd_6144213 : Nat := 1051644837534491490693595

theorem tailTrace_6144213 : CollatzResearch.WordTrace tailWord_6144213 prefixEnd_6144213 1051644837534491490693595 := by
  unfold tailWord_6144213
  simp only [CollatzResearch.WordTrace]
  refine ⟨224097858489573123882645293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149398572326382082588430195 224097858489573123882645293)
  ·
    refine ⟨84036696933589921455991985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 224097858489573123882645293 84036696933589921455991985)
    ·
      refine ⟨63027522700192441091993989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84036696933589921455991985 63027522700192441091993989)
      ·
        refine ⟨11817660506286082704748873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63027522700192441091993989 11817660506286082704748873)
        ·
          refine ⟨8863245379714562028561655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11817660506286082704748873 8863245379714562028561655)
          ·
            refine ⟨13294868069571843042842483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8863245379714562028561655 13294868069571843042842483)
            ·
              refine ⟨19942302104357764564263725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13294868069571843042842483 19942302104357764564263725)
              ·
                refine ⟨7478363289134161711598897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19942302104357764564263725 7478363289134161711598897)
                ·
                  refine ⟨5608772466850621283699173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7478363289134161711598897 5608772466850621283699173)
                  ·
                    refine ⟨1051644837534491490693595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5608772466850621283699173 1051644837534491490693595)
                    ·
                      rfl

theorem cell23_6144213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 3, 2, 4].length) (baseStart_6144213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6144213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6144213 prefixEnd_6144213 := by exact prefixLift 6144213
  have htrace : WordTrace (prefixWord ++ tailWord_6144213) baseStart_6144213 baseEnd_6144213 := by
    simpa [prefixWord, tailWord_6144213, baseEnd_6144213] using wordTrace_append hprefix tailTrace_6144213
  have hstable : (prefixWord ++ tailWord_6144213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6144213).length < 2 ^ (prefixWord ++ tailWord_6144213).sum := by decide
  have hdescent : baseEnd_6144213 < baseStart_6144213 := by decide
  rcases family_descends (prefixWord ++ tailWord_6144213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6144316 : List Nat := [2, 2, 2, 2, 1, 2, 1, 6, 5]
def baseStart_6144316 : Nat := 118140960795 + 6144316 * 2 ^ 59
def prefixEnd_6144316 : Nat := 4983230072969 + 3 ^ 40 * 6144316 * 2
def baseEnd_6144316 : Nat := 350554155678987507676979

theorem tailTrace_6144316 : CollatzResearch.WordTrace tailWord_6144316 prefixEnd_6144316 350554155678987507676979 := by
  unfold tailWord_6144316
  simp only [CollatzResearch.WordTrace]
  refine ⟨112050807604099986236822401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149401076805466648315763201 112050807604099986236822401)
  ·
    refine ⟨84038105703074989677616801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112050807604099986236822401 84038105703074989677616801)
    ·
      refine ⟨63028579277306242258212601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84038105703074989677616801 63028579277306242258212601)
      ·
        refine ⟨47271434457979681693659451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63028579277306242258212601 47271434457979681693659451)
        ·
          refine ⟨70907151686969522540489177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47271434457979681693659451 70907151686969522540489177)
          ·
            refine ⟨53180363765227141905366883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70907151686969522540489177 53180363765227141905366883)
            ·
              refine ⟨79770545647840712858050325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53180363765227141905366883 79770545647840712858050325)
              ·
                refine ⟨3739244327242533415221109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 79770545647840712858050325 3739244327242533415221109)
                ·
                  refine ⟨350554155678987507676979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3739244327242533415221109 350554155678987507676979)
                  ·
                    rfl

theorem cell23_6144316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 6, 5].length) (baseStart_6144316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6144316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6144316 prefixEnd_6144316 := by exact prefixLift 6144316
  have htrace : WordTrace (prefixWord ++ tailWord_6144316) baseStart_6144316 baseEnd_6144316 := by
    simpa [prefixWord, tailWord_6144316, baseEnd_6144316] using wordTrace_append hprefix tailTrace_6144316
  have hstable : (prefixWord ++ tailWord_6144316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6144316).length < 2 ^ (prefixWord ++ tailWord_6144316).sum := by decide
  have hdescent : baseEnd_6144316 < baseStart_6144316 := by decide
  rcases family_descends (prefixWord ++ tailWord_6144316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6144423 : List Nat := [1, 1, 6, 1, 1, 3, 2, 2, 6]
def baseStart_6144423 : Nat := 118140960795 + 6144423 * 2 ^ 59
def prefixEnd_6144423 : Nat := 4983230072969 + 3 ^ 40 * 6144423 * 2
def baseEnd_6144423 : Nat := 350560260393435405606091

theorem tailTrace_6144423 : CollatzResearch.WordTrace tailWord_6144423 prefixEnd_6144423 350560260393435405606091 := by
  unfold tailWord_6144423
  simp only [CollatzResearch.WordTrace]
  refine ⟨224105517818812329747789923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149403678545874886498526615 224105517818812329747789923)
  ·
    refine ⟨336158276728218494621684885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224105517818812329747789923 336158276728218494621684885)
    ·
      refine ⟨15757419221635241935391479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 336158276728218494621684885 15757419221635241935391479)
      ·
        refine ⟨23636128832452862903087219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15757419221635241935391479 23636128832452862903087219)
        ·
          refine ⟨35454193248679294354630829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23636128832452862903087219 35454193248679294354630829)
          ·
            refine ⟨13295322468254735382986561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35454193248679294354630829 13295322468254735382986561)
            ·
              refine ⟨9971491851191051537239921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13295322468254735382986561 9971491851191051537239921)
              ·
                refine ⟨7478618888393288652929941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9971491851191051537239921 7478618888393288652929941)
                ·
                  refine ⟨350560260393435405606091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7478618888393288652929941 350560260393435405606091)
                  ·
                    rfl

theorem cell23_6144423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 2, 2, 6].length) (baseStart_6144423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6144423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6144423 prefixEnd_6144423 := by exact prefixLift 6144423
  have htrace : WordTrace (prefixWord ++ tailWord_6144423) baseStart_6144423 baseEnd_6144423 := by
    simpa [prefixWord, tailWord_6144423, baseEnd_6144423] using wordTrace_append hprefix tailTrace_6144423
  have hstable : (prefixWord ++ tailWord_6144423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6144423).length < 2 ^ (prefixWord ++ tailWord_6144423).sum := by decide
  have hdescent : baseEnd_6144423 < baseStart_6144423 := by decide
  rcases family_descends (prefixWord ++ tailWord_6144423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6144460 : List Nat := [2, 2, 1, 4, 3, 1, 1, 1, 1, 5, 2]
def baseStart_6144460 : Nat := 118140960795 + 6144460 * 2 ^ 59
def prefixEnd_6144460 : Nat := 4983230072969 + 3 ^ 40 * 6144460 * 2
def baseEnd_6144460 : Nat := 3155061342325135005692149

theorem tailTrace_6144460 : CollatzResearch.WordTrace tailWord_6144460 prefixEnd_6144460 3155061342325135005692149 := by
  unfold tailWord_6144460
  simp only [CollatzResearch.WordTrace]
  refine ⟨112053433659839142533443417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149404578213118856711257889 112053433659839142533443417)
  ·
    refine ⟨84040075244879356900082563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112053433659839142533443417 84040075244879356900082563)
    ·
      refine ⟨126060112867319035350123845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84040075244879356900082563 126060112867319035350123845)
      ·
        refine ⟨23636271162622319128148221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 126060112867319035350123845 23636271162622319128148221)
        ·
          refine ⟨8863601685983369673055583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23636271162622319128148221 8863601685983369673055583)
          ·
            refine ⟨13295402528975054509583375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8863601685983369673055583 13295402528975054509583375)
            ·
              refine ⟨19943103793462581764375063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13295402528975054509583375 19943103793462581764375063)
              ·
                refine ⟨29914655690193872646562595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19943103793462581764375063 29914655690193872646562595)
                ·
                  refine ⟨44871983535290808969843893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29914655690193872646562595 44871983535290808969843893)
                  ·
                    refine ⟨4206748456433513340922865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44871983535290808969843893 4206748456433513340922865)
                    ·
                      refine ⟨3155061342325135005692149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4206748456433513340922865 3155061342325135005692149)
                      ·
                        rfl

theorem cell23_6144460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 1, 1, 5, 2].length) (baseStart_6144460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6144460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6144460 prefixEnd_6144460 := by exact prefixLift 6144460
  have htrace : WordTrace (prefixWord ++ tailWord_6144460) baseStart_6144460 baseEnd_6144460 := by
    simpa [prefixWord, tailWord_6144460, baseEnd_6144460] using wordTrace_append hprefix tailTrace_6144460
  have hstable : (prefixWord ++ tailWord_6144460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6144460).length < 2 ^ (prefixWord ++ tailWord_6144460).sum := by decide
  have hdescent : baseEnd_6144460 < baseStart_6144460 := by decide
  rcases family_descends (prefixWord ++ tailWord_6144460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6144470 : List Nat := [5, 2, 1, 1, 1, 1, 3, 3, 1, 5]
def baseStart_6144470 : Nat := 118140960795 + 6144470 * 2 ^ 59
def prefixEnd_6144470 : Nat := 4983230072969 + 3 ^ 40 * 6144470 * 2
def baseEnd_6144470 : Nat := 1051688825710559988855701

theorem tailTrace_6144470 : CollatzResearch.WordTrace tailWord_6144470 prefixEnd_6144470 1051688825710559988855701 := by
  unfold tailWord_6144470
  simp only [CollatzResearch.WordTrace]
  refine ⟨14006702003102628548421929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 149404821366428037849833909 14006702003102628548421929)
  ·
    refine ⟨10505026502326971411316447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14006702003102628548421929 10505026502326971411316447)
    ·
      refine ⟨15757539753490457116974671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10505026502326971411316447 15757539753490457116974671)
      ·
        refine ⟨23636309630235685675462007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15757539753490457116974671 23636309630235685675462007)
        ·
          refine ⟨35454464445353528513193011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23636309630235685675462007 35454464445353528513193011)
          ·
            refine ⟨53181696668030292769789517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35454464445353528513193011 53181696668030292769789517)
            ·
              refine ⟨19943136250511359788671069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53181696668030292769789517 19943136250511359788671069)
              ·
                refine ⟨7478676093941759920751651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19943136250511359788671069 7478676093941759920751651)
                ·
                  refine ⟨11218014140912639881127477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7478676093941759920751651 11218014140912639881127477)
                  ·
                    refine ⟨1051688825710559988855701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11218014140912639881127477 1051688825710559988855701)
                    ·
                      rfl

theorem cell23_6144470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 3, 1, 5].length) (baseStart_6144470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6144470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6144470 prefixEnd_6144470 := by exact prefixLift 6144470
  have htrace : WordTrace (prefixWord ++ tailWord_6144470) baseStart_6144470 baseEnd_6144470 := by
    simpa [prefixWord, tailWord_6144470, baseEnd_6144470] using wordTrace_append hprefix tailTrace_6144470
  have hstable : (prefixWord ++ tailWord_6144470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6144470).length < 2 ^ (prefixWord ++ tailWord_6144470).sum := by decide
  have hdescent : baseEnd_6144470 < baseStart_6144470 := by decide
  rcases family_descends (prefixWord ++ tailWord_6144470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6144473 : List Nat := [1, 2, 1, 2, 4, 1, 3, 3, 1, 1, 4]
def baseStart_6144473 : Nat := 118140960795 + 6144473 * 2 ^ 59
def prefixEnd_6144473 : Nat := 4983230072969 + 3 ^ 40 * 6144473 * 2
def baseEnd_6144473 : Nat := 3155068017573643454829589

theorem tailTrace_6144473 : CollatzResearch.WordTrace tailWord_6144473 prefixEnd_6144473 3155068017573643454829589 := by
  unfold tailWord_6144473
  simp only [CollatzResearch.WordTrace]
  refine ⟨224107341468631188287110073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149404894312420792191406715 224107341468631188287110073)
  ·
    refine ⟨168080506101473391215332555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224107341468631188287110073 168080506101473391215332555)
    ·
      refine ⟨252120759152210086822998833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168080506101473391215332555 252120759152210086822998833)
      ·
        refine ⟨189090569364157565117249125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 252120759152210086822998833 189090569364157565117249125)
        ·
          refine ⟨35454481755779543459484211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 189090569364157565117249125 35454481755779543459484211)
          ·
            refine ⟨53181722633669315189226317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35454481755779543459484211 53181722633669315189226317)
            ·
              refine ⟨19943145987625993195959869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53181722633669315189226317 19943145987625993195959869)
              ·
                refine ⟨7478679745359747448484951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19943145987625993195959869 7478679745359747448484951)
                ·
                  refine ⟨11218019618039621172727427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7478679745359747448484951 11218019618039621172727427)
                  ·
                    refine ⟨16827029427059431759091141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11218019618039621172727427 16827029427059431759091141)
                    ·
                      refine ⟨3155068017573643454829589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16827029427059431759091141 3155068017573643454829589)
                      ·
                        rfl

theorem cell23_6144473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 3, 1, 1, 4].length) (baseStart_6144473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6144473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6144473 prefixEnd_6144473 := by exact prefixLift 6144473
  have htrace : WordTrace (prefixWord ++ tailWord_6144473) baseStart_6144473 baseEnd_6144473 := by
    simpa [prefixWord, tailWord_6144473, baseEnd_6144473] using wordTrace_append hprefix tailTrace_6144473
  have hstable : (prefixWord ++ tailWord_6144473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6144473).length < 2 ^ (prefixWord ++ tailWord_6144473).sum := by decide
  have hdescent : baseEnd_6144473 < baseStart_6144473 := by decide
  rcases family_descends (prefixWord ++ tailWord_6144473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6144493 : List Nat := [1, 5, 1, 3, 1, 1, 1, 1, 3, 1, 5]
def baseStart_6144493 : Nat := 118140960795 + 6144493 * 2 ^ 59
def prefixEnd_6144493 : Nat := 4983230072969 + 3 ^ 40 * 6144493 * 2
def baseEnd_6144493 : Nat := 3155078287186733376579497

theorem tailTrace_6144493 : CollatzResearch.WordTrace tailWord_6144493 prefixEnd_6144493 3155078287186733376579497 := by
  unfold tailWord_6144493
  simp only [CollatzResearch.WordTrace]
  refine ⟨224108070928558731702838133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149405380619039154468558755 224108070928558731702838133)
  ·
    refine ⟨21010131649552381097141075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 224108070928558731702838133 21010131649552381097141075)
    ·
      refine ⟨31515197474328571645711613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21010131649552381097141075 31515197474328571645711613)
      ·
        refine ⟨11818199052873214367141855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31515197474328571645711613 11818199052873214367141855)
        ·
          refine ⟨17727298579309821550712783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11818199052873214367141855 17727298579309821550712783)
          ·
            refine ⟨26590947868964732326069175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17727298579309821550712783 26590947868964732326069175)
            ·
              refine ⟨39886421803447098489103763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26590947868964732326069175 39886421803447098489103763)
              ·
                refine ⟨59829632705170647733655645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39886421803447098489103763 59829632705170647733655645)
                ·
                  refine ⟨22436112264438992900120867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59829632705170647733655645 22436112264438992900120867)
                  ·
                    refine ⟨33654168396658489350181301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22436112264438992900120867 33654168396658489350181301)
                    ·
                      refine ⟨3155078287186733376579497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33654168396658489350181301 3155078287186733376579497)
                      ·
                        rfl

theorem cell23_6144493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_6144493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6144493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6144493 prefixEnd_6144493 := by exact prefixLift 6144493
  have htrace : WordTrace (prefixWord ++ tailWord_6144493) baseStart_6144493 baseEnd_6144493 := by
    simpa [prefixWord, tailWord_6144493, baseEnd_6144493] using wordTrace_append hprefix tailTrace_6144493
  have hstable : (prefixWord ++ tailWord_6144493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6144493).length < 2 ^ (prefixWord ++ tailWord_6144493).sum := by decide
  have hdescent : baseEnd_6144493 < baseStart_6144493 := by decide
  rcases family_descends (prefixWord ++ tailWord_6144493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6144513 : List Nat := [1, 2, 4, 1, 3, 1, 4, 7]
def baseStart_6144513 : Nat := 118140960795 + 6144513 * 2 ^ 59
def prefixEnd_6144513 : Nat := 4983230072969 + 3 ^ 40 * 6144513 * 2
def baseEnd_6144513 : Nat := 116855131733326788827015

theorem tailTrace_6144513 : CollatzResearch.WordTrace tailWord_6144513 prefixEnd_6144513 116855131733326788827015 := by
  unfold tailWord_6144513
  simp only [CollatzResearch.WordTrace]
  refine ⟨224108800388486275118566193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149405866925657516745710795 224108800388486275118566193)
  ·
    refine ⟨168081600291364706338924645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224108800388486275118566193 168081600291364706338924645)
    ·
      refine ⟨31515300054630882438548371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 168081600291364706338924645 31515300054630882438548371)
      ·
        refine ⟨47272950081946323657822557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31515300054630882438548371 47272950081946323657822557)
        ·
          refine ⟨17727356280729871371683459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47272950081946323657822557 17727356280729871371683459)
          ·
            refine ⟨26591034421094807057525189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17727356280729871371683459 26591034421094807057525189)
            ·
              refine ⟨4985818953955276323285973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26591034421094807057525189 4985818953955276323285973)
              ·
                refine ⟨116855131733326788827015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4985818953955276323285973 116855131733326788827015)
                ·
                  rfl

theorem cell23_6144513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 4, 7].length) (baseStart_6144513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6144513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6144513 prefixEnd_6144513 := by exact prefixLift 6144513
  have htrace : WordTrace (prefixWord ++ tailWord_6144513) baseStart_6144513 baseEnd_6144513 := by
    simpa [prefixWord, tailWord_6144513, baseEnd_6144513] using wordTrace_append hprefix tailTrace_6144513
  have hstable : (prefixWord ++ tailWord_6144513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6144513).length < 2 ^ (prefixWord ++ tailWord_6144513).sum := by decide
  have hdescent : baseEnd_6144513 < baseStart_6144513 := by decide
  rcases family_descends (prefixWord ++ tailWord_6144513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6144518 : List Nat := [6, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3]
def baseStart_6144518 : Nat := 118140960795 + 6144518 * 2 ^ 59
def prefixEnd_6144518 : Nat := 4983230072969 + 3 ^ 40 * 6144518 * 2
def baseEnd_6144518 : Nat := 3155091124203095778766883

theorem tailTrace_6144518 : CollatzResearch.WordTrace tailWord_6144518 prefixEnd_6144518 3155091124203095778766883 := by
  unfold tailWord_6144518
  simp only [CollatzResearch.WordTrace]
  refine ⟨7003405711045880030390569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 149405988502312107314998805 7003405711045880030390569)
  ·
    refine ⟨5252554283284410022792927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7003405711045880030390569 5252554283284410022792927)
    ·
      refine ⟨7878831424926615034189391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5252554283284410022792927 7878831424926615034189391)
      ·
        refine ⟨11818247137389922551284087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7878831424926615034189391 11818247137389922551284087)
        ·
          refine ⟨17727370706084883826926131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11818247137389922551284087 17727370706084883826926131)
          ·
            refine ⟨26591056059127325740389197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17727370706084883826926131 26591056059127325740389197)
            ·
              refine ⟨9971646022172747152645949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26591056059127325740389197 9971646022172747152645949)
              ·
                refine ⟨3739367258314780182242231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9971646022172747152645949 3739367258314780182242231)
                ·
                  refine ⟨5609050887472170273363347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3739367258314780182242231 5609050887472170273363347)
                  ·
                    refine ⟨8413576331208255410045021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5609050887472170273363347 8413576331208255410045021)
                    ·
                      refine ⟨3155091124203095778766883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8413576331208255410045021 3155091124203095778766883)
                      ·
                        rfl

theorem cell23_6144518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3].length) (baseStart_6144518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6144518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6144518 prefixEnd_6144518 := by exact prefixLift 6144518
  have htrace : WordTrace (prefixWord ++ tailWord_6144518) baseStart_6144518 baseEnd_6144518 := by
    simpa [prefixWord, tailWord_6144518, baseEnd_6144518] using wordTrace_append hprefix tailTrace_6144518
  have hstable : (prefixWord ++ tailWord_6144518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6144518).length < 2 ^ (prefixWord ++ tailWord_6144518).sum := by decide
  have hdescent : baseEnd_6144518 < baseStart_6144518 := by decide
  rcases family_descends (prefixWord ++ tailWord_6144518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6144524 : List Nat := [2, 2, 1, 2, 4, 1, 3, 3, 1, 2, 2]
def baseStart_6144524 : Nat := 118140960795 + 6144524 * 2 ^ 59
def prefixEnd_6144524 : Nat := 4983230072969 + 3 ^ 40 * 6144524 * 2
def baseEnd_6144524 : Nat := 3155094205087022755291855

theorem tailTrace_6144524 : CollatzResearch.WordTrace tailWord_6144524 prefixEnd_6144524 3155094205087022755291855 := by
  unfold tailWord_6144524
  simp only [CollatzResearch.WordTrace]
  refine ⟨112054600795723211998608313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149406134394297615998144417 112054600795723211998608313)
  ·
    refine ⟨84040950596792408998956235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112054600795723211998608313 84040950596792408998956235)
    ·
      refine ⟨126061425895188613498434353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84040950596792408998956235 126061425895188613498434353)
      ·
        refine ⟨94546069421391460123825765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126061425895188613498434353 94546069421391460123825765)
        ·
          refine ⟨17727388016510898773217331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 94546069421391460123825765 17727388016510898773217331)
          ·
            refine ⟨26591082024766348159825997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17727388016510898773217331 26591082024766348159825997)
            ·
              refine ⟨9971655759287380559934749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26591082024766348159825997 9971655759287380559934749)
              ·
                refine ⟨3739370909732767709975531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9971655759287380559934749 3739370909732767709975531)
                ·
                  refine ⟨5609056364599151564963297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3739370909732767709975531 5609056364599151564963297)
                  ·
                    refine ⟨4206792273449363673722473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5609056364599151564963297 4206792273449363673722473)
                    ·
                      refine ⟨3155094205087022755291855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4206792273449363673722473 3155094205087022755291855)
                      ·
                        rfl

theorem cell23_6144524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 3, 3, 1, 2, 2].length) (baseStart_6144524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6144524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6144524 prefixEnd_6144524 := by exact prefixLift 6144524
  have htrace : WordTrace (prefixWord ++ tailWord_6144524) baseStart_6144524 baseEnd_6144524 := by
    simpa [prefixWord, tailWord_6144524, baseEnd_6144524] using wordTrace_append hprefix tailTrace_6144524
  have hstable : (prefixWord ++ tailWord_6144524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6144524).length < 2 ^ (prefixWord ++ tailWord_6144524).sum := by decide
  have hdescent : baseEnd_6144524 < baseStart_6144524 := by decide
  rcases family_descends (prefixWord ++ tailWord_6144524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6144540 : List Nat := [2, 2, 3, 1, 2, 2, 2, 1, 4, 1, 3]
def baseStart_6144540 : Nat := 118140960795 + 6144540 * 2 ^ 59
def prefixEnd_6144540 : Nat := 4983230072969 + 3 ^ 40 * 6144540 * 2
def baseEnd_6144540 : Nat := 3155102420777494692691781

theorem tailTrace_6144540 : CollatzResearch.WordTrace tailWord_6144540 prefixEnd_6144540 3155102420777494692691781 := by
  unfold tailWord_6144540
  simp only [CollatzResearch.WordTrace]
  refine ⟨112054892579694229364899537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149406523439592305819866049 112054892579694229364899537)
  ·
    refine ⟨84041169434770672023674653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112054892579694229364899537 84041169434770672023674653)
    ·
      refine ⟨31515438538039002008877995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84041169434770672023674653 31515438538039002008877995)
      ·
        refine ⟨47273157807058503013316993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31515438538039002008877995 47273157807058503013316993)
        ·
          refine ⟨35454868355293877259987745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47273157807058503013316993 35454868355293877259987745)
          ·
            refine ⟨26591151266470407944990809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35454868355293877259987745 26591151266470407944990809)
            ·
              refine ⟨19943363449852805958743107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26591151266470407944990809 19943363449852805958743107)
              ·
                refine ⟨29915045174779208938114661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19943363449852805958743107 29915045174779208938114661)
                ·
                  refine ⟨5609070970271101675896499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29915045174779208938114661 5609070970271101675896499)
                  ·
                    refine ⟨8413606455406652513844749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5609070970271101675896499 8413606455406652513844749)
                    ·
                      refine ⟨3155102420777494692691781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8413606455406652513844749 3155102420777494692691781)
                      ·
                        rfl

theorem cell23_6144540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 1, 4, 1, 3].length) (baseStart_6144540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6144540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6144540 prefixEnd_6144540 := by exact prefixLift 6144540
  have htrace : WordTrace (prefixWord ++ tailWord_6144540) baseStart_6144540 baseEnd_6144540 := by
    simpa [prefixWord, tailWord_6144540, baseEnd_6144540] using wordTrace_append hprefix tailTrace_6144540
  have hstable : (prefixWord ++ tailWord_6144540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6144540).length < 2 ^ (prefixWord ++ tailWord_6144540).sum := by decide
  have hdescent : baseEnd_6144540 < baseStart_6144540 := by decide
  rcases family_descends (prefixWord ++ tailWord_6144540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6144541 : List Nat := [1, 4, 2, 2, 1, 3, 3, 2, 1, 2, 2]
def baseStart_6144541 : Nat := 118140960795 + 6144541 * 2 ^ 59
def prefixEnd_6144541 : Nat := 4983230072969 + 3 ^ 40 * 6144541 * 2
def baseEnd_6144541 : Nat := 3155102934258149188779277

theorem tailTrace_6144541 : CollatzResearch.WordTrace tailWord_6144541 prefixEnd_6144541 3155102934258149188779277 := by
  unfold tailWord_6144541
  simp only [CollatzResearch.WordTrace]
  refine ⟨224109821632384835900585477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149406547754923223933723651 224109821632384835900585477)
  ·
    refine ⟨42020591556072156731359777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 224109821632384835900585477 42020591556072156731359777)
    ·
      refine ⟨31515443667054117548519833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42020591556072156731359777 31515443667054117548519833)
      ·
        refine ⟨23636582750290588161389875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31515443667054117548519833 23636582750290588161389875)
        ·
          refine ⟨35454874125435882242084813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23636582750290588161389875 35454874125435882242084813)
          ·
            refine ⟨13295577797038455840781805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35454874125435882242084813 13295577797038455840781805)
            ·
              refine ⟨4985841673889420940293177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13295577797038455840781805 4985841673889420940293177)
              ·
                refine ⟨3739381255417065705219883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4985841673889420940293177 3739381255417065705219883)
                ·
                  refine ⟨5609071883125598557829825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3739381255417065705219883 5609071883125598557829825)
                  ·
                    refine ⟨4206803912344198918372369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5609071883125598557829825 4206803912344198918372369)
                    ·
                      refine ⟨3155102934258149188779277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4206803912344198918372369 3155102934258149188779277)
                      ·
                        rfl

theorem cell23_6144541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 3, 2, 1, 2, 2].length) (baseStart_6144541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6144541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6144541 prefixEnd_6144541 := by exact prefixLift 6144541
  have htrace : WordTrace (prefixWord ++ tailWord_6144541) baseStart_6144541 baseEnd_6144541 := by
    simpa [prefixWord, tailWord_6144541, baseEnd_6144541] using wordTrace_append hprefix tailTrace_6144541
  have hstable : (prefixWord ++ tailWord_6144541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6144541).length < 2 ^ (prefixWord ++ tailWord_6144541).sum := by decide
  have hdescent : baseEnd_6144541 < baseStart_6144541 := by decide
  rcases family_descends (prefixWord ++ tailWord_6144541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6144551 : List Nat := [1, 1, 7, 2, 1, 2, 2, 1, 2, 4]
def baseStart_6144551 : Nat := 118140960795 + 6144551 * 2 ^ 59
def prefixEnd_6144551 : Nat := 4983230072969 + 3 ^ 40 * 6144551 * 2
def baseEnd_6144551 : Nat := 1051702689688231383218077

theorem tailTrace_6144551 : CollatzResearch.WordTrace tailWord_6144551 prefixEnd_6144551 1051702689688231383218077 := by
  unfold tailWord_6144551
  simp only [CollatzResearch.WordTrace]
  refine ⟨224110186362348607608449507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149406790908232405072299671 224110186362348607608449507)
  ·
    refine ⟨336165279543522911412674261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224110186362348607608449507 336165279543522911412674261)
    ·
      refine ⟨7878873739301318236234553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 336165279543522911412674261 7878873739301318236234553)
      ·
        refine ⟨5909155304475988677175915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7878873739301318236234553 5909155304475988677175915)
        ·
          refine ⟨8863732956713983015763873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5909155304475988677175915 8863732956713983015763873)
          ·
            refine ⟨6647799717535487261822905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8863732956713983015763873 6647799717535487261822905)
            ·
              refine ⟨4985849788151615446367179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6647799717535487261822905 4985849788151615446367179)
              ·
                refine ⟨7478774682227423169550769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4985849788151615446367179 7478774682227423169550769)
                ·
                  refine ⟨5609081011670567377163077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7478774682227423169550769 5609081011670567377163077)
                  ·
                    refine ⟨1051702689688231383218077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5609081011670567377163077 1051702689688231383218077)
                    ·
                      rfl

theorem cell23_6144551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_6144551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6144551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6144551 prefixEnd_6144551 := by exact prefixLift 6144551
  have htrace : WordTrace (prefixWord ++ tailWord_6144551) baseStart_6144551 baseEnd_6144551 := by
    simpa [prefixWord, tailWord_6144551, baseEnd_6144551] using wordTrace_append hprefix tailTrace_6144551
  have hstable : (prefixWord ++ tailWord_6144551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6144551).length < 2 ^ (prefixWord ++ tailWord_6144551).sum := by decide
  have hdescent : baseEnd_6144551 < baseStart_6144551 := by decide
  rcases family_descends (prefixWord ++ tailWord_6144551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6144556 : List Nat := [2, 2, 1, 1, 1, 2, 1, 5, 2, 6]
def baseStart_6144556 : Nat := 118140960795 + 6144556 * 2 ^ 59
def prefixEnd_6144556 : Nat := 4983230072969 + 3 ^ 40 * 6144556 * 2
def baseEnd_6144556 : Nat := 1051703545489322210030569

theorem tailTrace_6144556 : CollatzResearch.WordTrace tailWord_6144556 prefixEnd_6144556 1051703545489322210030569 := by
  unfold tailWord_6144556
  simp only [CollatzResearch.WordTrace]
  refine ⟨112055184363665246731190761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149406912484886995641587681 112055184363665246731190761)
  ·
    refine ⟨84041388272748935048393071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112055184363665246731190761 84041388272748935048393071)
    ·
      refine ⟨126062082409123402572589607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84041388272748935048393071 126062082409123402572589607)
      ·
        refine ⟨189093123613685103858884411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126062082409123402572589607 189093123613685103858884411)
        ·
          refine ⟨283639685420527655788326617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189093123613685103858884411 283639685420527655788326617)
          ·
            refine ⟨212729764065395741841244963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 283639685420527655788326617 212729764065395741841244963)
            ·
              refine ⟨319094646098093612761867445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 212729764065395741841244963 319094646098093612761867445)
              ·
                refine ⟨29915123071696276196425073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 319094646098093612761867445 29915123071696276196425073)
                ·
                  refine ⟨22436342303772207147318805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29915123071696276196425073 22436342303772207147318805)
                  ·
                    refine ⟨1051703545489322210030569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22436342303772207147318805 1051703545489322210030569)
                    ·
                      rfl

theorem cell23_6144556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 6].length) (baseStart_6144556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6144556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6144556 prefixEnd_6144556 := by exact prefixLift 6144556
  have htrace : WordTrace (prefixWord ++ tailWord_6144556) baseStart_6144556 baseEnd_6144556 := by
    simpa [prefixWord, tailWord_6144556, baseEnd_6144556] using wordTrace_append hprefix tailTrace_6144556
  have hstable : (prefixWord ++ tailWord_6144556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6144556).length < 2 ^ (prefixWord ++ tailWord_6144556).sum := by decide
  have hdescent : baseEnd_6144556 < baseStart_6144556 := by decide
  rcases family_descends (prefixWord ++ tailWord_6144556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6144583 : List Nat := [1, 1, 4, 1, 4, 1, 2, 1, 2, 1, 5]
def baseStart_6144583 : Nat := 118140960795 + 6144583 * 2 ^ 59
def prefixEnd_6144583 : Nat := 4983230072969 + 3 ^ 40 * 6144583 * 2
def baseEnd_6144583 : Nat := 3155124500445638024454083

theorem tailTrace_6144583 : CollatzResearch.WordTrace tailWord_6144583 prefixEnd_6144583 3155124500445638024454083 := by
  unfold tailWord_6144583
  simp only [CollatzResearch.WordTrace]
  refine ⟨224111353498232677073614403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149407568998821784715742935 224111353498232677073614403)
  ·
    refine ⟨336167030247349015610421605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224111353498232677073614403 336167030247349015610421605)
    ·
      refine ⟨63031318171377940426954051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 336167030247349015610421605 63031318171377940426954051)
      ·
        refine ⟨94546977257066910640431077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63031318171377940426954051 94546977257066910640431077)
        ·
          refine ⟨17727558235700045745080827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 94546977257066910640431077 17727558235700045745080827)
          ·
            refine ⟨26591337353550068617621241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17727558235700045745080827 26591337353550068617621241)
            ·
              refine ⟨19943503015162551463215931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26591337353550068617621241 19943503015162551463215931)
              ·
                refine ⟨29915254522743827194823897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19943503015162551463215931 29915254522743827194823897)
                ·
                  refine ⟨22436440892057870396117923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29915254522743827194823897 22436440892057870396117923)
                  ·
                    refine ⟨33654661338086805594176885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22436440892057870396117923 33654661338086805594176885)
                    ·
                      refine ⟨3155124500445638024454083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33654661338086805594176885 3155124500445638024454083)
                      ·
                        rfl

theorem cell23_6144583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 1, 2, 1, 5].length) (baseStart_6144583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6144583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6144583 prefixEnd_6144583 := by exact prefixLift 6144583
  have htrace : WordTrace (prefixWord ++ tailWord_6144583) baseStart_6144583 baseEnd_6144583 := by
    simpa [prefixWord, tailWord_6144583, baseEnd_6144583] using wordTrace_append hprefix tailTrace_6144583
  have hstable : (prefixWord ++ tailWord_6144583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6144583).length < 2 ^ (prefixWord ++ tailWord_6144583).sum := by decide
  have hdescent : baseEnd_6144583 < baseStart_6144583 := by decide
  rcases family_descends (prefixWord ++ tailWord_6144583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6144597 : List Nat := [1, 3, 2, 2, 1, 1, 3, 4, 2, 2, 2]
def baseStart_6144597 : Nat := 118140960795 + 6144597 * 2 ^ 59
def prefixEnd_6144597 : Nat := 4983230072969 + 3 ^ 40 * 6144597 * 2
def baseEnd_6144597 : Nat := 3155131689174800969679019

theorem tailTrace_6144597 : CollatzResearch.WordTrace tailWord_6144597 prefixEnd_6144597 3155131689174800969679019 := by
  unfold tailWord_6144597
  simp only [CollatzResearch.WordTrace]
  refine ⟨224111864120181957464624045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149407909413454638309749363 224111864120181957464624045)
  ·
    refine ⟨84041949045068234049234017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 224111864120181957464624045 84041949045068234049234017)
    ·
      refine ⟨63031461783801175536925513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84041949045068234049234017 63031461783801175536925513)
      ·
        refine ⟨47273596337850881652694135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63031461783801175536925513 47273596337850881652694135)
        ·
          refine ⟨70910394506776322479041203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47273596337850881652694135 70910394506776322479041203)
          ·
            refine ⟨106365591760164483718561805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70910394506776322479041203 106365591760164483718561805)
            ·
              refine ⟨39887096910061681394460677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 106365591760164483718561805 39887096910061681394460677)
              ·
                refine ⟨7478830670636565261461377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39887096910061681394460677 7478830670636565261461377)
                ·
                  refine ⟨5609123002977423946096033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7478830670636565261461377 5609123002977423946096033)
                  ·
                    refine ⟨4206842252233067959572025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5609123002977423946096033 4206842252233067959572025)
                    ·
                      refine ⟨3155131689174800969679019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4206842252233067959572025 3155131689174800969679019)
                      ·
                        rfl

theorem cell23_6144597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 4, 2, 2, 2].length) (baseStart_6144597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6144597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6144597 prefixEnd_6144597 := by exact prefixLift 6144597
  have htrace : WordTrace (prefixWord ++ tailWord_6144597) baseStart_6144597 baseEnd_6144597 := by
    simpa [prefixWord, tailWord_6144597, baseEnd_6144597] using wordTrace_append hprefix tailTrace_6144597
  have hstable : (prefixWord ++ tailWord_6144597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6144597).length < 2 ^ (prefixWord ++ tailWord_6144597).sum := by decide
  have hdescent : baseEnd_6144597 < baseStart_6144597 := by decide
  rcases family_descends (prefixWord ++ tailWord_6144597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6144633 : List Nat := [1, 2, 1, 3, 3, 3, 1, 1, 1, 7]
def baseStart_6144633 : Nat := 118140960795 + 6144633 * 2 ^ 59
def prefixEnd_6144633 : Nat := 4983230072969 + 3 ^ 40 * 6144633 * 2
def baseEnd_6144633 : Nat := 1051716724826120942942951

theorem tailTrace_6144633 : CollatzResearch.WordTrace tailWord_6144633 prefixEnd_6144633 1051716724826120942942951 := by
  unfold tailWord_6144633
  simp only [CollatzResearch.WordTrace]
  refine ⟨224113177148051535612934553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149408784765367690408623035 224113177148051535612934553)
  ·
    refine ⟨168084882861038651709700915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224113177148051535612934553 168084882861038651709700915)
    ·
      refine ⟨252127324291557977564551373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168084882861038651709700915 252127324291557977564551373)
      ·
        refine ⟨94547746609334241586706765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 252127324291557977564551373 94547746609334241586706765)
        ·
          refine ⟨35455404978500340595015037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94547746609334241586706765 35455404978500340595015037)
          ·
            refine ⟨13295776866937627723130639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35455404978500340595015037 13295776866937627723130639)
            ·
              refine ⟨19943665300406441584695959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13295776866937627723130639 19943665300406441584695959)
              ·
                refine ⟨29915497950609662377043939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19943665300406441584695959 29915497950609662377043939)
                ·
                  refine ⟨44873246925914493565565909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29915497950609662377043939 44873246925914493565565909)
                  ·
                    refine ⟨1051716724826120942942951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44873246925914493565565909 1051716724826120942942951)
                    ·
                      rfl

theorem cell23_6144633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 1, 1, 7].length) (baseStart_6144633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6144633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6144633 prefixEnd_6144633 := by exact prefixLift 6144633
  have htrace : WordTrace (prefixWord ++ tailWord_6144633) baseStart_6144633 baseEnd_6144633 := by
    simpa [prefixWord, tailWord_6144633, baseEnd_6144633] using wordTrace_append hprefix tailTrace_6144633
  have hstable : (prefixWord ++ tailWord_6144633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6144633).length < 2 ^ (prefixWord ++ tailWord_6144633).sum := by decide
  have hdescent : baseEnd_6144633 < baseStart_6144633 := by decide
  rcases family_descends (prefixWord ++ tailWord_6144633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6144637 : List Nat := [1, 4, 1, 1, 5, 1, 2, 3, 5]
def baseStart_6144637 : Nat := 118140960795 + 6144637 * 2 ^ 59
def prefixEnd_6144637 : Nat := 4983230072969 + 3 ^ 40 * 6144637 * 2
def baseEnd_6144637 : Nat := 350572469822331201464315

theorem tailTrace_6144637 : CollatzResearch.WordTrace tailWord_6144637 prefixEnd_6144637 350572469822331201464315 := by
  unfold tailWord_6144637
  simp only [CollatzResearch.WordTrace]
  refine ⟨224113323040037044296080165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149408882026691362864053443 224113323040037044296080165)
  ·
    refine ⟨42021248070006945805515031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 224113323040037044296080165 42021248070006945805515031)
    ·
      refine ⟨63031872105010418708272547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42021248070006945805515031 63031872105010418708272547)
      ·
        refine ⟨94547808157515628062408821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63031872105010418708272547 94547808157515628062408821)
        ·
          refine ⟨8863857014767090130850827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 94547808157515628062408821 8863857014767090130850827)
          ·
            refine ⟨13295785522150635196276241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8863857014767090130850827 13295785522150635196276241)
            ·
              refine ⟨9971839141612976397207181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13295785522150635196276241 9971839141612976397207181)
              ·
                refine ⟨3739439678104866148952693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9971839141612976397207181 3739439678104866148952693)
                ·
                  refine ⟨350572469822331201464315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3739439678104866148952693 350572469822331201464315)
                  ·
                    rfl

theorem cell23_6144637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 2, 3, 5].length) (baseStart_6144637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6144637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6144637 prefixEnd_6144637 := by exact prefixLift 6144637
  have htrace : WordTrace (prefixWord ++ tailWord_6144637) baseStart_6144637 baseEnd_6144637 := by
    simpa [prefixWord, tailWord_6144637, baseEnd_6144637] using wordTrace_append hprefix tailTrace_6144637
  have hstable : (prefixWord ++ tailWord_6144637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6144637).length < 2 ^ (prefixWord ++ tailWord_6144637).sum := by decide
  have hdescent : baseEnd_6144637 < baseStart_6144637 := by decide
  rcases family_descends (prefixWord ++ tailWord_6144637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6144670 : List Nat := [4, 3, 1, 1, 1, 1, 1, 1, 3, 3, 4]
def baseStart_6144670 : Nat := 118140960795 + 6144670 * 2 ^ 59
def prefixEnd_6144670 : Nat := 4983230072969 + 3 ^ 40 * 6144670 * 2
def baseEnd_6144670 : Nat := 3155169173262579184066183

theorem tailTrace_6144670 : CollatzResearch.WordTrace tailWord_6144670 prefixEnd_6144670 3155169173262579184066183 := by
  unfold tailWord_6144670
  simp only [CollatzResearch.WordTrace]
  refine ⟨28014315831114686366503933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149409684432611660621354309 28014315831114686366503933)
  ·
    refine ⟨10505368436668007387438975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28014315831114686366503933 10505368436668007387438975)
    ·
      refine ⟨15758052655002011081158463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10505368436668007387438975 15758052655002011081158463)
      ·
        refine ⟨23637078982503016621737695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15758052655002011081158463 23637078982503016621737695)
        ·
          refine ⟨35455618473754524932606543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23637078982503016621737695 35455618473754524932606543)
          ·
            refine ⟨53183427710631787398909815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35455618473754524932606543 53183427710631787398909815)
            ·
              refine ⟨79775141565947681098364723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53183427710631787398909815 79775141565947681098364723)
              ·
                refine ⟨119662712348921521647547085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79775141565947681098364723 119662712348921521647547085)
                ·
                  refine ⟨44873517130845570617830157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 119662712348921521647547085 44873517130845570617830157)
                  ·
                    refine ⟨16827568924067088981686309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44873517130845570617830157 16827568924067088981686309)
                    ·
                      refine ⟨3155169173262579184066183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16827568924067088981686309 3155169173262579184066183)
                      ·
                        rfl

theorem cell23_6144670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_6144670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6144670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6144670 prefixEnd_6144670 := by exact prefixLift 6144670
  have htrace : WordTrace (prefixWord ++ tailWord_6144670) baseStart_6144670 baseEnd_6144670 := by
    simpa [prefixWord, tailWord_6144670, baseEnd_6144670] using wordTrace_append hprefix tailTrace_6144670
  have hstable : (prefixWord ++ tailWord_6144670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6144670).length < 2 ^ (prefixWord ++ tailWord_6144670).sum := by decide
  have hdescent : baseEnd_6144670 < baseStart_6144670 := by decide
  rcases family_descends (prefixWord ++ tailWord_6144670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6144690 : List Nat := [3, 2, 1, 1, 1, 2, 1, 5, 2, 2, 3]
def baseStart_6144690 : Nat := 118140960795 + 6144690 * 2 ^ 59
def prefixEnd_6144690 : Nat := 4983230072969 + 3 ^ 40 * 6144690 * 2
def baseEnd_6144690 : Nat := 3155179442875669105816091

theorem tailTrace_6144690 : CollatzResearch.WordTrace tailWord_6144690 prefixEnd_6144690 3155179442875669105816091 := by
  unfold tailWord_6144690
  simp only [CollatzResearch.WordTrace]
  refine ⟨56028814027211258586939881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149410170739230022898506349 56028814027211258586939881)
  ·
    refine ⟨42021610520408443940204911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56028814027211258586939881 42021610520408443940204911)
    ·
      refine ⟨63032415780612665910307367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42021610520408443940204911 63032415780612665910307367)
      ·
        refine ⟨94548623670918998865461051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63032415780612665910307367 94548623670918998865461051)
        ·
          refine ⟨141822935506378498298191577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94548623670918998865461051 141822935506378498298191577)
          ·
            refine ⟨106367201629783873723643683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141822935506378498298191577 106367201629783873723643683)
            ·
              refine ⟨159550802444675810585465525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106367201629783873723643683 159550802444675810585465525)
              ·
                refine ⟨14957887729188357242387393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 159550802444675810585465525 14957887729188357242387393)
                ·
                  refine ⟨11218415796891267931790545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14957887729188357242387393 11218415796891267931790545)
                  ·
                    refine ⟨8413811847668450948842909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11218415796891267931790545 8413811847668450948842909)
                    ·
                      refine ⟨3155179442875669105816091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8413811847668450948842909 3155179442875669105816091)
                      ·
                        rfl

theorem cell23_6144690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 5, 2, 2, 3].length) (baseStart_6144690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6144690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6144690 prefixEnd_6144690 := by exact prefixLift 6144690
  have htrace : WordTrace (prefixWord ++ tailWord_6144690) baseStart_6144690 baseEnd_6144690 := by
    simpa [prefixWord, tailWord_6144690, baseEnd_6144690] using wordTrace_append hprefix tailTrace_6144690
  have hstable : (prefixWord ++ tailWord_6144690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6144690).length < 2 ^ (prefixWord ++ tailWord_6144690).sum := by decide
  have hdescent : baseEnd_6144690 < baseStart_6144690 := by decide
  rcases family_descends (prefixWord ++ tailWord_6144690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6144727 : List Nat := [1, 1, 3, 2, 1, 6, 2, 1, 6]
def baseStart_6144727 : Nat := 118140960795 + 6144727 * 2 ^ 59
def prefixEnd_6144727 : Nat := 4983230072969 + 3 ^ 40 * 6144727 * 2
def baseEnd_6144727 : Nat := 350577604628876162339269

theorem tailTrace_6144727 : CollatzResearch.WordTrace tailWord_6144727 prefixEnd_6144727 350577604628876162339269 := by
  unfold tailWord_6144727
  simp only [CollatzResearch.WordTrace]
  refine ⟨224116605609710989666856435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149411070406473993111237623 224116605609710989666856435)
  ·
    refine ⟨336174908414566484500284653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224116605609710989666856435 336174908414566484500284653)
    ·
      refine ⟨126065590655462431687606745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 336174908414566484500284653 126065590655462431687606745)
      ·
        refine ⟨94549192991596823765705059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126065590655462431687606745 94549192991596823765705059)
        ·
          refine ⟨141823789487395235648557589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94549192991596823765705059 141823789487395235648557589)
          ·
            refine ⟨6647990132221651671026137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 141823789487395235648557589 6647990132221651671026137)
            ·
              refine ⟨4985992599166238753269603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6647990132221651671026137 4985992599166238753269603)
              ·
                refine ⟨7478988898749358129904405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4985992599166238753269603 7478988898749358129904405)
                ·
                  refine ⟨350577604628876162339269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7478988898749358129904405 350577604628876162339269)
                  ·
                    rfl

theorem cell23_6144727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 2, 1, 6].length) (baseStart_6144727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6144727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6144727 prefixEnd_6144727 := by exact prefixLift 6144727
  have htrace : WordTrace (prefixWord ++ tailWord_6144727) baseStart_6144727 baseEnd_6144727 := by
    simpa [prefixWord, tailWord_6144727, baseEnd_6144727] using wordTrace_append hprefix tailTrace_6144727
  have hstable : (prefixWord ++ tailWord_6144727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6144727).length < 2 ^ (prefixWord ++ tailWord_6144727).sum := by decide
  have hdescent : baseEnd_6144727 < baseStart_6144727 := by decide
  rcases family_descends (prefixWord ++ tailWord_6144727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6144740 : List Nat := [2, 3, 1, 1, 1, 5, 1, 1, 3, 5]
def baseStart_6144740 : Nat := 118140960795 + 6144740 * 2 ^ 59
def prefixEnd_6144740 : Nat := 4983230072969 + 3 ^ 40 * 6144740 * 2
def baseEnd_6144740 : Nat := 1051735038969464636730287

theorem tailTrace_6144740 : CollatzResearch.WordTrace tailWord_6144740 prefixEnd_6144740 1051735038969464636730287 := by
  unfold tailWord_6144740
  simp only [CollatzResearch.WordTrace]
  refine ⟨112058539879331946443539837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149411386505775928591386449 112058539879331946443539837)
  ·
    refine ⟨42021952454749479916327439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112058539879331946443539837 42021952454749479916327439)
    ·
      refine ⟨63032928682124219874491159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42021952454749479916327439 63032928682124219874491159)
      ·
        refine ⟨94549393023186329811736739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63032928682124219874491159 94549393023186329811736739)
        ·
          refine ⟨141824089534779494717605109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94549393023186329811736739 141824089534779494717605109)
          ·
            refine ⟨13296008393885577629775479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 141824089534779494717605109 13296008393885577629775479)
            ·
              refine ⟨19944012590828366444663219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13296008393885577629775479 19944012590828366444663219)
              ·
                refine ⟨29916018886242549666994829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19944012590828366444663219 29916018886242549666994829)
                ·
                  refine ⟨11218507082340956125123061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29916018886242549666994829 11218507082340956125123061)
                  ·
                    refine ⟨1051735038969464636730287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11218507082340956125123061 1051735038969464636730287)
                    ·
                      rfl

theorem cell23_6144740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 1, 3, 5].length) (baseStart_6144740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6144740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6144740 prefixEnd_6144740 := by exact prefixLift 6144740
  have htrace : WordTrace (prefixWord ++ tailWord_6144740) baseStart_6144740 baseEnd_6144740 := by
    simpa [prefixWord, tailWord_6144740, baseEnd_6144740] using wordTrace_append hprefix tailTrace_6144740
  have hstable : (prefixWord ++ tailWord_6144740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6144740).length < 2 ^ (prefixWord ++ tailWord_6144740).sum := by decide
  have hdescent : baseEnd_6144740 < baseStart_6144740 := by decide
  rcases family_descends (prefixWord ++ tailWord_6144740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6144773 : List Nat := [1, 3, 1, 1, 2, 1, 1, 3, 3, 1, 6]
def baseStart_6144773 : Nat := 118140960795 + 6144773 * 2 ^ 59
def prefixEnd_6144773 : Nat := 4983230072969 + 3 ^ 40 * 6144773 * 2
def baseEnd_6144773 : Nat := 3155222061769992281078209

theorem tailTrace_6144773 : CollatzResearch.WordTrace tailWord_6144773 prefixEnd_6144773 3155222061769992281078209 := by
  unfold tailWord_6144773
  simp only [CollatzResearch.WordTrace]
  refine ⟨224118283367544339523030973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149412188911696226348687315 224118283367544339523030973)
  ·
    refine ⟨84044356262829127321136615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 224118283367544339523030973 84044356262829127321136615)
    ·
      refine ⟨126066534394243690981704923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84044356262829127321136615 126066534394243690981704923)
      ·
        refine ⟨189099801591365536472557385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126066534394243690981704923 189099801591365536472557385)
        ·
          refine ⟨141824851193524152354418039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189099801591365536472557385 141824851193524152354418039)
          ·
            refine ⟨212737276790286228531627059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141824851193524152354418039 212737276790286228531627059)
            ·
              refine ⟨319105915185429342797440589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 212737276790286228531627059 319105915185429342797440589)
              ·
                refine ⟨119664718194536003549040221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 319105915185429342797440589 119664718194536003549040221)
                ·
                  refine ⟨44874269322951001330890083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 119664718194536003549040221 44874269322951001330890083)
                  ·
                    refine ⟨67311403984426501996335125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44874269322951001330890083 67311403984426501996335125)
                    ·
                      refine ⟨3155222061769992281078209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67311403984426501996335125 3155222061769992281078209)
                      ·
                        rfl

theorem cell23_6144773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 3, 1, 6].length) (baseStart_6144773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6144773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6144773 prefixEnd_6144773 := by exact prefixLift 6144773
  have htrace : WordTrace (prefixWord ++ tailWord_6144773) baseStart_6144773 baseEnd_6144773 := by
    simpa [prefixWord, tailWord_6144773, baseEnd_6144773] using wordTrace_append hprefix tailTrace_6144773
  have hstable : (prefixWord ++ tailWord_6144773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6144773).length < 2 ^ (prefixWord ++ tailWord_6144773).sum := by decide
  have hdescent : baseEnd_6144773 < baseStart_6144773 := by decide
  rcases family_descends (prefixWord ++ tailWord_6144773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6144794 : List Nat := [3, 1, 1, 3, 2, 1, 3, 2, 3, 2, 2]
def baseStart_6144794 : Nat := 118140960795 + 6144794 * 2 ^ 59
def prefixEnd_6144794 : Nat := 4983230072969 + 3 ^ 40 * 6144794 * 2
def baseEnd_6144794 : Nat := 3155232844863736698915613

theorem tailTrace_6144794 : CollatzResearch.WordTrace tailWord_6144794 prefixEnd_6144794 3155232844863736698915613 := by
  unfold tailWord_6144794
  simp only [CollatzResearch.WordTrace]
  refine ⟨56029762325117065027386359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149412699533645506739696957 56029762325117065027386359)
  ·
    refine ⟨84044643487675597541079539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56029762325117065027386359 84044643487675597541079539)
    ·
      refine ⟨126066965231513396311619309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84044643487675597541079539 126066965231513396311619309)
      ·
        refine ⟨47275111961817523616857241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126066965231513396311619309 47275111961817523616857241)
        ·
          refine ⟨35456333971363142712642931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47275111961817523616857241 35456333971363142712642931)
          ·
            refine ⟨53184500957044714068964397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35456333971363142712642931 53184500957044714068964397)
            ·
              refine ⟨19944187858891767775861649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53184500957044714068964397 19944187858891767775861649)
              ·
                refine ⟨14958140894168825831896237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19944187858891767775861649 14958140894168825831896237)
                ·
                  refine ⟨5609302835313309686961089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14958140894168825831896237 5609302835313309686961089)
                  ·
                    refine ⟨4206977126484982265220817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5609302835313309686961089 4206977126484982265220817)
                    ·
                      refine ⟨3155232844863736698915613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4206977126484982265220817 3155232844863736698915613)
                      ·
                        rfl

theorem cell23_6144794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 2, 3, 2, 2].length) (baseStart_6144794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6144794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6144794 prefixEnd_6144794 := by exact prefixLift 6144794
  have htrace : WordTrace (prefixWord ++ tailWord_6144794) baseStart_6144794 baseEnd_6144794 := by
    simpa [prefixWord, tailWord_6144794, baseEnd_6144794] using wordTrace_append hprefix tailTrace_6144794
  have hstable : (prefixWord ++ tailWord_6144794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6144794).length < 2 ^ (prefixWord ++ tailWord_6144794).sum := by decide
  have hdescent : baseEnd_6144794 < baseStart_6144794 := by decide
  rcases family_descends (prefixWord ++ tailWord_6144794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6144837 : List Nat := [1, 3, 1, 1, 1, 2, 2, 4, 3, 3, 2]
def baseStart_6144837 : Nat := 118140960795 + 6144837 * 2 ^ 59
def prefixEnd_6144837 : Nat := 4983230072969 + 3 ^ 40 * 6144837 * 2
def baseEnd_6144837 : Nat := 3155254924531880030677915

theorem tailTrace_6144837 : CollatzResearch.WordTrace tailWord_6144837 prefixEnd_6144837 3155254924531880030677915 := by
  unfold tailWord_6144837
  simp only [CollatzResearch.WordTrace]
  refine ⟨224120617639312478453360765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149413745092874985635573843 224120617639312478453360765)
  ·
    refine ⟨84045231614742179420010287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 224120617639312478453360765 84045231614742179420010287)
    ·
      refine ⟨126067847422113269130015431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84045231614742179420010287 126067847422113269130015431)
      ·
        refine ⟨189101771133169903695023147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126067847422113269130015431 189101771133169903695023147)
        ·
          refine ⟨283652656699754855542534721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189101771133169903695023147 283652656699754855542534721)
          ·
            refine ⟨212739492524816141656901041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 283652656699754855542534721 212739492524816141656901041)
            ·
              refine ⟨159554619393612106242675781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 212739492524816141656901041 159554619393612106242675781)
              ·
                refine ⟨29916491136302269920501709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 159554619393612106242675781 29916491136302269920501709)
                ·
                  refine ⟨11218684176113351220188141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29916491136302269920501709 11218684176113351220188141)
                  ·
                    refine ⟨4207006566042506707570553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11218684176113351220188141 4207006566042506707570553)
                    ·
                      refine ⟨3155254924531880030677915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4207006566042506707570553 3155254924531880030677915)
                      ·
                        rfl

theorem cell23_6144837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 4, 3, 3, 2].length) (baseStart_6144837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6144837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6144837 prefixEnd_6144837 := by exact prefixLift 6144837
  have htrace : WordTrace (prefixWord ++ tailWord_6144837) baseStart_6144837 baseEnd_6144837 := by
    simpa [prefixWord, tailWord_6144837, baseEnd_6144837] using wordTrace_append hprefix tailTrace_6144837
  have hstable : (prefixWord ++ tailWord_6144837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6144837).length < 2 ^ (prefixWord ++ tailWord_6144837).sum := by decide
  have hdescent : baseEnd_6144837 < baseStart_6144837 := by decide
  rcases family_descends (prefixWord ++ tailWord_6144837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6144838 : List Nat := [6, 1, 1, 2, 3, 1, 1, 1, 1, 6]
def baseStart_6144838 : Nat := 118140960795 + 6144838 * 2 ^ 59
def prefixEnd_6144838 : Nat := 4983230072969 + 3 ^ 40 * 6144838 * 2
def baseEnd_6144838 : Nat := 1051751812670844842255137

theorem tailTrace_6144838 : CollatzResearch.WordTrace tailWord_6144838 prefixEnd_6144838 1051751812670844842255137 := by
  unfold tailWord_6144838
  simp only [CollatzResearch.WordTrace]
  refine ⟨7003770441009651738254599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 149413769408205903749431445 7003770441009651738254599)
  ·
    refine ⟨10505655661514477607381899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7003770441009651738254599 10505655661514477607381899)
    ·
      refine ⟨15758483492271716411072849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10505655661514477607381899 15758483492271716411072849)
      ·
        refine ⟨11818862619203787308304637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15758483492271716411072849 11818862619203787308304637)
        ·
          refine ⟨4432073482201420240614239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11818862619203787308304637 4432073482201420240614239)
          ·
            refine ⟨6648110223302130360921359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4432073482201420240614239 6648110223302130360921359)
            ·
              refine ⟨9972165334953195541382039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6648110223302130360921359 9972165334953195541382039)
              ·
                refine ⟨14958248002429793312073059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9972165334953195541382039 14958248002429793312073059)
                ·
                  refine ⟨22437372003644689968109589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14958248002429793312073059 22437372003644689968109589)
                  ·
                    refine ⟨1051751812670844842255137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22437372003644689968109589 1051751812670844842255137)
                    ·
                      rfl

theorem cell23_6144838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 1, 1, 1, 6].length) (baseStart_6144838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6144838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6144838 prefixEnd_6144838 := by exact prefixLift 6144838
  have htrace : WordTrace (prefixWord ++ tailWord_6144838) baseStart_6144838 baseEnd_6144838 := by
    simpa [prefixWord, tailWord_6144838, baseEnd_6144838] using wordTrace_append hprefix tailTrace_6144838
  have hstable : (prefixWord ++ tailWord_6144838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6144838).length < 2 ^ (prefixWord ++ tailWord_6144838).sum := by decide
  have hdescent : baseEnd_6144838 < baseStart_6144838 := by decide
  rcases family_descends (prefixWord ++ tailWord_6144838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6144844 : List Nat := [2, 2, 1, 3, 3, 3, 1, 1, 1, 3, 3]
def baseStart_6144844 : Nat := 118140960795 + 6144844 * 2 ^ 59
def prefixEnd_6144844 : Nat := 4983230072969 + 3 ^ 40 * 6144844 * 2
def baseEnd_6144844 : Nat := 3155258518896461503290383

theorem tailTrace_6144844 : CollatzResearch.WordTrace tailWord_6144844 prefixEnd_6144844 3155258518896461503290383 := by
  unfold tailWord_6144844
  simp only [CollatzResearch.WordTrace]
  refine ⟨112060436475143559324432793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149413915300191412432577057 112060436475143559324432793)
  ·
    refine ⟨84045327356357669493324595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112060436475143559324432793 84045327356357669493324595)
    ·
      refine ⟨126067991034536504239986893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84045327356357669493324595 126067991034536504239986893)
      ·
        refine ⟨47275496637951189089995085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126067991034536504239986893 47275496637951189089995085)
        ·
          refine ⟨17728311239231695908748157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47275496637951189089995085 17728311239231695908748157)
          ·
            refine ⟨6648116714711885965780559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17728311239231695908748157 6648116714711885965780559)
            ·
              refine ⟨9972175072067828948670839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6648116714711885965780559 9972175072067828948670839)
              ·
                refine ⟨14958262608101743423006259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9972175072067828948670839 14958262608101743423006259)
                ·
                  refine ⟨22437393912152615134509389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14958262608101743423006259 22437393912152615134509389)
                  ·
                    refine ⟨8414022717057230675441021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22437393912152615134509389 8414022717057230675441021)
                    ·
                      refine ⟨3155258518896461503290383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8414022717057230675441021 3155258518896461503290383)
                      ·
                        rfl

theorem cell23_6144844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 1, 1, 1, 3, 3].length) (baseStart_6144844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6144844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6144844 prefixEnd_6144844 := by exact prefixLift 6144844
  have htrace : WordTrace (prefixWord ++ tailWord_6144844) baseStart_6144844 baseEnd_6144844 := by
    simpa [prefixWord, tailWord_6144844, baseEnd_6144844] using wordTrace_append hprefix tailTrace_6144844
  have hstable : (prefixWord ++ tailWord_6144844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6144844).length < 2 ^ (prefixWord ++ tailWord_6144844).sum := by decide
  have hdescent : baseEnd_6144844 < baseStart_6144844 := by decide
  rcases family_descends (prefixWord ++ tailWord_6144844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6144880 : List Nat := [2, 1, 1, 1, 4, 1, 2, 1, 4, 2, 4]
def baseStart_6144880 : Nat := 118140960795 + 6144880 * 2 ^ 59
def prefixEnd_6144880 : Nat := 4983230072969 + 3 ^ 40 * 6144880 * 2
def baseEnd_6144880 : Nat := 3155277004200023362440217

theorem tailTrace_6144880 : CollatzResearch.WordTrace tailWord_6144880 prefixEnd_6144880 3155277004200023362440217 := by
  unfold tailWord_6144880
  simp only [CollatzResearch.WordTrace]
  refine ⟨112061092989078348398588047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149414790652104464531450729 112061092989078348398588047)
  ·
    refine ⟨168091639483617522597882071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112061092989078348398588047 168091639483617522597882071)
    ·
      refine ⟨252137459225426283896823107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168091639483617522597882071 252137459225426283896823107)
      ·
        refine ⟨378206188838139425845234661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252137459225426283896823107 378206188838139425845234661)
        ·
          refine ⟨70913660407151142345981499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 378206188838139425845234661 70913660407151142345981499)
          ·
            refine ⟨106370490610726713518972249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70913660407151142345981499 106370490610726713518972249)
            ·
              refine ⟨79777867958045035139229187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106370490610726713518972249 79777867958045035139229187)
              ·
                refine ⟨119666801937067552708843781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79777867958045035139229187 119666801937067552708843781)
                ·
                  refine ⟨22437525363200166132908209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 119666801937067552708843781 22437525363200166132908209)
                  ·
                    refine ⟨16828144022400124599681157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22437525363200166132908209 16828144022400124599681157)
                    ·
                      refine ⟨3155277004200023362440217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16828144022400124599681157 3155277004200023362440217)
                      ·
                        rfl

theorem cell23_6144880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 4, 2, 4].length) (baseStart_6144880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6144880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6144880 prefixEnd_6144880 := by exact prefixLift 6144880
  have htrace : WordTrace (prefixWord ++ tailWord_6144880) baseStart_6144880 baseEnd_6144880 := by
    simpa [prefixWord, tailWord_6144880, baseEnd_6144880] using wordTrace_append hprefix tailTrace_6144880
  have hstable : (prefixWord ++ tailWord_6144880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6144880).length < 2 ^ (prefixWord ++ tailWord_6144880).sum := by decide
  have hdescent : baseEnd_6144880 < baseStart_6144880 := by decide
  rcases family_descends (prefixWord ++ tailWord_6144880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6144901 : List Nat := [1, 3, 1, 1, 3, 4, 1, 3, 2, 2, 2]
def baseStart_6144901 : Nat := 118140960795 + 6144901 * 2 ^ 59
def prefixEnd_6144901 : Nat := 4983230072969 + 3 ^ 40 * 6144901 * 2
def baseEnd_6144901 : Nat := 3155287787293767780277621

theorem tailTrace_6144901 : CollatzResearch.WordTrace tailWord_6144901 prefixEnd_6144901 3155287787293767780277621 := by
  unfold tailWord_6144901
  simp only [CollatzResearch.WordTrace]
  refine ⟨224122951911080617383690557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149415301274053744922460371 224122951911080617383690557)
  ·
    refine ⟨84046106966655231518883959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 224122951911080617383690557 84046106966655231518883959)
    ·
      refine ⟨126069160449982847278325939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84046106966655231518883959 126069160449982847278325939)
      ·
        refine ⟨189103740674974270917488909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126069160449982847278325939 189103740674974270917488909)
        ·
          refine ⟨70913902753115351594058341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 189103740674974270917488909 70913902753115351594058341)
          ·
            refine ⟨13296356766209128423885939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 70913902753115351594058341 13296356766209128423885939)
            ·
              refine ⟨19944535149313692635828909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13296356766209128423885939 19944535149313692635828909)
              ·
                refine ⟨7479200680992634738435841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19944535149313692635828909 7479200680992634738435841)
                ·
                  refine ⟨5609400510744476053826881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7479200680992634738435841 5609400510744476053826881)
                  ·
                    refine ⟨4207050383058357040370161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5609400510744476053826881 4207050383058357040370161)
                    ·
                      refine ⟨3155287787293767780277621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4207050383058357040370161 3155287787293767780277621)
                      ·
                        rfl

theorem cell23_6144901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 3, 2, 2, 2].length) (baseStart_6144901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6144901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6144901 prefixEnd_6144901 := by exact prefixLift 6144901
  have htrace : WordTrace (prefixWord ++ tailWord_6144901) baseStart_6144901 baseEnd_6144901 := by
    simpa [prefixWord, tailWord_6144901, baseEnd_6144901] using wordTrace_append hprefix tailTrace_6144901
  have hstable : (prefixWord ++ tailWord_6144901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6144901).length < 2 ^ (prefixWord ++ tailWord_6144901).sum := by decide
  have hdescent : baseEnd_6144901 < baseStart_6144901 := by decide
  rcases family_descends (prefixWord ++ tailWord_6144901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6144918 : List Nat := [5, 3, 1, 1, 1, 1, 1, 1, 3, 4, 2]
def baseStart_6144918 : Nat := 118140960795 + 6144918 * 2 ^ 59
def prefixEnd_6144918 : Nat := 4983230072969 + 3 ^ 40 * 6144918 * 2
def baseEnd_6144918 : Nat := 3155296516464894213765043

theorem tailTrace_6144918 : CollatzResearch.WordTrace tailWord_6144918 prefixEnd_6144918 3155296516464894213765043 := by
  unfold tailWord_6144918
  simp only [CollatzResearch.WordTrace]
  refine ⟨14007723247001189330441213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 149415714634679352858039605 14007723247001189330441213)
  ·
    refine ⟨5252896217625445998915455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14007723247001189330441213 5252896217625445998915455)
    ·
      refine ⟨7879344326438168998373183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5252896217625445998915455 7879344326438168998373183)
      ·
        refine ⟨11819016489657253497559775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7879344326438168998373183 11819016489657253497559775)
        ·
          refine ⟨17728524734485880246339663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11819016489657253497559775 17728524734485880246339663)
          ·
            refine ⟨26592787101728820369509495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17728524734485880246339663 26592787101728820369509495)
            ·
              refine ⟨39889180652593230554264243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26592787101728820369509495 39889180652593230554264243)
              ·
                refine ⟨59833770978889845831396365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39889180652593230554264243 59833770978889845831396365)
                ·
                  refine ⟨22437664117083692186773637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59833770978889845831396365 22437664117083692186773637)
                  ·
                    refine ⟨4207062021953192285020057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22437664117083692186773637 4207062021953192285020057)
                    ·
                      refine ⟨3155296516464894213765043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4207062021953192285020057 3155296516464894213765043)
                      ·
                        rfl

theorem cell23_6144918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 1, 3, 4, 2].length) (baseStart_6144918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6144918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6144918 prefixEnd_6144918 := by exact prefixLift 6144918
  have htrace : WordTrace (prefixWord ++ tailWord_6144918) baseStart_6144918 baseEnd_6144918 := by
    simpa [prefixWord, tailWord_6144918, baseEnd_6144918] using wordTrace_append hprefix tailTrace_6144918
  have hstable : (prefixWord ++ tailWord_6144918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6144918).length < 2 ^ (prefixWord ++ tailWord_6144918).sum := by decide
  have hdescent : baseEnd_6144918 < baseStart_6144918 := by decide
  rcases family_descends (prefixWord ++ tailWord_6144918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6144967 : List Nat := [1, 1, 4, 1, 1, 2, 3, 1, 5, 4]
def baseStart_6144967 : Nat := 118140960795 + 6144967 * 2 ^ 59
def prefixEnd_6144967 : Nat := 4983230072969 + 3 ^ 40 * 6144967 * 2
def baseEnd_6144967 : Nat := 1051773892338988174017439

theorem tailTrace_6144967 : CollatzResearch.WordTrace tailWord_6144967 prefixEnd_6144967 1051773892338988174017439 := by
  unfold tailWord_6144967
  simp only [CollatzResearch.WordTrace]
  refine ⟨224125359128841510655593155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149416906085894340437062103 224125359128841510655593155)
  ·
    refine ⟨336188038693262265983389733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224125359128841510655593155 336188038693262265983389733)
    ·
      refine ⟨63035257254986674871885575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 336188038693262265983389733 63035257254986674871885575)
      ·
        refine ⟨94552885882480012307828363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63035257254986674871885575 94552885882480012307828363)
        ·
          refine ⟨141829328823720018461742545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94552885882480012307828363 141829328823720018461742545)
          ·
            refine ⟨106371996617790013846306909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 141829328823720018461742545 106371996617790013846306909)
            ·
              refine ⟨39889498731671255192365091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 106371996617790013846306909 39889498731671255192365091)
              ·
                refine ⟨59834248097506882788547637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39889498731671255192365091 59834248097506882788547637)
                ·
                  refine ⟨5609460759141270261426341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 59834248097506882788547637 5609460759141270261426341)
                  ·
                    refine ⟨1051773892338988174017439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5609460759141270261426341 1051773892338988174017439)
                    ·
                      rfl

theorem cell23_6144967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 1, 5, 4].length) (baseStart_6144967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6144967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6144967 prefixEnd_6144967 := by exact prefixLift 6144967
  have htrace : WordTrace (prefixWord ++ tailWord_6144967) baseStart_6144967 baseEnd_6144967 := by
    simpa [prefixWord, tailWord_6144967, baseEnd_6144967] using wordTrace_append hprefix tailTrace_6144967
  have hstable : (prefixWord ++ tailWord_6144967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6144967).length < 2 ^ (prefixWord ++ tailWord_6144967).sum := by decide
  have hdescent : baseEnd_6144967 < baseStart_6144967 := by decide
  rcases family_descends (prefixWord ++ tailWord_6144967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6144974 : List Nat := [4, 1, 1, 1, 2, 3, 3, 1, 2, 1, 4]
def baseStart_6144974 : Nat := 118140960795 + 6144974 * 2 ^ 59
def prefixEnd_6144974 : Nat := 4983230072969 + 3 ^ 40 * 6144974 * 2
def baseEnd_6144974 : Nat := 3155325271381545994664785

theorem tailTrace_6144974 : CollatzResearch.WordTrace tailWord_6144974 prefixEnd_6144974 3155325271381545994664785 := by
  unfold tailWord_6144974
  simp only [CollatzResearch.WordTrace]
  refine ⟨28015701804977018856387247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149417076293210767234065317 28015701804977018856387247)
  ·
    refine ⟨42023552707465528284580871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28015701804977018856387247 42023552707465528284580871)
    ·
      refine ⟨63035329061198292426871307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42023552707465528284580871 63035329061198292426871307)
      ·
        refine ⟨94552993591797438640306961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63035329061198292426871307 94552993591797438640306961)
        ·
          refine ⟨70914745193848078980230221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94552993591797438640306961 70914745193848078980230221)
          ·
            refine ⟨26593029447693029617586333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70914745193848078980230221 26593029447693029617586333)
            ·
              refine ⟨9972386042884886106594875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26593029447693029617586333 9972386042884886106594875)
              ·
                refine ⟨14958579064327329159892313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9972386042884886106594875 14958579064327329159892313)
                ·
                  refine ⟨11218934298245496869919235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14958579064327329159892313 11218934298245496869919235)
                  ·
                    refine ⟨16828401447368245304878853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11218934298245496869919235 16828401447368245304878853)
                    ·
                      refine ⟨3155325271381545994664785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16828401447368245304878853 3155325271381545994664785)
                      ·
                        rfl

theorem cell23_6144974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 3, 1, 2, 1, 4].length) (baseStart_6144974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6144974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6144974 prefixEnd_6144974 := by exact prefixLift 6144974
  have htrace : WordTrace (prefixWord ++ tailWord_6144974) baseStart_6144974 baseEnd_6144974 := by
    simpa [prefixWord, tailWord_6144974, baseEnd_6144974] using wordTrace_append hprefix tailTrace_6144974
  have hstable : (prefixWord ++ tailWord_6144974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6144974).length < 2 ^ (prefixWord ++ tailWord_6144974).sum := by decide
  have hdescent : baseEnd_6144974 < baseStart_6144974 := by decide
  rcases family_descends (prefixWord ++ tailWord_6144974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6144977 : List Nat := [1, 2, 2, 1, 2, 1, 5, 1, 1, 4, 3]
def baseStart_6144977 : Nat := 118140960795 + 6144977 * 2 ^ 59
def prefixEnd_6144977 : Nat := 4983230072969 + 3 ^ 40 * 6144977 * 2
def baseEnd_6144977 : Nat := 3155326811823509482927271

theorem tailTrace_6144977 : CollatzResearch.WordTrace tailWord_6144977 prefixEnd_6144977 3155326811823509482927271 := by
  unfold tailWord_6144977
  simp only [CollatzResearch.WordTrace]
  refine ⟨224125723858805282363457185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149417149239203521575638123 224125723858805282363457185)
  ·
    refine ⟨168094292894103961772592889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224125723858805282363457185 168094292894103961772592889)
    ·
      refine ⟨126070719670577971329444667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168094292894103961772592889 126070719670577971329444667)
      ·
        refine ⟨189106079505866956994167001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126070719670577971329444667 189106079505866956994167001)
        ·
          refine ⟨141829559629400217745625251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189106079505866956994167001 141829559629400217745625251)
          ·
            refine ⟨212744339444100326618437877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141829559629400217745625251 212744339444100326618437877)
            ·
              refine ⟨19944781822884405620478551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 212744339444100326618437877 19944781822884405620478551)
              ·
                refine ⟨29917172734326608430717827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19944781822884405620478551 29917172734326608430717827)
                ·
                  refine ⟨44875759101489912646076741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29917172734326608430717827 44875759101489912646076741)
                  ·
                    refine ⟨8414204831529358621139389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44875759101489912646076741 8414204831529358621139389)
                    ·
                      refine ⟨3155326811823509482927271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8414204831529358621139389 3155326811823509482927271)
                      ·
                        rfl

theorem cell23_6144977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 1, 1, 4, 3].length) (baseStart_6144977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6144977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6144977 prefixEnd_6144977 := by exact prefixLift 6144977
  have htrace : WordTrace (prefixWord ++ tailWord_6144977) baseStart_6144977 baseEnd_6144977 := by
    simpa [prefixWord, tailWord_6144977, baseEnd_6144977] using wordTrace_append hprefix tailTrace_6144977
  have hstable : (prefixWord ++ tailWord_6144977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6144977).length < 2 ^ (prefixWord ++ tailWord_6144977).sum := by decide
  have hdescent : baseEnd_6144977 < baseStart_6144977 := by decide
  rcases family_descends (prefixWord ++ tailWord_6144977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6145058 : List Nat := [3, 3, 1, 1, 1, 5, 1, 1, 3, 1, 3]
def baseStart_6145058 : Nat := 118140960795 + 6145058 * 2 ^ 59
def prefixEnd_6145058 : Nat := 4983230072969 + 3 ^ 40 * 6145058 * 2
def baseEnd_6145058 : Nat := 3155368403756523666014399

theorem tailTrace_6145058 : CollatzResearch.WordTrace tailWord_6145058 prefixEnd_6145058 3155368403756523666014399 := by
  unfold tailWord_6145058
  simp only [CollatzResearch.WordTrace]
  refine ⟨56032169542877958299288957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149419118781007888798103885 56032169542877958299288957)
  ·
    refine ⟨21012063578579234362233359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56032169542877958299288957 21012063578579234362233359)
    ·
      refine ⟨31518095367868851543350039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21012063578579234362233359 31518095367868851543350039)
      ·
        refine ⟨47277143051803277315025059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31518095367868851543350039 47277143051803277315025059)
        ·
          refine ⟨70915714577704915972537589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47277143051803277315025059 70915714577704915972537589)
          ·
            refine ⟨6648348241659835872425399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 70915714577704915972537589 6648348241659835872425399)
            ·
              refine ⟨9972522362489753808638099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6648348241659835872425399 9972522362489753808638099)
              ·
                refine ⟨14958783543734630712957149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9972522362489753808638099 14958783543734630712957149)
                ·
                  refine ⟨5609543828900486517358931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14958783543734630712957149 5609543828900486517358931)
                  ·
                    refine ⟨8414315743350729776038397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5609543828900486517358931 8414315743350729776038397)
                    ·
                      refine ⟨3155368403756523666014399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8414315743350729776038397 3155368403756523666014399)
                      ·
                        rfl

theorem cell23_6145058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 1, 1, 3, 1, 3].length) (baseStart_6145058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6145058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6145058 prefixEnd_6145058 := by exact prefixLift 6145058
  have htrace : WordTrace (prefixWord ++ tailWord_6145058) baseStart_6145058 baseEnd_6145058 := by
    simpa [prefixWord, tailWord_6145058, baseEnd_6145058] using wordTrace_append hprefix tailTrace_6145058
  have hstable : (prefixWord ++ tailWord_6145058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6145058).length < 2 ^ (prefixWord ++ tailWord_6145058).sum := by decide
  have hdescent : baseEnd_6145058 < baseStart_6145058 := by decide
  rcases family_descends (prefixWord ++ tailWord_6145058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6145067 : List Nat := [1, 1, 1, 1, 2, 1, 5, 4, 1, 1, 5]
def baseStart_6145067 : Nat := 118140960795 + 6145067 * 2 ^ 59
def prefixEnd_6145067 : Nat := 4983230072969 + 3 ^ 40 * 6145067 * 2
def baseEnd_6145067 : Nat := 3155373025082414130801857

theorem tailTrace_6145067 : CollatzResearch.WordTrace tailWord_6145067 prefixEnd_6145067 3155373025082414130801857 := by
  unfold tailWord_6145067
  simp only [CollatzResearch.WordTrace]
  refine ⟨224129006428479227734233455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149419337618986151822822303 224129006428479227734233455)
  ·
    refine ⟨336193509642718841601350183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224129006428479227734233455 336193509642718841601350183)
    ·
      refine ⟨504290264464078262402025275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 336193509642718841601350183 504290264464078262402025275)
      ·
        refine ⟨756435396696117393603037913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 504290264464078262402025275 756435396696117393603037913)
        ·
          refine ⟨567326547522088045202278435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 756435396696117393603037913 567326547522088045202278435)
          ·
            refine ⟨850989821283132067803417653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 567326547522088045202278435 850989821283132067803417653)
            ·
              refine ⟨79780295745293631356570405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 850989821283132067803417653 79780295745293631356570405)
              ·
                refine ⟨14958805452242555879356951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 79780295745293631356570405 14958805452242555879356951)
                ·
                  refine ⟨22438208178363833819035427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14958805452242555879356951 22438208178363833819035427)
                  ·
                    refine ⟨33657312267545750728553141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22438208178363833819035427 33657312267545750728553141)
                    ·
                      refine ⟨3155373025082414130801857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33657312267545750728553141 3155373025082414130801857)
                      ·
                        rfl

theorem cell23_6145067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 4, 1, 1, 5].length) (baseStart_6145067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6145067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6145067 prefixEnd_6145067 := by exact prefixLift 6145067
  have htrace : WordTrace (prefixWord ++ tailWord_6145067) baseStart_6145067 baseEnd_6145067 := by
    simpa [prefixWord, tailWord_6145067, baseEnd_6145067] using wordTrace_append hprefix tailTrace_6145067
  have hstable : (prefixWord ++ tailWord_6145067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6145067).length < 2 ^ (prefixWord ++ tailWord_6145067).sum := by decide
  have hdescent : baseEnd_6145067 < baseStart_6145067 := by decide
  rcases family_descends (prefixWord ++ tailWord_6145067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6145078 : List Nat := [5, 1, 2, 1, 1, 4, 1, 2, 1, 5]
def baseStart_6145078 : Nat := 118140960795 + 6145078 * 2 ^ 59
def prefixEnd_6145078 : Nat := 4983230072969 + 3 ^ 40 * 6145078 * 2
def baseEnd_6145078 : Nat := 1051792891123204529254769

theorem tailTrace_6145078 : CollatzResearch.WordTrace tailWord_6145078 prefixEnd_6145078 1051792891123204529254769 := by
  unfold tailWord_6145078
  simp only [CollatzResearch.WordTrace]
  refine ⟨14008087976964961038305243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 149419605087626251075255925 14008087976964961038305243)
  ·
    refine ⟨21012131965447441557457865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14008087976964961038305243 21012131965447441557457865)
    ·
      refine ⟨15759098974085581168093399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21012131965447441557457865 15759098974085581168093399)
      ·
        refine ⟨23638648461128371752140099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15759098974085581168093399 23638648461128371752140099)
        ·
          refine ⟨35457972691692557628210149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23638648461128371752140099 35457972691692557628210149)
          ·
            refine ⟨6648369879692354555289403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35457972691692557628210149 6648369879692354555289403)
            ·
              refine ⟨9972554819538531832934105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6648369879692354555289403 9972554819538531832934105)
              ·
                refine ⟨7479416114653898874700579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9972554819538531832934105 7479416114653898874700579)
                ·
                  refine ⟨11219124171980848312050869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7479416114653898874700579 11219124171980848312050869)
                  ·
                    refine ⟨1051792891123204529254769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11219124171980848312050869 1051792891123204529254769)
                    ·
                      rfl

theorem cell23_6145078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 1, 2, 1, 5].length) (baseStart_6145078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6145078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6145078 prefixEnd_6145078 := by exact prefixLift 6145078
  have htrace : WordTrace (prefixWord ++ tailWord_6145078) baseStart_6145078 baseEnd_6145078 := by
    simpa [prefixWord, tailWord_6145078, baseEnd_6145078] using wordTrace_append hprefix tailTrace_6145078
  have hstable : (prefixWord ++ tailWord_6145078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6145078).length < 2 ^ (prefixWord ++ tailWord_6145078).sum := by decide
  have hdescent : baseEnd_6145078 < baseStart_6145078 := by decide
  rcases family_descends (prefixWord ++ tailWord_6145078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6145081 : List Nat := [1, 2, 1, 5, 2, 1, 3, 2, 1, 1, 4]
def baseStart_6145081 : Nat := 118140960795 + 6145081 * 2 ^ 59
def prefixEnd_6145081 : Nat := 4983230072969 + 3 ^ 40 * 6145081 * 2
def baseEnd_6145081 : Nat := 3155380213811577076026793

theorem tailTrace_6145081 : CollatzResearch.WordTrace tailWord_6145081 prefixEnd_6145081 3155380213811577076026793 := by
  unfold tailWord_6145081
  simp only [CollatzResearch.WordTrace]
  refine ⟨224129517050428508125243097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149419678033619005416828731 224129517050428508125243097)
  ·
    refine ⟨168097137787821381093932323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224129517050428508125243097 168097137787821381093932323)
    ·
      refine ⟨252145706681732071640898485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168097137787821381093932323 252145706681732071640898485)
      ·
        refine ⟨23638660001412381716334233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 252145706681732071640898485 23638660001412381716334233)
        ·
          refine ⟨17728995001059286287250675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23638660001412381716334233 17728995001059286287250675)
          ·
            refine ⟨26593492501588929430876013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17728995001059286287250675 26593492501588929430876013)
            ·
              refine ⟨9972559688095848536578505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26593492501588929430876013 9972559688095848536578505)
              ·
                refine ⟨7479419766071886402433879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9972559688095848536578505 7479419766071886402433879)
                ·
                  refine ⟨11219129649107829603650819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7479419766071886402433879 11219129649107829603650819)
                  ·
                    refine ⟨16828694473661744405476229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11219129649107829603650819 16828694473661744405476229)
                    ·
                      refine ⟨3155380213811577076026793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16828694473661744405476229 3155380213811577076026793)
                      ·
                        rfl

theorem cell23_6145081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 3, 2, 1, 1, 4].length) (baseStart_6145081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6145081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6145081 prefixEnd_6145081 := by exact prefixLift 6145081
  have htrace : WordTrace (prefixWord ++ tailWord_6145081) baseStart_6145081 baseEnd_6145081 := by
    simpa [prefixWord, tailWord_6145081, baseEnd_6145081] using wordTrace_append hprefix tailTrace_6145081
  have hstable : (prefixWord ++ tailWord_6145081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6145081).length < 2 ^ (prefixWord ++ tailWord_6145081).sum := by decide
  have hdescent : baseEnd_6145081 < baseStart_6145081 := by decide
  rcases family_descends (prefixWord ++ tailWord_6145081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6145101 : List Nat := [1, 6, 1, 1, 1, 2, 3, 1, 1, 1, 5]
def baseStart_6145101 : Nat := 118140960795 + 6145101 * 2 ^ 59
def prefixEnd_6145101 : Nat := 4983230072969 + 3 ^ 40 * 6145101 * 2
def baseEnd_6145101 : Nat := 3155390483424666997776701

theorem tailTrace_6145101 : CollatzResearch.WordTrace tailWord_6145101 prefixEnd_6145101 3155390483424666997776701 := by
  unfold tailWord_6145101
  simp only [CollatzResearch.WordTrace]
  refine ⟨224130246510356051540971157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149420164340237367693980771 224130246510356051540971157)
  ·
    refine ⟨10506105305172939915983023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 224130246510356051540971157 10506105305172939915983023)
    ·
      refine ⟨15759157957759409873974535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10506105305172939915983023 15759157957759409873974535)
      ·
        refine ⟨23638736936639114810961803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15759157957759409873974535 23638736936639114810961803)
        ·
          refine ⟨35458105404958672216442705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23638736936639114810961803 35458105404958672216442705)
          ·
            refine ⟨26593579053719004162332029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35458105404958672216442705 26593579053719004162332029)
            ·
              refine ⟨9972592145144626560874511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26593579053719004162332029 9972592145144626560874511)
              ·
                refine ⟨14958888217716939841311767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9972592145144626560874511 14958888217716939841311767)
                ·
                  refine ⟨22438332326575409761967651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14958888217716939841311767 22438332326575409761967651)
                  ·
                    refine ⟨33657498489863114642951477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22438332326575409761967651 33657498489863114642951477)
                    ·
                      refine ⟨3155390483424666997776701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33657498489863114642951477 3155390483424666997776701)
                      ·
                        rfl

theorem cell23_6145101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 3, 1, 1, 1, 5].length) (baseStart_6145101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6145101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6145101 prefixEnd_6145101 := by exact prefixLift 6145101
  have htrace : WordTrace (prefixWord ++ tailWord_6145101) baseStart_6145101 baseEnd_6145101 := by
    simpa [prefixWord, tailWord_6145101, baseEnd_6145101] using wordTrace_append hprefix tailTrace_6145101
  have hstable : (prefixWord ++ tailWord_6145101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6145101).length < 2 ^ (prefixWord ++ tailWord_6145101).sum := by decide
  have hdescent : baseEnd_6145101 < baseStart_6145101 := by decide
  rcases family_descends (prefixWord ++ tailWord_6145101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6145128 : List Nat := [2, 1, 4, 4, 1, 1, 2, 1, 1, 2, 4]
def baseStart_6145128 : Nat := 118140960795 + 6145128 * 2 ^ 59
def prefixEnd_6145128 : Nat := 4983230072969 + 3 ^ 40 * 6145128 * 2
def baseEnd_6145128 : Nat := 3155404347402338392139077

theorem tailTrace_6145128 : CollatzResearch.WordTrace tailWord_6145128 prefixEnd_6145128 3155404347402338392139077 := by
  unfold tailWord_6145128
  simp only [CollatzResearch.WordTrace]
  refine ⟨112065615640629117576102019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149420820854172156768136025 112065615640629117576102019)
  ·
    refine ⟨168098423460943676364153029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112065615640629117576102019 168098423460943676364153029)
    ·
      refine ⟨31518454398926939318278693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 168098423460943676364153029 31518454398926939318278693)
      ·
        refine ⟨5909710199798801122177255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31518454398926939318278693 5909710199798801122177255)
        ·
          refine ⟨8864565299698201683265883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5909710199798801122177255 8864565299698201683265883)
          ·
            refine ⟨13296847949547302524898825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8864565299698201683265883 13296847949547302524898825)
            ·
              refine ⟨9972635962160476893674119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13296847949547302524898825 9972635962160476893674119)
              ·
                refine ⟨14958953943240715340511179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9972635962160476893674119 14958953943240715340511179)
                ·
                  refine ⟨22438430914861073010766769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14958953943240715340511179 22438430914861073010766769)
                  ·
                    refine ⟨16828823186145804758075077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22438430914861073010766769 16828823186145804758075077)
                    ·
                      refine ⟨3155404347402338392139077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16828823186145804758075077 3155404347402338392139077)
                      ·
                        rfl

theorem cell23_6145128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_6145128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6145128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6145128 prefixEnd_6145128 := by exact prefixLift 6145128
  have htrace : WordTrace (prefixWord ++ tailWord_6145128) baseStart_6145128 baseEnd_6145128 := by
    simpa [prefixWord, tailWord_6145128, baseEnd_6145128] using wordTrace_append hprefix tailTrace_6145128
  have hstable : (prefixWord ++ tailWord_6145128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6145128).length < 2 ^ (prefixWord ++ tailWord_6145128).sum := by decide
  have hdescent : baseEnd_6145128 < baseStart_6145128 := by decide
  rcases family_descends (prefixWord ++ tailWord_6145128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6145182 : List Nat := [4, 3, 1, 1, 2, 2, 3, 1, 2, 1, 3]
def baseStart_6145182 : Nat := 118140960795 + 6145182 * 2 ^ 59
def prefixEnd_6145182 : Nat := 4983230072969 + 3 ^ 40 * 6145182 * 2
def baseEnd_6145182 : Nat := 3155432075357681180863829

theorem tailTrace_6145182 : CollatzResearch.WordTrace tailWord_6145182 prefixEnd_6145182 3155432075357681180863829 := by
  unfold tailWord_6145182
  simp only [CollatzResearch.WordTrace]
  refine ⟨28016650102882825296833725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149422133882041734916446533 28016650102882825296833725)
  ·
    refine ⟨10506243788581059486312647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28016650102882825296833725 10506243788581059486312647)
    ·
      refine ⟨15759365682871589229468971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10506243788581059486312647 15759365682871589229468971)
      ·
        refine ⟨23639048524307383844203457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15759365682871589229468971 23639048524307383844203457)
        ·
          refine ⟨17729286393230537883152593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23639048524307383844203457 17729286393230537883152593)
          ·
            refine ⟨13296964794922903412364445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17729286393230537883152593 13296964794922903412364445)
            ·
              refine ⟨4986361798096088779636667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13296964794922903412364445 4986361798096088779636667)
              ·
                refine ⟨7479542697144133169455001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4986361798096088779636667 7479542697144133169455001)
                ·
                  refine ⟨5609657022858099877091251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7479542697144133169455001 5609657022858099877091251)
                  ·
                    refine ⟨8414485534287149815636877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5609657022858099877091251 8414485534287149815636877)
                    ·
                      refine ⟨3155432075357681180863829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8414485534287149815636877 3155432075357681180863829)
                      ·
                        rfl

theorem cell23_6145182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 3, 1, 2, 1, 3].length) (baseStart_6145182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6145182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6145182 prefixEnd_6145182 := by exact prefixLift 6145182
  have htrace : WordTrace (prefixWord ++ tailWord_6145182) baseStart_6145182 baseEnd_6145182 := by
    simpa [prefixWord, tailWord_6145182, baseEnd_6145182] using wordTrace_append hprefix tailTrace_6145182
  have hstable : (prefixWord ++ tailWord_6145182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6145182).length < 2 ^ (prefixWord ++ tailWord_6145182).sum := by decide
  have hdescent : baseEnd_6145182 < baseStart_6145182 := by decide
  rcases family_descends (prefixWord ++ tailWord_6145182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6145184 : List Nat := [2, 1, 1, 4, 2, 1, 1, 3, 2, 2, 4]
def baseStart_6145184 : Nat := 118140960795 + 6145184 * 2 ^ 59
def prefixEnd_6145184 : Nat := 4983230072969 + 3 ^ 40 * 6145184 * 2
def baseEnd_6145184 : Nat := 3155433102318990173038819

theorem tailTrace_6145184 : CollatzResearch.WordTrace tailWord_6145184 prefixEnd_6145184 3155433102318990173038819 := by
  unfold tailWord_6145184
  simp only [CollatzResearch.WordTrace]
  refine ⟨112066636884527678358121303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149422182512703571144161737 112066636884527678358121303)
  ·
    refine ⟨168099955326791517537181955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112066636884527678358121303 168099955326791517537181955)
    ·
      refine ⟨252149932990187276305772933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 168099955326791517537181955 252149932990187276305772933)
      ·
        refine ⟨47278112435660114307332425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 252149932990187276305772933 47278112435660114307332425)
        ·
          refine ⟨35458584326745085730499319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47278112435660114307332425 35458584326745085730499319)
          ·
            refine ⟨53187876490117628595748979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35458584326745085730499319 53187876490117628595748979)
            ·
              refine ⟨79781814735176442893623469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53187876490117628595748979 79781814735176442893623469)
              ·
                refine ⟨29918180525691166085108801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79781814735176442893623469 29918180525691166085108801)
                ·
                  refine ⟨22438635394268374563831601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29918180525691166085108801 22438635394268374563831601)
                  ·
                    refine ⟨16828976545701280922873701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22438635394268374563831601 16828976545701280922873701)
                    ·
                      refine ⟨3155433102318990173038819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16828976545701280922873701 3155433102318990173038819)
                      ·
                        rfl

theorem cell23_6145184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 3, 2, 2, 4].length) (baseStart_6145184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6145184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6145184 prefixEnd_6145184 := by exact prefixLift 6145184
  have htrace : WordTrace (prefixWord ++ tailWord_6145184) baseStart_6145184 baseEnd_6145184 := by
    simpa [prefixWord, tailWord_6145184, baseEnd_6145184] using wordTrace_append hprefix tailTrace_6145184
  have hstable : (prefixWord ++ tailWord_6145184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6145184).length < 2 ^ (prefixWord ++ tailWord_6145184).sum := by decide
  have hdescent : baseEnd_6145184 < baseStart_6145184 := by decide
  rcases family_descends (prefixWord ++ tailWord_6145184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6145187 : List Nat := [1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 9]
def baseStart_6145187 : Nat := 118140960795 + 6145187 * 2 ^ 59
def prefixEnd_6145187 : Nat := 4983230072969 + 3 ^ 40 * 6145187 * 2
def baseEnd_6145187 : Nat := 3155434642760953661301305

theorem tailTrace_6145187 : CollatzResearch.WordTrace tailWord_6145187 prefixEnd_6145187 3155434642760953661301305 := by
  unfold tailWord_6145187
  simp only [CollatzResearch.WordTrace]
  refine ⟨224133383188044488228601815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149422255458696325485734543 224133383188044488228601815)
  ·
    refine ⟨336200074782066732342902723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 224133383188044488228601815 336200074782066732342902723)
    ·
      refine ⟨504300112173100098514354085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 336200074782066732342902723 504300112173100098514354085)
      ·
        refine ⟨94556271032456268471441391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 504300112173100098514354085 94556271032456268471441391)
        ·
          refine ⟨141834406548684402707162087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94556271032456268471441391 141834406548684402707162087)
          ·
            refine ⟨212751609823026604060743131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141834406548684402707162087 212751609823026604060743131)
            ·
              refine ⟨319127414734539906091114697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 212751609823026604060743131 319127414734539906091114697)
              ·
                refine ⟨239345561050904929568336023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 319127414734539906091114697 239345561050904929568336023)
                ·
                  refine ⟨359018341576357394352504035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 239345561050904929568336023 359018341576357394352504035)
                  ·
                    refine ⟨538527512364536091528756053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 359018341576357394352504035 538527512364536091528756053)
                    ·
                      refine ⟨3155434642760953661301305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 538527512364536091528756053 3155434642760953661301305)
                      ·
                        rfl

theorem cell23_6145187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 9].length) (baseStart_6145187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6145187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6145187 prefixEnd_6145187 := by exact prefixLift 6145187
  have htrace : WordTrace (prefixWord ++ tailWord_6145187) baseStart_6145187 baseEnd_6145187 := by
    simpa [prefixWord, tailWord_6145187, baseEnd_6145187] using wordTrace_append hprefix tailTrace_6145187
  have hstable : (prefixWord ++ tailWord_6145187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6145187).length < 2 ^ (prefixWord ++ tailWord_6145187).sum := by decide
  have hdescent : baseEnd_6145187 < baseStart_6145187 := by decide
  rcases family_descends (prefixWord ++ tailWord_6145187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6145188 : List Nat := [2, 3, 1, 2, 3, 1, 3, 1, 1, 4, 2]
def baseStart_6145188 : Nat := 118140960795 + 6145188 * 2 ^ 59
def prefixEnd_6145188 : Nat := 4983230072969 + 3 ^ 40 * 6145188 * 2
def baseEnd_6145188 : Nat := 3155435156241608157388801

theorem tailTrace_6145188 : CollatzResearch.WordTrace tailWord_6145188 prefixEnd_6145188 3155435156241608157388801 := by
  unfold tailWord_6145188
  simp only [CollatzResearch.WordTrace]
  refine ⟨112066709830520432699694109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149422279774027243599592145 112066709830520432699694109)
  ·
    refine ⟨42025016186445162262385291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112066709830520432699694109 42025016186445162262385291)
    ·
      refine ⟨63037524279667743393577937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42025016186445162262385291 63037524279667743393577937)
      ·
        refine ⟨47278143209750807545183453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63037524279667743393577937 47278143209750807545183453)
        ·
          refine ⟨17729303703656552829443795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47278143209750807545183453 17729303703656552829443795)
          ·
            refine ⟨26593955555484829244165693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17729303703656552829443795 26593955555484829244165693)
            ·
              refine ⟨9972733333306810966562135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26593955555484829244165693 9972733333306810966562135)
              ·
                refine ⟨14959099999960216449843203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9972733333306810966562135 14959099999960216449843203)
                ·
                  refine ⟨22438649999940324674764805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14959099999960216449843203 22438649999940324674764805)
                  ·
                    refine ⟨4207246874988810876518401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22438649999940324674764805 4207246874988810876518401)
                    ·
                      refine ⟨3155435156241608157388801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4207246874988810876518401 3155435156241608157388801)
                      ·
                        rfl

theorem cell23_6145188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 3, 1, 1, 4, 2].length) (baseStart_6145188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6145188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6145188 prefixEnd_6145188 := by exact prefixLift 6145188
  have htrace : WordTrace (prefixWord ++ tailWord_6145188) baseStart_6145188 baseEnd_6145188 := by
    simpa [prefixWord, tailWord_6145188, baseEnd_6145188] using wordTrace_append hprefix tailTrace_6145188
  have hstable : (prefixWord ++ tailWord_6145188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6145188).length < 2 ^ (prefixWord ++ tailWord_6145188).sum := by decide
  have hdescent : baseEnd_6145188 < baseStart_6145188 := by decide
  rcases family_descends (prefixWord ++ tailWord_6145188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6145224 : List Nat := [2, 1, 3, 1, 2, 1, 3, 1, 4, 5]
def baseStart_6145224 : Nat := 118140960795 + 6145224 * 2 ^ 59
def prefixEnd_6145224 : Nat := 4983230072969 + 3 ^ 40 * 6145224 * 2
def baseEnd_6145224 : Nat := 1051817880515056672179545

theorem tailTrace_6145224 : CollatzResearch.WordTrace tailWord_6145224 prefixEnd_6145224 1051817880515056672179545 := by
  unfold tailWord_6145224
  simp only [CollatzResearch.WordTrace]
  refine ⟨112067366344455221773849363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149423155125940295698465817 112067366344455221773849363)
  ·
    refine ⟨168101049516682832660774045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112067366344455221773849363 168101049516682832660774045)
    ·
      refine ⟨63037893568756062247790267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 168101049516682832660774045 63037893568756062247790267)
      ·
        refine ⟨94556840353134093371685401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63037893568756062247790267 94556840353134093371685401)
        ·
          refine ⟨70917630264850570028764051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 94556840353134093371685401 70917630264850570028764051)
          ·
            refine ⟨106376445397275855043146077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70917630264850570028764051 106376445397275855043146077)
            ·
              refine ⟨39891167023978445641179779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 106376445397275855043146077 39891167023978445641179779)
              ·
                refine ⟨59836750535967668461769669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39891167023978445641179779 59836750535967668461769669)
                ·
                  refine ⟨11219390725493937836581813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59836750535967668461769669 11219390725493937836581813)
                  ·
                    refine ⟨1051817880515056672179545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11219390725493937836581813 1051817880515056672179545)
                    ·
                      rfl

theorem cell23_6145224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 1, 4, 5].length) (baseStart_6145224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6145224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6145224 prefixEnd_6145224 := by exact prefixLift 6145224
  have htrace : WordTrace (prefixWord ++ tailWord_6145224) baseStart_6145224 baseEnd_6145224 := by
    simpa [prefixWord, tailWord_6145224, baseEnd_6145224] using wordTrace_append hprefix tailTrace_6145224
  have hstable : (prefixWord ++ tailWord_6145224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6145224).length < 2 ^ (prefixWord ++ tailWord_6145224).sum := by decide
  have hdescent : baseEnd_6145224 < baseStart_6145224 := by decide
  rcases family_descends (prefixWord ++ tailWord_6145224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6145274 : List Nat := [3, 1, 1, 1, 1, 4, 2, 1, 2, 1, 6]
def baseStart_6145274 : Nat := 118140960795 + 6145274 * 2 ^ 59
def prefixEnd_6145274 : Nat := 4983230072969 + 3 ^ 40 * 6145274 * 2
def baseEnd_6145274 : Nat := 3155479315577894820913405

theorem tailTrace_6145274 : CollatzResearch.WordTrace tailWord_6145274 prefixEnd_6145274 3155479315577894820913405 := by
  unfold tailWord_6145274
  simp only [CollatzResearch.WordTrace]
  refine ⟨56034139084682325521754719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149424370892486201391345917 56034139084682325521754719)
  ·
    refine ⟨84051208627023488282632079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56034139084682325521754719 84051208627023488282632079)
    ·
      refine ⟨126076812940535232423948119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84051208627023488282632079 126076812940535232423948119)
      ·
        refine ⟨189115219410802848635922179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126076812940535232423948119 189115219410802848635922179)
        ·
          refine ⟨283672829116204272953883269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189115219410802848635922179 283672829116204272953883269)
          ·
            refine ⟨53188655459288301178853113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 283672829116204272953883269 53188655459288301178853113)
            ·
              refine ⟨39891491594466225884139835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53188655459288301178853113 39891491594466225884139835)
              ·
                refine ⟨59837237391699338826209753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39891491594466225884139835 59837237391699338826209753)
                ·
                  refine ⟨44877928043774504119657315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 59837237391699338826209753 44877928043774504119657315)
                  ·
                    refine ⟨67316892065661756179485973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44877928043774504119657315 67316892065661756179485973)
                    ·
                      refine ⟨3155479315577894820913405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 67316892065661756179485973 3155479315577894820913405)
                      ·
                        rfl

theorem cell23_6145274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 1, 2, 1, 6].length) (baseStart_6145274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6145274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6145274 prefixEnd_6145274 := by exact prefixLift 6145274
  have htrace : WordTrace (prefixWord ++ tailWord_6145274) baseStart_6145274 baseEnd_6145274 := by
    simpa [prefixWord, tailWord_6145274, baseEnd_6145274] using wordTrace_append hprefix tailTrace_6145274
  have hstable : (prefixWord ++ tailWord_6145274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6145274).length < 2 ^ (prefixWord ++ tailWord_6145274).sum := by decide
  have hdescent : baseEnd_6145274 < baseStart_6145274 := by decide
  rcases family_descends (prefixWord ++ tailWord_6145274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6145278 : List Nat := [4, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4]
def baseStart_6145278 : Nat := 118140960795 + 6145278 * 2 ^ 59
def prefixEnd_6145278 : Nat := 4983230072969 + 3 ^ 40 * 6145278 * 2
def baseEnd_6145278 : Nat := 3155481369500512805263387

theorem tailTrace_6145278 : CollatzResearch.WordTrace tailWord_6145278 prefixEnd_6145278 3155481369500512805263387 := by
  unfold tailWord_6145278
  simp only [CollatzResearch.WordTrace]
  refine ⟨28017087778839351346270561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 149424468153809873846776325 28017087778839351346270561)
  ·
    refine ⟨21012815834129513509702921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28017087778839351346270561 21012815834129513509702921)
    ·
      refine ⟨15759611875597135132277191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21012815834129513509702921 15759611875597135132277191)
      ·
        refine ⟨23639417813395702698415787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15759611875597135132277191 23639417813395702698415787)
        ·
          refine ⟨35459126720093554047623681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23639417813395702698415787 35459126720093554047623681)
          ·
            refine ⟨26594345040070165535717761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35459126720093554047623681 26594345040070165535717761)
            ·
              refine ⟨19945758780052624151788321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26594345040070165535717761 19945758780052624151788321)
              ·
                refine ⟨14959319085039468113841241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19945758780052624151788321 14959319085039468113841241)
                ·
                  refine ⟨11219489313779601085380931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14959319085039468113841241 11219489313779601085380931)
                  ·
                    refine ⟨16829233970669401628071397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11219489313779601085380931 16829233970669401628071397)
                    ·
                      refine ⟨3155481369500512805263387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16829233970669401628071397 3155481369500512805263387)
                      ·
                        rfl

theorem cell23_6145278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_6145278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6145278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6145278 prefixEnd_6145278 := by exact prefixLift 6145278
  have htrace : WordTrace (prefixWord ++ tailWord_6145278) baseStart_6145278 baseEnd_6145278 := by
    simpa [prefixWord, tailWord_6145278, baseEnd_6145278] using wordTrace_append hprefix tailTrace_6145278
  have hstable : (prefixWord ++ tailWord_6145278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6145278).length < 2 ^ (prefixWord ++ tailWord_6145278).sum := by decide
  have hdescent : baseEnd_6145278 < baseStart_6145278 := by decide
  rcases family_descends (prefixWord ++ tailWord_6145278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6145322 : List Nat := [3, 1, 4, 2, 1, 2, 2, 3, 1, 4]
def baseStart_6145322 : Nat := 118140960795 + 6145322 * 2 ^ 59
def prefixEnd_6145322 : Nat := 4983230072969 + 3 ^ 40 * 6145322 * 2
def baseEnd_6145322 : Nat := 1051834654216436877704395

theorem tailTrace_6145322 : CollatzResearch.WordTrace tailWord_6145322 prefixEnd_6145322 1051834654216436877704395 := by
  unfold tailWord_6145322
  simp only [CollatzResearch.WordTrace]
  refine ⟨56034576760638851571191555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149425538028370270856510813 56034576760638851571191555)
  ·
    refine ⟨84051865140958277356787333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56034576760638851571191555 84051865140958277356787333)
    ·
      refine ⟨15759724713929677004397625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84051865140958277356787333 15759724713929677004397625)
      ·
        refine ⟨11819793535447257753298219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15759724713929677004397625 11819793535447257753298219)
        ·
          refine ⟨17729690303170886629947329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11819793535447257753298219 17729690303170886629947329)
          ·
            refine ⟨13297267727378164972460497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17729690303170886629947329 13297267727378164972460497)
            ·
              refine ⟨9972950795533623729345373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13297267727378164972460497 9972950795533623729345373)
              ·
                refine ⟨3739856548325108898504515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9972950795533623729345373 3739856548325108898504515)
                ·
                  refine ⟨5609784822487663347756773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3739856548325108898504515 5609784822487663347756773)
                  ·
                    refine ⟨1051834654216436877704395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5609784822487663347756773 1051834654216436877704395)
                    ·
                      rfl

theorem cell23_6145322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 2, 3, 1, 4].length) (baseStart_6145322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6145322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6145322 prefixEnd_6145322 := by exact prefixLift 6145322
  have htrace : WordTrace (prefixWord ++ tailWord_6145322) baseStart_6145322 baseEnd_6145322 := by
    simpa [prefixWord, tailWord_6145322, baseEnd_6145322] using wordTrace_append hprefix tailTrace_6145322
  have hstable : (prefixWord ++ tailWord_6145322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6145322).length < 2 ^ (prefixWord ++ tailWord_6145322).sum := by decide
  have hdescent : baseEnd_6145322 < baseStart_6145322 := by decide
  rcases family_descends (prefixWord ++ tailWord_6145322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6145324 : List Nat := [2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 5]
def baseStart_6145324 : Nat := 118140960795 + 6145324 * 2 ^ 59
def prefixEnd_6145324 : Nat := 4983230072969 + 3 ^ 40 * 6145324 * 2
def baseEnd_6145324 : Nat := 3155504989610619625288175

theorem tailTrace_6145324 : CollatzResearch.WordTrace tailWord_6145324 prefixEnd_6145324 3155504989610619625288175 := by
  unfold tailWord_6145324
  simp only [CollatzResearch.WordTrace]
  refine ⟨112069189994274080313169513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149425586659032107084226017 112069189994274080313169513)
  ·
    refine ⟨84051892495705560234877135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112069189994274080313169513 84051892495705560234877135)
    ·
      refine ⟨126077838743558340352315703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84051892495705560234877135 126077838743558340352315703)
      ·
        refine ⟨189116758115337510528473555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126077838743558340352315703 189116758115337510528473555)
        ·
          refine ⟨283675137173006265792710333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189116758115337510528473555 283675137173006265792710333)
          ·
            refine ⟨106378176439877349672266375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 283675137173006265792710333 106378176439877349672266375)
            ·
              refine ⟨159567264659816024508399563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106378176439877349672266375 159567264659816024508399563)
              ·
                refine ⟨239350896989724036762599345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 159567264659816024508399563 239350896989724036762599345)
                ·
                  refine ⟨179513172742293027571949509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 239350896989724036762599345 179513172742293027571949509)
                  ·
                    refine ⟨33658719889179942669740533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 179513172742293027571949509 33658719889179942669740533)
                    ·
                      refine ⟨3155504989610619625288175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33658719889179942669740533 3155504989610619625288175)
                      ·
                        rfl

theorem cell23_6145324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 5].length) (baseStart_6145324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6145324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6145324 prefixEnd_6145324 := by exact prefixLift 6145324
  have htrace : WordTrace (prefixWord ++ tailWord_6145324) baseStart_6145324 baseEnd_6145324 := by
    simpa [prefixWord, tailWord_6145324, baseEnd_6145324] using wordTrace_append hprefix tailTrace_6145324
  have hstable : (prefixWord ++ tailWord_6145324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6145324).length < 2 ^ (prefixWord ++ tailWord_6145324).sum := by decide
  have hdescent : baseEnd_6145324 < baseStart_6145324 := by decide
  rcases family_descends (prefixWord ++ tailWord_6145324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6145338 : List Nat := [3, 1, 1, 1, 4, 1, 2, 1, 4, 3, 2]
def baseStart_6145338 : Nat := 118140960795 + 6145338 * 2 ^ 59
def prefixEnd_6145338 : Nat := 4983230072969 + 3 ^ 40 * 6145338 * 2
def baseEnd_6145338 : Nat := 3155512178339782570513111

theorem tailTrace_6145338 : CollatzResearch.WordTrace tailWord_6145338 prefixEnd_6145338 3155512178339782570513111 := by
  unfold tailWord_6145338
  simp only [CollatzResearch.WordTrace]
  refine ⟨56034722652624360254337167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149425927073664960678232445 56034722652624360254337167)
  ·
    refine ⟨84052083978936540381505751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56034722652624360254337167 84052083978936540381505751)
    ·
      refine ⟨126078125968404810572258627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84052083978936540381505751 126078125968404810572258627)
      ·
        refine ⟨189117188952607215858387941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126078125968404810572258627 189117188952607215858387941)
        ·
          refine ⟨35459472928613852973447739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 189117188952607215858387941 35459472928613852973447739)
          ·
            refine ⟨53189209392920779460171609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35459472928613852973447739 53189209392920779460171609)
            ·
              refine ⟨39891907044690584595128707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53189209392920779460171609 39891907044690584595128707)
              ·
                refine ⟨59837860567035876892693061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39891907044690584595128707 59837860567035876892693061)
                ·
                  refine ⟨11219598856319226917379949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 59837860567035876892693061 11219598856319226917379949)
                  ·
                    refine ⟨4207349571119710094017481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11219598856319226917379949 4207349571119710094017481)
                    ·
                      refine ⟨3155512178339782570513111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4207349571119710094017481 3155512178339782570513111)
                      ·
                        rfl

theorem cell23_6145338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 1, 4, 3, 2].length) (baseStart_6145338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6145338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6145338 prefixEnd_6145338 := by exact prefixLift 6145338
  have htrace : WordTrace (prefixWord ++ tailWord_6145338) baseStart_6145338 baseEnd_6145338 := by
    simpa [prefixWord, tailWord_6145338, baseEnd_6145338] using wordTrace_append hprefix tailTrace_6145338
  have hstable : (prefixWord ++ tailWord_6145338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6145338).length < 2 ^ (prefixWord ++ tailWord_6145338).sum := by decide
  have hdescent : baseEnd_6145338 < baseStart_6145338 := by decide
  rcases family_descends (prefixWord ++ tailWord_6145338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6145345 : List Nat := [1, 2, 5, 2, 1, 1, 1, 3, 3, 1, 3]
def baseStart_6145345 : Nat := 118140960795 + 6145345 * 2 ^ 59
def prefixEnd_6145345 : Nat := 4983230072969 + 3 ^ 40 * 6145345 * 2
def baseEnd_6145345 : Nat := 3155515772704364043125579

theorem tailTrace_6145345 : CollatzResearch.WordTrace tailWord_6145345 prefixEnd_6145345 3155515772704364043125579 := by
  unfold tailWord_6145345
  simp only [CollatzResearch.WordTrace]
  refine ⟨224139145921472081212853489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149426097280981387475235659 224139145921472081212853489)
  ·
    refine ⟨168104359441104060909640117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 224139145921472081212853489 168104359441104060909640117)
    ·
      refine ⟨15759783697603505710278761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 168104359441104060909640117 15759783697603505710278761)
      ·
        refine ⟨11819837773202629282709071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15759783697603505710278761 11819837773202629282709071)
        ·
          refine ⟨17729756659803943924063607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11819837773202629282709071 17729756659803943924063607)
          ·
            refine ⟨26594634989705915886095411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17729756659803943924063607 26594634989705915886095411)
            ·
              refine ⟨39891952484558873829143117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26594634989705915886095411 39891952484558873829143117)
              ·
                refine ⟨14959482181709577685928669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39891952484558873829143117 14959482181709577685928669)
                ·
                  refine ⟨5609805818141091632223251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14959482181709577685928669 5609805818141091632223251)
                  ·
                    refine ⟨8414708727211637448334877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5609805818141091632223251 8414708727211637448334877)
                    ·
                      refine ⟨3155515772704364043125579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8414708727211637448334877 3155515772704364043125579)
                      ·
                        rfl

theorem cell23_6145345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_6145345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6145345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6145345 prefixEnd_6145345 := by exact prefixLift 6145345
  have htrace : WordTrace (prefixWord ++ tailWord_6145345) baseStart_6145345 baseEnd_6145345 := by
    simpa [prefixWord, tailWord_6145345, baseEnd_6145345] using wordTrace_append hprefix tailTrace_6145345
  have hstable : (prefixWord ++ tailWord_6145345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6145345).length < 2 ^ (prefixWord ++ tailWord_6145345).sum := by decide
  have hdescent : baseEnd_6145345 < baseStart_6145345 := by decide
  rcases family_descends (prefixWord ++ tailWord_6145345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6145368 : List Nat := [2, 1, 2, 2, 1, 1, 6, 2, 1, 1, 4]
def baseStart_6145368 : Nat := 118140960795 + 6145368 * 2 ^ 59
def prefixEnd_6145368 : Nat := 4983230072969 + 3 ^ 40 * 6145368 * 2
def baseEnd_6145368 : Nat := 3155527582759417453137973

theorem tailTrace_6145368 : CollatzResearch.WordTrace tailWord_6145368 prefixEnd_6145368 3155527582759417453137973 := by
  unfold tailWord_6145368
  simp only [CollatzResearch.WordTrace]
  refine ⟨112069992400194378070470379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149426656533592504093960505 112069992400194378070470379)
  ·
    refine ⟨168104988600291567105705569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 112069992400194378070470379 168104988600291567105705569)
    ·
      refine ⟨126078741450218675329279177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 168104988600291567105705569 126078741450218675329279177)
      ·
        refine ⟨94559056087664006496959383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126078741450218675329279177 94559056087664006496959383)
        ·
          refine ⟨141838584131496009745439075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94559056087664006496959383 141838584131496009745439075)
          ·
            refine ⟨212757876197244014618158613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141838584131496009745439075 212757876197244014618158613)
            ·
              refine ⟨9973025446745813185226185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 212757876197244014618158613 9973025446745813185226185)
              ·
                refine ⟨7479769085059359888919639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9973025446745813185226185 7479769085059359888919639)
                ·
                  refine ⟨11219653627589039833379459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7479769085059359888919639 11219653627589039833379459)
                  ·
                    refine ⟨16829480441383559750069189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11219653627589039833379459 16829480441383559750069189)
                    ·
                      refine ⟨3155527582759417453137973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16829480441383559750069189 3155527582759417453137973)
                      ·
                        rfl

theorem cell23_6145368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 6, 2, 1, 1, 4].length) (baseStart_6145368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6145368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6145368 prefixEnd_6145368 := by exact prefixLift 6145368
  have htrace : WordTrace (prefixWord ++ tailWord_6145368) baseStart_6145368 baseEnd_6145368 := by
    simpa [prefixWord, tailWord_6145368, baseEnd_6145368] using wordTrace_append hprefix tailTrace_6145368
  have hstable : (prefixWord ++ tailWord_6145368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6145368).length < 2 ^ (prefixWord ++ tailWord_6145368).sum := by decide
  have hdescent : baseEnd_6145368 < baseStart_6145368 := by decide
  rcases family_descends (prefixWord ++ tailWord_6145368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6145373 : List Nat := [1, 4, 5, 1, 2, 1, 1, 3, 1, 4]
def baseStart_6145373 : Nat := 118140960795 + 6145373 * 2 ^ 59
def prefixEnd_6145373 : Nat := 4983230072969 + 3 ^ 40 * 6145373 * 2
def baseEnd_6145373 : Nat := 1051843383387563311191817

theorem tailTrace_6145373 : CollatzResearch.WordTrace tailWord_6145373 prefixEnd_6145373 1051843383387563311191817 := by
  unfold tailWord_6145373
  simp only [CollatzResearch.WordTrace]
  refine ⟨224140167165370641994872773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149426778110247094663248515 224140167165370641994872773)
  ·
    refine ⟨42026281343506995374038645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 224140167165370641994872773 42026281343506995374038645)
    ·
      refine ⟨3939963875953780816316123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 42026281343506995374038645 3939963875953780816316123)
      ·
        refine ⟨5909945813930671224474185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3939963875953780816316123 5909945813930671224474185)
        ·
          refine ⟨4432459360448003418355639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5909945813930671224474185 4432459360448003418355639)
          ·
            refine ⟨6648689040672005127533459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4432459360448003418355639 6648689040672005127533459)
            ·
              refine ⟨9973033561008007691300189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6648689040672005127533459 9973033561008007691300189)
              ·
                refine ⟨3739887585378002884237571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9973033561008007691300189 3739887585378002884237571)
                ·
                  refine ⟨5609831378067004326356357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3739887585378002884237571 5609831378067004326356357)
                  ·
                    refine ⟨1051843383387563311191817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5609831378067004326356357 1051843383387563311191817)
                    ·
                      rfl

theorem cell23_6145373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_6145373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6145373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6145373 prefixEnd_6145373 := by exact prefixLift 6145373
  have htrace : WordTrace (prefixWord ++ tailWord_6145373) baseStart_6145373 baseEnd_6145373 := by
    simpa [prefixWord, tailWord_6145373, baseEnd_6145373] using wordTrace_append hprefix tailTrace_6145373
  have hstable : (prefixWord ++ tailWord_6145373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6145373).length < 2 ^ (prefixWord ++ tailWord_6145373).sum := by decide
  have hdescent : baseEnd_6145373 < baseStart_6145373 := by decide
  rcases family_descends (prefixWord ++ tailWord_6145373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6145378 : List Nat := [3, 3, 2, 1, 1, 1, 1, 1, 6, 4]
def baseStart_6145378 : Nat := 118140960795 + 6145378 * 2 ^ 59
def prefixEnd_6145378 : Nat := 4983230072969 + 3 ^ 40 * 6145378 * 2
def baseEnd_6145378 : Nat := 1051844239188654138004309

theorem tailTrace_6145378 : CollatzResearch.WordTrace tailWord_6145378 prefixEnd_6145378 1051844239188654138004309 := by
  unfold tailWord_6145378
  simp only [CollatzResearch.WordTrace]
  refine ⟨56035087382588131962201197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 149426899686901685232536525 56035087382588131962201197)
  ·
    refine ⟨21013157768470549485825449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56035087382588131962201197 21013157768470549485825449)
    ·
      refine ⟨15759868326352912114369087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21013157768470549485825449 15759868326352912114369087)
      ·
        refine ⟨23639802489529368171553631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15759868326352912114369087 23639802489529368171553631)
        ·
          refine ⟨35459703734294052257330447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23639802489529368171553631 35459703734294052257330447)
          ·
            refine ⟨53189555601441078385995671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35459703734294052257330447 53189555601441078385995671)
            ·
              refine ⟨79784333402161617578993507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53189555601441078385995671 79784333402161617578993507)
              ·
                refine ⟨119676500103242426368490261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79784333402161617578993507 119676500103242426368490261)
                ·
                  refine ⟨5609835942339488736022981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 119676500103242426368490261 5609835942339488736022981)
                  ·
                    refine ⟨1051844239188654138004309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5609835942339488736022981 1051844239188654138004309)
                    ·
                      rfl

theorem cell23_6145378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 6, 4].length) (baseStart_6145378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6145378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6145378 prefixEnd_6145378 := by exact prefixLift 6145378
  have htrace : WordTrace (prefixWord ++ tailWord_6145378) baseStart_6145378 baseEnd_6145378 := by
    simpa [prefixWord, tailWord_6145378, baseEnd_6145378] using wordTrace_append hprefix tailTrace_6145378
  have hstable : (prefixWord ++ tailWord_6145378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6145378).length < 2 ^ (prefixWord ++ tailWord_6145378).sum := by decide
  have hdescent : baseEnd_6145378 < baseStart_6145378 := by decide
  rcases family_descends (prefixWord ++ tailWord_6145378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6145381 : List Nat := [1, 3, 1, 3, 1, 2, 2, 1, 3, 2, 4]
def baseStart_6145381 : Nat := 118140960795 + 6145381 * 2 ^ 59
def prefixEnd_6145381 : Nat := 4983230072969 + 3 ^ 40 * 6145381 * 2
def baseEnd_6145381 : Nat := 3155534258007925902275413

theorem tailTrace_6145381 : CollatzResearch.WordTrace tailWord_6145381 prefixEnd_6145381 3155534258007925902275413 := by
  unfold tailWord_6145381
  simp only [CollatzResearch.WordTrace]
  refine ⟨224140458949341659361163997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149426972632894439574109331 224140458949341659361163997)
  ·
    refine ⟨84052672106003122260436499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 224140458949341659361163997 84052672106003122260436499)
    ·
      refine ⟨126079008159004683390654749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84052672106003122260436499 126079008159004683390654749)
      ·
        refine ⟨47279628059626756271495531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126079008159004683390654749 47279628059626756271495531)
        ·
          refine ⟨70919442089440134407243297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47279628059626756271495531 70919442089440134407243297)
          ·
            refine ⟨53189581567080100805432473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70919442089440134407243297 53189581567080100805432473)
            ·
              refine ⟨39892186175310075604074355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53189581567080100805432473 39892186175310075604074355)
              ·
                refine ⟨59838279262965113406111533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39892186175310075604074355 59838279262965113406111533)
                ·
                  refine ⟨22439354723611917527291825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 59838279262965113406111533 22439354723611917527291825)
                  ·
                    refine ⟨16829516042708938145468869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22439354723611917527291825 16829516042708938145468869)
                    ·
                      refine ⟨3155534258007925902275413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16829516042708938145468869 3155534258007925902275413)
                      ·
                        rfl

theorem cell23_6145381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 1, 3, 2, 4].length) (baseStart_6145381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6145381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6145381 prefixEnd_6145381 := by exact prefixLift 6145381
  have htrace : WordTrace (prefixWord ++ tailWord_6145381) baseStart_6145381 baseEnd_6145381 := by
    simpa [prefixWord, tailWord_6145381, baseEnd_6145381] using wordTrace_append hprefix tailTrace_6145381
  have hstable : (prefixWord ++ tailWord_6145381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6145381).length < 2 ^ (prefixWord ++ tailWord_6145381).sum := by decide
  have hdescent : baseEnd_6145381 < baseStart_6145381 := by decide
  rcases family_descends (prefixWord ++ tailWord_6145381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6145388 : List Nat := [2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 5]
def baseStart_6145388 : Nat := 118140960795 + 6145388 * 2 ^ 59
def prefixEnd_6145388 : Nat := 4983230072969 + 3 ^ 40 * 6145388 * 2
def baseEnd_6145388 : Nat := 3155537852372507374887881

theorem tailTrace_6145388 : CollatzResearch.WordTrace tailWord_6145388 prefixEnd_6145388 3155537852372507374887881 := by
  unfold tailWord_6145388
  simp only [CollatzResearch.WordTrace]
  refine ⟨112070357130158149778334409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149427142840210866371112545 112070357130158149778334409)
  ·
    refine ⟨84052767847618612333750807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 112070357130158149778334409 84052767847618612333750807)
    ·
      refine ⟨126079151771427918500626211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84052767847618612333750807 126079151771427918500626211)
      ·
        refine ⟨189118727657141877750939317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126079151771427918500626211 189118727657141877750939317)
        ·
          refine ⟨17729880717857051039150561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 189118727657141877750939317 17729880717857051039150561)
          ·
            refine ⟨13297410538392788279362921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17729880717857051039150561 13297410538392788279362921)
            ·
              refine ⟨9973057903794591209522191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13297410538392788279362921 9973057903794591209522191)
              ·
                refine ⟨14959586855691886814283287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9973057903794591209522191 14959586855691886814283287)
                ·
                  refine ⟨22439380283537830221424931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14959586855691886814283287 22439380283537830221424931)
                  ·
                    refine ⟨33659070425306745332137397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22439380283537830221424931 33659070425306745332137397)
                    ·
                      refine ⟨3155537852372507374887881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33659070425306745332137397 3155537852372507374887881)
                      ·
                        rfl

theorem cell23_6145388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 5].length) (baseStart_6145388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6145388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6145388 prefixEnd_6145388 := by exact prefixLift 6145388
  have htrace : WordTrace (prefixWord ++ tailWord_6145388) baseStart_6145388 baseEnd_6145388 := by
    simpa [prefixWord, tailWord_6145388, baseEnd_6145388] using wordTrace_append hprefix tailTrace_6145388
  have hstable : (prefixWord ++ tailWord_6145388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6145388).length < 2 ^ (prefixWord ++ tailWord_6145388).sum := by decide
  have hdescent : baseEnd_6145388 < baseStart_6145388 := by decide
  rcases family_descends (prefixWord ++ tailWord_6145388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6145412 : List Nat := [2, 3, 2, 1, 1, 5, 2, 1, 2, 4]
def baseStart_6145412 : Nat := 118140960795 + 6145412 * 2 ^ 59
def prefixEnd_6145412 : Nat := 4983230072969 + 3 ^ 40 * 6145412 * 2
def baseEnd_6145412 : Nat := 1051850058636071760329257

theorem tailTrace_6145412 : CollatzResearch.WordTrace tailWord_6145412 prefixEnd_6145412 1051850058636071760329257 := by
  unfold tailWord_6145412
  simp only [CollatzResearch.WordTrace]
  refine ⟨112070794806114675827771245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 149427726408152901103694993 112070794806114675827771245)
  ·
    refine ⟨42026548052293003435414217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 112070794806114675827771245 42026548052293003435414217)
    ·
      refine ⟨31519911039219752576560663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42026548052293003435414217 31519911039219752576560663)
      ·
        refine ⟨47279866558829628864840995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31519911039219752576560663 47279866558829628864840995)
        ·
          refine ⟨70919799838244443297261493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47279866558829628864840995 70919799838244443297261493)
          ·
            refine ⟨6648731234835416559118265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 70919799838244443297261493 6648731234835416559118265)
            ·
              refine ⟨4986548426126562419338699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6648731234835416559118265 4986548426126562419338699)
              ·
                refine ⟨7479822639189843629008049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4986548426126562419338699 7479822639189843629008049)
                ·
                  refine ⟨5609866979392382721756037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7479822639189843629008049 5609866979392382721756037)
                  ·
                    refine ⟨1051850058636071760329257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5609866979392382721756037 1051850058636071760329257)
                    ·
                      rfl

theorem cell23_6145412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 2, 1, 2, 4].length) (baseStart_6145412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6145412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6145412 prefixEnd_6145412 := by exact prefixLift 6145412
  have htrace : WordTrace (prefixWord ++ tailWord_6145412) baseStart_6145412 baseEnd_6145412 := by
    simpa [prefixWord, tailWord_6145412, baseEnd_6145412] using wordTrace_append hprefix tailTrace_6145412
  have hstable : (prefixWord ++ tailWord_6145412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6145412).length < 2 ^ (prefixWord ++ tailWord_6145412).sum := by decide
  have hdescent : baseEnd_6145412 < baseStart_6145412 := by decide
  rcases family_descends (prefixWord ++ tailWord_6145412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6145453 : List Nat := [1, 5, 2, 2, 1, 3, 2, 2, 1, 2, 2]
def baseStart_6145453 : Nat := 118140960795 + 6145453 * 2 ^ 59
def prefixEnd_6145453 : Nat := 4983230072969 + 3 ^ 40 * 6145453 * 2
def baseEnd_6145453 : Nat := 3155571228615049620575083

theorem tailTrace_6145453 : CollatzResearch.WordTrace tailWord_6145453 prefixEnd_6145453 3155571228615049620575083 := by
  unfold tailWord_6145453
  simp only [CollatzResearch.WordTrace]
  refine ⟨224143085005080815657785013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149428723336720543771856675 224143085005080815657785013)
  ·
    refine ⟨21013414219226326467917345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 224143085005080815657785013 21013414219226326467917345)
    ·
      refine ⟨15760060664419744850938009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21013414219226326467917345 15760060664419744850938009)
      ·
        refine ⟨11820045498314808638203507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15760060664419744850938009 11820045498314808638203507)
        ·
          refine ⟨17730068247472212957305261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11820045498314808638203507 17730068247472212957305261)
          ·
            refine ⟨6648775592802079858989473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17730068247472212957305261 6648775592802079858989473)
            ·
              refine ⟨4986581694601559894242105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6648775592802079858989473 4986581694601559894242105)
              ·
                refine ⟨3739936270951169920681579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4986581694601559894242105 3739936270951169920681579)
                ·
                  refine ⟨5609904406426754881022369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3739936270951169920681579 5609904406426754881022369)
                  ·
                    refine ⟨4207428304820066160766777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5609904406426754881022369 4207428304820066160766777)
                    ·
                      refine ⟨3155571228615049620575083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4207428304820066160766777 3155571228615049620575083)
                      ·
                        rfl

theorem cell23_6145453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 2, 2, 1, 2, 2].length) (baseStart_6145453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6145453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6145453 prefixEnd_6145453 := by exact prefixLift 6145453
  have htrace : WordTrace (prefixWord ++ tailWord_6145453) baseStart_6145453 baseEnd_6145453 := by
    simpa [prefixWord, tailWord_6145453, baseEnd_6145453] using wordTrace_append hprefix tailTrace_6145453
  have hstable : (prefixWord ++ tailWord_6145453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6145453).length < 2 ^ (prefixWord ++ tailWord_6145453).sum := by decide
  have hdescent : baseEnd_6145453 < baseStart_6145453 := by decide
  rcases family_descends (prefixWord ++ tailWord_6145453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6145509 : List Nat := [1, 3, 1, 5, 1, 1, 3, 2, 2, 2, 2]
def baseStart_6145509 : Nat := 118140960795 + 6145509 * 2 ^ 59
def prefixEnd_6145509 : Nat := 4983230072969 + 3 ^ 40 * 6145509 * 2
def baseEnd_6145509 : Nat := 3155599983531701401474825

theorem tailTrace_6145509 : CollatzResearch.WordTrace tailWord_6145509 prefixEnd_6145509 3155599983531701401474825 := by
  unfold tailWord_6145509
  simp only [CollatzResearch.WordTrace]
  refine ⟨224145127492877937221823581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 149430084995251958147882387 224145127492877937221823581)
  ·
    refine ⟨84054422809829226458183843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 224145127492877937221823581 84054422809829226458183843)
    ·
      refine ⟨126081634214743839687275765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84054422809829226458183843 126081634214743839687275765)
      ·
        refine ⟨11820153207632234970682103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 126081634214743839687275765 11820153207632234970682103)
        ·
          refine ⟨17730229811448352456023155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11820153207632234970682103 17730229811448352456023155)
          ·
            refine ⟨26595344717172528684034733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17730229811448352456023155 26595344717172528684034733)
            ·
              refine ⟨9973254268939698256513025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26595344717172528684034733 9973254268939698256513025)
              ·
                refine ⟨7479940701704773692384769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9973254268939698256513025 7479940701704773692384769)
                ·
                  refine ⟨5609955526278580269288577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7479940701704773692384769 5609955526278580269288577)
                  ·
                    refine ⟨4207466644708935201966433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5609955526278580269288577 4207466644708935201966433)
                    ·
                      refine ⟨3155599983531701401474825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4207466644708935201966433 3155599983531701401474825)
                      ·
                        rfl

theorem cell23_6145509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 3, 2, 2, 2, 2].length) (baseStart_6145509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6145509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6145509 prefixEnd_6145509 := by exact prefixLift 6145509
  have htrace : WordTrace (prefixWord ++ tailWord_6145509) baseStart_6145509 baseEnd_6145509 := by
    simpa [prefixWord, tailWord_6145509, baseEnd_6145509] using wordTrace_append hprefix tailTrace_6145509
  have hstable : (prefixWord ++ tailWord_6145509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6145509).length < 2 ^ (prefixWord ++ tailWord_6145509).sum := by decide
  have hdescent : baseEnd_6145509 < baseStart_6145509 := by decide
  rcases family_descends (prefixWord ++ tailWord_6145509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
