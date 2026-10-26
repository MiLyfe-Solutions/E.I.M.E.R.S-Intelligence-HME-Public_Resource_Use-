import V185TrunkScan23Chunk0959

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5683781 : List Nat := [1, 3, 1, 1, 1, 6, 1, 1, 1, 5, 2]
def baseStart_5683781 : Nat := 118140960795 + 5683781 * 2 ^ 59
def prefixEnd_5683781 : Nat := 4983230072969 + 3 ^ 40 * 5683781 * 2
def baseEnd_5683781 : Nat := 2918511587892531914398273

theorem tailTrace_5683781 : CollatzResearch.WordTrace tailWord_5683781 prefixEnd_5683781 2918511587892531914398273 := by
  unfold tailWord_5683781
  simp only [CollatzResearch.WordTrace]
  refine ⟨207304523821639624357539197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138203015881093082905026131 207304523821639624357539197)
  ·
    refine ⟨77739196433114859134077199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 207304523821639624357539197 77739196433114859134077199)
    ·
      refine ⟨116608794649672288701115799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77739196433114859134077199 116608794649672288701115799)
      ·
        refine ⟨174913191974508433051673699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116608794649672288701115799 174913191974508433051673699)
        ·
          refine ⟨262369787961762649577510549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174913191974508433051673699 262369787961762649577510549)
          ·
            refine ⟨12298583810707624198945807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 262369787961762649577510549 12298583810707624198945807)
            ·
              refine ⟨18447875716061436298418711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12298583810707624198945807 18447875716061436298418711)
              ·
                refine ⟨27671813574092154447628067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18447875716061436298418711 27671813574092154447628067)
                ·
                  refine ⟨41507720361138231671442101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27671813574092154447628067 41507720361138231671442101)
                  ·
                    refine ⟨3891348783856709219197697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41507720361138231671442101 3891348783856709219197697)
                    ·
                      refine ⟨2918511587892531914398273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3891348783856709219197697 2918511587892531914398273)
                      ·
                        rfl

theorem cell23_5683781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 1, 1, 5, 2].length) (baseStart_5683781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5683781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5683781 prefixEnd_5683781 := by exact prefixLift 5683781
  have htrace : WordTrace (prefixWord ++ tailWord_5683781) baseStart_5683781 baseEnd_5683781 := by
    simpa [prefixWord, tailWord_5683781, baseEnd_5683781] using wordTrace_append hprefix tailTrace_5683781
  have hstable : (prefixWord ++ tailWord_5683781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5683781).length < 2 ^ (prefixWord ++ tailWord_5683781).sum := by decide
  have hdescent : baseEnd_5683781 < baseStart_5683781 := by decide
  rcases family_descends (prefixWord ++ tailWord_5683781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5683782 : List Nat := [6, 1, 1, 1, 2, 2, 2, 3, 1, 4]
def baseStart_5683782 : Nat := 118140960795 + 5683782 * 2 ^ 59
def prefixEnd_5683782 : Nat := 4983230072969 + 3 ^ 40 * 5683782 * 2
def baseEnd_5683782 : Nat := 972837367124395470161923

theorem tailTrace_5683782 : CollatzResearch.WordTrace tailWord_5683782 prefixEnd_5683782 972837367124395470161923 := by
  unfold tailWord_5683782
  simp only [CollatzResearch.WordTrace]
  refine ⟨6478267509207375047760175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 138203040196424001018883733 6478267509207375047760175)
  ·
    refine ⟨9717401263811062571640263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6478267509207375047760175 9717401263811062571640263)
    ·
      refine ⟨14576101895716593857460395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9717401263811062571640263 14576101895716593857460395)
      ·
        refine ⟨21864152843574890786190593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14576101895716593857460395 21864152843574890786190593)
        ·
          refine ⟨16398114632681168089642945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21864152843574890786190593 16398114632681168089642945)
          ·
            refine ⟨12298585974510876067232209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16398114632681168089642945 12298585974510876067232209)
            ·
              refine ⟨9223939480883157050424157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12298585974510876067232209 9223939480883157050424157)
              ·
                refine ⟨3458977305331183893909059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9223939480883157050424157 3458977305331183893909059)
                ·
                  refine ⟨5188465957996775840863589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3458977305331183893909059 5188465957996775840863589)
                  ·
                    refine ⟨972837367124395470161923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5188465957996775840863589 972837367124395470161923)
                    ·
                      rfl

theorem cell23_5683782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 2, 3, 1, 4].length) (baseStart_5683782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5683782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5683782 prefixEnd_5683782 := by exact prefixLift 5683782
  have htrace : WordTrace (prefixWord ++ tailWord_5683782) baseStart_5683782 baseEnd_5683782 := by
    simpa [prefixWord, tailWord_5683782, baseEnd_5683782] using wordTrace_append hprefix tailTrace_5683782
  have hstable : (prefixWord ++ tailWord_5683782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5683782).length < 2 ^ (prefixWord ++ tailWord_5683782).sum := by decide
  have hdescent : baseEnd_5683782 < baseStart_5683782 := by decide
  rcases family_descends (prefixWord ++ tailWord_5683782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5683791 : List Nat := [1, 1, 2, 1, 1, 2, 8, 1, 1, 5]
def baseStart_5683791 : Nat := 118140960795 + 5683791 * 2 ^ 59
def prefixEnd_5683791 : Nat := 4983230072969 + 3 ^ 40 * 5683791 * 2
def baseEnd_5683791 : Nat := 972838907566358958424409

theorem tailTrace_5683791 : CollatzResearch.WordTrace tailWord_5683791 prefixEnd_5683791 972838907566358958424409 := by
  unfold tailWord_5683791
  simp only [CollatzResearch.WordTrace]
  refine ⟨207304888551603396065403227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138203259034402264043602151 207304888551603396065403227)
  ·
    refine ⟨310957332827405094098104841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207304888551603396065403227 310957332827405094098104841)
    ·
      refine ⟨233217999620553820573578631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 310957332827405094098104841 233217999620553820573578631)
      ·
        refine ⟨349826999430830730860367947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233217999620553820573578631 349826999430830730860367947)
        ·
          refine ⟨524740499146246096290551921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 349826999430830730860367947 524740499146246096290551921)
          ·
            refine ⟨393555374359684572217913941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 524740499146246096290551921 393555374359684572217913941)
            ·
              refine ⟨4611977043277553580678679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 393555374359684572217913941 4611977043277553580678679)
              ·
                refine ⟨6917965564916330371018019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4611977043277553580678679 6917965564916330371018019)
                ·
                  refine ⟨10376948347374495556527029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6917965564916330371018019 10376948347374495556527029)
                  ·
                    refine ⟨972838907566358958424409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10376948347374495556527029 972838907566358958424409)
                    ·
                      rfl

theorem cell23_5683791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 8, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 8, 1, 1, 5].length) (baseStart_5683791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5683791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5683791 prefixEnd_5683791 := by exact prefixLift 5683791
  have htrace : WordTrace (prefixWord ++ tailWord_5683791) baseStart_5683791 baseEnd_5683791 := by
    simpa [prefixWord, tailWord_5683791, baseEnd_5683791] using wordTrace_append hprefix tailTrace_5683791
  have hstable : (prefixWord ++ tailWord_5683791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5683791).length < 2 ^ (prefixWord ++ tailWord_5683791).sum := by decide
  have hdescent : baseEnd_5683791 < baseStart_5683791 := by decide
  rcases family_descends (prefixWord ++ tailWord_5683791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5683817 : List Nat := [1, 2, 1, 1, 1, 4, 1, 12]
def baseStart_5683817 : Nat := 118140960795 + 5683817 * 2 ^ 59
def prefixEnd_5683817 : Nat := 4983230072969 + 3 ^ 40 * 5683817 * 2
def baseEnd_5683817 : Nat := 108093706414670139761041

theorem tailTrace_5683817 : CollatzResearch.WordTrace tailWord_5683817 prefixEnd_5683817 108093706414670139761041 := by
  unfold tailWord_5683817
  simp only [CollatzResearch.WordTrace]
  refine ⟨207305836849509202505849705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138203891233006135003899803 207305836849509202505849705)
  ·
    refine ⟨155479377637131901879387279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207305836849509202505849705 155479377637131901879387279)
    ·
      refine ⟨233219066455697852819080919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155479377637131901879387279 233219066455697852819080919)
      ·
        refine ⟨349828599683546779228621379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233219066455697852819080919 349828599683546779228621379)
        ·
          refine ⟨524742899525320168842932069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 349828599683546779228621379 524742899525320168842932069)
          ·
            refine ⟨98389293660997531658049763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 524742899525320168842932069 98389293660997531658049763)
            ·
              refine ⟨147583940491496297487074645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98389293660997531658049763 147583940491496297487074645)
              ·
                refine ⟨108093706414670139761041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 147583940491496297487074645 108093706414670139761041)
                ·
                  rfl

theorem cell23_5683817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 12].length) (baseStart_5683817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5683817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5683817 prefixEnd_5683817 := by exact prefixLift 5683817
  have htrace : WordTrace (prefixWord ++ tailWord_5683817) baseStart_5683817 baseEnd_5683817 := by
    simpa [prefixWord, tailWord_5683817, baseEnd_5683817] using wordTrace_append hprefix tailTrace_5683817
  have hstable : (prefixWord ++ tailWord_5683817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5683817).length < 2 ^ (prefixWord ++ tailWord_5683817).sum := by decide
  have hdescent : baseEnd_5683817 < baseStart_5683817 := by decide
  rcases family_descends (prefixWord ++ tailWord_5683817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5683821 : List Nat := [1, 5, 1, 1, 3, 1, 3, 1, 1, 6]
def baseStart_5683821 : Nat := 118140960795 + 5683821 * 2 ^ 59
def prefixEnd_5683821 : Nat := 4983230072969 + 3 ^ 40 * 5683821 * 2
def baseEnd_5683821 : Nat := 972844042372903919299363

theorem tailTrace_5683821 : CollatzResearch.WordTrace tailWord_5683821 prefixEnd_5683821 972844042372903919299363 := by
  unfold tailWord_5683821
  simp only [CollatzResearch.WordTrace]
  refine ⟨207305982741494711188995317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138203988494329807459330211 207305982741494711188995317)
  ·
    refine ⟨19434935882015129173968311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 207305982741494711188995317 19434935882015129173968311)
    ·
      refine ⟨29152403823022693760952467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19434935882015129173968311 29152403823022693760952467)
      ·
        refine ⟨43728605734534040641428701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29152403823022693760952467 43728605734534040641428701)
        ·
          refine ⟨16398227150450265240535763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43728605734534040641428701 16398227150450265240535763)
          ·
            refine ⟨24597340725675397860803645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16398227150450265240535763 24597340725675397860803645)
            ·
              refine ⟨9224002772128274197801367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24597340725675397860803645 9224002772128274197801367)
              ·
                refine ⟨13836004158192411296702051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9224002772128274197801367 13836004158192411296702051)
                ·
                  refine ⟨20754006237288616945053077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13836004158192411296702051 20754006237288616945053077)
                  ·
                    refine ⟨972844042372903919299363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20754006237288616945053077 972844042372903919299363)
                    ·
                      rfl

theorem cell23_5683821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 3, 1, 1, 6].length) (baseStart_5683821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5683821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5683821 prefixEnd_5683821 := by exact prefixLift 5683821
  have htrace : WordTrace (prefixWord ++ tailWord_5683821) baseStart_5683821 baseEnd_5683821 := by
    simpa [prefixWord, tailWord_5683821, baseEnd_5683821] using wordTrace_append hprefix tailTrace_5683821
  have hstable : (prefixWord ++ tailWord_5683821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5683821).length < 2 ^ (prefixWord ++ tailWord_5683821).sum := by decide
  have hdescent : baseEnd_5683821 < baseStart_5683821 := by decide
  rcases family_descends (prefixWord ++ tailWord_5683821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5683831 : List Nat := [1, 1, 3, 1, 1, 3, 3, 4, 1, 2, 3]
def baseStart_5683831 : Nat := 118140960795 + 5683831 * 2 ^ 59
def prefixEnd_5683831 : Nat := 4983230072969 + 3 ^ 40 * 5683831 * 2
def baseEnd_5683831 : Nat := 2918537261925256718773043

theorem tailTrace_5683831 : CollatzResearch.WordTrace tailWord_5683831 prefixEnd_5683831 2918537261925256718773043 := by
  unfold tailWord_5683831
  simp only [CollatzResearch.WordTrace]
  refine ⟨207306347471458482896859347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138204231647638988597906231 207306347471458482896859347)
  ·
    refine ⟨310959521207187724345289021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207306347471458482896859347 310959521207187724345289021)
    ·
      refine ⟨116609820452695396629483383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 310959521207187724345289021 116609820452695396629483383)
      ·
        refine ⟨174914730679043094944225075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116609820452695396629483383 174914730679043094944225075)
        ·
          refine ⟨262372096018564642416337613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174914730679043094944225075 262372096018564642416337613)
          ·
            refine ⟨98389536006961740906126605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 262372096018564642416337613 98389536006961740906126605)
            ·
              refine ⟨36896076002610652839797477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 98389536006961740906126605 36896076002610652839797477)
              ·
                refine ⟨6918014250489497407462027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36896076002610652839797477 6918014250489497407462027)
                ·
                  refine ⟨10377021375734246111193041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6918014250489497407462027 10377021375734246111193041)
                  ·
                    refine ⟨7782766031800684583394781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10377021375734246111193041 7782766031800684583394781)
                    ·
                      refine ⟨2918537261925256718773043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7782766031800684583394781 2918537261925256718773043)
                      ·
                        rfl

theorem cell23_5683831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 4, 1, 2, 3].length) (baseStart_5683831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5683831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5683831 prefixEnd_5683831 := by exact prefixLift 5683831
  have htrace : WordTrace (prefixWord ++ tailWord_5683831) baseStart_5683831 baseEnd_5683831 := by
    simpa [prefixWord, tailWord_5683831, baseEnd_5683831] using wordTrace_append hprefix tailTrace_5683831
  have hstable : (prefixWord ++ tailWord_5683831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5683831).length < 2 ^ (prefixWord ++ tailWord_5683831).sum := by decide
  have hdescent : baseEnd_5683831 < baseStart_5683831 := by decide
  rcases family_descends (prefixWord ++ tailWord_5683831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5683864 : List Nat := [2, 1, 2, 4, 1, 1, 2, 1, 2, 7]
def baseStart_5683864 : Nat := 118140960795 + 5683864 * 2 ^ 59
def prefixEnd_5683864 : Nat := 4983230072969 + 3 ^ 40 * 5683864 * 2
def baseEnd_5683864 : Nat := 972851402262285029886797

theorem tailTrace_5683864 : CollatzResearch.WordTrace tailWord_5683864 prefixEnd_5683864 972851402262285029886797 := by
  unfold tailWord_5683864
  simp only [CollatzResearch.WordTrace]
  refine ⟨103653775540169464766405323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138205034053559286355207097 103653775540169464766405323)
  ·
    refine ⟨155480663310254197149607985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103653775540169464766405323 155480663310254197149607985)
    ·
      refine ⟨116610497482690647862205989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155480663310254197149607985 116610497482690647862205989)
      ·
        refine ⟨21864468278004496474163623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 116610497482690647862205989 21864468278004496474163623)
        ·
          refine ⟨32796702417006744711245435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21864468278004496474163623 32796702417006744711245435)
          ·
            refine ⟨49195053625510117066868153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32796702417006744711245435 49195053625510117066868153)
            ·
              refine ⟨36896290219132587800151115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49195053625510117066868153 36896290219132587800151115)
              ·
                refine ⟨55344435328698881700226673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36896290219132587800151115 55344435328698881700226673)
                ·
                  refine ⟨41508326496524161275170005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55344435328698881700226673 41508326496524161275170005)
                  ·
                    refine ⟨972851402262285029886797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41508326496524161275170005 972851402262285029886797)
                    ·
                      rfl

theorem cell23_5683864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 1, 2, 7].length) (baseStart_5683864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5683864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5683864 prefixEnd_5683864 := by exact prefixLift 5683864
  have htrace : WordTrace (prefixWord ++ tailWord_5683864) baseStart_5683864 baseEnd_5683864 := by
    simpa [prefixWord, tailWord_5683864, baseEnd_5683864] using wordTrace_append hprefix tailTrace_5683864
  have hstable : (prefixWord ++ tailWord_5683864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5683864).length < 2 ^ (prefixWord ++ tailWord_5683864).sum := by decide
  have hdescent : baseEnd_5683864 < baseStart_5683864 := by decide
  rcases family_descends (prefixWord ++ tailWord_5683864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5683872 : List Nat := [2, 1, 1, 4, 5, 1, 2, 1, 2, 4]
def baseStart_5683872 : Nat := 118140960795 + 5683872 * 2 ^ 59
def prefixEnd_5683872 : Nat := 4983230072969 + 3 ^ 40 * 5683872 * 2
def baseEnd_5683872 : Nat := 972852771544030352786785

theorem tailTrace_5683872 : CollatzResearch.WordTrace tailWord_5683872 prefixEnd_5683872 972852771544030352786785 := by
  unfold tailWord_5683872
  simp only [CollatzResearch.WordTrace]
  refine ⟨103653921432154973449550935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138205228576206631266067913 103653921432154973449550935)
  ·
    refine ⟨155480882148232460174326403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103653921432154973449550935 155480882148232460174326403)
    ·
      refine ⟨233221323222348690261489605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155480882148232460174326403 233221323222348690261489605)
      ·
        refine ⟨43728998104190379424029301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 233221323222348690261489605 43728998104190379424029301)
        ·
          refine ⟨4099593572267848071002747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 43728998104190379424029301 4099593572267848071002747)
          ·
            refine ⟨6149390358401772106504121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4099593572267848071002747 6149390358401772106504121)
            ·
              refine ⟨4612042768801329079878091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6149390358401772106504121 4612042768801329079878091)
              ·
                refine ⟨6918064153201993619817137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4612042768801329079878091 6918064153201993619817137)
                ·
                  refine ⟨5188548114901495214862853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6918064153201993619817137 5188548114901495214862853)
                  ·
                    refine ⟨972852771544030352786785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5188548114901495214862853 972852771544030352786785)
                    ·
                      rfl

theorem cell23_5683872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 2, 1, 2, 4].length) (baseStart_5683872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5683872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5683872 prefixEnd_5683872 := by exact prefixLift 5683872
  have htrace : WordTrace (prefixWord ++ tailWord_5683872) baseStart_5683872 baseEnd_5683872 := by
    simpa [prefixWord, tailWord_5683872, baseEnd_5683872] using wordTrace_append hprefix tailTrace_5683872
  have hstable : (prefixWord ++ tailWord_5683872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5683872).length < 2 ^ (prefixWord ++ tailWord_5683872).sum := by decide
  have hdescent : baseEnd_5683872 < baseStart_5683872 := by decide
  rcases family_descends (prefixWord ++ tailWord_5683872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5683935 : List Nat := [1, 1, 2, 3, 2, 3, 2, 3, 2, 2, 2]
def baseStart_5683935 : Nat := 118140960795 + 5683935 * 2 ^ 59
def prefixEnd_5683935 : Nat := 4983230072969 + 3 ^ 40 * 5683935 * 2
def baseEnd_5683935 : Nat := 2918590663913324311872565

theorem tailTrace_5683935 : CollatzResearch.WordTrace tailWord_5683935 prefixEnd_5683935 2918590663913324311872565 := by
  unfold tailWord_5683935
  simp only [CollatzResearch.WordTrace]
  refine ⟨207310140663081708658645259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138206760442054472439096839 207310140663081708658645259)
  ·
    refine ⟨310965210994622562987967889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207310140663081708658645259 310965210994622562987967889)
    ·
      refine ⟨233223908245966922240975917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 310965210994622562987967889 233223908245966922240975917)
      ·
        refine ⟨87458965592237595840365969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 233223908245966922240975917 87458965592237595840365969)
        ·
          refine ⟨65594224194178196880274477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87458965592237595840365969 65594224194178196880274477)
          ·
            refine ⟨24597834072816823830102929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65594224194178196880274477 24597834072816823830102929)
            ·
              refine ⟨18448375554612617872577197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24597834072816823830102929 18448375554612617872577197)
              ·
                refine ⟨6918140832979731702216449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18448375554612617872577197 6918140832979731702216449)
                ·
                  refine ⟨5188605624734798776662337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6918140832979731702216449 5188605624734798776662337)
                  ·
                    refine ⟨3891454218551099082496753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5188605624734798776662337 3891454218551099082496753)
                    ·
                      refine ⟨2918590663913324311872565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3891454218551099082496753 2918590663913324311872565)
                      ·
                        rfl

theorem cell23_5683935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 3, 2, 2, 2].length) (baseStart_5683935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5683935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5683935 prefixEnd_5683935 := by exact prefixLift 5683935
  have htrace : WordTrace (prefixWord ++ tailWord_5683935) baseStart_5683935 baseEnd_5683935 := by
    simpa [prefixWord, tailWord_5683935, baseEnd_5683935] using wordTrace_append hprefix tailTrace_5683935
  have hstable : (prefixWord ++ tailWord_5683935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5683935).length < 2 ^ (prefixWord ++ tailWord_5683935).sum := by decide
  have hdescent : baseEnd_5683935 < baseStart_5683935 := by decide
  rcases family_descends (prefixWord ++ tailWord_5683935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5683941 : List Nat := [1, 3, 1, 4, 1, 3, 1, 2, 7]
def baseStart_5683941 : Nat := 118140960795 + 5683941 * 2 ^ 59
def prefixEnd_5683941 : Nat := 4983230072969 + 3 ^ 40 * 5683941 * 2
def baseEnd_5683941 : Nat := 324288193866361254266393

theorem tailTrace_5683941 : CollatzResearch.WordTrace tailWord_5683941 prefixEnd_5683941 324288193866361254266393 := by
  unfold tailWord_5683941
  simp only [CollatzResearch.WordTrace]
  refine ⟨207310359501059971683363677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138206906334039981122242451 207310359501059971683363677)
  ·
    refine ⟨77741384812897489381261379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 207310359501059971683363677 77741384812897489381261379)
    ·
      refine ⟨116612077219346234071892069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77741384812897489381261379 116612077219346234071892069)
      ·
        refine ⟨21864764478627418888479763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 116612077219346234071892069 21864764478627418888479763)
        ·
          refine ⟨32797146717941128332719645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21864764478627418888479763 32797146717941128332719645)
          ·
            refine ⟨12298930019227923124769867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32797146717941128332719645 12298930019227923124769867)
            ·
              refine ⟨18448395028841884687154801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12298930019227923124769867 18448395028841884687154801)
              ·
                refine ⟨13836296271631413515366101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18448395028841884687154801 13836296271631413515366101)
                ·
                  refine ⟨324288193866361254266393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13836296271631413515366101 324288193866361254266393)
                  ·
                    rfl

theorem cell23_5683941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 2, 7].length) (baseStart_5683941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5683941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5683941 prefixEnd_5683941 := by exact prefixLift 5683941
  have htrace : WordTrace (prefixWord ++ tailWord_5683941) baseStart_5683941 baseEnd_5683941 := by
    simpa [prefixWord, tailWord_5683941, baseEnd_5683941] using wordTrace_append hprefix tailTrace_5683941
  have hstable : (prefixWord ++ tailWord_5683941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5683941).length < 2 ^ (prefixWord ++ tailWord_5683941).sum := by decide
  have hdescent : baseEnd_5683941 < baseStart_5683941 := by decide
  rcases family_descends (prefixWord ++ tailWord_5683941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5683986 : List Nat := [3, 2, 4, 1, 2, 1, 3, 1, 2, 2, 2]
def baseStart_5683986 : Nat := 118140960795 + 5683986 * 2 ^ 59
def prefixEnd_5683986 : Nat := 4983230072969 + 3 ^ 40 * 5683986 * 2
def baseEnd_5683986 : Nat := 2918616851426703612334831

theorem tailTrace_5683986 : CollatzResearch.WordTrace tailWord_5683986 prefixEnd_5683986 2918616851426703612334831 := by
  unfold tailWord_5683986
  simp only [CollatzResearch.WordTrace]
  refine ⟨51828000196474236092187953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138208000523931296245834541 51828000196474236092187953)
  ·
    refine ⟨38871000147355677069140965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51828000196474236092187953 38871000147355677069140965)
    ·
      refine ⟨7288312527629189450463931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38871000147355677069140965 7288312527629189450463931)
      ·
        refine ⟨10932468791443784175695897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7288312527629189450463931 10932468791443784175695897)
        ·
          refine ⟨8199351593582838131771923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10932468791443784175695897 8199351593582838131771923)
          ·
            refine ⟨12299027390374257197657885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8199351593582838131771923 12299027390374257197657885)
            ·
              refine ⟨4612135271390346449121707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12299027390374257197657885 4612135271390346449121707)
              ·
                refine ⟨6918202907085519673682561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4612135271390346449121707 6918202907085519673682561)
                ·
                  refine ⟨5188652180314139755261921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6918202907085519673682561 5188652180314139755261921)
                  ·
                    refine ⟨3891489135235604816446441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5188652180314139755261921 3891489135235604816446441)
                    ·
                      refine ⟨2918616851426703612334831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3891489135235604816446441 2918616851426703612334831)
                      ·
                        rfl

theorem cell23_5683986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 3, 1, 2, 2, 2].length) (baseStart_5683986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5683986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5683986 prefixEnd_5683986 := by exact prefixLift 5683986
  have htrace : WordTrace (prefixWord ++ tailWord_5683986) baseStart_5683986 baseEnd_5683986 := by
    simpa [prefixWord, tailWord_5683986, baseEnd_5683986] using wordTrace_append hprefix tailTrace_5683986
  have hstable : (prefixWord ++ tailWord_5683986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5683986).length < 2 ^ (prefixWord ++ tailWord_5683986).sum := by decide
  have hdescent : baseEnd_5683986 < baseStart_5683986 := by decide
  rcases family_descends (prefixWord ++ tailWord_5683986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5684008 : List Nat := [2, 1, 5, 1, 1, 1, 2, 3, 2, 1, 4]
def baseStart_5684008 : Nat := 118140960795 + 5684008 * 2 ^ 59
def prefixEnd_5684008 : Nat := 4983230072969 + 3 ^ 40 * 5684008 * 2
def baseEnd_5684008 : Nat := 2918628148001102526259729

theorem tailTrace_5684008 : CollatzResearch.WordTrace tailWord_5684008 prefixEnd_5684008 2918628148001102526259729 := by
  unfold tailWord_5684008
  simp only [CollatzResearch.WordTrace]
  refine ⟨103656401595908621063026339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138208535461211494750701785 103656401595908621063026339)
  ·
    refine ⟨155484602393862931594539509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103656401595908621063026339 155484602393862931594539509)
    ·
      refine ⟨14576681474424649836988079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 155484602393862931594539509 14576681474424649836988079)
      ·
        refine ⟨21865022211636974755482119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14576681474424649836988079 21865022211636974755482119)
        ·
          refine ⟨32797533317455462133223179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21865022211636974755482119 32797533317455462133223179)
          ·
            refine ⟨49196299976183193199834769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32797533317455462133223179 49196299976183193199834769)
            ·
              refine ⟨36897224982137394899876077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49196299976183193199834769 36897224982137394899876077)
              ·
                refine ⟨13836459368301523087453529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36897224982137394899876077 13836459368301523087453529)
                ·
                  refine ⟨10377344526226142315590147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13836459368301523087453529 10377344526226142315590147)
                  ·
                    refine ⟨15566016789339213473385221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10377344526226142315590147 15566016789339213473385221)
                    ·
                      refine ⟨2918628148001102526259729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15566016789339213473385221 2918628148001102526259729)
                      ·
                        rfl

theorem cell23_5684008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_5684008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5684008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5684008 prefixEnd_5684008 := by exact prefixLift 5684008
  have htrace : WordTrace (prefixWord ++ tailWord_5684008) baseStart_5684008 baseEnd_5684008 := by
    simpa [prefixWord, tailWord_5684008, baseEnd_5684008] using wordTrace_append hprefix tailTrace_5684008
  have hstable : (prefixWord ++ tailWord_5684008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5684008).length < 2 ^ (prefixWord ++ tailWord_5684008).sum := by decide
  have hdescent : baseEnd_5684008 < baseStart_5684008 := by decide
  rcases family_descends (prefixWord ++ tailWord_5684008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5684031 : List Nat := [1, 1, 2, 2, 5, 1, 2, 1, 8]
def baseStart_5684031 : Nat := 118140960795 + 5684031 * 2 ^ 59
def prefixEnd_5684031 : Nat := 4983230072969 + 3 ^ 40 * 5684031 * 2
def baseEnd_5684031 : Nat := 324293328672906215141347

theorem tailTrace_5684031 : CollatzResearch.WordTrace tailWord_5684031 prefixEnd_5684031 324293328672906215141347 := by
  unfold tailWord_5684031
  simp only [CollatzResearch.WordTrace]
  refine ⟨207313642070733917054139947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138209094713822611369426631 207313642070733917054139947)
  ·
    refine ⟨310970463106100875581209921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207313642070733917054139947 310970463106100875581209921)
    ·
      refine ⟨233227847329575656685907441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 310970463106100875581209921 233227847329575656685907441)
      ·
        refine ⟨174920885497181742514430581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 233227847329575656685907441 174920885497181742514430581)
        ·
          refine ⟨16398833015360788360727867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 174920885497181742514430581 16398833015360788360727867)
          ·
            refine ⟨24598249523041182541091801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16398833015360788360727867 24598249523041182541091801)
            ·
              refine ⟨18448687142280886905818851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24598249523041182541091801 18448687142280886905818851)
              ·
                refine ⟨27673030713421330358728277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18448687142280886905818851 27673030713421330358728277)
                ·
                  refine ⟨324293328672906215141347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27673030713421330358728277 324293328672906215141347)
                  ·
                    rfl

theorem cell23_5684031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 1, 8].length) (baseStart_5684031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5684031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5684031 prefixEnd_5684031 := by exact prefixLift 5684031
  have htrace : WordTrace (prefixWord ++ tailWord_5684031) baseStart_5684031 baseEnd_5684031 := by
    simpa [prefixWord, tailWord_5684031, baseEnd_5684031] using wordTrace_append hprefix tailTrace_5684031
  have hstable : (prefixWord ++ tailWord_5684031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5684031).length < 2 ^ (prefixWord ++ tailWord_5684031).sum := by decide
  have hdescent : baseEnd_5684031 < baseStart_5684031 := by decide
  rcases family_descends (prefixWord ++ tailWord_5684031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5684048 : List Nat := [2, 1, 1, 1, 1, 4, 6, 1, 6]
def baseStart_5684048 : Nat := 118140960795 + 5684048 * 2 ^ 59
def prefixEnd_5684048 : Nat := 4983230072969 + 3 ^ 40 * 5684048 * 2
def baseEnd_5684048 : Nat := 324294298580809152195505

theorem tailTrace_5684048 : CollatzResearch.WordTrace tailWord_5684048 prefixEnd_5684048 324294298580809152195505 := by
  unfold tailWord_5684048
  simp only [CollatzResearch.WordTrace]
  refine ⟨103657131055836164478754399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138209508074448219305005865 103657131055836164478754399)
  ·
    refine ⟨155485696583754246718131599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103657131055836164478754399 155485696583754246718131599)
    ·
      refine ⟨233228544875631370077197399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155485696583754246718131599 233228544875631370077197399)
      ·
        refine ⟨349842817313447055115796099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233228544875631370077197399 349842817313447055115796099)
        ·
          refine ⟨524764225970170582673694149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 349842817313447055115796099 524764225970170582673694149)
          ·
            refine ⟨98393292369406984251317653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 524764225970170582673694149 98393292369406984251317653)
            ·
              refine ⟨4612185579815952386780515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 98393292369406984251317653 4612185579815952386780515)
              ·
                refine ⟨6918278369723928580170773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4612185579815952386780515 6918278369723928580170773)
                ·
                  refine ⟨324294298580809152195505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6918278369723928580170773 324294298580809152195505)
                  ·
                    rfl

theorem cell23_5684048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 6, 1, 6].length) (baseStart_5684048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5684048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5684048 prefixEnd_5684048 := by exact prefixLift 5684048
  have htrace : WordTrace (prefixWord ++ tailWord_5684048) baseStart_5684048 baseEnd_5684048 := by
    simpa [prefixWord, tailWord_5684048, baseEnd_5684048] using wordTrace_append hprefix tailTrace_5684048
  have hstable : (prefixWord ++ tailWord_5684048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5684048).length < 2 ^ (prefixWord ++ tailWord_5684048).sum := by decide
  have hdescent : baseEnd_5684048 < baseStart_5684048 := by decide
  rcases family_descends (prefixWord ++ tailWord_5684048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5684086 : List Nat := [5, 1, 1, 3, 1, 3, 2, 2, 1, 4]
def baseStart_5684086 : Nat := 118140960795 + 5684086 * 2 ^ 59
def prefixEnd_5684086 : Nat := 4983230072969 + 3 ^ 40 * 5684086 * 2
def baseEnd_5684086 : Nat := 972889399830717740361457

theorem tailTrace_5684086 : CollatzResearch.WordTrace tailWord_5684086 prefixEnd_5684086 972889399830717740361457 := by
  unfold tailWord_5684086
  simp only [CollatzResearch.WordTrace]
  refine ⟨12957228005345916340462007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 138210432057023107631594741 12957228005345916340462007)
  ·
    refine ⟨19435842008018874510693011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12957228005345916340462007 19435842008018874510693011)
    ·
      refine ⟨29153763012028311766039517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19435842008018874510693011 29153763012028311766039517)
      ·
        refine ⟨10932661129510616912264819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29153763012028311766039517 10932661129510616912264819)
        ·
          refine ⟨16398991694265925368397229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10932661129510616912264819 16398991694265925368397229)
          ·
            refine ⟨6149621885349722013148961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16398991694265925368397229 6149621885349722013148961)
            ·
              refine ⟨4612216414012291509861721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6149621885349722013148961 4612216414012291509861721)
              ·
                refine ⟨3459162310509218632396291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4612216414012291509861721 3459162310509218632396291)
                ·
                  refine ⟨5188743465763827948594437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3459162310509218632396291 5188743465763827948594437)
                  ·
                    refine ⟨972889399830717740361457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5188743465763827948594437 972889399830717740361457)
                    ·
                      rfl

theorem cell23_5684086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 2, 2, 1, 4].length) (baseStart_5684086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5684086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5684086 prefixEnd_5684086 := by exact prefixLift 5684086
  have htrace : WordTrace (prefixWord ++ tailWord_5684086) baseStart_5684086 baseEnd_5684086 := by
    simpa [prefixWord, tailWord_5684086, baseEnd_5684086] using wordTrace_append hprefix tailTrace_5684086
  have hstable : (prefixWord ++ tailWord_5684086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5684086).length < 2 ^ (prefixWord ++ tailWord_5684086).sum := by decide
  have hdescent : baseEnd_5684086 < baseStart_5684086 := by decide
  rcases family_descends (prefixWord ++ tailWord_5684086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5684128 : List Nat := [2, 1, 1, 4, 1, 1, 4, 2, 1, 2, 4]
def baseStart_5684128 : Nat := 118140960795 + 5684128 * 2 ^ 59
def prefixEnd_5684128 : Nat := 4983230072969 + 3 ^ 40 * 5684128 * 2
def baseEnd_5684128 : Nat := 2918689765679642056759177

theorem tailTrace_5684128 : CollatzResearch.WordTrace tailWord_5684128 prefixEnd_5684128 2918689765679642056759177 := by
  unfold tailWord_5684128
  simp only [CollatzResearch.WordTrace]
  refine ⟨103658589975691251310210519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138211453300921668413614025 103658589975691251310210519)
  ·
    refine ⟨155487884963536876965315779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103658589975691251310210519 155487884963536876965315779)
    ·
      refine ⟨233231827445305315447973669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155487884963536876965315779 233231827445305315447973669)
      ·
        refine ⟨43730967645994746646495063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 233231827445305315447973669 43730967645994746646495063)
        ·
          refine ⟨65596451468992119969742595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43730967645994746646495063 65596451468992119969742595)
          ·
            refine ⟨98394677203488179954613893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65596451468992119969742595 98394677203488179954613893)
            ·
              refine ⟨18449001975654033741490105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 98394677203488179954613893 18449001975654033741490105)
              ·
                refine ⟨13836751481740525306117579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18449001975654033741490105 13836751481740525306117579)
                ·
                  refine ⟨20755127222610787959176369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13836751481740525306117579 20755127222610787959176369)
                  ·
                    refine ⟨15566345416958090969382277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20755127222610787959176369 15566345416958090969382277)
                    ·
                      refine ⟨2918689765679642056759177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15566345416958090969382277 2918689765679642056759177)
                      ·
                        rfl

theorem cell23_5684128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 2, 1, 2, 4].length) (baseStart_5684128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5684128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5684128 prefixEnd_5684128 := by exact prefixLift 5684128
  have htrace : WordTrace (prefixWord ++ tailWord_5684128) baseStart_5684128 baseEnd_5684128 := by
    simpa [prefixWord, tailWord_5684128, baseEnd_5684128] using wordTrace_append hprefix tailTrace_5684128
  have hstable : (prefixWord ++ tailWord_5684128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5684128).length < 2 ^ (prefixWord ++ tailWord_5684128).sum := by decide
  have hdescent : baseEnd_5684128 < baseStart_5684128 := by decide
  rcases family_descends (prefixWord ++ tailWord_5684128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5684149 : List Nat := [1, 3, 3, 2, 1, 1, 1, 6, 1, 2, 2]
def baseStart_5684149 : Nat := 118140960795 + 5684149 * 2 ^ 59
def prefixEnd_5684149 : Nat := 4983230072969 + 3 ^ 40 * 5684149 * 2
def baseEnd_5684149 : Nat := 2918700548773386474596581

theorem tailTrace_5684149 : CollatzResearch.WordTrace tailWord_5684149 prefixEnd_5684149 2918700548773386474596581 := by
  unfold tailWord_5684149
  simp only [CollatzResearch.WordTrace]
  refine ⟨207317945884306423206935501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138211963922870948804623667 207317945884306423206935501)
  ·
    refine ⟨77744229706614908702600813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 207317945884306423206935501 77744229706614908702600813)
    ·
      refine ⟨29154086139980590763475305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77744229706614908702600813 29154086139980590763475305)
      ·
        refine ⟨21865564604985443072606479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29154086139980590763475305 21865564604985443072606479)
        ·
          refine ⟨32798346907478164608909719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21865564604985443072606479 32798346907478164608909719)
          ·
            refine ⟨49197520361217246913364579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32798346907478164608909719 49197520361217246913364579)
            ·
              refine ⟨73796280541825870370046869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49197520361217246913364579 73796280541825870370046869)
              ·
                refine ⟨3459200650398087673595947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 73796280541825870370046869 3459200650398087673595947)
                ·
                  refine ⟨5188800975597131510393921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3459200650398087673595947 5188800975597131510393921)
                  ·
                    refine ⟨3891600731697848632795441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5188800975597131510393921 3891600731697848632795441)
                    ·
                      refine ⟨2918700548773386474596581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3891600731697848632795441 2918700548773386474596581)
                      ·
                        rfl

theorem cell23_5684149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 6, 1, 2, 2].length) (baseStart_5684149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5684149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5684149 prefixEnd_5684149 := by exact prefixLift 5684149
  have htrace : WordTrace (prefixWord ++ tailWord_5684149) baseStart_5684149 baseEnd_5684149 := by
    simpa [prefixWord, tailWord_5684149, baseEnd_5684149] using wordTrace_append hprefix tailTrace_5684149
  have hstable : (prefixWord ++ tailWord_5684149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5684149).length < 2 ^ (prefixWord ++ tailWord_5684149).sum := by decide
  have hdescent : baseEnd_5684149 < baseStart_5684149 := by decide
  rcases family_descends (prefixWord ++ tailWord_5684149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5684151 : List Nat := [1, 1, 3, 1, 3, 1, 2, 1, 1, 9]
def baseStart_5684151 : Nat := 118140960795 + 5684151 * 2 ^ 59
def prefixEnd_5684151 : Nat := 4983230072969 + 3 ^ 40 * 5684151 * 2
def baseEnd_5684151 : Nat := 972900525244898488923857

theorem tailTrace_5684151 : CollatzResearch.WordTrace tailWord_5684151 prefixEnd_5684151 972900525244898488923857 := by
  unfold tailWord_5684151
  simp only [CollatzResearch.WordTrace]
  refine ⟨207318018830299177548508307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138212012553532785032338871 207318018830299177548508307)
  ·
    refine ⟨310977028245448766322762461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207318018830299177548508307 310977028245448766322762461)
    ·
      refine ⟨116616385592043287371035923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 310977028245448766322762461 116616385592043287371035923)
      ·
        refine ⟨174924578388064931056553885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116616385592043287371035923 174924578388064931056553885)
        ·
          refine ⟨65596716895524349146207707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 174924578388064931056553885 65596716895524349146207707)
          ·
            refine ⟨98395075343286523719311561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65596716895524349146207707 98395075343286523719311561)
            ·
              refine ⟨73796306507464892789483671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98395075343286523719311561 73796306507464892789483671)
              ·
                refine ⟨110694459761197339184225507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73796306507464892789483671 110694459761197339184225507)
                ·
                  refine ⟨166041689641796008776338261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 110694459761197339184225507 166041689641796008776338261)
                  ·
                    refine ⟨972900525244898488923857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 166041689641796008776338261 972900525244898488923857)
                    ·
                      rfl

theorem cell23_5684151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 9].length) (baseStart_5684151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5684151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5684151 prefixEnd_5684151 := by exact prefixLift 5684151
  have htrace : WordTrace (prefixWord ++ tailWord_5684151) baseStart_5684151 baseEnd_5684151 := by
    simpa [prefixWord, tailWord_5684151, baseEnd_5684151] using wordTrace_append hprefix tailTrace_5684151
  have hstable : (prefixWord ++ tailWord_5684151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5684151).length < 2 ^ (prefixWord ++ tailWord_5684151).sum := by decide
  have hdescent : baseEnd_5684151 < baseStart_5684151 := by decide
  rcases family_descends (prefixWord ++ tailWord_5684151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5684208 : List Nat := [2, 1, 1, 1, 3, 2, 1, 3, 2, 4, 3]
def baseStart_5684208 : Nat := 118140960795 + 5684208 * 2 ^ 59
def prefixEnd_5684208 : Nat := 4983230072969 + 3 ^ 40 * 5684208 * 2
def baseEnd_5684208 : Nat := 2918730844132001743758809

theorem tailTrace_5684208 : CollatzResearch.WordTrace tailWord_5684208 prefixEnd_5684208 2918730844132001743758809 := by
  unfold tailWord_5684208
  simp only [CollatzResearch.WordTrace]
  refine ⟨103660048895546338141666639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138213398527395117522222185 103660048895546338141666639)
  ·
    refine ⟨155490073343319507212499959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103660048895546338141666639 155490073343319507212499959)
    ·
      refine ⟨233235110014979260818749939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155490073343319507212499959 233235110014979260818749939)
      ·
        refine ⟨349852665022468891228124909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233235110014979260818749939 349852665022468891228124909)
        ·
          refine ⟨131194749383425834210546841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 349852665022468891228124909 131194749383425834210546841)
          ·
            refine ⟨98396062037569375657910131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131194749383425834210546841 98396062037569375657910131)
            ·
              refine ⟨147594093056354063486865197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98396062037569375657910131 147594093056354063486865197)
              ·
                refine ⟨55347784896132773807574449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 147594093056354063486865197 55347784896132773807574449)
                ·
                  refine ⟨41510838672099580355680837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55347784896132773807574449 41510838672099580355680837)
                  ·
                    refine ⟨7783282251018671316690157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41510838672099580355680837 7783282251018671316690157)
                    ·
                      refine ⟨2918730844132001743758809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7783282251018671316690157 2918730844132001743758809)
                      ·
                        rfl

theorem cell23_5684208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 3, 2, 4, 3].length) (baseStart_5684208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5684208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5684208 prefixEnd_5684208 := by exact prefixLift 5684208
  have htrace : WordTrace (prefixWord ++ tailWord_5684208) baseStart_5684208 baseEnd_5684208 := by
    simpa [prefixWord, tailWord_5684208, baseEnd_5684208] using wordTrace_append hprefix tailTrace_5684208
  have hstable : (prefixWord ++ tailWord_5684208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5684208).length < 2 ^ (prefixWord ++ tailWord_5684208).sum := by decide
  have hdescent : baseEnd_5684208 < baseStart_5684208 := by decide
  rcases family_descends (prefixWord ++ tailWord_5684208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5684218 : List Nat := [3, 1, 1, 1, 1, 2, 1, 5, 2, 2, 4]
def baseStart_5684218 : Nat := 118140960795 + 5684218 * 2 ^ 59
def prefixEnd_5684218 : Nat := 4983230072969 + 3 ^ 40 * 5684218 * 2
def baseEnd_5684218 : Nat := 2918735978938546704633763

theorem tailTrace_5684218 : CollatzResearch.WordTrace tailWord_5684218 prefixEnd_5684218 2918735978938546704633763 := by
  unfold tailWord_5684218
  simp only [CollatzResearch.WordTrace]
  refine ⟨51830115630264111997799327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138213641680704298660798205 51830115630264111997799327)
  ·
    refine ⟨77745173445396167996698991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51830115630264111997799327 77745173445396167996698991)
    ·
      refine ⟨116617760168094251995048487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77745173445396167996698991 116617760168094251995048487)
      ·
        refine ⟨174926640252141377992572731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116617760168094251995048487 174926640252141377992572731)
        ·
          refine ⟨262389960378212066988859097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174926640252141377992572731 262389960378212066988859097)
          ·
            refine ⟨196792470283659050241644323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 262389960378212066988859097 196792470283659050241644323)
            ·
              refine ⟨295188705425488575362466485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 196792470283659050241644323 295188705425488575362466485)
              ·
                refine ⟨27673941133639553940231233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 295188705425488575362466485 27673941133639553940231233)
                ·
                  refine ⟨20755455850229665455173425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27673941133639553940231233 20755455850229665455173425)
                  ·
                    refine ⟨15566591887672249091380069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20755455850229665455173425 15566591887672249091380069)
                    ·
                      refine ⟨2918735978938546704633763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15566591887672249091380069 2918735978938546704633763)
                      ·
                        rfl

theorem cell23_5684218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 5, 2, 2, 4].length) (baseStart_5684218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5684218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5684218 prefixEnd_5684218 := by exact prefixLift 5684218
  have htrace : WordTrace (prefixWord ++ tailWord_5684218) baseStart_5684218 baseEnd_5684218 := by
    simpa [prefixWord, tailWord_5684218, baseEnd_5684218] using wordTrace_append hprefix tailTrace_5684218
  have hstable : (prefixWord ++ tailWord_5684218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5684218).length < 2 ^ (prefixWord ++ tailWord_5684218).sum := by decide
  have hdescent : baseEnd_5684218 < baseStart_5684218 := by decide
  rcases family_descends (prefixWord ++ tailWord_5684218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5684226 : List Nat := [3, 4, 1, 3, 1, 1, 1, 1, 3, 3, 2]
def baseStart_5684226 : Nat := 118140960795 + 5684226 * 2 ^ 59
def prefixEnd_5684226 : Nat := 4983230072969 + 3 ^ 40 * 5684226 * 2
def baseEnd_5684226 : Nat := 2918740086783782673333727

theorem tailTrace_5684226 : CollatzResearch.WordTrace tailWord_5684226 prefixEnd_5684226 2918740086783782673333727 := by
  unfold tailWord_5684226
  simp only [CollatzResearch.WordTrace]
  refine ⟨51830188576256866339372133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138213836203351643571659021 51830188576256866339372133)
  ·
    refine ⟨9718160358048162438632275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51830188576256866339372133 9718160358048162438632275)
    ·
      refine ⟨14577240537072243657948413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9718160358048162438632275 14577240537072243657948413)
      ·
        refine ⟨5466465201402091371730655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14577240537072243657948413 5466465201402091371730655)
        ·
          refine ⟨8199697802103137057595983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5466465201402091371730655 8199697802103137057595983)
          ·
            refine ⟨12299546703154705586393975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8199697802103137057595983 12299546703154705586393975)
            ·
              refine ⟨18449320054732058379590963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12299546703154705586393975 18449320054732058379590963)
              ·
                refine ⟨27673980082098087569386445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18449320054732058379590963 27673980082098087569386445)
                ·
                  refine ⟨10377742530786782838519917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27673980082098087569386445 10377742530786782838519917)
                  ·
                    refine ⟨3891653449045043564444969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10377742530786782838519917 3891653449045043564444969)
                    ·
                      refine ⟨2918740086783782673333727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3891653449045043564444969 2918740086783782673333727)
                      ·
                        rfl

theorem cell23_5684226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_5684226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5684226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5684226 prefixEnd_5684226 := by exact prefixLift 5684226
  have htrace : WordTrace (prefixWord ++ tailWord_5684226) baseStart_5684226 baseEnd_5684226 := by
    simpa [prefixWord, tailWord_5684226, baseEnd_5684226] using wordTrace_append hprefix tailTrace_5684226
  have hstable : (prefixWord ++ tailWord_5684226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5684226).length < 2 ^ (prefixWord ++ tailWord_5684226).sum := by decide
  have hdescent : baseEnd_5684226 < baseStart_5684226 := by decide
  rcases family_descends (prefixWord ++ tailWord_5684226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5684268 : List Nat := [2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 5]
def baseStart_5684268 : Nat := 118140960795 + 5684268 * 2 ^ 59
def prefixEnd_5684268 : Nat := 4983230072969 + 3 ^ 40 * 5684268 * 2
def baseEnd_5684268 : Nat := 2918761652971271509008533

theorem tailTrace_5684268 : CollatzResearch.WordTrace tailWord_5684268 prefixEnd_5684268 2918761652971271509008533 := by
  unfold tailWord_5684268
  simp only [CollatzResearch.WordTrace]
  refine ⟨103661143085437653265258729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138214857447250204353678305 103661143085437653265258729)
  ·
    refine ⟨77745857314078239948944047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103661143085437653265258729 77745857314078239948944047)
    ·
      refine ⟨116618785971117359923416071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77745857314078239948944047 116618785971117359923416071)
      ·
        refine ⟨174928178956676039885124107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116618785971117359923416071 174928178956676039885124107)
        ·
          refine ⟨262392268435014059827686161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174928178956676039885124107 262392268435014059827686161)
          ·
            refine ⟨196794201326260544870764621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 262392268435014059827686161 196794201326260544870764621)
            ·
              refine ⟨73797825497347704326536733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 196794201326260544870764621 73797825497347704326536733)
              ·
                refine ⟨27674184561505389122451275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73797825497347704326536733 27674184561505389122451275)
                ·
                  refine ⟨41511276842258083683676913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27674184561505389122451275 41511276842258083683676913)
                  ·
                    refine ⟨31133457631693562762757685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41511276842258083683676913 31133457631693562762757685)
                    ·
                      refine ⟨2918761652971271509008533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31133457631693562762757685 2918761652971271509008533)
                      ·
                        rfl

theorem cell23_5684268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 5].length) (baseStart_5684268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5684268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5684268 prefixEnd_5684268 := by exact prefixLift 5684268
  have htrace : WordTrace (prefixWord ++ tailWord_5684268) baseStart_5684268 baseEnd_5684268 := by
    simpa [prefixWord, tailWord_5684268, baseEnd_5684268] using wordTrace_append hprefix tailTrace_5684268
  have hstable : (prefixWord ++ tailWord_5684268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5684268).length < 2 ^ (prefixWord ++ tailWord_5684268).sum := by decide
  have hdescent : baseEnd_5684268 < baseStart_5684268 := by decide
  rcases family_descends (prefixWord ++ tailWord_5684268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5684295 : List Nat := [1, 1, 4, 1, 3, 3, 1, 1, 1, 3, 4]
def baseStart_5684295 : Nat := 118140960795 + 5684295 * 2 ^ 59
def prefixEnd_5684295 : Nat := 4983230072969 + 3 ^ 40 * 5684295 * 2
def baseEnd_5684295 : Nat := 2918775516948942903370909

theorem tailTrace_5684295 : CollatzResearch.WordTrace tailWord_5684295 prefixEnd_5684295 2918775516948942903370909 := by
  unfold tailWord_5684295
  simp only [CollatzResearch.WordTrace]
  refine ⟨207323270941777490141750339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138215513961184993427833559 207323270941777490141750339)
  ·
    refine ⟨310984906412666235212625509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207323270941777490141750339 310984906412666235212625509)
    ·
      refine ⟨58309669952374919102367283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 310984906412666235212625509 58309669952374919102367283)
      ·
        refine ⟨87464504928562378653550925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58309669952374919102367283 87464504928562378653550925)
        ·
          refine ⟨32799189348210891995081597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87464504928562378653550925 32799189348210891995081597)
          ·
            refine ⟨12299696005579084498155599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32799189348210891995081597 12299696005579084498155599)
            ·
              refine ⟨18449544008368626747233399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12299696005579084498155599 18449544008368626747233399)
              ·
                refine ⟨27674316012552940120850099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18449544008368626747233399 27674316012552940120850099)
                ·
                  refine ⟨41511474018829410181275149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27674316012552940120850099 41511474018829410181275149)
                  ·
                    refine ⟨15566802757061028817978181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41511474018829410181275149 15566802757061028817978181)
                    ·
                      refine ⟨2918775516948942903370909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15566802757061028817978181 2918775516948942903370909)
                      ·
                        rfl

theorem cell23_5684295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 1, 1, 3, 4].length) (baseStart_5684295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5684295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5684295 prefixEnd_5684295 := by exact prefixLift 5684295
  have htrace : WordTrace (prefixWord ++ tailWord_5684295) baseStart_5684295 baseEnd_5684295 := by
    simpa [prefixWord, tailWord_5684295, baseEnd_5684295] using wordTrace_append hprefix tailTrace_5684295
  have hstable : (prefixWord ++ tailWord_5684295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5684295).length < 2 ^ (prefixWord ++ tailWord_5684295).sum := by decide
  have hdescent : baseEnd_5684295 < baseStart_5684295 := by decide
  rcases family_descends (prefixWord ++ tailWord_5684295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5684356 : List Nat := [2, 3, 2, 1, 2, 4, 1, 3, 1, 4]
def baseStart_5684356 : Nat := 118140960795 + 5684356 * 2 ^ 59
def prefixEnd_5684356 : Nat := 4983230072969 + 3 ^ 40 * 5684356 * 2
def baseEnd_5684356 : Nat := 972935613089622388236043

theorem tailTrace_5684356 : CollatzResearch.WordTrace tailWord_5684356 prefixEnd_5684356 972935613089622388236043 := by
  unfold tailWord_5684356
  simp only [CollatzResearch.WordTrace]
  refine ⟨103662747897278248779860461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138216997196370998373147281 103662747897278248779860461)
  ·
    refine ⟨38873530461479343292447673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103662747897278248779860461 38873530461479343292447673)
    ·
      refine ⟨29155147846109507469335755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38873530461479343292447673 29155147846109507469335755)
      ·
        refine ⟨43732721769164261204003633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29155147846109507469335755 43732721769164261204003633)
        ·
          refine ⟨32799541326873195903002725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43732721769164261204003633 32799541326873195903002725)
          ·
            refine ⟨6149913998788724231813011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32799541326873195903002725 6149913998788724231813011)
            ·
              refine ⟨9224870998183086347719517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6149913998788724231813011 9224870998183086347719517)
              ·
                refine ⟨3459326624318657380394819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9224870998183086347719517 3459326624318657380394819)
                ·
                  refine ⟨5188989936477986070592229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3459326624318657380394819 5188989936477986070592229)
                  ·
                    refine ⟨972935613089622388236043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5188989936477986070592229 972935613089622388236043)
                    ·
                      rfl

theorem cell23_5684356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 1, 3, 1, 4].length) (baseStart_5684356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5684356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5684356 prefixEnd_5684356 := by exact prefixLift 5684356
  have htrace : WordTrace (prefixWord ++ tailWord_5684356) baseStart_5684356 baseEnd_5684356 := by
    simpa [prefixWord, tailWord_5684356, baseEnd_5684356] using wordTrace_append hprefix tailTrace_5684356
  have hstable : (prefixWord ++ tailWord_5684356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5684356).length < 2 ^ (prefixWord ++ tailWord_5684356).sum := by decide
  have hdescent : baseEnd_5684356 < baseStart_5684356 := by decide
  rcases family_descends (prefixWord ++ tailWord_5684356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5684386 : List Nat := [3, 3, 1, 3, 2, 2, 2, 1, 6]
def baseStart_5684386 : Nat := 118140960795 + 5684386 * 2 ^ 59
def prefixEnd_5684386 : Nat := 4983230072969 + 3 ^ 40 * 5684386 * 2
def baseEnd_5684386 : Nat := 324313582632055783036999

theorem tailTrace_5684386 : CollatzResearch.WordTrace tailWord_5684386 prefixEnd_5684386 324313582632055783036999 := by
  unfold tailWord_5684386
  simp only [CollatzResearch.WordTrace]
  refine ⟨51831647496111953170828253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138217726656298541788875341 51831647496111953170828253)
  ·
    refine ⟨19436867811041982439060595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51831647496111953170828253 19436867811041982439060595)
    ·
      refine ⟨29155301716562973658590893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19436867811041982439060595 29155301716562973658590893)
      ·
        refine ⟨10933238143711115121971585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29155301716562973658590893 10933238143711115121971585)
        ·
          refine ⟨8199928607783336341478689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10933238143711115121971585 8199928607783336341478689)
          ·
            refine ⟨6149946455837502256109017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8199928607783336341478689 6149946455837502256109017)
            ·
              refine ⟨4612459841878126692081763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6149946455837502256109017 4612459841878126692081763)
              ·
                refine ⟨6918689762817190038122645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4612459841878126692081763 6918689762817190038122645)
                ·
                  refine ⟨324313582632055783036999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6918689762817190038122645 324313582632055783036999)
                  ·
                    rfl

theorem cell23_5684386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 2, 1, 6].length) (baseStart_5684386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5684386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5684386 prefixEnd_5684386 := by exact prefixLift 5684386
  have htrace : WordTrace (prefixWord ++ tailWord_5684386) baseStart_5684386 baseEnd_5684386 := by
    simpa [prefixWord, tailWord_5684386, baseEnd_5684386] using wordTrace_append hprefix tailTrace_5684386
  have hstable : (prefixWord ++ tailWord_5684386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5684386).length < 2 ^ (prefixWord ++ tailWord_5684386).sum := by decide
  have hdescent : baseEnd_5684386 < baseStart_5684386 := by decide
  rcases family_descends (prefixWord ++ tailWord_5684386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5684402 : List Nat := [3, 2, 1, 1, 1, 5, 1, 1, 3, 1, 4]
def baseStart_5684402 : Nat := 118140960795 + 5684402 * 2 ^ 59
def prefixEnd_5684402 : Nat := 4983230072969 + 3 ^ 40 * 5684402 * 2
def baseEnd_5684402 : Nat := 2918830459378973984732917

theorem tailTrace_5684402 : CollatzResearch.WordTrace tailWord_5684402 prefixEnd_5684402 2918830459378973984732917 := by
  unfold tailWord_5684402
  simp only [CollatzResearch.WordTrace]
  refine ⟨51831793388097461853973865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138218115701593231610596973 51831793388097461853973865)
  ·
    refine ⟨38873845041073096390480399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51831793388097461853973865 38873845041073096390480399)
    ·
      refine ⟨58310767561609644585720599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38873845041073096390480399 58310767561609644585720599)
      ·
        refine ⟨87466151342414466878580899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58310767561609644585720599 87466151342414466878580899)
        ·
          refine ⟨131199227013621700317871349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87466151342414466878580899 131199227013621700317871349)
          ·
            refine ⟨12299927532527034404800439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 131199227013621700317871349 12299927532527034404800439)
            ·
              refine ⟨18449891298790551607200659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12299927532527034404800439 18449891298790551607200659)
              ·
                refine ⟨27674836948185827410800989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18449891298790551607200659 27674836948185827410800989)
                ·
                  refine ⟨10378063855569685279050371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27674836948185827410800989 10378063855569685279050371)
                  ·
                    refine ⟨15567095783354527918575557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10378063855569685279050371 15567095783354527918575557)
                    ·
                      refine ⟨2918830459378973984732917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15567095783354527918575557 2918830459378973984732917)
                      ·
                        rfl

theorem cell23_5684402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 1, 3, 1, 4].length) (baseStart_5684402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5684402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5684402 prefixEnd_5684402 := by exact prefixLift 5684402
  have htrace : WordTrace (prefixWord ++ tailWord_5684402) baseStart_5684402 baseEnd_5684402 := by
    simpa [prefixWord, tailWord_5684402, baseEnd_5684402] using wordTrace_append hprefix tailTrace_5684402
  have hstable : (prefixWord ++ tailWord_5684402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5684402).length < 2 ^ (prefixWord ++ tailWord_5684402).sum := by decide
  have hdescent : baseEnd_5684402 < baseStart_5684402 := by decide
  rcases family_descends (prefixWord ++ tailWord_5684402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5684412 : List Nat := [2, 2, 2, 3, 2, 2, 1, 2, 1, 6]
def baseStart_5684412 : Nat := 118140960795 + 5684412 * 2 ^ 59
def prefixEnd_5684412 : Nat := 4983230072969 + 3 ^ 40 * 5684412 * 2
def baseEnd_5684412 : Nat := 972945198061839648535957

theorem tailTrace_5684412 : CollatzResearch.WordTrace tailWord_5684412 prefixEnd_5684412 972945198061839648535957 := by
  unfold tailWord_5684412
  simp only [CollatzResearch.WordTrace]
  refine ⟨103663769141176809561879745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138218358854902412749172993 103663769141176809561879745)
  ·
    refine ⟨77747826855882607171409809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103663769141176809561879745 77747826855882607171409809)
    ·
      refine ⟨58310870141911955378557357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77747826855882607171409809 58310870141911955378557357)
      ·
        refine ⟨21866576303216983266959009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58310870141911955378557357 21866576303216983266959009)
        ·
          refine ⟨16399932227412737450219257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21866576303216983266959009 16399932227412737450219257)
          ·
            refine ⟨12299949170559553087664443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16399932227412737450219257 12299949170559553087664443)
            ·
              refine ⟨18449923755839329631496665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12299949170559553087664443 18449923755839329631496665)
              ·
                refine ⟨13837442816879497223622499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18449923755839329631496665 13837442816879497223622499)
                ·
                  refine ⟨20756164225319245835433749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13837442816879497223622499 20756164225319245835433749)
                  ·
                    refine ⟨972945198061839648535957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20756164225319245835433749 972945198061839648535957)
                    ·
                      rfl

theorem cell23_5684412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 2, 1, 6].length) (baseStart_5684412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5684412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5684412 prefixEnd_5684412 := by exact prefixLift 5684412
  have htrace : WordTrace (prefixWord ++ tailWord_5684412) baseStart_5684412 baseEnd_5684412 := by
    simpa [prefixWord, tailWord_5684412, baseEnd_5684412] using wordTrace_append hprefix tailTrace_5684412
  have hstable : (prefixWord ++ tailWord_5684412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5684412).length < 2 ^ (prefixWord ++ tailWord_5684412).sum := by decide
  have hdescent : baseEnd_5684412 < baseStart_5684412 := by decide
  rcases family_descends (prefixWord ++ tailWord_5684412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5684415 : List Nat := [1, 1, 2, 2, 2, 2, 3, 1, 3, 2, 4]
def baseStart_5684415 : Nat := 118140960795 + 5684415 * 2 ^ 59
def prefixEnd_5684415 : Nat := 4983230072969 + 3 ^ 40 * 5684415 * 2
def baseEnd_5684415 : Nat := 2918837134627482433870357

theorem tailTrace_5684415 : CollatzResearch.WordTrace tailWord_5684415 prefixEnd_5684415 2918837134627482433870357 := by
  unfold tailWord_5684415
  simp only [CollatzResearch.WordTrace]
  refine ⟨207327647701342750636118699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138218431800895167090745799 207327647701342750636118699)
  ·
    refine ⟨310991471552014125954178049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207327647701342750636118699 310991471552014125954178049)
    ·
      refine ⟨233243603664010594465633537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 310991471552014125954178049 233243603664010594465633537)
      ·
        refine ⟨174932702748007945849225153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 233243603664010594465633537 174932702748007945849225153)
        ·
          refine ⟨131199527061005959386918865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174932702748007945849225153 131199527061005959386918865)
          ·
            refine ⟨98399645295754469540189149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131199527061005959386918865 98399645295754469540189149)
            ·
              refine ⟨36899866985907926077570931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 98399645295754469540189149 36899866985907926077570931)
              ·
                refine ⟨55349800478861889116356397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36899866985907926077570931 55349800478861889116356397)
                ·
                  refine ⟨20756175179573208418633649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55349800478861889116356397 20756175179573208418633649)
                  ·
                    refine ⟨15567131384679906313975237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20756175179573208418633649 15567131384679906313975237)
                    ·
                      refine ⟨2918837134627482433870357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15567131384679906313975237 2918837134627482433870357)
                      ·
                        rfl

theorem cell23_5684415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 1, 3, 2, 4].length) (baseStart_5684415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5684415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5684415 prefixEnd_5684415 := by exact prefixLift 5684415
  have htrace : WordTrace (prefixWord ++ tailWord_5684415) baseStart_5684415 baseEnd_5684415 := by
    simpa [prefixWord, tailWord_5684415, baseEnd_5684415] using wordTrace_append hprefix tailTrace_5684415
  have hstable : (prefixWord ++ tailWord_5684415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5684415).length < 2 ^ (prefixWord ++ tailWord_5684415).sum := by decide
  have hdescent : baseEnd_5684415 < baseStart_5684415 := by decide
  rcases family_descends (prefixWord ++ tailWord_5684415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5684430 : List Nat := [4, 1, 1, 1, 5, 2, 2, 2, 1, 1, 3]
def baseStart_5684430 : Nat := 118140960795 + 5684430 * 2 ^ 59
def prefixEnd_5684430 : Nat := 4983230072969 + 3 ^ 40 * 5684430 * 2
def baseEnd_5684430 : Nat := 2918844836837299875182789

theorem tailTrace_5684430 : CollatzResearch.WordTrace tailWord_5684430 prefixEnd_5684430 2918844836837299875182789 := by
  unfold tailWord_5684430
  simp only [CollatzResearch.WordTrace]
  refine ⟨25916024349536051024739343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138218796530858938798609829 25916024349536051024739343)
  ·
    refine ⟨38874036524304076537109015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25916024349536051024739343 38874036524304076537109015)
    ·
      refine ⟨58311054786456114805663523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38874036524304076537109015 58311054786456114805663523)
      ·
        refine ⟨87466582179684172208495285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58311054786456114805663523 87466582179684172208495285)
        ·
          refine ⟨8199992079345391144546433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 87466582179684172208495285 8199992079345391144546433)
          ·
            refine ⟨6149994059509043358409825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8199992079345391144546433 6149994059509043358409825)
            ·
              refine ⟨4612495544631782518807369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6149994059509043358409825 4612495544631782518807369)
              ·
                refine ⟨3459371658473836889105527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4612495544631782518807369 3459371658473836889105527)
                ·
                  refine ⟨5189057487710755333658291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3459371658473836889105527 5189057487710755333658291)
                  ·
                    refine ⟨7783586231566133000487437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5189057487710755333658291 7783586231566133000487437)
                    ·
                      refine ⟨2918844836837299875182789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7783586231566133000487437 2918844836837299875182789)
                      ·
                        rfl

theorem cell23_5684430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 2, 2, 1, 1, 3].length) (baseStart_5684430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5684430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5684430 prefixEnd_5684430 := by exact prefixLift 5684430
  have htrace : WordTrace (prefixWord ++ tailWord_5684430) baseStart_5684430 baseEnd_5684430 := by
    simpa [prefixWord, tailWord_5684430, baseEnd_5684430] using wordTrace_append hprefix tailTrace_5684430
  have hstable : (prefixWord ++ tailWord_5684430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5684430).length < 2 ^ (prefixWord ++ tailWord_5684430).sum := by decide
  have hdescent : baseEnd_5684430 < baseStart_5684430 := by decide
  rcases family_descends (prefixWord ++ tailWord_5684430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5684452 : List Nat := [2, 3, 1, 1, 1, 2, 3, 3, 1, 3, 3]
def baseStart_5684452 : Nat := 118140960795 + 5684452 * 2 ^ 59
def prefixEnd_5684452 : Nat := 4983230072969 + 3 ^ 40 * 5684452 * 2
def baseEnd_5684452 : Nat := 2918856133411698789107687

theorem tailTrace_5684452 : CollatzResearch.WordTrace tailWord_5684452 prefixEnd_5684452 2918856133411698789107687 := by
  unfold tailWord_5684452
  simp only [CollatzResearch.WordTrace]
  refine ⟨103664498601104352977607805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138219331468139137303477073 103664498601104352977607805)
  ·
    refine ⟨38874186975414132366602927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103664498601104352977607805 38874186975414132366602927)
    ·
      refine ⟨58311280463121198549904391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38874186975414132366602927 58311280463121198549904391)
      ·
        refine ⟨87466920694681797824856587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58311280463121198549904391 87466920694681797824856587)
        ·
          refine ⟨131200381042022696737284881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87466920694681797824856587 131200381042022696737284881)
          ·
            refine ⟨98400285781517022552963661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131200381042022696737284881 98400285781517022552963661)
            ·
              refine ⟨36900107168068883457361373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 98400285781517022552963661 36900107168068883457361373)
              ·
                refine ⟨13837540188025831296510515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36900107168068883457361373 13837540188025831296510515)
                ·
                  refine ⟨20756310282038746944765773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13837540188025831296510515 20756310282038746944765773)
                  ·
                    refine ⟨7783616355764530104287165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20756310282038746944765773 7783616355764530104287165)
                    ·
                      refine ⟨2918856133411698789107687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7783616355764530104287165 2918856133411698789107687)
                      ·
                        rfl

theorem cell23_5684452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 3, 1, 3, 3].length) (baseStart_5684452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5684452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5684452 prefixEnd_5684452 := by exact prefixLift 5684452
  have htrace : WordTrace (prefixWord ++ tailWord_5684452) baseStart_5684452 baseEnd_5684452 := by
    simpa [prefixWord, tailWord_5684452, baseEnd_5684452] using wordTrace_append hprefix tailTrace_5684452
  have hstable : (prefixWord ++ tailWord_5684452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5684452).length < 2 ^ (prefixWord ++ tailWord_5684452).sum := by decide
  have hdescent : baseEnd_5684452 < baseStart_5684452 := by decide
  rcases family_descends (prefixWord ++ tailWord_5684452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5684465 : List Nat := [1, 2, 2, 2, 2, 1, 1, 3, 2, 2, 5]
def baseStart_5684465 : Nat := 118140960795 + 5684465 * 2 ^ 59
def prefixEnd_5684465 : Nat := 4983230072969 + 3 ^ 40 * 5684465 * 2
def baseEnd_5684465 : Nat := 2918862808660207238245127

theorem tailTrace_5684465 : CollatzResearch.WordTrace tailWord_5684465 prefixEnd_5684465 2918862808660207238245127 := by
  unfold tailWord_5684465
  simp only [CollatzResearch.WordTrace]
  refine ⟨207329471351161609175438849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138219647567441072783625899 207329471351161609175438849)
  ·
    refine ⟨155497103513371206881579137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207329471351161609175438849 155497103513371206881579137)
    ·
      refine ⟨116622827635028405161184353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155497103513371206881579137 116622827635028405161184353)
      ·
        refine ⟨87467120726271303870888265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116622827635028405161184353 87467120726271303870888265)
        ·
          refine ⟨65600340544703477903166199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87467120726271303870888265 65600340544703477903166199)
          ·
            refine ⟨98400510817055216854749299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65600340544703477903166199 98400510817055216854749299)
            ·
              refine ⟨147600766225582825282123949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98400510817055216854749299 147600766225582825282123949)
              ·
                refine ⟨55350287334593559480796481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 147600766225582825282123949 55350287334593559480796481)
                ·
                  refine ⟨41512715500945169610597361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55350287334593559480796481 41512715500945169610597361)
                  ·
                    refine ⟨31134536625708877207948021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41512715500945169610597361 31134536625708877207948021)
                    ·
                      refine ⟨2918862808660207238245127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31134536625708877207948021 2918862808660207238245127)
                      ·
                        rfl

theorem cell23_5684465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 3, 2, 2, 5].length) (baseStart_5684465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5684465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5684465 prefixEnd_5684465 := by exact prefixLift 5684465
  have htrace : WordTrace (prefixWord ++ tailWord_5684465) baseStart_5684465 baseEnd_5684465 := by
    simpa [prefixWord, tailWord_5684465, baseEnd_5684465] using wordTrace_append hprefix tailTrace_5684465
  have hstable : (prefixWord ++ tailWord_5684465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5684465).length < 2 ^ (prefixWord ++ tailWord_5684465).sum := by decide
  have hdescent : baseEnd_5684465 < baseStart_5684465 := by decide
  rcases family_descends (prefixWord ++ tailWord_5684465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5684485 : List Nat := [1, 3, 1, 1, 2, 1, 3, 1, 4, 6]
def baseStart_5684485 : Nat := 118140960795 + 5684485 * 2 ^ 59
def prefixEnd_5684485 : Nat := 4983230072969 + 3 ^ 40 * 5684485 * 2
def baseEnd_5684485 : Nat := 972957692757765719998345

theorem tailTrace_5684485 : CollatzResearch.WordTrace tailWord_5684485 prefixEnd_5684485 972957692757765719998345 := by
  unfold tailWord_5684485
  simp only [CollatzResearch.WordTrace]
  refine ⟨207330200811089152591166909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138220133874059435060777939 207330200811089152591166909)
  ·
    refine ⟨77748825304158432221687591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 207330200811089152591166909 77748825304158432221687591)
    ·
      refine ⟨116623237956237648332531387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77748825304158432221687591 116623237956237648332531387)
      ·
        refine ⟨174934856934356472498797081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116623237956237648332531387 174934856934356472498797081)
        ·
          refine ⟨131201142700767354374097811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174934856934356472498797081 131201142700767354374097811)
          ·
            refine ⟨196801714051151031561146717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131201142700767354374097811 196801714051151031561146717)
            ·
              refine ⟨73800642769181636835430019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 196801714051151031561146717 73800642769181636835430019)
              ·
                refine ⟨110700964153772455253145029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73800642769181636835430019 110700964153772455253145029)
                ·
                  refine ⟨20756430778832335359964693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 110700964153772455253145029 20756430778832335359964693)
                  ·
                    refine ⟨972957692757765719998345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20756430778832335359964693 972957692757765719998345)
                    ·
                      rfl

theorem cell23_5684485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 4, 6].length) (baseStart_5684485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5684485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5684485 prefixEnd_5684485 := by exact prefixLift 5684485
  have htrace : WordTrace (prefixWord ++ tailWord_5684485) baseStart_5684485 baseEnd_5684485 := by
    simpa [prefixWord, tailWord_5684485, baseEnd_5684485] using wordTrace_append hprefix tailTrace_5684485
  have hstable : (prefixWord ++ tailWord_5684485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5684485).length < 2 ^ (prefixWord ++ tailWord_5684485).sum := by decide
  have hdescent : baseEnd_5684485 < baseStart_5684485 := by decide
  rcases family_descends (prefixWord ++ tailWord_5684485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5684495 : List Nat := [1, 1, 2, 1, 1, 1, 3, 1, 6, 1, 5]
def baseStart_5684495 : Nat := 118140960795 + 5684495 * 2 ^ 59
def prefixEnd_5684495 : Nat := 4983230072969 + 3 ^ 40 * 5684495 * 2
def baseEnd_5684495 : Nat := 2918878213079842120869989

theorem tailTrace_5684495 : CollatzResearch.WordTrace tailWord_5684495 prefixEnd_5684495 2918878213079842120869989 := by
  unfold tailWord_5684495
  simp only [CollatzResearch.WordTrace]
  refine ⟨207330565541052924299030939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138220377027368616199353959 207330565541052924299030939)
  ·
    refine ⟨310995848311579386448546409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207330565541052924299030939 310995848311579386448546409)
    ·
      refine ⟨233246886233684539836409807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 310995848311579386448546409 233246886233684539836409807)
      ·
        refine ⟨349870329350526809754614711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233246886233684539836409807 349870329350526809754614711)
        ·
          refine ⟨524805494025790214631922067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 349870329350526809754614711 524805494025790214631922067)
          ·
            refine ⟨787208241038685321947883101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 524805494025790214631922067 787208241038685321947883101)
            ·
              refine ⟨295203090389506995730456163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 787208241038685321947883101 295203090389506995730456163)
              ·
                refine ⟨442804635584260493595684245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 295203090389506995730456163 442804635584260493595684245)
                ·
                  refine ⟨20756467293012210637297699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 442804635584260493595684245 20756467293012210637297699)
                  ·
                    refine ⟨31134700939518315955946549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20756467293012210637297699 31134700939518315955946549)
                    ·
                      refine ⟨2918878213079842120869989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31134700939518315955946549 2918878213079842120869989)
                      ·
                        rfl

theorem cell23_5684495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 6, 1, 5].length) (baseStart_5684495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5684495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5684495 prefixEnd_5684495 := by exact prefixLift 5684495
  have htrace : WordTrace (prefixWord ++ tailWord_5684495) baseStart_5684495 baseEnd_5684495 := by
    simpa [prefixWord, tailWord_5684495, baseEnd_5684495] using wordTrace_append hprefix tailTrace_5684495
  have hstable : (prefixWord ++ tailWord_5684495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5684495).length < 2 ^ (prefixWord ++ tailWord_5684495).sum := by decide
  have hdescent : baseEnd_5684495 < baseStart_5684495 := by decide
  rcases family_descends (prefixWord ++ tailWord_5684495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5684535 : List Nat := [1, 1, 3, 1, 2, 1, 1, 1, 2, 4, 6]
def baseStart_5684535 : Nat := 118140960795 + 5684535 * 2 ^ 59
def prefixEnd_5684535 : Nat := 4983230072969 + 3 ^ 40 * 5684535 * 2
def baseEnd_5684535 : Nat := 2918898752306021964369805

theorem tailTrace_5684535 : CollatzResearch.WordTrace tailWord_5684535 prefixEnd_5684535 2918898752306021964369805 := by
  unfold tailWord_5684535
  simp only [CollatzResearch.WordTrace]
  refine ⟨207332024460908011130487059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138221349640605340753658039 207332024460908011130487059)
  ·
    refine ⟨310998036691362016695730589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207332024460908011130487059 310998036691362016695730589)
    ·
      refine ⟨116624263759260756260898971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 310998036691362016695730589 116624263759260756260898971)
      ·
        refine ⟨174936395638891134391348457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116624263759260756260898971 174936395638891134391348457)
        ·
          refine ⟨131202296729168350793511343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174936395638891134391348457 131202296729168350793511343)
          ·
            refine ⟨196803445093752526190267015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131202296729168350793511343 196803445093752526190267015)
            ·
              refine ⟨295205167640628789285400523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 196803445093752526190267015 295205167640628789285400523)
              ·
                refine ⟨442807751460943183928100785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 295205167640628789285400523 442807751460943183928100785)
                ·
                  refine ⟨332105813595707387946075589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 442807751460943183928100785 332105813595707387946075589)
                  ·
                    refine ⟨62269840049195135239889173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 332105813595707387946075589 62269840049195135239889173)
                    ·
                      refine ⟨2918898752306021964369805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62269840049195135239889173 2918898752306021964369805)
                      ·
                        rfl

theorem cell23_5684535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 4, 6].length) (baseStart_5684535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5684535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5684535 prefixEnd_5684535 := by exact prefixLift 5684535
  have htrace : WordTrace (prefixWord ++ tailWord_5684535) baseStart_5684535 baseEnd_5684535 := by
    simpa [prefixWord, tailWord_5684535, baseEnd_5684535] using wordTrace_append hprefix tailTrace_5684535
  have hstable : (prefixWord ++ tailWord_5684535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5684535).length < 2 ^ (prefixWord ++ tailWord_5684535).sum := by decide
  have hdescent : baseEnd_5684535 < baseStart_5684535 := by decide
  rcases family_descends (prefixWord ++ tailWord_5684535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5684542 : List Nat := [4, 2, 1, 2, 1, 1, 1, 1, 1, 2, 7]
def baseStart_5684542 : Nat := 118140960795 + 5684542 * 2 ^ 59
def prefixEnd_5684542 : Nat := 4983230072969 + 3 ^ 40 * 5684542 * 2
def baseEnd_5684542 : Nat := 2918902346670603436982273

theorem tailTrace_5684542 : CollatzResearch.WordTrace tailWord_5684542 prefixEnd_5684542 2918902346670603436982273 := by
  unfold tailWord_5684542
  simp only [CollatzResearch.WordTrace]
  refine ⟨25916534971485331415748985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138221519847921767550661253 25916534971485331415748985)
  ·
    refine ⟨19437401228613998561811739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25916534971485331415748985 19437401228613998561811739)
    ·
      refine ⟨29156101842920997842717609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19437401228613998561811739 29156101842920997842717609)
      ·
        refine ⟨21867076382190748382038207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29156101842920997842717609 21867076382190748382038207)
        ·
          refine ⟨32800614573286122573057311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21867076382190748382038207 32800614573286122573057311)
          ·
            refine ⟨49200921859929183859585967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32800614573286122573057311 49200921859929183859585967)
            ·
              refine ⟨73801382789893775789378951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49200921859929183859585967 73801382789893775789378951)
              ·
                refine ⟨110702074184840663684068427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73801382789893775789378951 110702074184840663684068427)
                ·
                  refine ⟨166053111277260995526102641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 110702074184840663684068427 166053111277260995526102641)
                  ·
                    refine ⟨124539833457945746644576981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 166053111277260995526102641 124539833457945746644576981)
                    ·
                      refine ⟨2918902346670603436982273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 124539833457945746644576981 2918902346670603436982273)
                      ·
                        rfl

theorem cell23_5684542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_5684542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5684542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5684542 prefixEnd_5684542 := by exact prefixLift 5684542
  have htrace : WordTrace (prefixWord ++ tailWord_5684542) baseStart_5684542 baseEnd_5684542 := by
    simpa [prefixWord, tailWord_5684542, baseEnd_5684542] using wordTrace_append hprefix tailTrace_5684542
  have hstable : (prefixWord ++ tailWord_5684542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5684542).length < 2 ^ (prefixWord ++ tailWord_5684542).sum := by decide
  have hdescent : baseEnd_5684542 < baseStart_5684542 := by decide
  rcases family_descends (prefixWord ++ tailWord_5684542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5684562 : List Nat := [3, 2, 2, 1, 1, 1, 1, 1, 6, 5]
def baseStart_5684562 : Nat := 118140960795 + 5684562 * 2 ^ 59
def prefixEnd_5684562 : Nat := 4983230072969 + 3 ^ 40 * 5684562 * 2
def baseEnd_5684562 : Nat := 972970872094564452910727

theorem tailTrace_5684562 : CollatzResearch.WordTrace tailWord_5684562 prefixEnd_5684562 972970872094564452910727 := by
  unfold tailWord_5684562
  simp only [CollatzResearch.WordTrace]
  refine ⟨51833252307952548685429985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138222006154540129827813293 51833252307952548685429985)
  ·
    refine ⟨38874939230964411514072489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51833252307952548685429985 38874939230964411514072489)
    ·
      refine ⟨29156204423223308635554367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38874939230964411514072489 29156204423223308635554367)
      ·
        refine ⟨43734306634834962953331551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29156204423223308635554367 43734306634834962953331551)
        ·
          refine ⟨65601459952252444429997327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43734306634834962953331551 65601459952252444429997327)
          ·
            refine ⟨98402189928378666644995991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65601459952252444429997327 98402189928378666644995991)
            ·
              refine ⟨147603284892567999967493987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98402189928378666644995991 147603284892567999967493987)
              ·
                refine ⟨221404927338851999951240981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 147603284892567999967493987 221404927338851999951240981)
                ·
                  refine ⟨10378355969008687497714421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 221404927338851999951240981 10378355969008687497714421)
                  ·
                    refine ⟨972970872094564452910727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10378355969008687497714421 972970872094564452910727)
                    ·
                      rfl

theorem cell23_5684562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 6, 5].length) (baseStart_5684562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5684562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5684562 prefixEnd_5684562 := by exact prefixLift 5684562
  have htrace : WordTrace (prefixWord ++ tailWord_5684562) baseStart_5684562 baseEnd_5684562 := by
    simpa [prefixWord, tailWord_5684562, baseEnd_5684562] using wordTrace_append hprefix tailTrace_5684562
  have hstable : (prefixWord ++ tailWord_5684562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5684562).length < 2 ^ (prefixWord ++ tailWord_5684562).sum := by decide
  have hdescent : baseEnd_5684562 < baseStart_5684562 := by decide
  rcases family_descends (prefixWord ++ tailWord_5684562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5684579 : List Nat := [1, 1, 1, 5, 2, 3, 2, 1, 2, 5]
def baseStart_5684579 : Nat := 118140960795 + 5684579 * 2 ^ 59
def prefixEnd_5684579 : Nat := 4983230072969 + 3 ^ 40 * 5684579 * 2
def baseEnd_5684579 : Nat := 972973781818273264073201

theorem tailTrace_5684579 : CollatzResearch.WordTrace tailWord_5684579 prefixEnd_5684579 972973781818273264073201 := by
  unfold tailWord_5684579
  simp only [CollatzResearch.WordTrace]
  refine ⟨207333629272748606645088791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138222419515165737763392527 207333629272748606645088791)
  ·
    refine ⟨311000443909122909967633187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207333629272748606645088791 311000443909122909967633187)
    ·
      refine ⟨466500665863684364951449781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 311000443909122909967633187 466500665863684364951449781)
      ·
        refine ⟨43734437424720409214198417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 466500665863684364951449781 43734437424720409214198417)
        ·
          refine ⟨32800828068540306910648813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43734437424720409214198417 32800828068540306910648813)
          ·
            refine ⟨12300310525702615091493305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32800828068540306910648813 12300310525702615091493305)
            ·
              refine ⟨9225232894276961318619979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12300310525702615091493305 9225232894276961318619979)
              ·
                refine ⟨13837849341415441977929969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9225232894276961318619979 13837849341415441977929969)
                ·
                  refine ⟨10378387006061581483447477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13837849341415441977929969 10378387006061581483447477)
                  ·
                    refine ⟨972973781818273264073201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10378387006061581483447477 972973781818273264073201)
                    ·
                      rfl

theorem cell23_5684579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 2, 1, 2, 5].length) (baseStart_5684579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5684579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5684579 prefixEnd_5684579 := by exact prefixLift 5684579
  have htrace : WordTrace (prefixWord ++ tailWord_5684579) baseStart_5684579 baseEnd_5684579 := by
    simpa [prefixWord, tailWord_5684579, baseEnd_5684579] using wordTrace_append hprefix tailTrace_5684579
  have hstable : (prefixWord ++ tailWord_5684579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5684579).length < 2 ^ (prefixWord ++ tailWord_5684579).sum := by decide
  have hdescent : baseEnd_5684579 < baseStart_5684579 := by decide
  rcases family_descends (prefixWord ++ tailWord_5684579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5684599 : List Nat := [1, 1, 3, 1, 1, 2, 4, 2, 2, 4, 2]
def baseStart_5684599 : Nat := 118140960795 + 5684599 * 2 ^ 59
def prefixEnd_5684599 : Nat := 4983230072969 + 3 ^ 40 * 5684599 * 2
def baseEnd_5684599 : Nat := 2918931615067909713969511

theorem tailTrace_5684599 : CollatzResearch.WordTrace tailWord_5684599 prefixEnd_5684599 2918931615067909713969511 := by
  unfold tailWord_5684599
  simp only [CollatzResearch.WordTrace]
  refine ⟨207334358732676150060816851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138222905821784100040544567 207334358732676150060816851)
  ·
    refine ⟨311001538099014225091225277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207334358732676150060816851 311001538099014225091225277)
    ·
      refine ⟨116625576787130334409209479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 311001538099014225091225277 116625576787130334409209479)
      ·
        refine ⟨174938365180695501613814219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116625576787130334409209479 174938365180695501613814219)
        ·
          refine ⟨262407547771043252420721329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174938365180695501613814219 262407547771043252420721329)
          ·
            refine ⟨196805660828282439315540997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 262407547771043252420721329 196805660828282439315540997)
            ·
              refine ⟨36901061405302957371663937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 196805660828282439315540997 36901061405302957371663937)
              ·
                refine ⟨27675796053977218028747953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36901061405302957371663937 27675796053977218028747953)
                ·
                  refine ⟨20756847040482913521560965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27675796053977218028747953 20756847040482913521560965)
                  ·
                    refine ⟨3891908820090546285292681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20756847040482913521560965 3891908820090546285292681)
                    ·
                      refine ⟨2918931615067909713969511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3891908820090546285292681 2918931615067909713969511)
                      ·
                        rfl

theorem cell23_5684599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 4, 2, 2, 4, 2].length) (baseStart_5684599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5684599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5684599 prefixEnd_5684599 := by exact prefixLift 5684599
  have htrace : WordTrace (prefixWord ++ tailWord_5684599) baseStart_5684599 baseEnd_5684599 := by
    simpa [prefixWord, tailWord_5684599, baseEnd_5684599] using wordTrace_append hprefix tailTrace_5684599
  have hstable : (prefixWord ++ tailWord_5684599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5684599).length < 2 ^ (prefixWord ++ tailWord_5684599).sum := by decide
  have hdescent : baseEnd_5684599 < baseStart_5684599 := by decide
  rcases family_descends (prefixWord ++ tailWord_5684599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5684616 : List Nat := [2, 1, 3, 3, 1, 3, 1, 1, 2, 4, 2]
def baseStart_5684616 : Nat := 118140960795 + 5684616 * 2 ^ 59
def prefixEnd_5684616 : Nat := 4983230072969 + 3 ^ 40 * 5684616 * 2
def baseEnd_5684616 : Nat := 2918940344239036147456933

theorem tailTrace_5684616 : CollatzResearch.WordTrace tailWord_5684616 prefixEnd_5684616 2918940344239036147456933 := by
  unfold tailWord_5684616
  simp only [CollatzResearch.WordTrace]
  refine ⟨103667489386807280982092851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138223319182409707976123801 103667489386807280982092851)
  ·
    refine ⟨155501234080210921473139277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103667489386807280982092851 155501234080210921473139277)
    ·
      refine ⟨58312962780079095552427229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 155501234080210921473139277 58312962780079095552427229)
      ·
        refine ⟨21867361042529660832160211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58312962780079095552427229 21867361042529660832160211)
        ·
          refine ⟨32801041563794491248240317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21867361042529660832160211 32801041563794491248240317)
          ·
            refine ⟨12300390586422934218090119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32801041563794491248240317 12300390586422934218090119)
            ·
              refine ⟨18450585879634401327135179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12300390586422934218090119 18450585879634401327135179)
              ·
                refine ⟨27675878819451601990702769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18450585879634401327135179 27675878819451601990702769)
                ·
                  refine ⟨20756909114588701493027077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27675878819451601990702769 20756909114588701493027077)
                  ·
                    refine ⟨3891920458985381529942577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20756909114588701493027077 3891920458985381529942577)
                    ·
                      refine ⟨2918940344239036147456933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3891920458985381529942577 2918940344239036147456933)
                      ·
                        rfl

theorem cell23_5684616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 1, 1, 2, 4, 2].length) (baseStart_5684616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5684616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5684616 prefixEnd_5684616 := by exact prefixLift 5684616
  have htrace : WordTrace (prefixWord ++ tailWord_5684616) baseStart_5684616 baseEnd_5684616 := by
    simpa [prefixWord, tailWord_5684616, baseEnd_5684616] using wordTrace_append hprefix tailTrace_5684616
  have hstable : (prefixWord ++ tailWord_5684616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5684616).length < 2 ^ (prefixWord ++ tailWord_5684616).sum := by decide
  have hdescent : baseEnd_5684616 < baseStart_5684616 := by decide
  rcases family_descends (prefixWord ++ tailWord_5684616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5684717 : List Nat := [1, 5, 1, 3, 3, 1, 1, 1, 3, 1, 3]
def baseStart_5684717 : Nat := 118140960795 + 5684717 * 2 ^ 59
def prefixEnd_5684717 : Nat := 4983230072969 + 3 ^ 40 * 5684717 * 2
def baseEnd_5684717 : Nat := 2918992205785140252293969

theorem tailTrace_5684717 : CollatzResearch.WordTrace tailWord_5684717 prefixEnd_5684717 2918992205785140252293969 := by
  unfold tailWord_5684717
  simp only [CollatzResearch.WordTrace]
  refine ⟨207338662546248656213612405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138225775030832437475741603 207338662546248656213612405)
  ·
    refine ⟨19437999613710811520026163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 207338662546248656213612405 19437999613710811520026163)
    ·
      refine ⟨29156999420566217280039245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19437999613710811520026163 29156999420566217280039245)
      ·
        refine ⟨10933874782712331480014717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29156999420566217280039245 10933874782712331480014717)
        ·
          refine ⟨4100203043517124305005519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10933874782712331480014717 4100203043517124305005519)
          ·
            refine ⟨6150304565275686457508279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4100203043517124305005519 6150304565275686457508279)
            ·
              refine ⟨9225456847913529686262419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6150304565275686457508279 9225456847913529686262419)
              ·
                refine ⟨13838185271870294529393629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9225456847913529686262419 13838185271870294529393629)
                ·
                  refine ⟨5189319476951360448522611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13838185271870294529393629 5189319476951360448522611)
                  ·
                    refine ⟨7783979215427040672783917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5189319476951360448522611 7783979215427040672783917)
                    ·
                      refine ⟨2918992205785140252293969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7783979215427040672783917 2918992205785140252293969)
                      ·
                        rfl

theorem cell23_5684717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 1, 1, 3, 1, 3].length) (baseStart_5684717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5684717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5684717 prefixEnd_5684717 := by exact prefixLift 5684717
  have htrace : WordTrace (prefixWord ++ tailWord_5684717) baseStart_5684717 baseEnd_5684717 := by
    simpa [prefixWord, tailWord_5684717, baseEnd_5684717] using wordTrace_append hprefix tailTrace_5684717
  have hstable : (prefixWord ++ tailWord_5684717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5684717).length < 2 ^ (prefixWord ++ tailWord_5684717).sum := by decide
  have hdescent : baseEnd_5684717 < baseStart_5684717 := by decide
  rcases family_descends (prefixWord ++ tailWord_5684717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5684726 : List Nat := [5, 1, 1, 1, 2, 2, 2, 2, 1, 1, 5]
def baseStart_5684726 : Nat := 118140960795 + 5684726 * 2 ^ 59
def prefixEnd_5684726 : Nat := 4983230072969 + 3 ^ 40 * 5684726 * 2
def baseEnd_5684726 : Nat := 2918996827111030717081427

theorem tailTrace_5684726 : CollatzResearch.WordTrace tailWord_5684726 prefixEnd_5684726 2918996827111030717081427 := by
  unfold tailWord_5684726
  simp only [CollatzResearch.WordTrace]
  refine ⟨12958686925201003171918127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 138225993868810700500460021 12958686925201003171918127)
  ·
    refine ⟨19438030387801504757877191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12958686925201003171918127 19438030387801504757877191)
    ·
      refine ⟨29157045581702257136815787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19438030387801504757877191 29157045581702257136815787)
      ·
        refine ⟨43735568372553385705223681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29157045581702257136815787 43735568372553385705223681)
        ·
          refine ⟨32801676279415039278917761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43735568372553385705223681 32801676279415039278917761)
          ·
            refine ⟨24601257209561279459188321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32801676279415039278917761 24601257209561279459188321)
            ·
              refine ⟨18450942907170959594391241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24601257209561279459188321 18450942907170959594391241)
              ·
                refine ⟨13838207180378219695793431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18450942907170959594391241 13838207180378219695793431)
                ·
                  refine ⟨20757310770567329543690147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13838207180378219695793431 20757310770567329543690147)
                  ·
                    refine ⟨31135966155850994315535221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20757310770567329543690147 31135966155850994315535221)
                    ·
                      refine ⟨2918996827111030717081427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31135966155850994315535221 2918996827111030717081427)
                      ·
                        rfl

theorem cell23_5684726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 2, 1, 1, 5].length) (baseStart_5684726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5684726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5684726 prefixEnd_5684726 := by exact prefixLift 5684726
  have htrace : WordTrace (prefixWord ++ tailWord_5684726) baseStart_5684726 baseEnd_5684726 := by
    simpa [prefixWord, tailWord_5684726, baseEnd_5684726] using wordTrace_append hprefix tailTrace_5684726
  have hstable : (prefixWord ++ tailWord_5684726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5684726).length < 2 ^ (prefixWord ++ tailWord_5684726).sum := by decide
  have hdescent : baseEnd_5684726 < baseStart_5684726 := by decide
  rcases family_descends (prefixWord ++ tailWord_5684726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5684733 : List Nat := [1, 4, 1, 1, 1, 4, 4, 1, 2, 4]
def baseStart_5684733 : Nat := 118140960795 + 5684733 * 2 ^ 59
def prefixEnd_5684733 : Nat := 4983230072969 + 3 ^ 40 * 5684733 * 2
def baseEnd_5684733 : Nat := 973000140491870729897965

theorem tailTrace_5684733 : CollatzResearch.WordTrace tailWord_5684733 prefixEnd_5684733 973000140491870729897965 := by
  unfold tailWord_5684733
  simp only [CollatzResearch.WordTrace]
  refine ⟨207339246114190690946194853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138226164076127127297463235 207339246114190690946194853)
  ·
    refine ⟨38876108646410754552411535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 207339246114190690946194853 38876108646410754552411535)
    ·
      refine ⟨58314162969616131828617303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38876108646410754552411535 58314162969616131828617303)
      ·
        refine ⟨87471244454424197742925955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58314162969616131828617303 87471244454424197742925955)
        ·
          refine ⟨131206866681636296614388933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87471244454424197742925955 131206866681636296614388933)
          ·
            refine ⟨24601287502806805615197925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 131206866681636296614388933 24601287502806805615197925)
            ·
              refine ⟨4612741406776276052849611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24601287502806805615197925 4612741406776276052849611)
              ·
                refine ⟨6919112110164414079274417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4612741406776276052849611 6919112110164414079274417)
                ·
                  refine ⟨5189334082623310559455813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6919112110164414079274417 5189334082623310559455813)
                  ·
                    refine ⟨973000140491870729897965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5189334082623310559455813 973000140491870729897965)
                    ·
                      rfl

theorem cell23_5684733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 4, 1, 2, 4].length) (baseStart_5684733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5684733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5684733 prefixEnd_5684733 := by exact prefixLift 5684733
  have htrace : WordTrace (prefixWord ++ tailWord_5684733) baseStart_5684733 baseEnd_5684733 := by
    simpa [prefixWord, tailWord_5684733, baseEnd_5684733] using wordTrace_append hprefix tailTrace_5684733
  have hstable : (prefixWord ++ tailWord_5684733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5684733).length < 2 ^ (prefixWord ++ tailWord_5684733).sum := by decide
  have hdescent : baseEnd_5684733 < baseStart_5684733 := by decide
  rcases family_descends (prefixWord ++ tailWord_5684733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5684740 : List Nat := [2, 3, 2, 3, 2, 2, 1, 2, 1, 1, 4]
def baseStart_5684740 : Nat := 118140960795 + 5684740 * 2 ^ 59
def prefixEnd_5684740 : Nat := 4983230072969 + 3 ^ 40 * 5684740 * 2
def baseEnd_5684740 : Nat := 2919004015840193662306363

theorem tailTrace_5684740 : CollatzResearch.WordTrace tailWord_5684740 prefixEnd_5684740 2919004015840193662306363 := by
  unfold tailWord_5684740
  simp only [CollatzResearch.WordTrace]
  refine ⟨103669750712582665570849837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138226334283443554094466449 103669750712582665570849837)
  ·
    refine ⟨38876156517218499589068689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103669750712582665570849837 38876156517218499589068689)
    ·
      refine ⟨29157117387913874691801517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38876156517218499589068689 29157117387913874691801517)
      ·
        refine ⟨10933919020467703009425569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29157117387913874691801517 10933919020467703009425569)
        ·
          refine ⟨8200439265350777257069177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10933919020467703009425569 8200439265350777257069177)
          ·
            refine ⟨6150329449013082942801883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8200439265350777257069177 6150329449013082942801883)
            ·
              refine ⟨9225494173519624414202825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6150329449013082942801883 9225494173519624414202825)
              ·
                refine ⟨6919120630139718310652119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9225494173519624414202825 6919120630139718310652119)
                ·
                  refine ⟨10378680945209577465978179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6919120630139718310652119 10378680945209577465978179)
                  ·
                    refine ⟨15568021417814366198967269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10378680945209577465978179 15568021417814366198967269)
                    ·
                      refine ⟨2919004015840193662306363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15568021417814366198967269 2919004015840193662306363)
                      ·
                        rfl

theorem cell23_5684740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_5684740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5684740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5684740 prefixEnd_5684740 := by exact prefixLift 5684740
  have htrace : WordTrace (prefixWord ++ tailWord_5684740) baseStart_5684740 baseEnd_5684740 := by
    simpa [prefixWord, tailWord_5684740, baseEnd_5684740] using wordTrace_append hprefix tailTrace_5684740
  have hstable : (prefixWord ++ tailWord_5684740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5684740).length < 2 ^ (prefixWord ++ tailWord_5684740).sum := by decide
  have hdescent : baseEnd_5684740 < baseStart_5684740 := by decide
  rcases family_descends (prefixWord ++ tailWord_5684740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5684743 : List Nat := [1, 1, 4, 3, 2, 1, 3, 2, 1, 2, 3]
def baseStart_5684743 : Nat := 118140960795 + 5684743 * 2 ^ 59
def prefixEnd_5684743 : Nat := 4983230072969 + 3 ^ 40 * 5684743 * 2
def baseEnd_5684743 : Nat := 2919005556282157150568849

theorem tailTrace_5684743 : CollatzResearch.WordTrace tailWord_5684743 prefixEnd_5684743 2919005556282157150568849 := by
  unfold tailWord_5684743
  simp only [CollatzResearch.WordTrace]
  refine ⟨207339610844154462654058883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138226407229436308436039255 207339610844154462654058883)
  ·
    refine ⟨311009416266231693981088325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207339610844154462654058883 311009416266231693981088325)
    ·
      refine ⟨58314265549918442621454061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 311009416266231693981088325 58314265549918442621454061)
      ·
        refine ⟨21867849581219415983045273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58314265549918442621454061 21867849581219415983045273)
        ·
          refine ⟨16400887185914561987283955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21867849581219415983045273 16400887185914561987283955)
          ·
            refine ⟨24601330778871842980925933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16400887185914561987283955 24601330778871842980925933)
            ·
              refine ⟨9225499042076941117847225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24601330778871842980925933 9225499042076941117847225)
              ·
                refine ⟨6919124281557705838385419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9225499042076941117847225 6919124281557705838385419)
                ·
                  refine ⟨10378686422336558757578129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6919124281557705838385419 10378686422336558757578129)
                  ·
                    refine ⟨7784014816752419068183597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10378686422336558757578129 7784014816752419068183597)
                    ·
                      refine ⟨2919005556282157150568849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7784014816752419068183597 2919005556282157150568849)
                      ·
                        rfl

theorem cell23_5684743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 3, 2, 1, 2, 3].length) (baseStart_5684743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5684743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5684743 prefixEnd_5684743 := by exact prefixLift 5684743
  have htrace : WordTrace (prefixWord ++ tailWord_5684743) baseStart_5684743 baseEnd_5684743 := by
    simpa [prefixWord, tailWord_5684743, baseEnd_5684743] using wordTrace_append hprefix tailTrace_5684743
  have hstable : (prefixWord ++ tailWord_5684743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5684743).length < 2 ^ (prefixWord ++ tailWord_5684743).sum := by decide
  have hdescent : baseEnd_5684743 < baseStart_5684743 := by decide
  rcases family_descends (prefixWord ++ tailWord_5684743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5684760 : List Nat := [2, 1, 2, 3, 4, 1, 3, 1, 1, 2, 3]
def baseStart_5684760 : Nat := 118140960795 + 5684760 * 2 ^ 59
def prefixEnd_5684760 : Nat := 4983230072969 + 3 ^ 40 * 5684760 * 2
def baseEnd_5684760 : Nat := 2919014285453283584056271

theorem tailTrace_5684760 : CollatzResearch.WordTrace tailWord_5684760 prefixEnd_5684760 2919014285453283584056271 := by
  unfold tailWord_5684760
  simp only [CollatzResearch.WordTrace]
  refine ⟨103670115442546437278713867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138226820590061916371618489 103670115442546437278713867)
  ·
    refine ⟨155505173163819655918070801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103670115442546437278713867 155505173163819655918070801)
    ·
      refine ⟨116628879872864741938553101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155505173163819655918070801 116628879872864741938553101)
      ·
        refine ⟨43735829952324278226957413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116628879872864741938553101 43735829952324278226957413)
        ·
          refine ⟨8200468116060802167554515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43735829952324278226957413 8200468116060802167554515)
          ·
            refine ⟨12300702174091203251331773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8200468116060802167554515 12300702174091203251331773)
            ·
              refine ⟨4612763315284201219249415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12300702174091203251331773 4612763315284201219249415)
              ·
                refine ⟨6919144972926301828874123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4612763315284201219249415 6919144972926301828874123)
                ·
                  refine ⟨10378717459389452743311185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6919144972926301828874123 10378717459389452743311185)
                  ·
                    refine ⟨7784038094542089557483389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10378717459389452743311185 7784038094542089557483389)
                    ·
                      refine ⟨2919014285453283584056271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7784038094542089557483389 2919014285453283584056271)
                      ·
                        rfl

theorem cell23_5684760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 3, 1, 1, 2, 3].length) (baseStart_5684760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5684760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5684760 prefixEnd_5684760 := by exact prefixLift 5684760
  have htrace : WordTrace (prefixWord ++ tailWord_5684760) baseStart_5684760 baseEnd_5684760 := by
    simpa [prefixWord, tailWord_5684760, baseEnd_5684760] using wordTrace_append hprefix tailTrace_5684760
  have hstable : (prefixWord ++ tailWord_5684760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5684760).length < 2 ^ (prefixWord ++ tailWord_5684760).sum := by decide
  have hdescent : baseEnd_5684760 < baseStart_5684760 := by decide
  rcases family_descends (prefixWord ++ tailWord_5684760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5684789 : List Nat := [1, 3, 3, 1, 1, 3, 1, 1, 1, 8]
def baseStart_5684789 : Nat := 118140960795 + 5684789 * 2 ^ 59
def prefixEnd_5684789 : Nat := 4983230072969 + 3 ^ 40 * 5684789 * 2
def baseEnd_5684789 : Nat := 973009725464087990197879

theorem tailTrace_5684789 : CollatzResearch.WordTrace tailWord_5684789 prefixEnd_5684789 973009725464087990197879 := by
  unfold tailWord_5684789
  simp only [CollatzResearch.WordTrace]
  refine ⟨207341288601987812510233421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138227525734658541673488947 207341288601987812510233421)
  ·
    refine ⟨77752983225745429691337533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 207341288601987812510233421 77752983225745429691337533)
    ·
      refine ⟨29157368709654536134251575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77752983225745429691337533 29157368709654536134251575)
      ·
        refine ⟨43736053064481804201377363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29157368709654536134251575 43736053064481804201377363)
        ·
          refine ⟨65604079596722706302066045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43736053064481804201377363 65604079596722706302066045)
          ·
            refine ⟨24601529848771014863274767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65604079596722706302066045 24601529848771014863274767)
            ·
              refine ⟨36902294773156522294912151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24601529848771014863274767 36902294773156522294912151)
              ·
                refine ⟨55353442159734783442368227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36902294773156522294912151 55353442159734783442368227)
                ·
                  refine ⟨83030163239602175163552341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55353442159734783442368227 83030163239602175163552341)
                  ·
                    refine ⟨973009725464087990197879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 83030163239602175163552341 973009725464087990197879)
                    ·
                      rfl

theorem cell23_5684789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 1, 1, 8].length) (baseStart_5684789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5684789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5684789 prefixEnd_5684789 := by exact prefixLift 5684789
  have htrace : WordTrace (prefixWord ++ tailWord_5684789) baseStart_5684789 baseEnd_5684789 := by
    simpa [prefixWord, tailWord_5684789, baseEnd_5684789] using wordTrace_append hprefix tailTrace_5684789
  have hstable : (prefixWord ++ tailWord_5684789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5684789).length < 2 ^ (prefixWord ++ tailWord_5684789).sum := by decide
  have hdescent : baseEnd_5684789 < baseStart_5684789 := by decide
  rcases family_descends (prefixWord ++ tailWord_5684789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5684790 : List Nat := [5, 1, 2, 1, 3, 1, 2, 1, 1, 3, 3]
def baseStart_5684790 : Nat := 118140960795 + 5684790 * 2 ^ 59
def prefixEnd_5684790 : Nat := 4983230072969 + 3 ^ 40 * 5684790 * 2
def baseEnd_5684790 : Nat := 2919029689872918466681133

theorem tailTrace_5684790 : CollatzResearch.WordTrace tailWord_5684790 prefixEnd_5684790 2919029689872918466681133 := by
  unfold tailWord_5684790
  simp only [CollatzResearch.WordTrace]
  refine ⟨12958832817186511855063739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 138227550049989459787346549 12958832817186511855063739)
  ·
    refine ⟨19438249225779767782595609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12958832817186511855063739 19438249225779767782595609)
    ·
      refine ⟨14578686919334825836946707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19438249225779767782595609 14578686919334825836946707)
      ·
        refine ⟨21868030379002238755420061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14578686919334825836946707 21868030379002238755420061)
        ·
          refine ⟨8200511392125839533282523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21868030379002238755420061 8200511392125839533282523)
          ·
            refine ⟨12300767088188759299923785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8200511392125839533282523 12300767088188759299923785)
            ·
              refine ⟨9225575316141569474942839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12300767088188759299923785 9225575316141569474942839)
              ·
                refine ⟨13838362974212354212414259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9225575316141569474942839 13838362974212354212414259)
                ·
                  refine ⟨20757544461318531318621389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13838362974212354212414259 20757544461318531318621389)
                  ·
                    refine ⟨7784079172994449244483021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20757544461318531318621389 7784079172994449244483021)
                    ·
                      refine ⟨2919029689872918466681133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7784079172994449244483021 2919029689872918466681133)
                      ·
                        rfl

theorem cell23_5684790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 2, 1, 1, 3, 3].length) (baseStart_5684790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5684790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5684790 prefixEnd_5684790 := by exact prefixLift 5684790
  have htrace : WordTrace (prefixWord ++ tailWord_5684790) baseStart_5684790 baseEnd_5684790 := by
    simpa [prefixWord, tailWord_5684790, baseEnd_5684790] using wordTrace_append hprefix tailTrace_5684790
  have hstable : (prefixWord ++ tailWord_5684790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5684790).length < 2 ^ (prefixWord ++ tailWord_5684790).sum := by decide
  have hdescent : baseEnd_5684790 < baseStart_5684790 := by decide
  rcases family_descends (prefixWord ++ tailWord_5684790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5684836 : List Nat := [2, 3, 1, 1, 2, 4, 2, 1, 7]
def baseStart_5684836 : Nat := 118140960795 + 5684836 * 2 ^ 59
def prefixEnd_5684836 : Nat := 4983230072969 + 3 ^ 40 * 5684836 * 2
def baseEnd_5684836 : Nat := 324339256664780587411769

theorem tailTrace_5684836 : CollatzResearch.WordTrace tailWord_5684836 prefixEnd_5684836 324339256664780587411769 := by
  unfold tailWord_5684836
  simp only [CollatzResearch.WordTrace]
  refine ⟨103671501416408769768597181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138228668555211693024796241 103671501416408769768597181)
  ·
    refine ⟨38876813031153288663223943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103671501416408769768597181 38876813031153288663223943)
    ·
      refine ⟨58315219546729932994835915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38876813031153288663223943 58315219546729932994835915)
      ·
        refine ⟨87472829320094899492253873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58315219546729932994835915 87472829320094899492253873)
        ·
          refine ⟨65604621990071174619190405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87472829320094899492253873 65604621990071174619190405)
          ·
            refine ⟨12300866623138345241098201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65604621990071174619190405 12300866623138345241098201)
            ·
              refine ⟨9225649967353758930823651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12300866623138345241098201 9225649967353758930823651)
              ·
                refine ⟨13838474951030638396235477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9225649967353758930823651 13838474951030638396235477)
                ·
                  refine ⟨324339256664780587411769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13838474951030638396235477 324339256664780587411769)
                  ·
                    rfl

theorem cell23_5684836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 2, 1, 7].length) (baseStart_5684836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5684836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5684836 prefixEnd_5684836 := by exact prefixLift 5684836
  have htrace : WordTrace (prefixWord ++ tailWord_5684836) baseStart_5684836 baseEnd_5684836 := by
    simpa [prefixWord, tailWord_5684836, baseEnd_5684836] using wordTrace_append hprefix tailTrace_5684836
  have hstable : (prefixWord ++ tailWord_5684836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5684836).length < 2 ^ (prefixWord ++ tailWord_5684836).sum := by decide
  have hdescent : baseEnd_5684836 < baseStart_5684836 := by decide
  rcases family_descends (prefixWord ++ tailWord_5684836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5684889 : List Nat := [1, 2, 1, 2, 1, 2, 2, 1, 1, 5, 5]
def baseStart_5684889 : Nat := 118140960795 + 5684889 * 2 ^ 59
def prefixEnd_5684889 : Nat := 4983230072969 + 3 ^ 40 * 5684889 * 2
def baseEnd_5684889 : Nat := 2919080524457713579343177

theorem tailTrace_5684889 : CollatzResearch.WordTrace tailWord_5684889 prefixEnd_5684889 2919080524457713579343177 := by
  unfold tailWord_5684889
  simp only [CollatzResearch.WordTrace]
  refine ⟨207344935901625529588873721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138229957267750353059249147 207344935901625529588873721)
  ·
    refine ⟨155508701926219147191655291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207344935901625529588873721 155508701926219147191655291)
    ·
      refine ⟨233263052889328720787482937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155508701926219147191655291 233263052889328720787482937)
      ·
        refine ⟨174947289666996540590612203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 233263052889328720787482937 174947289666996540590612203)
        ·
          refine ⟨262420934500494810885918305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174947289666996540590612203 262420934500494810885918305)
          ·
            refine ⟨196815700875371108164438729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 262420934500494810885918305 196815700875371108164438729)
            ·
              refine ⟨147611775656528331123329047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 196815700875371108164438729 147611775656528331123329047)
              ·
                refine ⟨221417663484792496684993571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 147611775656528331123329047 221417663484792496684993571)
                ·
                  refine ⟨332126495227188745027490357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 221417663484792496684993571 332126495227188745027490357)
                  ·
                    refine ⟨31136858927548944846327221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 332126495227188745027490357 31136858927548944846327221)
                    ·
                      refine ⟨2919080524457713579343177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31136858927548944846327221 2919080524457713579343177)
                      ·
                        rfl

theorem cell23_5684889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 5, 5].length) (baseStart_5684889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5684889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5684889 prefixEnd_5684889 := by exact prefixLift 5684889
  have htrace : WordTrace (prefixWord ++ tailWord_5684889) baseStart_5684889 baseEnd_5684889 := by
    simpa [prefixWord, tailWord_5684889, baseEnd_5684889] using wordTrace_append hprefix tailTrace_5684889
  have hstable : (prefixWord ++ tailWord_5684889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5684889).length < 2 ^ (prefixWord ++ tailWord_5684889).sum := by decide
  have hdescent : baseEnd_5684889 < baseStart_5684889 := by decide
  rcases family_descends (prefixWord ++ tailWord_5684889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5684898 : List Nat := [3, 3, 1, 4, 2, 1, 2, 1, 2, 2, 2]
def baseStart_5684898 : Nat := 118140960795 + 5684898 * 2 ^ 59
def prefixEnd_5684898 : Nat := 4983230072969 + 3 ^ 40 * 5684898 * 2
def baseEnd_5684898 : Nat := 2919085145783604044130637

theorem tailTrace_5684898 : CollatzResearch.WordTrace tailWord_5684898 prefixEnd_5684898 2919085145783604044130637 := by
  unfold tailWord_5684898
  simp only [CollatzResearch.WordTrace]
  refine ⟨51836316039648231031487837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138230176105728616083967565 51836316039648231031487837)
  ·
    refine ⟨19438618514868086636807939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51836316039648231031487837 19438618514868086636807939)
    ·
      refine ⟨29157927772302129955211909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19438618514868086636807939 29157927772302129955211909)
      ·
        refine ⟨5467111457306649366602233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29157927772302129955211909 5467111457306649366602233)
        ·
          refine ⟨4100333592979987024951675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5467111457306649366602233 4100333592979987024951675)
          ·
            refine ⟨6150500389469980537427513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4100333592979987024951675 6150500389469980537427513)
            ·
              refine ⟨4612875292102485403070635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6150500389469980537427513 4612875292102485403070635)
              ·
                refine ⟨6919312938153728104605953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4612875292102485403070635 6919312938153728104605953)
                ·
                  refine ⟨5189484703615296078454465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6919312938153728104605953 5189484703615296078454465)
                  ·
                    refine ⟨3892113527711472058840849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5189484703615296078454465 3892113527711472058840849)
                    ·
                      refine ⟨2919085145783604044130637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3892113527711472058840849 2919085145783604044130637)
                      ·
                        rfl

theorem cell23_5684898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_5684898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5684898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5684898 prefixEnd_5684898 := by exact prefixLift 5684898
  have htrace : WordTrace (prefixWord ++ tailWord_5684898) baseStart_5684898 baseEnd_5684898 := by
    simpa [prefixWord, tailWord_5684898, baseEnd_5684898] using wordTrace_append hprefix tailTrace_5684898
  have hstable : (prefixWord ++ tailWord_5684898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5684898).length < 2 ^ (prefixWord ++ tailWord_5684898).sum := by decide
  have hdescent : baseEnd_5684898 < baseStart_5684898 := by decide
  rcases family_descends (prefixWord ++ tailWord_5684898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5684973 : List Nat := [1, 5, 1, 2, 1, 2, 2, 1, 3, 5]
def baseStart_5684973 : Nat := 118140960795 + 5684973 * 2 ^ 59
def prefixEnd_5684973 : Nat := 4983230072969 + 3 ^ 40 * 5684973 * 2
def baseEnd_5684973 : Nat := 973041218944230416897597

theorem tailTrace_5684973 : CollatzResearch.WordTrace tailWord_5684973 prefixEnd_5684973 973041218944230416897597 := by
  unfold tailWord_5684973
  simp only [CollatzResearch.WordTrace]
  refine ⟨207347999633321211934931573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138231999755547474623287715 207347999633321211934931573)
  ·
    refine ⟨19438874965623863618899835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 207347999633321211934931573 19438874965623863618899835)
    ·
      refine ⟨29158312448435795428349753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19438874965623863618899835 29158312448435795428349753)
      ·
        refine ⟨21868734336326846571262315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29158312448435795428349753 21868734336326846571262315)
        ·
          refine ⟨32803101504490269856893473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21868734336326846571262315 32803101504490269856893473)
          ·
            refine ⟨24602326128367702392670105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32803101504490269856893473 24602326128367702392670105)
            ·
              refine ⟨18451744596275776794502579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24602326128367702392670105 18451744596275776794502579)
              ·
                refine ⟨27677616894413665191753869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18451744596275776794502579 27677616894413665191753869)
                ·
                  refine ⟨10379106335405124446907701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27677616894413665191753869 10379106335405124446907701)
                  ·
                    refine ⟨973041218944230416897597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10379106335405124446907701 973041218944230416897597)
                    ·
                      rfl

theorem cell23_5684973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 1, 3, 5].length) (baseStart_5684973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5684973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5684973 prefixEnd_5684973 := by exact prefixLift 5684973
  have htrace : WordTrace (prefixWord ++ tailWord_5684973) baseStart_5684973 baseEnd_5684973 := by
    simpa [prefixWord, tailWord_5684973, baseEnd_5684973] using wordTrace_append hprefix tailTrace_5684973
  have hstable : (prefixWord ++ tailWord_5684973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5684973).length < 2 ^ (prefixWord ++ tailWord_5684973).sum := by decide
  have hdescent : baseEnd_5684973 < baseStart_5684973 := by decide
  rcases family_descends (prefixWord ++ tailWord_5684973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5684998 : List Nat := [6, 2, 2, 1, 1, 1, 2, 1, 3, 4]
def baseStart_5684998 : Nat := 118140960795 + 5684998 * 2 ^ 59
def prefixEnd_5684998 : Nat := 4983230072969 + 3 ^ 40 * 5684998 * 2
def baseEnd_5684998 : Nat := 973045497949684550960059

theorem tailTrace_5684998 : CollatzResearch.WordTrace tailWord_5684998 prefixEnd_5684998 973045497949684550960059 := by
  unfold tailWord_5684998
  simp only [CollatzResearch.WordTrace]
  refine ⟨6479653483069707537643489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 138232607638820427469727765 6479653483069707537643489)
  ·
    refine ⟨4859740112302280653232617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6479653483069707537643489 4859740112302280653232617)
    ·
      refine ⟨3644805084226710489924463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4859740112302280653232617 3644805084226710489924463)
      ·
        refine ⟨5467207626340065734886695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3644805084226710489924463 5467207626340065734886695)
        ·
          refine ⟨8200811439510098602330043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5467207626340065734886695 8200811439510098602330043)
          ·
            refine ⟨12301217159265147903495065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8200811439510098602330043 12301217159265147903495065)
            ·
              refine ⟨9225912869448860927621299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12301217159265147903495065 9225912869448860927621299)
              ·
                refine ⟨13838869304173291391431949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9225912869448860927621299 13838869304173291391431949)
                ·
                  refine ⟨5189575989064984271786981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13838869304173291391431949 5189575989064984271786981)
                  ·
                    refine ⟨973045497949684550960059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5189575989064984271786981 973045497949684550960059)
                    ·
                      rfl

theorem cell23_5684998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_5684998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5684998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5684998 prefixEnd_5684998 := by exact prefixLift 5684998
  have htrace : WordTrace (prefixWord ++ tailWord_5684998) baseStart_5684998 baseEnd_5684998 := by
    simpa [prefixWord, tailWord_5684998, baseEnd_5684998] using wordTrace_append hprefix tailTrace_5684998
  have hstable : (prefixWord ++ tailWord_5684998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5684998).length < 2 ^ (prefixWord ++ tailWord_5684998).sum := by decide
  have hdescent : baseEnd_5684998 < baseStart_5684998 := by decide
  rcases family_descends (prefixWord ++ tailWord_5684998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5685013 : List Nat := [1, 3, 2, 1, 2, 4, 1, 2, 1, 1, 5]
def baseStart_5685013 : Nat := 118140960795 + 5685013 * 2 ^ 59
def prefixEnd_5685013 : Nat := 4983230072969 + 3 ^ 40 * 5685013 * 2
def baseEnd_5685013 : Nat := 2919144196058871094192607

theorem tailTrace_5685013 : CollatzResearch.WordTrace tailWord_5685013 prefixEnd_5685013 2919144196058871094192607 := by
  unfold tailWord_5685013
  simp only [CollatzResearch.WordTrace]
  refine ⟨207349458553176298766387693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138232972368784199177591795 207349458553176298766387693)
  ·
    refine ⟨77756046957441112037395385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 207349458553176298766387693 77756046957441112037395385)
    ·
      refine ⟨58317035218080834028046539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77756046957441112037395385 58317035218080834028046539)
      ·
        refine ⟨87475552827121251042069809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58317035218080834028046539 87475552827121251042069809)
        ·
          refine ⟨65606664620340938281552357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87475552827121251042069809 65606664620340938281552357)
          ·
            refine ⟨12301249616313925927791067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65606664620340938281552357 12301249616313925927791067)
            ·
              refine ⟨18451874424470888891686601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12301249616313925927791067 18451874424470888891686601)
              ·
                refine ⟨13838905818353166668764951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18451874424470888891686601 13838905818353166668764951)
                ·
                  refine ⟨20758358727529750003147427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13838905818353166668764951 20758358727529750003147427)
                  ·
                    refine ⟨31137538091294625004721141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20758358727529750003147427 31137538091294625004721141)
                    ·
                      refine ⟨2919144196058871094192607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31137538091294625004721141 2919144196058871094192607)
                      ·
                        rfl

theorem cell23_5685013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 2, 1, 1, 5].length) (baseStart_5685013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5685013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5685013 prefixEnd_5685013 := by exact prefixLift 5685013
  have htrace : WordTrace (prefixWord ++ tailWord_5685013) baseStart_5685013 baseEnd_5685013 := by
    simpa [prefixWord, tailWord_5685013, baseEnd_5685013] using wordTrace_append hprefix tailTrace_5685013
  have hstable : (prefixWord ++ tailWord_5685013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5685013).length < 2 ^ (prefixWord ++ tailWord_5685013).sum := by decide
  have hdescent : baseEnd_5685013 < baseStart_5685013 := by decide
  rcases family_descends (prefixWord ++ tailWord_5685013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5685038 : List Nat := [4, 1, 3, 2, 3, 1, 1, 3, 1, 1, 3]
def baseStart_5685038 : Nat := 118140960795 + 5685038 * 2 ^ 59
def prefixEnd_5685038 : Nat := 4983230072969 + 3 ^ 40 * 5685038 * 2
def baseEnd_5685038 : Nat := 2919157033075233496379993

theorem tailTrace_5685038 : CollatzResearch.WordTrace tailWord_5685038 prefixEnd_5685038 2919157033075233496379993 := by
  unfold tailWord_5685038
  simp only [CollatzResearch.WordTrace]
  refine ⟨25918796297260716004505971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138233580252057152024031845 25918796297260716004505971)
  ·
    refine ⟨38878194445891074006758957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25918796297260716004505971 38878194445891074006758957)
    ·
      refine ⟨14579322917209152752534609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38878194445891074006758957 14579322917209152752534609)
      ·
        refine ⟨10934492187906864564400957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14579322917209152752534609 10934492187906864564400957)
        ·
          refine ⟨4100434570465074211650359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10934492187906864564400957 4100434570465074211650359)
          ·
            refine ⟨6150651855697611317475539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4100434570465074211650359 6150651855697611317475539)
            ·
              refine ⟨9225977783546416976213309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6150651855697611317475539 9225977783546416976213309)
              ·
                refine ⟨3459741668829906366079991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9225977783546416976213309 3459741668829906366079991)
                ·
                  refine ⟨5189612503244859549119987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3459741668829906366079991 5189612503244859549119987)
                  ·
                    refine ⟨7784418754867289323679981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5189612503244859549119987 7784418754867289323679981)
                    ·
                      refine ⟨2919157033075233496379993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7784418754867289323679981 2919157033075233496379993)
                      ·
                        rfl

theorem cell23_5685038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 1, 3, 1, 1, 3].length) (baseStart_5685038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5685038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5685038 prefixEnd_5685038 := by exact prefixLift 5685038
  have htrace : WordTrace (prefixWord ++ tailWord_5685038) baseStart_5685038 baseEnd_5685038 := by
    simpa [prefixWord, tailWord_5685038, baseEnd_5685038] using wordTrace_append hprefix tailTrace_5685038
  have hstable : (prefixWord ++ tailWord_5685038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5685038).length < 2 ^ (prefixWord ++ tailWord_5685038).sum := by decide
  have hdescent : baseEnd_5685038 < baseStart_5685038 := by decide
  rcases family_descends (prefixWord ++ tailWord_5685038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5685077 : List Nat := [1, 3, 2, 2, 2, 3, 1, 3, 2, 1, 3]
def baseStart_5685077 : Nat := 118140960795 + 5685077 * 2 ^ 59
def prefixEnd_5685077 : Nat := 4983230072969 + 3 ^ 40 * 5685077 * 2
def baseEnd_5685077 : Nat := 2919177058820758843792313

theorem tailTrace_5685077 : CollatzResearch.WordTrace tailWord_5685077 prefixEnd_5685077 2919177058820758843792313 := by
  unfold tailWord_5685077
  simp only [CollatzResearch.WordTrace]
  refine ⟨207351792824944437696717485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138234528549962958464478323 207351792824944437696717485)
  ·
    refine ⟨77756922309354164136269057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 207351792824944437696717485 77756922309354164136269057)
    ·
      refine ⟨58317691732015623102201793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77756922309354164136269057 58317691732015623102201793)
      ·
        refine ⟨43738268799011717326651345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58317691732015623102201793 43738268799011717326651345)
        ·
          refine ⟨32803701599258787994988509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43738268799011717326651345 32803701599258787994988509)
          ·
            refine ⟨12301388099722045498120691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32803701599258787994988509 12301388099722045498120691)
            ·
              refine ⟨18452082149583068247181037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12301388099722045498120691 18452082149583068247181037)
              ·
                refine ⟨6919530806093650592692889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18452082149583068247181037 6919530806093650592692889)
                ·
                  refine ⟨5189648104570237944519667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6919530806093650592692889 5189648104570237944519667)
                  ·
                    refine ⟨7784472156855356916779501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5189648104570237944519667 7784472156855356916779501)
                    ·
                      refine ⟨2919177058820758843792313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7784472156855356916779501 2919177058820758843792313)
                      ·
                        rfl

theorem cell23_5685077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 3, 2, 1, 3].length) (baseStart_5685077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5685077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5685077 prefixEnd_5685077 := by exact prefixLift 5685077
  have htrace : WordTrace (prefixWord ++ tailWord_5685077) baseStart_5685077 baseEnd_5685077 := by
    simpa [prefixWord, tailWord_5685077, baseEnd_5685077] using wordTrace_append hprefix tailTrace_5685077
  have hstable : (prefixWord ++ tailWord_5685077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5685077).length < 2 ^ (prefixWord ++ tailWord_5685077).sum := by decide
  have hdescent : baseEnd_5685077 < baseStart_5685077 := by decide
  rcases family_descends (prefixWord ++ tailWord_5685077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5685083 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 3, 10, 2]
def baseStart_5685083 : Nat := 118140960795 + 5685083 * 2 ^ 59
def prefixEnd_5685083 : Nat := 4983230072969 + 3 ^ 40 * 5685083 * 2
def baseEnd_5685083 : Nat := 2919180139704685820317285

theorem tailTrace_5685083 : CollatzResearch.WordTrace tailWord_5685083 prefixEnd_5685083 2919180139704685820317285 := by
  unfold tailWord_5685083
  simp only [CollatzResearch.WordTrace]
  refine ⟨207352011662922700721435903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138234674441948467147623935 207352011662922700721435903)
  ·
    refine ⟨311028017494384051082153855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207352011662922700721435903 311028017494384051082153855)
    ·
      refine ⟨466542026241576076623230783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 311028017494384051082153855 466542026241576076623230783)
      ·
        refine ⟨699813039362364114934846175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 466542026241576076623230783 699813039362364114934846175)
        ·
          refine ⟨1049719559043546172402269263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 699813039362364114934846175 1049719559043546172402269263)
          ·
            refine ⟨1574579338565319258603403895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1049719559043546172402269263 1574579338565319258603403895)
            ·
              refine ⟨2361869007847978887905105843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1574579338565319258603403895 2361869007847978887905105843)
              ·
                refine ⟨3542803511771968331857658765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2361869007847978887905105843 3542803511771968331857658765)
                ·
                  refine ⟨1328551316914488124446622037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3542803511771968331857658765 1328551316914488124446622037)
                  ·
                    refine ⟨3892240186272914427089713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 1328551316914488124446622037 3892240186272914427089713)
                    ·
                      refine ⟨2919180139704685820317285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3892240186272914427089713 2919180139704685820317285)
                      ·
                        rfl

theorem cell23_5685083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 10, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 10, 2].length) (baseStart_5685083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5685083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5685083 prefixEnd_5685083 := by exact prefixLift 5685083
  have htrace : WordTrace (prefixWord ++ tailWord_5685083) baseStart_5685083 baseEnd_5685083 := by
    simpa [prefixWord, tailWord_5685083, baseEnd_5685083] using wordTrace_append hprefix tailTrace_5685083
  have hstable : (prefixWord ++ tailWord_5685083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5685083).length < 2 ^ (prefixWord ++ tailWord_5685083).sum := by decide
  have hdescent : baseEnd_5685083 < baseStart_5685083 := by decide
  rcases family_descends (prefixWord ++ tailWord_5685083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5685087 : List Nat := [1, 1, 2, 3, 1, 4, 3, 2, 1, 3, 2]
def baseStart_5685087 : Nat := 118140960795 + 5685087 * 2 ^ 59
def prefixEnd_5685087 : Nat := 4983230072969 + 3 ^ 40 * 5685087 * 2
def baseEnd_5685087 : Nat := 2919182193627303804667267

theorem tailTrace_5685087 : CollatzResearch.WordTrace tailWord_5685087 prefixEnd_5685087 2919182193627303804667267 := by
  unfold tailWord_5685087
  simp only [CollatzResearch.WordTrace]
  refine ⟨207352157554908209404581515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138234771703272139603054343 207352157554908209404581515)
  ·
    refine ⟨311028236332362314106872273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207352157554908209404581515 311028236332362314106872273)
    ·
      refine ⟨233271177249271735580154205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 311028236332362314106872273 233271177249271735580154205)
      ·
        refine ⟨87476691468476900842557827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 233271177249271735580154205 87476691468476900842557827)
        ·
          refine ⟨131215037202715351263836741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87476691468476900842557827 131215037202715351263836741)
          ·
            refine ⟨24602819475509128361969389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 131215037202715351263836741 24602819475509128361969389)
            ·
              refine ⟨9226057303315923135738521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24602819475509128361969389 9226057303315923135738521)
              ·
                refine ⟨6919542977486942351803891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9226057303315923135738521 6919542977486942351803891)
                ·
                  refine ⟨10379314466230413527705837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6919542977486942351803891 10379314466230413527705837)
                  ·
                    refine ⟨3892242924836405072889689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10379314466230413527705837 3892242924836405072889689)
                    ·
                      refine ⟨2919182193627303804667267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3892242924836405072889689 2919182193627303804667267)
                      ·
                        rfl

theorem cell23_5685087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 3, 2, 1, 3, 2].length) (baseStart_5685087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5685087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5685087 prefixEnd_5685087 := by exact prefixLift 5685087
  have htrace : WordTrace (prefixWord ++ tailWord_5685087) baseStart_5685087 baseEnd_5685087 := by
    simpa [prefixWord, tailWord_5685087, baseEnd_5685087] using wordTrace_append hprefix tailTrace_5685087
  have hstable : (prefixWord ++ tailWord_5685087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5685087).length < 2 ^ (prefixWord ++ tailWord_5685087).sum := by decide
  have hdescent : baseEnd_5685087 < baseStart_5685087 := by decide
  rcases family_descends (prefixWord ++ tailWord_5685087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5685100 : List Nat := [2, 2, 1, 1, 4, 2, 1, 1, 3, 4, 2]
def baseStart_5685100 : Nat := 118140960795 + 5685100 * 2 ^ 59
def prefixEnd_5685100 : Nat := 4983230072969 + 3 ^ 40 * 5685100 * 2
def baseEnd_5685100 : Nat := 2919188868875812253804707

theorem tailTrace_5685100 : CollatzResearch.WordTrace tailWord_5685100 prefixEnd_5685100 2919188868875812253804707 := by
  unfold tailWord_5685100
  simp only [CollatzResearch.WordTrace]
  refine ⟨103676315851930556312402377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138235087802574075083203169 103676315851930556312402377)
  ·
    refine ⟨77757236888947917234301783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103676315851930556312402377 77757236888947917234301783)
    ·
      refine ⟨116635855333421875851452675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77757236888947917234301783 116635855333421875851452675)
      ·
        refine ⟨174953783000132813777179013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116635855333421875851452675 174953783000132813777179013)
        ·
          refine ⟨32803834312524902583221065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 174953783000132813777179013 32803834312524902583221065)
          ·
            refine ⟨24602875734393676937415799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32803834312524902583221065 24602875734393676937415799)
            ·
              refine ⟨36904313601590515406123699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24602875734393676937415799 36904313601590515406123699)
              ·
                refine ⟨55356470402385773109185549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36904313601590515406123699 55356470402385773109185549)
                ·
                  refine ⟨20758676400894664915944581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55356470402385773109185549 20758676400894664915944581)
                  ·
                    refine ⟨3892251825167749671739609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20758676400894664915944581 3892251825167749671739609)
                    ·
                      refine ⟨2919188868875812253804707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3892251825167749671739609 2919188868875812253804707)
                      ·
                        rfl

theorem cell23_5685100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 4, 2].length) (baseStart_5685100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5685100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5685100 prefixEnd_5685100 := by exact prefixLift 5685100
  have htrace : WordTrace (prefixWord ++ tailWord_5685100) baseStart_5685100 baseEnd_5685100 := by
    simpa [prefixWord, tailWord_5685100, baseEnd_5685100] using wordTrace_append hprefix tailTrace_5685100
  have hstable : (prefixWord ++ tailWord_5685100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5685100).length < 2 ^ (prefixWord ++ tailWord_5685100).sum := by decide
  have hdescent : baseEnd_5685100 < baseStart_5685100 := by decide
  rcases family_descends (prefixWord ++ tailWord_5685100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5685113 : List Nat := [1, 2, 1, 3, 2, 2, 2, 2, 2, 2, 4]
def baseStart_5685113 : Nat := 118140960795 + 5685113 * 2 ^ 59
def prefixEnd_5685113 : Nat := 4983230072969 + 3 ^ 40 * 5685113 * 2
def baseEnd_5685113 : Nat := 2919195544124320702942147

theorem tailTrace_5685113 : CollatzResearch.WordTrace tailWord_5685113 prefixEnd_5685113 2919195544124320702942147 := by
  unfold tailWord_5685113
  simp only [CollatzResearch.WordTrace]
  refine ⟨207353105852814015845027993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138235403901876010563351995 207353105852814015845027993)
  ·
    refine ⟨155514829389610511883770995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207353105852814015845027993 155514829389610511883770995)
    ·
      refine ⟨233272244084415767825656493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155514829389610511883770995 233272244084415767825656493)
      ·
        refine ⟨87477091531655912934621185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 233272244084415767825656493 87477091531655912934621185)
        ·
          refine ⟨65607818648741934700965889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87477091531655912934621185 65607818648741934700965889)
          ·
            refine ⟨49205863986556451025724417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65607818648741934700965889 49205863986556451025724417)
            ·
              refine ⟨36904397989917338269293313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49205863986556451025724417 36904397989917338269293313)
              ·
                refine ⟨27678298492438003701969985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36904397989917338269293313 27678298492438003701969985)
                ·
                  refine ⟨20758723869328502776477489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27678298492438003701969985 20758723869328502776477489)
                  ·
                    refine ⟨15569042901996377082358117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20758723869328502776477489 15569042901996377082358117)
                    ·
                      refine ⟨2919195544124320702942147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15569042901996377082358117 2919195544124320702942147)
                      ·
                        rfl

theorem cell23_5685113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 2, 2, 2, 4].length) (baseStart_5685113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5685113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5685113 prefixEnd_5685113 := by exact prefixLift 5685113
  have htrace : WordTrace (prefixWord ++ tailWord_5685113) baseStart_5685113 baseEnd_5685113 := by
    simpa [prefixWord, tailWord_5685113, baseEnd_5685113] using wordTrace_append hprefix tailTrace_5685113
  have hstable : (prefixWord ++ tailWord_5685113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5685113).length < 2 ^ (prefixWord ++ tailWord_5685113).sum := by decide
  have hdescent : baseEnd_5685113 < baseStart_5685113 := by decide
  rcases family_descends (prefixWord ++ tailWord_5685113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5685140 : List Nat := [2, 4, 2, 1, 1, 3, 1, 2, 7]
def baseStart_5685140 : Nat := 118140960795 + 5685140 * 2 ^ 59
def prefixEnd_5685140 : Nat := 4983230072969 + 3 ^ 40 * 5685140 * 2
def baseEnd_5685140 : Nat := 324356600900221344144947

theorem tailTrace_5685140 : CollatzResearch.WordTrace tailWord_5685140 prefixEnd_5685140 324356600900221344144947 := by
  unfold tailWord_5685140
  simp only [CollatzResearch.WordTrace]
  refine ⟨103677045311858099728130437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138236060415810799637507249 103677045311858099728130437)
  ·
    refine ⟨19439445995973393699024457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103677045311858099728130437 19439445995973393699024457)
    ·
      refine ⟨14579584496980045274268343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19439445995973393699024457 14579584496980045274268343)
      ·
        refine ⟨21869376745470067911402515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14579584496980045274268343 21869376745470067911402515)
        ·
          refine ⟨32804065118205101867103773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21869376745470067911402515 32804065118205101867103773)
          ·
            refine ⟨12301524419326913200163915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32804065118205101867103773 12301524419326913200163915)
            ·
              refine ⟨18452286628990369800245873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12301524419326913200163915 18452286628990369800245873)
              ·
                refine ⟨13839214971742777350184405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18452286628990369800245873 13839214971742777350184405)
                ·
                  refine ⟨324356600900221344144947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13839214971742777350184405 324356600900221344144947)
                  ·
                    rfl

theorem cell23_5685140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 2, 7].length) (baseStart_5685140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5685140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5685140 prefixEnd_5685140 := by exact prefixLift 5685140
  have htrace : WordTrace (prefixWord ++ tailWord_5685140) baseStart_5685140 baseEnd_5685140 := by
    simpa [prefixWord, tailWord_5685140, baseEnd_5685140] using wordTrace_append hprefix tailTrace_5685140
  have hstable : (prefixWord ++ tailWord_5685140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5685140).length < 2 ^ (prefixWord ++ tailWord_5685140).sum := by decide
  have hdescent : baseEnd_5685140 < baseStart_5685140 := by decide
  rcases family_descends (prefixWord ++ tailWord_5685140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5685200 : List Nat := [2, 1, 1, 1, 1, 2, 6, 2, 3, 4]
def baseStart_5685200 : Nat := 118140960795 + 5685200 * 2 ^ 59
def prefixEnd_5685200 : Nat := 4983230072969 + 3 ^ 40 * 5685200 * 2
def baseEnd_5685200 : Nat := 973080072313753954184749

theorem tailTrace_5685200 : CollatzResearch.WordTrace tailWord_5685200 prefixEnd_5685200 973080072313753954184749 := by
  unfold tailWord_5685200
  simp only [CollatzResearch.WordTrace]
  refine ⟨103678139501749414851722527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138237519335665886468963369 103678139501749414851722527)
  ·
    refine ⟨155517209252624122277583791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103678139501749414851722527 155517209252624122277583791)
    ·
      refine ⟨233275813878936183416375687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155517209252624122277583791 233275813878936183416375687)
      ·
        refine ⟨349913720818404275124563531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233275813878936183416375687 349913720818404275124563531)
        ·
          refine ⟨524870581227606412686845297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 349913720818404275124563531 524870581227606412686845297)
          ·
            refine ⟨393652935920704809515133973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 524870581227606412686845297 393652935920704809515133973)
            ·
              refine ⟨18452481371283037946021905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 393652935920704809515133973 18452481371283037946021905)
              ·
                refine ⟨13839361028462278459516429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18452481371283037946021905 13839361028462278459516429)
                ·
                  refine ⟨5189760385673354422318661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13839361028462278459516429 5189760385673354422318661)
                  ·
                    refine ⟨973080072313753954184749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5189760385673354422318661 973080072313753954184749)
                    ·
                      rfl

theorem cell23_5685200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 2, 3, 4].length) (baseStart_5685200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5685200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5685200 prefixEnd_5685200 := by exact prefixLift 5685200
  have htrace : WordTrace (prefixWord ++ tailWord_5685200) baseStart_5685200 baseEnd_5685200 := by
    simpa [prefixWord, tailWord_5685200, baseEnd_5685200] using wordTrace_append hprefix tailTrace_5685200
  have hstable : (prefixWord ++ tailWord_5685200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5685200).length < 2 ^ (prefixWord ++ tailWord_5685200).sum := by decide
  have hdescent : baseEnd_5685200 < baseStart_5685200 := by decide
  rcases family_descends (prefixWord ++ tailWord_5685200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5685230 : List Nat := [4, 1, 2, 1, 3, 1, 2, 1, 8]
def baseStart_5685230 : Nat := 118140960795 + 5685230 * 2 ^ 59
def prefixEnd_5685230 : Nat := 4983230072969 + 3 ^ 40 * 5685230 * 2
def baseEnd_5685230 : Nat := 324361735706766305019901

theorem tailTrace_5685230 : CollatzResearch.WordTrace tailWord_5685230 prefixEnd_5685230 324361735706766305019901 := by
  unfold tailWord_5685230
  simp only [CollatzResearch.WordTrace]
  refine ⟨25919671649173768103379643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138238248795593429884691429 25919671649173768103379643)
  ·
    refine ⟨38879507473760652155069465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25919671649173768103379643 38879507473760652155069465)
    ·
      refine ⟨29159630605320489116302099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38879507473760652155069465 29159630605320489116302099)
      ·
        refine ⟨43739445907980733674453149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29159630605320489116302099 43739445907980733674453149)
        ·
          refine ⟨16402292215492775127919931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43739445907980733674453149 16402292215492775127919931)
          ·
            refine ⟨24603438323239162691879897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16402292215492775127919931 24603438323239162691879897)
            ·
              refine ⟨18452578742429372018909923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24603438323239162691879897 18452578742429372018909923)
              ·
                refine ⟨27678868113644058028364885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18452578742429372018909923 27678868113644058028364885)
                ·
                  refine ⟨324361735706766305019901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27678868113644058028364885 324361735706766305019901)
                  ·
                    rfl

theorem cell23_5685230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 1, 8].length) (baseStart_5685230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5685230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5685230 prefixEnd_5685230 := by exact prefixLift 5685230
  have htrace : WordTrace (prefixWord ++ tailWord_5685230) baseStart_5685230 baseEnd_5685230 := by
    simpa [prefixWord, tailWord_5685230, baseEnd_5685230] using wordTrace_append hprefix tailTrace_5685230
  have hstable : (prefixWord ++ tailWord_5685230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5685230).length < 2 ^ (prefixWord ++ tailWord_5685230).sum := by decide
  have hdescent : baseEnd_5685230 < baseStart_5685230 := by decide
  rcases family_descends (prefixWord ++ tailWord_5685230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5685260 : List Nat := [2, 2, 1, 2, 3, 1, 3, 1, 3, 5]
def baseStart_5685260 : Nat := 118140960795 + 5685260 * 2 ^ 59
def prefixEnd_5685260 : Nat := 4983230072969 + 3 ^ 40 * 5685260 * 2
def baseEnd_5685260 : Nat := 973090341926843875934657

theorem tailTrace_5685260 : CollatzResearch.WordTrace tailWord_5685260 prefixEnd_5685260 973090341926843875934657 := by
  unfold tailWord_5685260
  simp only [CollatzResearch.WordTrace]
  refine ⟨103679233691640729975314617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138238978255520973300419489 103679233691640729975314617)
  ·
    refine ⟨77759425268730547481485963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103679233691640729975314617 77759425268730547481485963)
    ·
      refine ⟨116639137903095821222228945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77759425268730547481485963 116639137903095821222228945)
      ·
        refine ⟨87479353427321865916671709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116639137903095821222228945 87479353427321865916671709)
        ·
          refine ⟨32804757535245699718751891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87479353427321865916671709 32804757535245699718751891)
          ·
            refine ⟨49207136302868549578127837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32804757535245699718751891 49207136302868549578127837)
            ·
              refine ⟨18452676113575706091797939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49207136302868549578127837 18452676113575706091797939)
              ·
                refine ⟨27679014170363559137696909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18452676113575706091797939 27679014170363559137696909)
                ·
                  refine ⟨10379630313886334676636341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27679014170363559137696909 10379630313886334676636341)
                  ·
                    refine ⟨973090341926843875934657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10379630313886334676636341 973090341926843875934657)
                    ·
                      rfl

theorem cell23_5685260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 1, 3, 5].length) (baseStart_5685260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5685260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5685260 prefixEnd_5685260 := by exact prefixLift 5685260
  have htrace : WordTrace (prefixWord ++ tailWord_5685260) baseStart_5685260 baseEnd_5685260 := by
    simpa [prefixWord, tailWord_5685260, baseEnd_5685260] using wordTrace_append hprefix tailTrace_5685260
  have hstable : (prefixWord ++ tailWord_5685260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5685260).length < 2 ^ (prefixWord ++ tailWord_5685260).sum := by decide
  have hdescent : baseEnd_5685260 < baseStart_5685260 := by decide
  rcases family_descends (prefixWord ++ tailWord_5685260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5685267 : List Nat := [1, 1, 1, 2, 1, 4, 3, 3, 2, 3, 2]
def baseStart_5685267 : Nat := 118140960795 + 5685267 * 2 ^ 59
def prefixEnd_5685267 : Nat := 4983230072969 + 3 ^ 40 * 5685267 * 2
def baseEnd_5685267 : Nat := 2919274620145113100416439

theorem tailTrace_5685267 : CollatzResearch.WordTrace tailWord_5685267 prefixEnd_5685267 2919274620145113100416439 := by
  unfold tailWord_5685267
  simp only [CollatzResearch.WordTrace]
  refine ⟨207358722694256100146134055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138239148462837400097422703 207358722694256100146134055)
  ·
    refine ⟨311038084041384150219201083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207358722694256100146134055 311038084041384150219201083)
    ·
      refine ⟨466557126062076225328801625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 311038084041384150219201083 466557126062076225328801625)
      ·
        refine ⟨349917844546557168996601219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 466557126062076225328801625 349917844546557168996601219)
        ·
          refine ⟨524876766819835753494901829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 349917844546557168996601219 524876766819835753494901829)
          ·
            refine ⟨98414393778719203780294093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 524876766819835753494901829 98414393778719203780294093)
            ·
              refine ⟨36905397667019701417610285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 98414393778719203780294093 36905397667019701417610285)
              ·
                refine ⟨13839524125132388031603857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36905397667019701417610285 13839524125132388031603857)
                ·
                  refine ⟨10379643093849291023702893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13839524125132388031603857 10379643093849291023702893)
                  ·
                    refine ⟨3892366160193484133888585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10379643093849291023702893 3892366160193484133888585)
                    ·
                      refine ⟨2919274620145113100416439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3892366160193484133888585 2919274620145113100416439)
                      ·
                        rfl

theorem cell23_5685267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 3, 2, 3, 2].length) (baseStart_5685267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5685267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5685267 prefixEnd_5685267 := by exact prefixLift 5685267
  have htrace : WordTrace (prefixWord ++ tailWord_5685267) baseStart_5685267 baseEnd_5685267 := by
    simpa [prefixWord, tailWord_5685267, baseEnd_5685267] using wordTrace_append hprefix tailTrace_5685267
  have hstable : (prefixWord ++ tailWord_5685267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5685267).length < 2 ^ (prefixWord ++ tailWord_5685267).sum := by decide
  have hdescent : baseEnd_5685267 < baseStart_5685267 := by decide
  rcases family_descends (prefixWord ++ tailWord_5685267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5685317 : List Nat := [1, 3, 1, 1, 1, 3, 1, 6, 1, 2, 3]
def baseStart_5685317 : Nat := 118140960795 + 5685317 * 2 ^ 59
def prefixEnd_5685317 : Nat := 4983230072969 + 3 ^ 40 * 5685317 * 2
def baseEnd_5685317 : Nat := 2919300294177837904791209

theorem tailTrace_5685317 : CollatzResearch.WordTrace tailWord_5685317 prefixEnd_5685317 2919300294177837904791209 := by
  unfold tailWord_5685317
  simp only [CollatzResearch.WordTrace]
  refine ⟨207360546344074958685454205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138240364229383305790302803 207360546344074958685454205)
  ·
    refine ⟨77760204879028109507045327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 207360546344074958685454205 77760204879028109507045327)
    ·
      refine ⟨116640307318542164260567991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77760204879028109507045327 116640307318542164260567991)
      ·
        refine ⟨174960460977813246390851987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116640307318542164260567991 174960460977813246390851987)
        ·
          refine ⟨262440691466719869586277981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174960460977813246390851987 262440691466719869586277981)
          ·
            refine ⟨98415259300019951094854243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 262440691466719869586277981 98415259300019951094854243)
            ·
              refine ⟨147622888950029926642281365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98415259300019951094854243 147622888950029926642281365)
              ·
                refine ⟨6919822919532652811356939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 147622888950029926642281365 6919822919532652811356939)
                ·
                  refine ⟨10379734379298979217035409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6919822919532652811356939 10379734379298979217035409)
                  ·
                    refine ⟨7784800784474234412776557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10379734379298979217035409 7784800784474234412776557)
                    ·
                      refine ⟨2919300294177837904791209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7784800784474234412776557 2919300294177837904791209)
                      ·
                        rfl

theorem cell23_5685317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 6, 1, 2, 3].length) (baseStart_5685317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5685317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5685317 prefixEnd_5685317 := by exact prefixLift 5685317
  have htrace : WordTrace (prefixWord ++ tailWord_5685317) baseStart_5685317 baseEnd_5685317 := by
    simpa [prefixWord, tailWord_5685317, baseEnd_5685317] using wordTrace_append hprefix tailTrace_5685317
  have hstable : (prefixWord ++ tailWord_5685317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5685317).length < 2 ^ (prefixWord ++ tailWord_5685317).sum := by decide
  have hdescent : baseEnd_5685317 < baseStart_5685317 := by decide
  rcases family_descends (prefixWord ++ tailWord_5685317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5685341 : List Nat := [1, 4, 4, 1, 1, 1, 3, 2, 2, 4]
def baseStart_5685341 : Nat := 118140960795 + 5685341 * 2 ^ 59
def prefixEnd_5685341 : Nat := 4983230072969 + 3 ^ 40 * 5685341 * 2
def baseEnd_5685341 : Nat := 973104205904515270297033

theorem tailTrace_5685341 : CollatzResearch.WordTrace tailWord_5685341 prefixEnd_5685341 973104205904515270297033 := by
  unfold tailWord_5685341
  simp only [CollatzResearch.WordTrace]
  refine ⟨207361421695988010784327877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138240947797325340522885251 207361421695988010784327877)
  ·
    refine ⟨38880266567997752022061477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 207361421695988010784327877 38880266567997752022061477)
    ·
      refine ⟨7290049981499578504136527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38880266567997752022061477 7290049981499578504136527)
      ·
        refine ⟨10935074972249367756204791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7290049981499578504136527 10935074972249367756204791)
        ·
          refine ⟨16402612458374051634307187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10935074972249367756204791 16402612458374051634307187)
          ·
            refine ⟨24603918687561077451460781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16402612458374051634307187 24603918687561077451460781)
            ·
              refine ⟨9226469507835404044297793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24603918687561077451460781 9226469507835404044297793)
              ·
                refine ⟨6919852130876553033223345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9226469507835404044297793 6919852130876553033223345)
                ·
                  refine ⟨5189889098157414774917509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6919852130876553033223345 5189889098157414774917509)
                  ·
                    refine ⟨973104205904515270297033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5189889098157414774917509 973104205904515270297033)
                    ·
                      rfl

theorem cell23_5685341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_5685341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5685341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5685341 prefixEnd_5685341 := by exact prefixLift 5685341
  have htrace : WordTrace (prefixWord ++ tailWord_5685341) baseStart_5685341 baseEnd_5685341 := by
    simpa [prefixWord, tailWord_5685341, baseEnd_5685341] using wordTrace_append hprefix tailTrace_5685341
  have hstable : (prefixWord ++ tailWord_5685341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5685341).length < 2 ^ (prefixWord ++ tailWord_5685341).sum := by decide
  have hdescent : baseEnd_5685341 < baseStart_5685341 := by decide
  rcases family_descends (prefixWord ++ tailWord_5685341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5685415 : List Nat := [1, 1, 6, 2, 2, 2, 2, 1, 2, 1, 3]
def baseStart_5685415 : Nat := 118140960795 + 5685415 * 2 ^ 59
def prefixEnd_5685415 : Nat := 4983230072969 + 3 ^ 40 * 5685415 * 2
def baseEnd_5685415 : Nat := 2919350615281978521365759

theorem tailTrace_5685415 : CollatzResearch.WordTrace tailWord_5685415 prefixEnd_5685415 2919350615281978521365759 := by
  unfold tailWord_5685415
  simp only [CollatzResearch.WordTrace]
  refine ⟨207364120697719921422521699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138242747131813280948347799 207364120697719921422521699)
  ·
    refine ⟨311046181046579882133782549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207364120697719921422521699 311046181046579882133782549)
    ·
      refine ⟨14580289736558431975021057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 311046181046579882133782549 14580289736558431975021057)
      ·
        refine ⟨10935217302418823981265793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14580289736558431975021057 10935217302418823981265793)
        ·
          refine ⟨8201412976814117985949345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10935217302418823981265793 8201412976814117985949345)
          ·
            refine ⟨6151059732610588489462009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8201412976814117985949345 6151059732610588489462009)
            ·
              refine ⟨4613294799457941367096507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6151059732610588489462009 4613294799457941367096507)
              ·
                refine ⟨6919942199186912050644761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4613294799457941367096507 6919942199186912050644761)
                ·
                  refine ⟨5189956649390184037983571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6919942199186912050644761 5189956649390184037983571)
                  ·
                    refine ⟨7784934974085276056975357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5189956649390184037983571 7784934974085276056975357)
                    ·
                      refine ⟨2919350615281978521365759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7784934974085276056975357 2919350615281978521365759)
                      ·
                        rfl

theorem cell23_5685415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 2, 1, 2, 1, 3].length) (baseStart_5685415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5685415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5685415 prefixEnd_5685415 := by exact prefixLift 5685415
  have htrace : WordTrace (prefixWord ++ tailWord_5685415) baseStart_5685415 baseEnd_5685415 := by
    simpa [prefixWord, tailWord_5685415, baseEnd_5685415] using wordTrace_append hprefix tailTrace_5685415
  have hstable : (prefixWord ++ tailWord_5685415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5685415).length < 2 ^ (prefixWord ++ tailWord_5685415).sum := by decide
  have hdescent : baseEnd_5685415 < baseStart_5685415 := by decide
  rcases family_descends (prefixWord ++ tailWord_5685415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5685425 : List Nat := [1, 2, 2, 5, 3, 1, 1, 2, 1, 3, 2]
def baseStart_5685425 : Nat := 118140960795 + 5685425 * 2 ^ 59
def prefixEnd_5685425 : Nat := 4983230072969 + 3 ^ 40 * 5685425 * 2
def baseEnd_5685425 : Nat := 2919355750088523482240713

theorem tailTrace_5685425 : CollatzResearch.WordTrace tailWord_5685425 prefixEnd_5685425 2919355750088523482240713 := by
  unfold tailWord_5685425
  simp only [CollatzResearch.WordTrace]
  refine ⟨207364485427683693130385729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138242990285122462086923819 207364485427683693130385729)
  ·
    refine ⟨155523364070762769847789297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207364485427683693130385729 155523364070762769847789297)
    ·
      refine ⟨116642523053072077385841973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155523364070762769847789297 116642523053072077385841973)
      ·
        refine ⟨10935236536225507254922685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 116642523053072077385841973 10935236536225507254922685)
        ·
          refine ⟨4100713701084565220596007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10935236536225507254922685 4100713701084565220596007)
          ·
            refine ⟨6151070551626847830894011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4100713701084565220596007 6151070551626847830894011)
            ·
              refine ⟨9226605827440271746341017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6151070551626847830894011 9226605827440271746341017)
              ·
                refine ⟨6919954370580203809755763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9226605827440271746341017 6919954370580203809755763)
                ·
                  refine ⟨10379931555870305714633645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6919954370580203809755763 10379931555870305714633645)
                  ·
                    refine ⟨3892474333451364642987617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10379931555870305714633645 3892474333451364642987617)
                    ·
                      refine ⟨2919355750088523482240713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3892474333451364642987617 2919355750088523482240713)
                      ·
                        rfl

theorem cell23_5685425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 1, 2, 1, 3, 2].length) (baseStart_5685425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5685425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5685425 prefixEnd_5685425 := by exact prefixLift 5685425
  have htrace : WordTrace (prefixWord ++ tailWord_5685425) baseStart_5685425 baseEnd_5685425 := by
    simpa [prefixWord, tailWord_5685425, baseEnd_5685425] using wordTrace_append hprefix tailTrace_5685425
  have hstable : (prefixWord ++ tailWord_5685425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5685425).length < 2 ^ (prefixWord ++ tailWord_5685425).sum := by decide
  have hdescent : baseEnd_5685425 < baseStart_5685425 := by decide
  rcases family_descends (prefixWord ++ tailWord_5685425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5685437 : List Nat := [1, 4, 1, 2, 1, 1, 1, 2, 4, 3, 3]
def baseStart_5685437 : Nat := 118140960795 + 5685437 * 2 ^ 59
def prefixEnd_5685437 : Nat := 4983230072969 + 3 ^ 40 * 5685437 * 2
def baseEnd_5685437 : Nat := 2919361911856377435290657

theorem tailTrace_5685437 : CollatzResearch.WordTrace tailWord_5685437 prefixEnd_5685437 2919361911856377435290657 := by
  unfold tailWord_5685437
  simp only [CollatzResearch.WordTrace]
  refine ⟨207364923103640219179822565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138243282069093479453215043 207364923103640219179822565)
  ·
    refine ⟨38880923081932541096216731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 207364923103640219179822565 38880923081932541096216731)
    ·
      refine ⟨58321384622898811644325097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38880923081932541096216731 58321384622898811644325097)
      ·
        refine ⟨43741038467174108733243823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58321384622898811644325097 43741038467174108733243823)
        ·
          refine ⟨65611557700761163099865735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43741038467174108733243823 65611557700761163099865735)
          ·
            refine ⟨98417336551141744649798603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65611557700761163099865735 98417336551141744649798603)
            ·
              refine ⟨147626004826712616974697905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98417336551141744649798603 147626004826712616974697905)
              ·
                refine ⟨110719503620034462731023429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 147626004826712616974697905 110719503620034462731023429)
                ·
                  refine ⟨20759906928756461762066893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 110719503620034462731023429 20759906928756461762066893)
                  ·
                    refine ⟨7784965098283673160775085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20759906928756461762066893 7784965098283673160775085)
                    ·
                      refine ⟨2919361911856377435290657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7784965098283673160775085 2919361911856377435290657)
                      ·
                        rfl

theorem cell23_5685437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 4, 3, 3].length) (baseStart_5685437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5685437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5685437 prefixEnd_5685437 := by exact prefixLift 5685437
  have htrace : WordTrace (prefixWord ++ tailWord_5685437) baseStart_5685437 baseEnd_5685437 := by
    simpa [prefixWord, tailWord_5685437, baseEnd_5685437] using wordTrace_append hprefix tailTrace_5685437
  have hstable : (prefixWord ++ tailWord_5685437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5685437).length < 2 ^ (prefixWord ++ tailWord_5685437).sum := by decide
  have hdescent : baseEnd_5685437 < baseStart_5685437 := by decide
  rcases family_descends (prefixWord ++ tailWord_5685437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5685442 : List Nat := [3, 5, 1, 1, 1, 2, 3, 1, 1, 3, 2]
def baseStart_5685442 : Nat := 118140960795 + 5685442 * 2 ^ 59
def prefixEnd_5685442 : Nat := 4983230072969 + 3 ^ 40 * 5685442 * 2
def baseEnd_5685442 : Nat := 2919364479259649915728135

theorem tailTrace_5685442 : CollatzResearch.WordTrace tailWord_5685442 prefixEnd_5685442 2919364479259649915728135 := by
  unfold tailWord_5685442
  simp only [CollatzResearch.WordTrace]
  refine ⟨51841276367155526258438645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138243403645748070022503053 51841276367155526258438645)
  ·
    refine ⟨4860119659420830586728623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 51841276367155526258438645 4860119659420830586728623)
    ·
      refine ⟨7290179489131245880092935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4860119659420830586728623 7290179489131245880092935)
      ·
        refine ⟨10935269233696868820139403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7290179489131245880092935 10935269233696868820139403)
        ·
          refine ⟨16402903850545303230209105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10935269233696868820139403 16402903850545303230209105)
          ·
            refine ⟨12302177887908977422656829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16402903850545303230209105 12302177887908977422656829)
            ·
              refine ⟨4613316707965866533496311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12302177887908977422656829 4613316707965866533496311)
              ·
                refine ⟨6919975061948799800244467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4613316707965866533496311 6919975061948799800244467)
                ·
                  refine ⟨10379962592923199700366701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6919975061948799800244467 10379962592923199700366701)
                  ·
                    refine ⟨3892485972346199887637513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10379962592923199700366701 3892485972346199887637513)
                    ·
                      refine ⟨2919364479259649915728135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3892485972346199887637513 2919364479259649915728135)
                      ·
                        rfl

theorem cell23_5685442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 3, 1, 1, 3, 2].length) (baseStart_5685442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5685442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5685442 prefixEnd_5685442 := by exact prefixLift 5685442
  have htrace : WordTrace (prefixWord ++ tailWord_5685442) baseStart_5685442 baseEnd_5685442 := by
    simpa [prefixWord, tailWord_5685442, baseEnd_5685442] using wordTrace_append hprefix tailTrace_5685442
  have hstable : (prefixWord ++ tailWord_5685442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5685442).length < 2 ^ (prefixWord ++ tailWord_5685442).sum := by decide
  have hdescent : baseEnd_5685442 < baseStart_5685442 := by decide
  rcases family_descends (prefixWord ++ tailWord_5685442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5685457 : List Nat := [1, 2, 2, 1, 2, 2, 4, 2, 2, 5]
def baseStart_5685457 : Nat := 118140960795 + 5685457 * 2 ^ 59
def prefixEnd_5685457 : Nat := 4983230072969 + 3 ^ 40 * 5685457 * 2
def baseEnd_5685457 : Nat := 973124060489822452346855

theorem tailTrace_5685457 : CollatzResearch.WordTrace tailWord_5685457 prefixEnd_5685457 973124060489822452346855 := by
  unfold tailWord_5685457
  simp only [CollatzResearch.WordTrace]
  refine ⟨207365652563567762595550625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138243768375711841730367083 207365652563567762595550625)
  ·
    refine ⟨155524239422675821946662969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207365652563567762595550625 155524239422675821946662969)
    ·
      refine ⟨116643179567006866459997227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155524239422675821946662969 116643179567006866459997227)
      ·
        refine ⟨174964769350510299689995841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116643179567006866459997227 174964769350510299689995841)
        ·
          refine ⟨131223577012882724767496881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174964769350510299689995841 131223577012882724767496881)
          ·
            refine ⟨98417682759662043575622661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131223577012882724767496881 98417682759662043575622661)
            ·
              refine ⟨18453315517436633170429249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 98417682759662043575622661 18453315517436633170429249)
              ·
                refine ⟨13839986638077474877821937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18453315517436633170429249 13839986638077474877821937)
                ·
                  refine ⟨10379989978558106158366453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13839986638077474877821937 10379989978558106158366453)
                  ·
                    refine ⟨973124060489822452346855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10379989978558106158366453 973124060489822452346855)
                    ·
                      rfl

theorem cell23_5685457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 2, 2, 5].length) (baseStart_5685457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5685457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5685457 prefixEnd_5685457 := by exact prefixLift 5685457
  have htrace : WordTrace (prefixWord ++ tailWord_5685457) baseStart_5685457 baseEnd_5685457 := by
    simpa [prefixWord, tailWord_5685457, baseEnd_5685457] using wordTrace_append hprefix tailTrace_5685457
  have hstable : (prefixWord ++ tailWord_5685457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5685457).length < 2 ^ (prefixWord ++ tailWord_5685457).sum := by decide
  have hdescent : baseEnd_5685457 < baseStart_5685457 := by decide
  rcases family_descends (prefixWord ++ tailWord_5685457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5685461 : List Nat := [1, 3, 2, 4, 2, 1, 1, 4, 5]
def baseStart_5685461 : Nat := 118140960795 + 5685461 * 2 ^ 59
def prefixEnd_5685461 : Nat := 4983230072969 + 3 ^ 40 * 5685461 * 2
def baseEnd_5685461 : Nat := 324374915043565037932283

theorem tailTrace_5685461 : CollatzResearch.WordTrace tailWord_5685461 prefixEnd_5685461 324374915043565037932283 := by
  unfold tailWord_5685461
  simp only [CollatzResearch.WordTrace]
  refine ⟨207365798455553271278696237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138243865637035514185797491 207365798455553271278696237)
  ·
    refine ⟨77762174420832476729511089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 207365798455553271278696237 77762174420832476729511089)
    ·
      refine ⟨58321630815624357547133317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77762174420832476729511089 58321630815624357547133317)
      ·
        refine ⟨10935305777929567040087497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58321630815624357547133317 10935305777929567040087497)
        ·
          refine ⟨8201479333447175280065623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10935305777929567040087497 8201479333447175280065623)
          ·
            refine ⟨12302219000170762920098435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8201479333447175280065623 12302219000170762920098435)
            ·
              refine ⟨18453328500256144380147653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12302219000170762920098435 18453328500256144380147653)
              ·
                refine ⟨3459999093798027071277685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18453328500256144380147653 3459999093798027071277685)
                ·
                  refine ⟨324374915043565037932283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3459999093798027071277685 324374915043565037932283)
                  ·
                    rfl

theorem cell23_5685461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 4, 5].length) (baseStart_5685461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5685461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5685461 prefixEnd_5685461 := by exact prefixLift 5685461
  have htrace : WordTrace (prefixWord ++ tailWord_5685461) baseStart_5685461 baseEnd_5685461 := by
    simpa [prefixWord, tailWord_5685461, baseEnd_5685461] using wordTrace_append hprefix tailTrace_5685461
  have hstable : (prefixWord ++ tailWord_5685461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5685461).length < 2 ^ (prefixWord ++ tailWord_5685461).sum := by decide
  have hdescent : baseEnd_5685461 < baseStart_5685461 := by decide
  rcases family_descends (prefixWord ++ tailWord_5685461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5685464 : List Nat := [2, 1, 2, 2, 4, 1, 1, 1, 2, 5, 2]
def baseStart_5685464 : Nat := 118140960795 + 5685464 * 2 ^ 59
def prefixEnd_5685464 : Nat := 4983230072969 + 3 ^ 40 * 5685464 * 2
def baseEnd_5685464 : Nat := 2919375775834048829653033

theorem tailTrace_5685464 : CollatzResearch.WordTrace tailWord_5685464 prefixEnd_5685464 2919375775834048829653033 := by
  unfold tailWord_5685464
  simp only [CollatzResearch.WordTrace]
  refine ⟨103682953937271201395527723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138243938583028268527370297 103682953937271201395527723)
  ·
    refine ⟨155524430905906802093291585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103682953937271201395527723 155524430905906802093291585)
    ·
      refine ⟨116643323179430101569968689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155524430905906802093291585 116643323179430101569968689)
      ·
        refine ⟨87482492384572576177476517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116643323179430101569968689 87482492384572576177476517)
        ·
          refine ⟨16402967322107358033276847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87482492384572576177476517 16402967322107358033276847)
          ·
            refine ⟨24604450983161037049915271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16402967322107358033276847 24604450983161037049915271)
            ·
              refine ⟨36906676474741555574872907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24604450983161037049915271 36906676474741555574872907)
              ·
                refine ⟨55360014712112333362309361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36906676474741555574872907 55360014712112333362309361)
                ·
                  refine ⟨41520011034084250021732021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55360014712112333362309361 41520011034084250021732021)
                  ·
                    refine ⟨3892501034445398439537377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41520011034084250021732021 3892501034445398439537377)
                    ·
                      refine ⟨2919375775834048829653033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3892501034445398439537377 2919375775834048829653033)
                      ·
                        rfl

theorem cell23_5685464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 1, 2, 5, 2].length) (baseStart_5685464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5685464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5685464 prefixEnd_5685464 := by exact prefixLift 5685464
  have htrace : WordTrace (prefixWord ++ tailWord_5685464) baseStart_5685464 baseEnd_5685464 := by
    simpa [prefixWord, tailWord_5685464, baseEnd_5685464] using wordTrace_append hprefix tailTrace_5685464
  have hstable : (prefixWord ++ tailWord_5685464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5685464).length < 2 ^ (prefixWord ++ tailWord_5685464).sum := by decide
  have hdescent : baseEnd_5685464 < baseStart_5685464 := by decide
  rcases family_descends (prefixWord ++ tailWord_5685464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5685514 : List Nat := [3, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3]
def baseStart_5685514 : Nat := 118140960795 + 5685514 * 2 ^ 59
def prefixEnd_5685514 : Nat := 4983230072969 + 3 ^ 40 * 5685514 * 2
def baseEnd_5685514 : Nat := 2919401449866773634027803

theorem tailTrace_5685514 : CollatzResearch.WordTrace tailWord_5685514 prefixEnd_5685514 2919401449866773634027803 := by
  unfold tailWord_5685514
  simp only [CollatzResearch.WordTrace]
  refine ⟨51841932881090315332593899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138245154349574174220250397 51841932881090315332593899)
  ·
    refine ⟨77762899321635472998890849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51841932881090315332593899 77762899321635472998890849)
    ·
      refine ⟨58322174491226604749168137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77762899321635472998890849 58322174491226604749168137)
      ·
        refine ⟨43741630868419953561876103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58322174491226604749168137 43741630868419953561876103)
        ·
          refine ⟨65612446302629930342814155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43741630868419953561876103 65612446302629930342814155)
          ·
            refine ⟨98418669453944895514221233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65612446302629930342814155 98418669453944895514221233)
            ·
              refine ⟨73814002090458671635665925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98418669453944895514221233 73814002090458671635665925)
              ·
                refine ⟨13840125391961000931687361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 73814002090458671635665925 13840125391961000931687361)
                ·
                  refine ⟨10380094043970750698765521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13840125391961000931687361 10380094043970750698765521)
                  ·
                    refine ⟨7785070532978063024074141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10380094043970750698765521 7785070532978063024074141)
                    ·
                      refine ⟨2919401449866773634027803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7785070532978063024074141 2919401449866773634027803)
                      ·
                        rfl

theorem cell23_5685514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3].length) (baseStart_5685514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5685514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5685514 prefixEnd_5685514 := by exact prefixLift 5685514
  have htrace : WordTrace (prefixWord ++ tailWord_5685514) baseStart_5685514 baseEnd_5685514 := by
    simpa [prefixWord, tailWord_5685514, baseEnd_5685514] using wordTrace_append hprefix tailTrace_5685514
  have hstable : (prefixWord ++ tailWord_5685514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5685514).length < 2 ^ (prefixWord ++ tailWord_5685514).sum := by decide
  have hdescent : baseEnd_5685514 < baseStart_5685514 := by decide
  rcases family_descends (prefixWord ++ tailWord_5685514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5685521 : List Nat := [1, 2, 2, 1, 1, 5, 2, 4, 1, 4]
def baseStart_5685521 : Nat := 118140960795 + 5685521 * 2 ^ 59
def prefixEnd_5685521 : Nat := 4983230072969 + 3 ^ 40 * 5685521 * 2
def baseEnd_5685521 : Nat := 973135014743785035546757

theorem tailTrace_5685521 : CollatzResearch.WordTrace tailWord_5685521 prefixEnd_5685521 973135014743785035546757 := by
  unfold tailWord_5685521
  simp only [CollatzResearch.WordTrace]
  refine ⟨207367986835335901525880417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138245324556890601017253611 207367986835335901525880417)
  ·
    refine ⟨155525990126501926144410313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207367986835335901525880417 155525990126501926144410313)
    ·
      refine ⟨116644492594876444608307735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155525990126501926144410313 116644492594876444608307735)
      ·
        refine ⟨174966738892314666912461603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116644492594876444608307735 174966738892314666912461603)
        ·
          refine ⟨262450108338472000368692405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174966738892314666912461603 262450108338472000368692405)
          ·
            refine ⟨24604697656731750034564913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 262450108338472000368692405 24604697656731750034564913)
            ·
              refine ⟨18453523242548812525923685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24604697656731750034564913 18453523242548812525923685)
              ·
                refine ⟨3460035607977902348610691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18453523242548812525923685 3460035607977902348610691)
                ·
                  refine ⟨5190053411966853522916037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3460035607977902348610691 5190053411966853522916037)
                  ·
                    refine ⟨973135014743785035546757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5190053411966853522916037 973135014743785035546757)
                    ·
                      rfl

theorem cell23_5685521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 4, 1, 4].length) (baseStart_5685521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5685521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5685521 prefixEnd_5685521 := by exact prefixLift 5685521
  have htrace : WordTrace (prefixWord ++ tailWord_5685521) baseStart_5685521 baseEnd_5685521 := by
    simpa [prefixWord, tailWord_5685521, baseEnd_5685521] using wordTrace_append hprefix tailTrace_5685521
  have hstable : (prefixWord ++ tailWord_5685521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5685521).length < 2 ^ (prefixWord ++ tailWord_5685521).sum := by decide
  have hdescent : baseEnd_5685521 < baseStart_5685521 := by decide
  rcases family_descends (prefixWord ++ tailWord_5685521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5685564 : List Nat := [2, 2, 2, 2, 1, 2, 1, 5, 1, 5]
def baseStart_5685564 : Nat := 118140960795 + 5685564 * 2 ^ 59
def prefixEnd_5685564 : Nat := 4983230072969 + 3 ^ 40 * 5685564 * 2
def baseEnd_5685564 : Nat := 973142374633166146134191

theorem tailTrace_5685564 : CollatzResearch.WordTrace tailWord_5685564 prefixEnd_5685564 973142374633166146134191 := by
  unfold tailWord_5685564
  simp only [CollatzResearch.WordTrace]
  refine ⟨103684777587090059934847873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138246370116120079913130497 103684777587090059934847873)
  ·
    refine ⟨77763583190317544951135905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103684777587090059934847873 77763583190317544951135905)
    ·
      refine ⟨58322687392738158713351929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77763583190317544951135905 58322687392738158713351929)
      ·
        refine ⟨43742015544553619035013947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58322687392738158713351929 43742015544553619035013947)
        ·
          refine ⟨65613023316830428552520921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43742015544553619035013947 65613023316830428552520921)
          ·
            refine ⟨49209767487622821414390691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65613023316830428552520921 49209767487622821414390691)
            ·
              refine ⟨73814651231434232121586037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49209767487622821414390691 73814651231434232121586037)
              ·
                refine ⟨6920123552946959261398691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 73814651231434232121586037 6920123552946959261398691)
                ·
                  refine ⟨10380185329420438892098037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6920123552946959261398691 10380185329420438892098037)
                  ·
                    refine ⟨973142374633166146134191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10380185329420438892098037 973142374633166146134191)
                    ·
                      rfl

theorem cell23_5685564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 5, 1, 5].length) (baseStart_5685564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5685564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5685564 prefixEnd_5685564 := by exact prefixLift 5685564
  have htrace : WordTrace (prefixWord ++ tailWord_5685564) baseStart_5685564 baseEnd_5685564 := by
    simpa [prefixWord, tailWord_5685564, baseEnd_5685564] using wordTrace_append hprefix tailTrace_5685564
  have hstable : (prefixWord ++ tailWord_5685564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5685564).length < 2 ^ (prefixWord ++ tailWord_5685564).sum := by decide
  have hdescent : baseEnd_5685564 < baseStart_5685564 := by decide
  rcases family_descends (prefixWord ++ tailWord_5685564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5685572 : List Nat := [2, 3, 4, 1, 2, 1, 3, 2, 1, 4]
def baseStart_5685572 : Nat := 118140960795 + 5685572 * 2 ^ 59
def prefixEnd_5685572 : Nat := 4983230072969 + 3 ^ 40 * 5685572 * 2
def baseEnd_5685572 : Nat := 973143743914911469034179

theorem tailTrace_5685572 : CollatzResearch.WordTrace tailWord_5685572 prefixEnd_5685572 973143743914911469034179 := by
  unfold tailWord_5685572
  simp only [CollatzResearch.WordTrace]
  refine ⟨103684923479075568617993485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138246564638767424823991313 103684923479075568617993485)
  ·
    refine ⟨38881846304653338231747557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103684923479075568617993485 38881846304653338231747557)
    ·
      refine ⟨7290346182122500918452667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38881846304653338231747557 7290346182122500918452667)
      ·
        refine ⟨10935519273183751377679001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7290346182122500918452667 10935519273183751377679001)
        ·
          refine ⟨8201639454887813533259251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10935519273183751377679001 8201639454887813533259251)
          ·
            refine ⟨12302459182331720299888877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8201639454887813533259251 12302459182331720299888877)
            ·
              refine ⟨4613422193374395112458329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12302459182331720299888877 4613422193374395112458329)
              ·
                refine ⟨3460066645030796334343747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4613422193374395112458329 3460066645030796334343747)
                ·
                  refine ⟨5190099967546194501515621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3460066645030796334343747 5190099967546194501515621)
                  ·
                    refine ⟨973143743914911469034179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5190099967546194501515621 973143743914911469034179)
                    ·
                      rfl

theorem cell23_5685572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_5685572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5685572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5685572 prefixEnd_5685572 := by exact prefixLift 5685572
  have htrace : WordTrace (prefixWord ++ tailWord_5685572) baseStart_5685572 baseEnd_5685572 := by
    simpa [prefixWord, tailWord_5685572, baseEnd_5685572] using wordTrace_append hprefix tailTrace_5685572
  have hstable : (prefixWord ++ tailWord_5685572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5685572).length < 2 ^ (prefixWord ++ tailWord_5685572).sum := by decide
  have hdescent : baseEnd_5685572 < baseStart_5685572 := by decide
  rcases family_descends (prefixWord ++ tailWord_5685572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5685587 : List Nat := [1, 1, 1, 2, 1, 1, 4, 3, 3, 1, 5]
def baseStart_5685587 : Nat := 118140960795 + 5685587 * 2 ^ 59
def prefixEnd_5685587 : Nat := 4983230072969 + 3 ^ 40 * 5685587 * 2
def baseEnd_5685587 : Nat := 2919438933954551848414967

theorem tailTrace_5685587 : CollatzResearch.WordTrace tailWord_5685587 prefixEnd_5685587 2919438933954551848414967 := by
  unfold tailWord_5685587
  simp only [CollatzResearch.WordTrace]
  refine ⟨207370394053096794797783015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138246929368731196531855343 207370394053096794797783015)
  ·
    refine ⟨311055591079645192196674523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207370394053096794797783015 311055591079645192196674523)
    ·
      refine ⟨466583386619467788295011785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 311055591079645192196674523 466583386619467788295011785)
      ·
        refine ⟨349937539964600841221258839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 466583386619467788295011785 349937539964600841221258839)
        ·
          refine ⟨524906309946901261831888259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 349937539964600841221258839 524906309946901261831888259)
          ·
            refine ⟨787359464920351892747832389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 524906309946901261831888259 787359464920351892747832389)
            ·
              refine ⟨147629899672565979890218573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 787359464920351892747832389 147629899672565979890218573)
              ·
                refine ⟨55361212377212242458831965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 147629899672565979890218573 55361212377212242458831965)
                ·
                  refine ⟨20760454641454590922061987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55361212377212242458831965 20760454641454590922061987)
                  ·
                    refine ⟨31140681962181886383092981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20760454641454590922061987 31140681962181886383092981)
                    ·
                      refine ⟨2919438933954551848414967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31140681962181886383092981 2919438933954551848414967)
                      ·
                        rfl

theorem cell23_5685587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 3, 3, 1, 5].length) (baseStart_5685587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5685587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5685587 prefixEnd_5685587 := by exact prefixLift 5685587
  have htrace : WordTrace (prefixWord ++ tailWord_5685587) baseStart_5685587 baseEnd_5685587 := by
    simpa [prefixWord, tailWord_5685587, baseEnd_5685587] using wordTrace_append hprefix tailTrace_5685587
  have hstable : (prefixWord ++ tailWord_5685587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5685587).length < 2 ^ (prefixWord ++ tailWord_5685587).sum := by decide
  have hdescent : baseEnd_5685587 < baseStart_5685587 := by decide
  rcases family_descends (prefixWord ++ tailWord_5685587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5685618 : List Nat := [3, 2, 1, 2, 1, 4, 3, 1, 1, 1, 4]
def baseStart_5685618 : Nat := 118140960795 + 5685618 * 2 ^ 59
def prefixEnd_5685618 : Nat := 4983230072969 + 3 ^ 40 * 5685618 * 2
def baseEnd_5685618 : Nat := 2919454851854841227127325

theorem tailTrace_5685618 : CollatzResearch.WordTrace tailWord_5685618 prefixEnd_5685618 2919454851854841227127325 := by
  unfold tailWord_5685618
  simp only [CollatzResearch.WordTrace]
  refine ⟨51842881178996121773040377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138247683143989658061441005 51842881178996121773040377)
  ·
    refine ⟨38882160884247091329780283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51842881178996121773040377 38882160884247091329780283)
    ·
      refine ⟨58323241326370636994670425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38882160884247091329780283 58323241326370636994670425)
      ·
        refine ⟨43742430994777977746002819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58323241326370636994670425 43742430994777977746002819)
        ·
          refine ⟨65613646492166966619004229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43742430994777977746002819 65613646492166966619004229)
          ·
            refine ⟨12302558717281306241063293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65613646492166966619004229 12302558717281306241063293)
            ·
              refine ⟨4613459518980489840398735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12302558717281306241063293 4613459518980489840398735)
              ·
                refine ⟨6920189278470734760598103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4613459518980489840398735 6920189278470734760598103)
                ·
                  refine ⟨10380283917706102140897155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6920189278470734760598103 10380283917706102140897155)
                  ·
                    refine ⟨15570425876559153211345733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10380283917706102140897155 15570425876559153211345733)
                    ·
                      refine ⟨2919454851854841227127325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15570425876559153211345733 2919454851854841227127325)
                      ·
                        rfl

theorem cell23_5685618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 3, 1, 1, 1, 4].length) (baseStart_5685618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5685618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5685618 prefixEnd_5685618 := by exact prefixLift 5685618
  have htrace : WordTrace (prefixWord ++ tailWord_5685618) baseStart_5685618 baseEnd_5685618 := by
    simpa [prefixWord, tailWord_5685618, baseEnd_5685618] using wordTrace_append hprefix tailTrace_5685618
  have hstable : (prefixWord ++ tailWord_5685618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5685618).length < 2 ^ (prefixWord ++ tailWord_5685618).sum := by decide
  have hdescent : baseEnd_5685618 < baseStart_5685618 := by decide
  rcases family_descends (prefixWord ++ tailWord_5685618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5685621 : List Nat := [1, 3, 4, 1, 2, 1, 3, 1, 1, 1, 5]
def baseStart_5685621 : Nat := 118140960795 + 5685621 * 2 ^ 59
def prefixEnd_5685621 : Nat := 4983230072969 + 3 ^ 40 * 5685621 * 2
def baseEnd_5685621 : Nat := 2919456392296804715389811

theorem tailTrace_5685621 : CollatzResearch.WordTrace tailWord_5685621 prefixEnd_5685621 2919456392296804715389811 := by
  unfold tailWord_5685621
  simp only [CollatzResearch.WordTrace]
  refine ⟨207371634134973618604520717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138247756089982412403013811 207371634134973618604520717)
  ·
    refine ⟨77764362800615106976695269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 207371634134973618604520717 77764362800615106976695269)
    ·
      refine ⟨14580818025115332558130363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77764362800615106976695269 14580818025115332558130363)
      ·
        refine ⟨21871227037672998837195545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14580818025115332558130363 21871227037672998837195545)
        ·
          refine ⟨16403420278254749127896659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21871227037672998837195545 16403420278254749127896659)
          ·
            refine ⟨24605130417382123691844989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16403420278254749127896659 24605130417382123691844989)
            ·
              refine ⟨9226923906518296384441871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24605130417382123691844989 9226923906518296384441871)
              ·
                refine ⟨13840385859777444576662807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9226923906518296384441871 13840385859777444576662807)
                ·
                  refine ⟨20760578789666166864994211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13840385859777444576662807 20760578789666166864994211)
                  ·
                    refine ⟨31140868184499250297491317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20760578789666166864994211 31140868184499250297491317)
                    ·
                      refine ⟨2919456392296804715389811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31140868184499250297491317 2919456392296804715389811)
                      ·
                        rfl

theorem cell23_5685621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 3, 1, 1, 1, 5].length) (baseStart_5685621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5685621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5685621 prefixEnd_5685621 := by exact prefixLift 5685621
  have htrace : WordTrace (prefixWord ++ tailWord_5685621) baseStart_5685621 baseEnd_5685621 := by
    simpa [prefixWord, tailWord_5685621, baseEnd_5685621] using wordTrace_append hprefix tailTrace_5685621
  have hstable : (prefixWord ++ tailWord_5685621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5685621).length < 2 ^ (prefixWord ++ tailWord_5685621).sum := by decide
  have hdescent : baseEnd_5685621 < baseStart_5685621 := by decide
  rcases family_descends (prefixWord ++ tailWord_5685621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5685672 : List Nat := [2, 1, 6, 1, 1, 3, 2, 1, 1, 2, 3]
def baseStart_5685672 : Nat := 118140960795 + 5685672 * 2 ^ 59
def prefixEnd_5685672 : Nat := 4983230072969 + 3 ^ 40 * 5685672 * 2
def baseEnd_5685672 : Nat := 2919482579810184015852077

theorem tailTrace_5685672 : CollatzResearch.WordTrace tailWord_5685672 prefixEnd_5685672 2919482579810184015852077 := by
  unfold tailWord_5685672
  simp only [CollatzResearch.WordTrace]
  refine ⟨103686747128894427157313635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138248996171859236209751513 103686747128894427157313635)
  ·
    refine ⟨155530120693341640735970453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103686747128894427157313635 155530120693341640735970453)
    ·
      refine ⟨7290474407500389409498615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 155530120693341640735970453 7290474407500389409498615)
      ·
        refine ⟨10935711611250584114247923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7290474407500389409498615 10935711611250584114247923)
        ·
          refine ⟨16403567416875876171371885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10935711611250584114247923 16403567416875876171371885)
          ·
            refine ⟨6151337781328453564264457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16403567416875876171371885 6151337781328453564264457)
            ·
              refine ⟨4613503335996340173198343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6151337781328453564264457 4613503335996340173198343)
              ·
                refine ⟨6920255003994510259797515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4613503335996340173198343 6920255003994510259797515)
                ·
                  refine ⟨10380382505991765389696273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6920255003994510259797515 10380382505991765389696273)
                  ·
                    refine ⟨7785286879493824042272205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10380382505991765389696273 7785286879493824042272205)
                    ·
                      refine ⟨2919482579810184015852077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7785286879493824042272205 2919482579810184015852077)
                      ·
                        rfl

theorem cell23_5685672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 3, 2, 1, 1, 2, 3].length) (baseStart_5685672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5685672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5685672 prefixEnd_5685672 := by exact prefixLift 5685672
  have htrace : WordTrace (prefixWord ++ tailWord_5685672) baseStart_5685672 baseEnd_5685672 := by
    simpa [prefixWord, tailWord_5685672, baseEnd_5685672] using wordTrace_append hprefix tailTrace_5685672
  have hstable : (prefixWord ++ tailWord_5685672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5685672).length < 2 ^ (prefixWord ++ tailWord_5685672).sum := by decide
  have hdescent : baseEnd_5685672 < baseStart_5685672 := by decide
  rcases family_descends (prefixWord ++ tailWord_5685672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5685799 : List Nat := [1, 1, 7, 2, 1, 2, 2, 2, 5]
def baseStart_5685799 : Nat := 118140960795 + 5685799 * 2 ^ 59
def prefixEnd_5685799 : Nat := 4983230072969 + 3 ^ 40 * 5685799 * 2
def baseEnd_5685799 : Nat := 324394199094811668773777

theorem tailTrace_5685799 : CollatzResearch.WordTrace tailWord_5685799 prefixEnd_5685799 324394199094811668773777 := by
  unfold tailWord_5685799
  simp only [CollatzResearch.WordTrace]
  refine ⟨207378126328328755004500451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138252084218885836669666967 207378126328328755004500451)
  ·
    refine ⟨311067189492493132506750677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207378126328328755004500451 311067189492493132506750677)
    ·
      refine ⟨7290637253730307793126969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 311067189492493132506750677 7290637253730307793126969)
      ·
        refine ⟨5467977940297730844845227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7290637253730307793126969 5467977940297730844845227)
        ·
          refine ⟨8201966910446596267267841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5467977940297730844845227 8201966910446596267267841)
          ·
            refine ⟨6151475182834947200450881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8201966910446596267267841 6151475182834947200450881)
            ·
              refine ⟨4613606387126210400338161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6151475182834947200450881 4613606387126210400338161)
              ·
                refine ⟨3460204790344657800253621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4613606387126210400338161 3460204790344657800253621)
                ·
                  refine ⟨324394199094811668773777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3460204790344657800253621 324394199094811668773777)
                  ·
                    rfl

theorem cell23_5685799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 2, 2, 5].length) (baseStart_5685799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5685799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5685799 prefixEnd_5685799 := by exact prefixLift 5685799
  have htrace : WordTrace (prefixWord ++ tailWord_5685799) baseStart_5685799 baseEnd_5685799 := by
    simpa [prefixWord, tailWord_5685799, baseEnd_5685799] using wordTrace_append hprefix tailTrace_5685799
  have hstable : (prefixWord ++ tailWord_5685799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5685799).length < 2 ^ (prefixWord ++ tailWord_5685799).sum := by decide
  have hdescent : baseEnd_5685799 < baseStart_5685799 := by decide
  rcases family_descends (prefixWord ++ tailWord_5685799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5685804 : List Nat := [2, 2, 1, 1, 1, 2, 1, 5, 8]
def baseStart_5685804 : Nat := 118140960795 + 5685804 * 2 ^ 59
def prefixEnd_5685804 : Nat := 4983230072969 + 3 ^ 40 * 5685804 * 2
def baseEnd_5685804 : Nat := 324394484361841944377941

theorem tailTrace_5685804 : CollatzResearch.WordTrace tailWord_5685804 prefixEnd_5685804 324394484361841944377941 := by
  unfold tailWord_5685804
  simp only [CollatzResearch.WordTrace]
  refine ⟨103689154346655320429216233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138252205795540427238954977 103689154346655320429216233)
  ·
    refine ⟨77766865759991490321912175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103689154346655320429216233 77766865759991490321912175)
    ·
      refine ⟨116650298639987235482868263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77766865759991490321912175 116650298639987235482868263)
      ·
        refine ⟨174975447959980853224302395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116650298639987235482868263 174975447959980853224302395)
        ·
          refine ⟨262463171939971279836453593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174975447959980853224302395 262463171939971279836453593)
          ·
            refine ⟨196847378954978459877340195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 262463171939971279836453593 196847378954978459877340195)
            ·
              refine ⟨295271068432467689816010293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 196847378954978459877340195 295271068432467689816010293)
              ·
                refine ⟨27681662665543845920250965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 295271068432467689816010293 27681662665543845920250965)
                ·
                  refine ⟨324394484361841944377941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27681662665543845920250965 324394484361841944377941)
                  ·
                    rfl

theorem cell23_5685804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 8].length) (baseStart_5685804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5685804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5685804 prefixEnd_5685804 := by exact prefixLift 5685804
  have htrace : WordTrace (prefixWord ++ tailWord_5685804) baseStart_5685804 baseEnd_5685804 := by
    simpa [prefixWord, tailWord_5685804, baseEnd_5685804] using wordTrace_append hprefix tailTrace_5685804
  have hstable : (prefixWord ++ tailWord_5685804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5685804).length < 2 ^ (prefixWord ++ tailWord_5685804).sum := by decide
  have hdescent : baseEnd_5685804 < baseStart_5685804 := by decide
  rcases family_descends (prefixWord ++ tailWord_5685804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5685871 : List Nat := [1, 1, 2, 1, 3, 2, 2, 1, 5, 1, 4]
def baseStart_5685871 : Nat := 118140960795 + 5685871 * 2 ^ 59
def prefixEnd_5685871 : Nat := 4983230072969 + 3 ^ 40 * 5685871 * 2
def baseEnd_5685871 : Nat := 2919584762460428737263661

theorem tailTrace_5685871 : CollatzResearch.WordTrace tailWord_5685871 prefixEnd_5685871 2919584762460428737263661 := by
  unfold tailWord_5685871
  simp only [CollatzResearch.WordTrace]
  refine ⟨207380752384067911301121467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138253834922711940867414311 207380752384067911301121467)
  ·
    refine ⟨311071128576101866951682201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207380752384067911301121467 311071128576101866951682201)
    ·
      refine ⟨233303346432076400213761651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 311071128576101866951682201 233303346432076400213761651)
      ·
        refine ⟨349955019648114600320642477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233303346432076400213761651 349955019648114600320642477)
        ·
          refine ⟨131233132368042975120240929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 349955019648114600320642477 131233132368042975120240929)
          ·
            refine ⟨98424849276032231340180697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131233132368042975120240929 98424849276032231340180697)
            ·
              refine ⟨73818636957024173505135523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98424849276032231340180697 73818636957024173505135523)
              ·
                refine ⟨110727955435536260257703285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73818636957024173505135523 110727955435536260257703285)
                ·
                  refine ⟨10380745822081524399159683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 110727955435536260257703285 10380745822081524399159683)
                  ·
                    refine ⟨15571118733122286598739525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10380745822081524399159683 15571118733122286598739525)
                    ·
                      refine ⟨2919584762460428737263661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15571118733122286598739525 2919584762460428737263661)
                      ·
                        rfl

theorem cell23_5685871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 5, 1, 4].length) (baseStart_5685871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5685871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5685871 prefixEnd_5685871 := by exact prefixLift 5685871
  have htrace : WordTrace (prefixWord ++ tailWord_5685871) baseStart_5685871 baseEnd_5685871 := by
    simpa [prefixWord, tailWord_5685871, baseEnd_5685871] using wordTrace_append hprefix tailTrace_5685871
  have hstable : (prefixWord ++ tailWord_5685871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5685871).length < 2 ^ (prefixWord ++ tailWord_5685871).sum := by decide
  have hdescent : baseEnd_5685871 < baseStart_5685871 := by decide
  rcases family_descends (prefixWord ++ tailWord_5685871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5685885 : List Nat := [1, 4, 1, 1, 5, 1, 2, 2, 1, 5]
def baseStart_5685885 : Nat := 118140960795 + 5685885 * 2 ^ 59
def prefixEnd_5685885 : Nat := 4983230072969 + 3 ^ 40 * 5685885 * 2
def baseEnd_5685885 : Nat := 973197317063197227496199

theorem tailTrace_5685885 : CollatzResearch.WordTrace tailWord_5685885 prefixEnd_5685885 973197317063197227496199 := by
  unfold tailWord_5685885
  simp only [CollatzResearch.WordTrace]
  refine ⟨207381263006017191692131109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138254175337344794461420739 207381263006017191692131109)
  ·
    refine ⟨38883986813628223442274583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 207381263006017191692131109 38883986813628223442274583)
    ·
      refine ⟨58325980220442335163411875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38883986813628223442274583 58325980220442335163411875)
      ·
        refine ⟨87488970330663502745117813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58325980220442335163411875 87488970330663502745117813)
        ·
          refine ⟨8202090968499703382354795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 87488970330663502745117813 8202090968499703382354795)
          ·
            refine ⟨12303136452749555073532193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8202090968499703382354795 12303136452749555073532193)
            ·
              refine ⟨9227352339562166305149145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12303136452749555073532193 9227352339562166305149145)
              ·
                refine ⟨6920514254671624728861859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9227352339562166305149145 6920514254671624728861859)
                ·
                  refine ⟨10380771382007437093292789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6920514254671624728861859 10380771382007437093292789)
                  ·
                    refine ⟨973197317063197227496199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10380771382007437093292789 973197317063197227496199)
                    ·
                      rfl

theorem cell23_5685885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 2, 2, 1, 5].length) (baseStart_5685885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5685885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5685885 prefixEnd_5685885 := by exact prefixLift 5685885
  have htrace : WordTrace (prefixWord ++ tailWord_5685885) baseStart_5685885 baseEnd_5685885 := by
    simpa [prefixWord, tailWord_5685885, baseEnd_5685885] using wordTrace_append hprefix tailTrace_5685885
  have hstable : (prefixWord ++ tailWord_5685885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5685885).length < 2 ^ (prefixWord ++ tailWord_5685885).sum := by decide
  have hdescent : baseEnd_5685885 < baseStart_5685885 := by decide
  rcases family_descends (prefixWord ++ tailWord_5685885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5685888 : List Nat := [2, 1, 1, 2, 1, 5, 1, 4, 1, 1, 4]
def baseStart_5685888 : Nat := 118140960795 + 5685888 * 2 ^ 59
def prefixEnd_5685888 : Nat := 4983230072969 + 3 ^ 40 * 5685888 * 2
def baseEnd_5685888 : Nat := 2919593491631555170751083

theorem tailTrace_5685888 : CollatzResearch.WordTrace tailWord_5685888 prefixEnd_5685888 2919593491631555170751083 := by
  unfold tailWord_5685888
  simp only [CollatzResearch.WordTrace]
  refine ⟨103690686212503161602245159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138254248283337548802993545 103690686212503161602245159)
  ·
    refine ⟨155536029318754742403367739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103690686212503161602245159 155536029318754742403367739)
    ·
      refine ⟨233304043978132113605051609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155536029318754742403367739 233304043978132113605051609)
      ·
        refine ⟨174978032983599085203788707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 233304043978132113605051609 174978032983599085203788707)
        ·
          refine ⟨262467049475398627805683061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174978032983599085203788707 262467049475398627805683061)
          ·
            refine ⟨24606285888318621356782787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 262467049475398627805683061 24606285888318621356782787)
            ·
              refine ⟨36909428832477932035174181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24606285888318621356782787 36909428832477932035174181)
              ·
                refine ⟨6920517906089612256595159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36909428832477932035174181 6920517906089612256595159)
                ·
                  refine ⟨10380776859134418384892739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6920517906089612256595159 10380776859134418384892739)
                  ·
                    refine ⟨15571165288701627577339109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10380776859134418384892739 15571165288701627577339109)
                    ·
                      refine ⟨2919593491631555170751083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15571165288701627577339109 2919593491631555170751083)
                      ·
                        rfl

theorem cell23_5685888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 1, 4, 1, 1, 4].length) (baseStart_5685888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5685888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5685888 prefixEnd_5685888 := by exact prefixLift 5685888
  have htrace : WordTrace (prefixWord ++ tailWord_5685888) baseStart_5685888 baseEnd_5685888 := by
    simpa [prefixWord, tailWord_5685888, baseEnd_5685888] using wordTrace_append hprefix tailTrace_5685888
  have hstable : (prefixWord ++ tailWord_5685888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5685888).length < 2 ^ (prefixWord ++ tailWord_5685888).sum := by decide
  have hdescent : baseEnd_5685888 < baseStart_5685888 := by decide
  rcases family_descends (prefixWord ++ tailWord_5685888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5685918 : List Nat := [4, 3, 1, 1, 1, 1, 1, 1, 3, 1, 6]
def baseStart_5685918 : Nat := 118140960795 + 5685918 * 2 ^ 59
def prefixEnd_5685918 : Nat := 4983230072969 + 3 ^ 40 * 5685918 * 2
def baseEnd_5685918 : Nat := 2919608896051190053375945

theorem tailTrace_5685918 : CollatzResearch.WordTrace tailWord_5685918 prefixEnd_5685918 2919608896051190053375945 := by
  unfold tailWord_5685918
  simp only [CollatzResearch.WordTrace]
  refine ⟨25922808326862204791010301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138254977743265092218721605 25922808326862204791010301)
  ·
    refine ⟨9721053122573326796628863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25922808326862204791010301 9721053122573326796628863)
    ·
      refine ⟨14581579683859990194943295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9721053122573326796628863 14581579683859990194943295)
      ·
        refine ⟨21872369525789985292414943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14581579683859990194943295 21872369525789985292414943)
        ·
          refine ⟨32808554288684977938622415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21872369525789985292414943 32808554288684977938622415)
          ·
            refine ⟨49212831433027466907933623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32808554288684977938622415 49212831433027466907933623)
            ·
              refine ⟨73819247149541200361900435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49212831433027466907933623 73819247149541200361900435)
              ·
                refine ⟨110728870724311800542850653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73819247149541200361900435 110728870724311800542850653)
                ·
                  refine ⟨41523326521616925203568995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 110728870724311800542850653 41523326521616925203568995)
                  ·
                    refine ⟨62284989782425387805353493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41523326521616925203568995 62284989782425387805353493)
                    ·
                      refine ⟨2919608896051190053375945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62284989782425387805353493 2919608896051190053375945)
                      ·
                        rfl

theorem cell23_5685918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_5685918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5685918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5685918 prefixEnd_5685918 := by exact prefixLift 5685918
  have htrace : WordTrace (prefixWord ++ tailWord_5685918) baseStart_5685918 baseEnd_5685918 := by
    simpa [prefixWord, tailWord_5685918, baseEnd_5685918] using wordTrace_append hprefix tailTrace_5685918
  have hstable : (prefixWord ++ tailWord_5685918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5685918).length < 2 ^ (prefixWord ++ tailWord_5685918).sum := by decide
  have hdescent : baseEnd_5685918 < baseStart_5685918 := by decide
  rcases family_descends (prefixWord ++ tailWord_5685918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5685938 : List Nat := [3, 2, 1, 1, 1, 2, 1, 5, 1, 3, 3]
def baseStart_5685938 : Nat := 118140960795 + 5685938 * 2 ^ 59
def prefixEnd_5685938 : Nat := 4983230072969 + 3 ^ 40 * 5685938 * 2
def baseEnd_5685938 : Nat := 2919619165664279975125853

theorem tailTrace_5685938 : CollatzResearch.WordTrace tailWord_5685938 prefixEnd_5685938 2919619165664279975125853 := by
  unfold tailWord_5685938
  simp only [CollatzResearch.WordTrace]
  refine ⟨51845799018706295435952617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138255464049883454495873645 51845799018706295435952617)
  ·
    refine ⟨38884349264029721576964463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51845799018706295435952617 38884349264029721576964463)
    ·
      refine ⟨58326523896044582365446695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38884349264029721576964463 58326523896044582365446695)
      ·
        refine ⟨87489785844066873548170043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58326523896044582365446695 87489785844066873548170043)
        ·
          refine ⟨131234678766100310322255065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87489785844066873548170043 131234678766100310322255065)
          ·
            refine ⟨98426009074575232741691299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131234678766100310322255065 98426009074575232741691299)
            ·
              refine ⟨147639013611862849112536949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98426009074575232741691299 147639013611862849112536949)
              ·
                refine ⟨13841157526112142104300339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 147639013611862849112536949 13841157526112142104300339)
                ·
                  refine ⟨20761736289168213156450509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13841157526112142104300339 20761736289168213156450509)
                  ·
                    refine ⟨7785651108438079933668941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20761736289168213156450509 7785651108438079933668941)
                    ·
                      refine ⟨2919619165664279975125853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7785651108438079933668941 2919619165664279975125853)
                      ·
                        rfl

theorem cell23_5685938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 5, 1, 3, 3].length) (baseStart_5685938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5685938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5685938 prefixEnd_5685938 := by exact prefixLift 5685938
  have htrace : WordTrace (prefixWord ++ tailWord_5685938) baseStart_5685938 baseEnd_5685938 := by
    simpa [prefixWord, tailWord_5685938, baseEnd_5685938] using wordTrace_append hprefix tailTrace_5685938
  have hstable : (prefixWord ++ tailWord_5685938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5685938).length < 2 ^ (prefixWord ++ tailWord_5685938).sum := by decide
  have hdescent : baseEnd_5685938 < baseStart_5685938 := by decide
  rcases family_descends (prefixWord ++ tailWord_5685938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5685961 : List Nat := [1, 2, 1, 1, 2, 1, 1, 1, 6, 3, 4]
def baseStart_5685961 : Nat := 118140960795 + 5685961 * 2 ^ 59
def prefixEnd_5685961 : Nat := 4983230072969 + 3 ^ 40 * 5685961 * 2
def baseEnd_5685961 : Nat := 2919630975719333385138247

theorem tailTrace_5685961 : CollatzResearch.WordTrace tailWord_5685961 prefixEnd_5685961 2919630975719333385138247 := by
  unfold tailWord_5685961
  simp only [CollatzResearch.WordTrace]
  refine ⟨207384034953741856671897737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138256023302494571114598491 207384034953741856671897737)
  ·
    refine ⟨155538026215306392503923303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207384034953741856671897737 155538026215306392503923303)
    ·
      refine ⟨233307039322959588755884955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155538026215306392503923303 233307039322959588755884955)
      ·
        refine ⟨349960558984439383133827433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233307039322959588755884955 349960558984439383133827433)
        ·
          refine ⟨262470419238329537350370575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 349960558984439383133827433 262470419238329537350370575)
          ·
            refine ⟨393705628857494306025555863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 262470419238329537350370575 393705628857494306025555863)
            ·
              refine ⟨590558443286241459038333795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 393705628857494306025555863 590558443286241459038333795)
              ·
                refine ⟨885837664929362188557500693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 590558443286241459038333795 885837664929362188557500693)
                ·
                  refine ⟨41523640543563852588632845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 885837664929362188557500693 41523640543563852588632845)
                  ·
                    refine ⟨15571365203836444720737317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41523640543563852588632845 15571365203836444720737317)
                    ·
                      refine ⟨2919630975719333385138247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15571365203836444720737317 2919630975719333385138247)
                      ·
                        rfl

theorem cell23_5685961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 6, 3, 4].length) (baseStart_5685961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5685961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5685961 prefixEnd_5685961 := by exact prefixLift 5685961
  have htrace : WordTrace (prefixWord ++ tailWord_5685961) baseStart_5685961 baseEnd_5685961 := by
    simpa [prefixWord, tailWord_5685961, baseEnd_5685961] using wordTrace_append hprefix tailTrace_5685961
  have hstable : (prefixWord ++ tailWord_5685961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5685961).length < 2 ^ (prefixWord ++ tailWord_5685961).sum := by decide
  have hdescent : baseEnd_5685961 < baseStart_5685961 := by decide
  rcases family_descends (prefixWord ++ tailWord_5685961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5685988 : List Nat := [2, 3, 1, 1, 1, 5, 1, 1, 2, 6]
def baseStart_5685988 : Nat := 118140960795 + 5685988 * 2 ^ 59
def prefixEnd_5685988 : Nat := 4983230072969 + 3 ^ 40 * 5685988 * 2
def baseEnd_5685988 : Nat := 973214946565668259833541

theorem tailTrace_5685988 : CollatzResearch.WordTrace tailWord_5685988 prefixEnd_5685988 973214946565668259833541 := by
  unfold tailWord_5685988
  simp only [CollatzResearch.WordTrace]
  refine ⟨103692509862322020141565309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138256679816429360188753745 103692509862322020141565309)
  ·
    refine ⟨38884691198370757553086991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103692509862322020141565309 38884691198370757553086991)
    ·
      refine ⟨58327036797556136329630487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38884691198370757553086991 58327036797556136329630487)
      ·
        refine ⟨87490555196334204494445731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58327036797556136329630487 87490555196334204494445731)
        ·
          refine ⟨131235832794501306741668597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87490555196334204494445731 131235832794501306741668597)
          ·
            refine ⟨12303359324484497507031431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 131235832794501306741668597 12303359324484497507031431)
            ·
              refine ⟨18455038986726746260547147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12303359324484497507031431 18455038986726746260547147)
              ·
                refine ⟨27682558480090119390820721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18455038986726746260547147 27682558480090119390820721)
                ·
                  refine ⟨20761918860067589543115541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27682558480090119390820721 20761918860067589543115541)
                  ·
                    refine ⟨973214946565668259833541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20761918860067589543115541 973214946565668259833541)
                    ·
                      rfl

theorem cell23_5685988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 1, 2, 6].length) (baseStart_5685988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5685988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5685988 prefixEnd_5685988 := by exact prefixLift 5685988
  have htrace : WordTrace (prefixWord ++ tailWord_5685988) baseStart_5685988 baseEnd_5685988 := by
    simpa [prefixWord, tailWord_5685988, baseEnd_5685988] using wordTrace_append hprefix tailTrace_5685988
  have hstable : (prefixWord ++ tailWord_5685988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5685988).length < 2 ^ (prefixWord ++ tailWord_5685988).sum := by decide
  have hdescent : baseEnd_5685988 < baseStart_5685988 := by decide
  rcases family_descends (prefixWord ++ tailWord_5685988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5685995 : List Nat := [1, 1, 1, 1, 2, 4, 1, 2, 6, 2, 2]
def baseStart_5685995 : Nat := 118140960795 + 5685995 * 2 ^ 59
def prefixEnd_5685995 : Nat := 4983230072969 + 3 ^ 40 * 5685995 * 2
def baseEnd_5685995 : Nat := 2919648434061586252113091

theorem tailTrace_5685995 : CollatzResearch.WordTrace tailWord_5685995 prefixEnd_5685995 2919648434061586252113091 := by
  unfold tailWord_5685995
  simp only [CollatzResearch.WordTrace]
  refine ⟨207385275035618680478635439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138256850023745786985756959 207385275035618680478635439)
  ·
    refine ⟨311077912553428020717953159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207385275035618680478635439 311077912553428020717953159)
    ·
      refine ⟨466616868830142031076929739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 311077912553428020717953159 466616868830142031076929739)
      ·
        refine ⟨699925303245213046615394609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 466616868830142031076929739 699925303245213046615394609)
        ·
          refine ⟨524943977433909784961545957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 699925303245213046615394609 524943977433909784961545957)
          ·
            refine ⟨98426995768858084680289867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 524943977433909784961545957 98426995768858084680289867)
            ·
              refine ⟨147640493653287127020434801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98426995768858084680289867 147640493653287127020434801)
              ·
                refine ⟨110730370239965345265326101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 147640493653287127020434801 110730370239965345265326101)
                ·
                  refine ⟨5190486104998375559312161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 110730370239965345265326101 5190486104998375559312161)
                  ·
                    refine ⟨3892864578748781669484121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5190486104998375559312161 3892864578748781669484121)
                    ·
                      refine ⟨2919648434061586252113091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3892864578748781669484121 2919648434061586252113091)
                      ·
                        rfl

theorem cell23_5685995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 6, 2, 2].length) (baseStart_5685995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5685995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5685995 prefixEnd_5685995 := by exact prefixLift 5685995
  have htrace : WordTrace (prefixWord ++ tailWord_5685995) baseStart_5685995 baseEnd_5685995 := by
    simpa [prefixWord, tailWord_5685995, baseEnd_5685995] using wordTrace_append hprefix tailTrace_5685995
  have hstable : (prefixWord ++ tailWord_5685995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5685995).length < 2 ^ (prefixWord ++ tailWord_5685995).sum := by decide
  have hdescent : baseEnd_5685995 < baseStart_5685995 := by decide
  rcases family_descends (prefixWord ++ tailWord_5685995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5686048 : List Nat := [2, 1, 1, 5, 1, 2, 1, 2, 1, 7]
def baseStart_5686048 : Nat := 118140960795 + 5686048 * 2 ^ 59
def prefixEnd_5686048 : Nat := 4983230072969 + 3 ^ 40 * 5686048 * 2
def baseEnd_5686048 : Nat := 973225216178758181583449

theorem tailTrace_5686048 : CollatzResearch.WordTrace tailWord_5686048 prefixEnd_5686048 973225216178758181583449 := by
  unfold tailWord_5686048
  simp only [CollatzResearch.WordTrace]
  refine ⟨103693604052213335265157399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138258138736284447020209865 103693604052213335265157399)
  ·
    refine ⟨155540406078320002897736099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103693604052213335265157399 155540406078320002897736099)
    ·
      refine ⟨233310609117480004346604149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155540406078320002897736099 233310609117480004346604149)
      ·
        refine ⟨21872869604763750407494139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 233310609117480004346604149 21872869604763750407494139)
        ·
          refine ⟨32809304407145625611241209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21872869604763750407494139 32809304407145625611241209)
          ·
            refine ⟨24606978305359219208430907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32809304407145625611241209 24606978305359219208430907)
            ·
              refine ⟨36910467458038828812646361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24606978305359219208430907 36910467458038828812646361)
              ·
                refine ⟨27682850593529121609484771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36910467458038828812646361 27682850593529121609484771)
                ·
                  refine ⟨41524275890293682414227157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27682850593529121609484771 41524275890293682414227157)
                  ·
                    refine ⟨973225216178758181583449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41524275890293682414227157 973225216178758181583449)
                    ·
                      rfl

theorem cell23_5686048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 2, 1, 7].length) (baseStart_5686048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5686048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5686048 prefixEnd_5686048 := by exact prefixLift 5686048
  have htrace : WordTrace (prefixWord ++ tailWord_5686048) baseStart_5686048 baseEnd_5686048 := by
    simpa [prefixWord, tailWord_5686048, baseEnd_5686048] using wordTrace_append hprefix tailTrace_5686048
  have hstable : (prefixWord ++ tailWord_5686048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5686048).length < 2 ^ (prefixWord ++ tailWord_5686048).sum := by decide
  have hdescent : baseEnd_5686048 < baseStart_5686048 := by decide
  rcases family_descends (prefixWord ++ tailWord_5686048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5686085 : List Nat := [1, 3, 1, 1, 1, 2, 2, 4, 2, 4, 2]
def baseStart_5686085 : Nat := 118140960795 + 5686085 * 2 ^ 59
def prefixEnd_5686085 : Nat := 4983230072969 + 3 ^ 40 * 5686085 * 2
def baseEnd_5686085 : Nat := 2919694647320490899987677

theorem tailTrace_5686085 : CollatzResearch.WordTrace tailWord_5686085 prefixEnd_5686085 2919694647320490899987677 := by
  unfold tailWord_5686085
  simp only [CollatzResearch.WordTrace]
  refine ⟨207388557605292625849411709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138259038403528417232941139 207388557605292625849411709)
  ·
    refine ⟨77770709101984734693529391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 207388557605292625849411709 77770709101984734693529391)
    ·
      refine ⟨116656063652977102040294087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77770709101984734693529391 116656063652977102040294087)
      ·
        refine ⟨174984095479465653060441131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116656063652977102040294087 174984095479465653060441131)
        ·
          refine ⟨262476143219198479590661697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174984095479465653060441131 262476143219198479590661697)
          ·
            refine ⟨196857107414398859692996273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 262476143219198479590661697 196857107414398859692996273)
            ·
              refine ⟨147642830560799144769747205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 196857107414398859692996273 147642830560799144769747205)
              ·
                refine ⟨27683030730149839644327601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 147642830560799144769747205 27683030730149839644327601)
                ·
                  refine ⟨20762273047612379733245701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27683030730149839644327601 20762273047612379733245701)
                  ·
                    refine ⟨3892926196427321199983569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20762273047612379733245701 3892926196427321199983569)
                    ·
                      refine ⟨2919694647320490899987677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3892926196427321199983569 2919694647320490899987677)
                      ·
                        rfl

theorem cell23_5686085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 4, 2, 4, 2].length) (baseStart_5686085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5686085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5686085 prefixEnd_5686085 := by exact prefixLift 5686085
  have htrace : WordTrace (prefixWord ++ tailWord_5686085) baseStart_5686085 baseEnd_5686085 := by
    simpa [prefixWord, tailWord_5686085, baseEnd_5686085] using wordTrace_append hprefix tailTrace_5686085
  have hstable : (prefixWord ++ tailWord_5686085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5686085).length < 2 ^ (prefixWord ++ tailWord_5686085).sum := by decide
  have hdescent : baseEnd_5686085 < baseStart_5686085 := by decide
  rcases family_descends (prefixWord ++ tailWord_5686085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5686086 : List Nat := [6, 1, 1, 2, 3, 1, 1, 1, 7]
def baseStart_5686086 : Nat := 118140960795 + 5686086 * 2 ^ 59
def prefixEnd_5686086 : Nat := 4983230072969 + 3 ^ 40 * 5686086 * 2
def baseEnd_5686086 : Nat := 324410573422349488452797

theorem tailTrace_5686086 : CollatzResearch.WordTrace tailWord_5686086 prefixEnd_5686086 324410573422349488452797 := by
  unfold tailWord_5686086
  simp only [CollatzResearch.WordTrace]
  refine ⟨6480893564946531344381191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 138259062718859335346798741 6480893564946531344381191)
  ·
    refine ⟨9721340347419797016571787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6480893564946531344381191 9721340347419797016571787)
    ·
      refine ⟨14582010521129695524857681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9721340347419797016571787 14582010521129695524857681)
      ·
        refine ⟨10936507890847271643643261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14582010521129695524857681 10936507890847271643643261)
        ·
          refine ⟨4101190459067726866366223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10936507890847271643643261 4101190459067726866366223)
          ·
            refine ⟨6151785688601590299549335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4101190459067726866366223 6151785688601590299549335)
            ·
              refine ⟨9227678532902385449324003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6151785688601590299549335 9227678532902385449324003)
              ·
                refine ⟨13841517799353578173986005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9227678532902385449324003 13841517799353578173986005)
                ·
                  refine ⟨324410573422349488452797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13841517799353578173986005 324410573422349488452797)
                  ·
                    rfl

theorem cell23_5686086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 3, 1, 1, 1, 7].length) (baseStart_5686086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5686086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5686086 prefixEnd_5686086 := by exact prefixLift 5686086
  have htrace : WordTrace (prefixWord ++ tailWord_5686086) baseStart_5686086 baseEnd_5686086 := by
    simpa [prefixWord, tailWord_5686086, baseEnd_5686086] using wordTrace_append hprefix tailTrace_5686086
  have hstable : (prefixWord ++ tailWord_5686086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5686086).length < 2 ^ (prefixWord ++ tailWord_5686086).sum := by decide
  have hdescent : baseEnd_5686086 < baseStart_5686086 := by decide
  rcases family_descends (prefixWord ++ tailWord_5686086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5686185 : List Nat := [1, 2, 1, 1, 1, 1, 6, 2, 4, 4]
def baseStart_5686185 : Nat := 118140960795 + 5686185 * 2 ^ 59
def prefixEnd_5686185 : Nat := 4983230072969 + 3 ^ 40 * 5686185 * 2
def baseEnd_5686185 : Nat := 973248665128646836245739

theorem tailTrace_5686185 : CollatzResearch.WordTrace tailWord_5686185 prefixEnd_5686185 973248665128646836245739 := by
  unfold tailWord_5686185
  simp only [CollatzResearch.WordTrace]
  refine ⟨207392204904930342928052009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138261469936620228618701339 207392204904930342928052009)
  ·
    refine ⟨155544153678697757196039007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207392204904930342928052009 155544153678697757196039007)
    ·
      refine ⟨233316230518046635794058511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155544153678697757196039007 233316230518046635794058511)
      ·
        refine ⟨349974345777069953691087767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233316230518046635794058511 349974345777069953691087767)
        ·
          refine ⟨524961518665604930536631651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 349974345777069953691087767 524961518665604930536631651)
          ·
            refine ⟨787442277998407395804947477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 524961518665604930536631651 787442277998407395804947477)
            ·
              refine ⟨36911356781175346678356913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 787442277998407395804947477 36911356781175346678356913)
              ·
                refine ⟨27683517585881510008767685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36911356781175346678356913 27683517585881510008767685)
                ·
                  refine ⟨5190659547352783126643941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27683517585881510008767685 5190659547352783126643941)
                  ·
                    refine ⟨973248665128646836245739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5190659547352783126643941 973248665128646836245739)
                    ·
                      rfl

theorem cell23_5686185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 2, 4, 4].length) (baseStart_5686185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5686185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5686185 prefixEnd_5686185 := by exact prefixLift 5686185
  have htrace : WordTrace (prefixWord ++ tailWord_5686185) baseStart_5686185 baseEnd_5686185 := by
    simpa [prefixWord, tailWord_5686185, baseEnd_5686185] using wordTrace_append hprefix tailTrace_5686185
  have hstable : (prefixWord ++ tailWord_5686185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5686185).length < 2 ^ (prefixWord ++ tailWord_5686185).sum := by decide
  have hdescent : baseEnd_5686185 < baseStart_5686185 := by decide
  rcases family_descends (prefixWord ++ tailWord_5686185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5686195 : List Nat := [1, 1, 1, 2, 3, 1, 2, 2, 5, 2, 3]
def baseStart_5686195 : Nat := 118140960795 + 5686195 * 2 ^ 59
def prefixEnd_5686195 : Nat := 4983230072969 + 3 ^ 40 * 5686195 * 2
def baseEnd_5686195 : Nat := 2919751130192485469612171

theorem tailTrace_5686195 : CollatzResearch.WordTrace tailWord_5686195 prefixEnd_5686195 2919751130192485469612171 := by
  unfold tailWord_5686195
  simp only [CollatzResearch.WordTrace]
  refine ⟨207392569634894114635916039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138261713089929409757277359 207392569634894114635916039)
  ·
    refine ⟨311088854452341171953874059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207392569634894114635916039 311088854452341171953874059)
    ·
      refine ⟨466633281678511757930811089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 311088854452341171953874059 466633281678511757930811089)
      ·
        refine ⟨349974961258883818448108317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 466633281678511757930811089 349974961258883818448108317)
        ·
          refine ⟨131240610472081431918040619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 349974961258883818448108317 131240610472081431918040619)
          ·
            refine ⟨196860915708122147877060929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131240610472081431918040619 196860915708122147877060929)
            ·
              refine ⟨147645686781091610907795697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 196860915708122147877060929 147645686781091610907795697)
              ·
                refine ⟨110734265085818708180846773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 147645686781091610907795697 110734265085818708180846773)
                ·
                  refine ⟨10381337351795503891954385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 110734265085818708180846773 10381337351795503891954385)
                  ·
                    refine ⟨7786003013846627918965789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10381337351795503891954385 7786003013846627918965789)
                    ·
                      refine ⟨2919751130192485469612171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7786003013846627918965789 2919751130192485469612171)
                      ·
                        rfl

theorem cell23_5686195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 2, 5, 2, 3].length) (baseStart_5686195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5686195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5686195 prefixEnd_5686195 := by exact prefixLift 5686195
  have htrace : WordTrace (prefixWord ++ tailWord_5686195) baseStart_5686195 baseEnd_5686195 := by
    simpa [prefixWord, tailWord_5686195, baseEnd_5686195] using wordTrace_append hprefix tailTrace_5686195
  have hstable : (prefixWord ++ tailWord_5686195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5686195).length < 2 ^ (prefixWord ++ tailWord_5686195).sum := by decide
  have hdescent : baseEnd_5686195 < baseStart_5686195 := by decide
  rcases family_descends (prefixWord ++ tailWord_5686195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5686219 : List Nat := [1, 1, 1, 1, 3, 6, 3, 1, 2, 4]
def baseStart_5686219 : Nat := 118140960795 + 5686219 * 2 ^ 59
def prefixEnd_5686219 : Nat := 4983230072969 + 3 ^ 40 * 5686219 * 2
def baseEnd_5686219 : Nat := 973254484576064458570687

theorem tailTrace_5686219 : CollatzResearch.WordTrace tailWord_5686219 prefixEnd_5686219 973254484576064458570687 := by
  unfold tailWord_5686219
  simp only [CollatzResearch.WordTrace]
  refine ⟨207393444986807166734789711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138262296657871444489859807 207393444986807166734789711)
  ·
    refine ⟨311090167480210750102184567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207393444986807166734789711 311090167480210750102184567)
    ·
      refine ⟨466635251220316125153276851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 311090167480210750102184567 466635251220316125153276851)
      ·
        refine ⟨699952876830474187729915277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 466635251220316125153276851 699952876830474187729915277)
        ·
          refine ⟨262482328811427820398718229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 699952876830474187729915277 262482328811427820398718229)
          ·
            refine ⟨12303859163035679081189917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 262482328811427820398718229 12303859163035679081189917)
            ·
              refine ⟨4613947186138379655446219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12303859163035679081189917 4613947186138379655446219)
              ·
                refine ⟨6920920779207569483169329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4613947186138379655446219 6920920779207569483169329)
                ·
                  refine ⟨5190690584405677112376997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6920920779207569483169329 5190690584405677112376997)
                  ·
                    refine ⟨973254484576064458570687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5190690584405677112376997 973254484576064458570687)
                    ·
                      rfl

theorem cell23_5686219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 3, 1, 2, 4].length) (baseStart_5686219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5686219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5686219 prefixEnd_5686219 := by exact prefixLift 5686219
  have htrace : WordTrace (prefixWord ++ tailWord_5686219) baseStart_5686219 baseEnd_5686219 := by
    simpa [prefixWord, tailWord_5686219, baseEnd_5686219] using wordTrace_append hprefix tailTrace_5686219
  have hstable : (prefixWord ++ tailWord_5686219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5686219).length < 2 ^ (prefixWord ++ tailWord_5686219).sum := by decide
  have hdescent : baseEnd_5686219 < baseStart_5686219 := by decide
  rcases family_descends (prefixWord ++ tailWord_5686219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5686222 : List Nat := [4, 1, 1, 1, 2, 3, 3, 1, 1, 2, 4]
def baseStart_5686222 : Nat := 118140960795 + 5686222 * 2 ^ 59
def prefixEnd_5686222 : Nat := 4983230072969 + 3 ^ 40 * 5686222 * 2
def baseEnd_5686222 : Nat := 2919764994170156863974547

theorem tailTrace_5686222 : CollatzResearch.WordTrace tailWord_5686222 prefixEnd_5686222 2919764994170156863974547 := by
  unfold tailWord_5686222
  simp only [CollatzResearch.WordTrace]
  refine ⟨25924194300724537280893615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138262369603864198831432613 25924194300724537280893615)
  ·
    refine ⟨38886291451086805921340423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25924194300724537280893615 38886291451086805921340423)
    ·
      refine ⟨58329437176630208882010635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38886291451086805921340423 58329437176630208882010635)
      ·
        refine ⟨87494155764945313323015953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58329437176630208882010635 87494155764945313323015953)
        ·
          refine ⟨65620616823708984992261965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87494155764945313323015953 65620616823708984992261965)
          ·
            refine ⟨24607731308890869372098237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65620616823708984992261965 24607731308890869372098237)
            ·
              refine ⟨9227899240834076014536839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24607731308890869372098237 9227899240834076014536839)
              ·
                refine ⟨13841848861251114021805259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9227899240834076014536839 13841848861251114021805259)
                ·
                  refine ⟨20762773291876671032707889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13841848861251114021805259 20762773291876671032707889)
                  ·
                    refine ⟨15572079968907503274530917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20762773291876671032707889 15572079968907503274530917)
                    ·
                      refine ⟨2919764994170156863974547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15572079968907503274530917 2919764994170156863974547)
                      ·
                        rfl

theorem cell23_5686222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 3, 1, 1, 2, 4].length) (baseStart_5686222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5686222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5686222 prefixEnd_5686222 := by exact prefixLift 5686222
  have htrace : WordTrace (prefixWord ++ tailWord_5686222) baseStart_5686222 baseEnd_5686222 := by
    simpa [prefixWord, tailWord_5686222, baseEnd_5686222] using wordTrace_append hprefix tailTrace_5686222
  have hstable : (prefixWord ++ tailWord_5686222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5686222).length < 2 ^ (prefixWord ++ tailWord_5686222).sum := by decide
  have hdescent : baseEnd_5686222 < baseStart_5686222 := by decide
  rcases family_descends (prefixWord ++ tailWord_5686222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5686226 : List Nat := [3, 2, 2, 3, 1, 1, 2, 2, 3, 2, 2]
def baseStart_5686226 : Nat := 118140960795 + 5686226 * 2 ^ 59
def prefixEnd_5686226 : Nat := 4983230072969 + 3 ^ 40 * 5686226 * 2
def baseEnd_5686226 : Nat := 2919767048092774848324529

theorem tailTrace_5686226 : CollatzResearch.WordTrace tailWord_5686226 prefixEnd_5686226 2919767048092774848324529 := by
  unfold tailWord_5686226
  simp only [CollatzResearch.WordTrace]
  refine ⟨51848425074445451732573633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138262466865187871286863021 51848425074445451732573633)
  ·
    refine ⟨38886318805834088799430225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51848425074445451732573633 38886318805834088799430225)
    ·
      refine ⟨29164739104375566599572669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38886318805834088799430225 29164739104375566599572669)
      ·
        refine ⟨10936777164140837474839751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29164739104375566599572669 10936777164140837474839751)
        ·
          refine ⟨16405165746211256212259627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10936777164140837474839751 16405165746211256212259627)
          ·
            refine ⟨24607748619316884318389441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16405165746211256212259627 24607748619316884318389441)
            ·
              refine ⟨18455811464487663238792081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24607748619316884318389441 18455811464487663238792081)
              ·
                refine ⟨13841858598365747429094061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18455811464487663238792081 13841858598365747429094061)
                ·
                  refine ⟨5190696974387155285910273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13841858598365747429094061 5190696974387155285910273)
                  ·
                    refine ⟨3893022730790366464432705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5190696974387155285910273 3893022730790366464432705)
                    ·
                      refine ⟨2919767048092774848324529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3893022730790366464432705 2919767048092774848324529)
                      ·
                        rfl

theorem cell23_5686226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 2, 3, 2, 2].length) (baseStart_5686226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5686226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5686226 prefixEnd_5686226 := by exact prefixLift 5686226
  have htrace : WordTrace (prefixWord ++ tailWord_5686226) baseStart_5686226 baseEnd_5686226 := by
    simpa [prefixWord, tailWord_5686226, baseEnd_5686226] using wordTrace_append hprefix tailTrace_5686226
  have hstable : (prefixWord ++ tailWord_5686226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5686226).length < 2 ^ (prefixWord ++ tailWord_5686226).sum := by decide
  have hdescent : baseEnd_5686226 < baseStart_5686226 := by decide
  rcases family_descends (prefixWord ++ tailWord_5686226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5686232 : List Nat := [2, 1, 2, 2, 2, 5, 2, 7]
def baseStart_5686232 : Nat := 118140960795 + 5686232 * 2 ^ 59
def prefixEnd_5686232 : Nat := 4983230072969 + 3 ^ 40 * 5686232 * 2
def baseEnd_5686232 : Nat := 108139634406544512031463

theorem tailTrace_5686232 : CollatzResearch.WordTrace tailWord_5686232 prefixEnd_5686232 108139634406544512031463 := by
  unfold tailWord_5686232
  simp only [CollatzResearch.WordTrace]
  refine ⟨103696959567880034977506475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138262612757173379970008633 103696959567880034977506475)
  ·
    refine ⟨155545439351820052466259713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103696959567880034977506475 155545439351820052466259713)
    ·
      refine ⟨116659079513865039349694785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155545439351820052466259713 116659079513865039349694785)
      ·
        refine ⟨87494309635398779512271089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116659079513865039349694785 87494309635398779512271089)
        ·
          refine ⟨65620732226549084634203317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87494309635398779512271089 65620732226549084634203317)
          ·
            refine ⟨6151943646238976684456561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 65620732226549084634203317 6151943646238976684456561)
            ·
              refine ⟨4613957734679232513342421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6151943646238976684456561 4613957734679232513342421)
              ·
                refine ⟨108139634406544512031463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4613957734679232513342421 108139634406544512031463)
                ·
                  rfl

theorem cell23_5686232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 2, 7].length) (baseStart_5686232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5686232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5686232 prefixEnd_5686232 := by exact prefixLift 5686232
  have htrace : WordTrace (prefixWord ++ tailWord_5686232) baseStart_5686232 baseEnd_5686232 := by
    simpa [prefixWord, tailWord_5686232, baseEnd_5686232] using wordTrace_append hprefix tailTrace_5686232
  have hstable : (prefixWord ++ tailWord_5686232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5686232).length < 2 ^ (prefixWord ++ tailWord_5686232).sum := by decide
  have hdescent : baseEnd_5686232 < baseStart_5686232 := by decide
  rcases family_descends (prefixWord ++ tailWord_5686232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5686252 : List Nat := [2, 2, 1, 1, 2, 1, 1, 1, 7, 3, 2]
def baseStart_5686252 : Nat := 118140960795 + 5686252 * 2 ^ 59
def prefixEnd_5686252 : Nat := 4983230072969 + 3 ^ 40 * 5686252 * 2
def baseEnd_5686252 : Nat := 2919780398589791746599409

theorem tailTrace_5686252 : CollatzResearch.WordTrace tailWord_5686252 prefixEnd_5686252 2919780398589791746599409 := by
  unfold tailWord_5686252
  simp only [CollatzResearch.WordTrace]
  refine ⟨103697324297843806685370505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138263099063791742247160673 103697324297843806685370505)
  ·
    refine ⟨77772993223382855014027879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103697324297843806685370505 77772993223382855014027879)
    ·
      refine ⟨116659489835074282521041819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77772993223382855014027879 116659489835074282521041819)
      ·
        refine ⟨174989234752611423781562729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116659489835074282521041819 174989234752611423781562729)
        ·
          refine ⟨131241926064458567836172047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 174989234752611423781562729 131241926064458567836172047)
          ·
            refine ⟨196862889096687851754258071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131241926064458567836172047 196862889096687851754258071)
            ·
              refine ⟨295294333645031777631387107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 196862889096687851754258071 295294333645031777631387107)
              ·
                refine ⟨442941500467547666447080661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 295294333645031777631387107 442941500467547666447080661)
                ·
                  refine ⟨10381441417208148432353453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 442941500467547666447080661 10381441417208148432353453)
                  ·
                    refine ⟨3893040531453055662132545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10381441417208148432353453 3893040531453055662132545)
                    ·
                      refine ⟨2919780398589791746599409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3893040531453055662132545 2919780398589791746599409)
                      ·
                        rfl

theorem cell23_5686252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 3, 2].length) (baseStart_5686252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5686252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5686252 prefixEnd_5686252 := by exact prefixLift 5686252
  have htrace : WordTrace (prefixWord ++ tailWord_5686252) baseStart_5686252 baseEnd_5686252 := by
    simpa [prefixWord, tailWord_5686252, baseEnd_5686252] using wordTrace_append hprefix tailTrace_5686252
  have hstable : (prefixWord ++ tailWord_5686252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5686252).length < 2 ^ (prefixWord ++ tailWord_5686252).sum := by decide
  have hdescent : baseEnd_5686252 < baseStart_5686252 := by decide
  rcases family_descends (prefixWord ++ tailWord_5686252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5686265 : List Nat := [1, 2, 1, 3, 1, 3, 2, 1, 2, 3, 4]
def baseStart_5686265 : Nat := 118140960795 + 5686265 * 2 ^ 59
def prefixEnd_5686265 : Nat := 4983230072969 + 3 ^ 40 * 5686265 * 2
def baseEnd_5686265 : Nat := 2919787073838300195736849

theorem tailTrace_5686265 : CollatzResearch.WordTrace tailWord_5686265 prefixEnd_5686265 2919787073838300195736849 := by
  unfold tailWord_5686265
  simp only [CollatzResearch.WordTrace]
  refine ⟨207395122744640516590964249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138263415163093677727309499 207395122744640516590964249)
  ·
    refine ⟨155546342058480387443223187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207395122744640516590964249 155546342058480387443223187)
    ·
      refine ⟨233319513087720581164834781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155546342058480387443223187 233319513087720581164834781)
      ·
        refine ⟨87494817407895217936813043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 233319513087720581164834781 87494817407895217936813043)
        ·
          refine ⟨131242226111842826905219565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87494817407895217936813043 131242226111842826905219565)
          ·
            refine ⟨49215834791941060089457337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 131242226111842826905219565 49215834791941060089457337)
            ·
              refine ⟨36911876093955795067093003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49215834791941060089457337 36911876093955795067093003)
              ·
                refine ⟨55367814140933692600639505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36911876093955795067093003 55367814140933692600639505)
                ·
                  refine ⟨41525860605700269450479629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55367814140933692600639505 41525860605700269450479629)
                  ·
                    refine ⟨15572197727137601043929861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41525860605700269450479629 15572197727137601043929861)
                    ·
                      refine ⟨2919787073838300195736849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15572197727137601043929861 2919787073838300195736849)
                      ·
                        rfl

theorem cell23_5686265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 1, 2, 3, 4].length) (baseStart_5686265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5686265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5686265 prefixEnd_5686265 := by exact prefixLift 5686265
  have htrace : WordTrace (prefixWord ++ tailWord_5686265) baseStart_5686265 baseEnd_5686265 := by
    simpa [prefixWord, tailWord_5686265, baseEnd_5686265] using wordTrace_append hprefix tailTrace_5686265
  have hstable : (prefixWord ++ tailWord_5686265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5686265).length < 2 ^ (prefixWord ++ tailWord_5686265).sum := by decide
  have hdescent : baseEnd_5686265 < baseStart_5686265 := by decide
  rcases family_descends (prefixWord ++ tailWord_5686265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5686270 : List Nat := [4, 2, 2, 2, 3, 1, 2, 1, 2, 4]
def baseStart_5686270 : Nat := 118140960795 + 5686270 * 2 ^ 59
def prefixEnd_5686270 : Nat := 4983230072969 + 3 ^ 40 * 5686270 * 2
def baseEnd_5686270 : Nat := 973263213747190892058109

theorem tailTrace_5686270 : CollatzResearch.WordTrace tailWord_5686270 prefixEnd_5686270 973263213747190892058109 := by
  unfold tailWord_5686270
  simp only [CollatzResearch.WordTrace]
  refine ⟨25924413138702800305612033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138263536739748268296597509 25924413138702800305612033)
  ·
    refine ⟨19443309854027100229209025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25924413138702800305612033 19443309854027100229209025)
    ·
      refine ⟨14582482390520325171906769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19443309854027100229209025 14582482390520325171906769)
      ·
        refine ⟨10936861792890243878930077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14582482390520325171906769 10936861792890243878930077)
        ·
          refine ⟨4101323172333841454598779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10936861792890243878930077 4101323172333841454598779)
          ·
            refine ⟨6151984758500762181898169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4101323172333841454598779 6151984758500762181898169)
            ·
              refine ⟨4613988568875571636423627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6151984758500762181898169 4613988568875571636423627)
              ·
                refine ⟨6920982853313357454635441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4613988568875571636423627 6920982853313357454635441)
                ·
                  refine ⟨5190737139985018090976581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6920982853313357454635441 5190737139985018090976581)
                  ·
                    refine ⟨973263213747190892058109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5190737139985018090976581 973263213747190892058109)
                    ·
                      rfl

theorem cell23_5686270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 2, 1, 2, 4].length) (baseStart_5686270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5686270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5686270 prefixEnd_5686270 := by exact prefixLift 5686270
  have htrace : WordTrace (prefixWord ++ tailWord_5686270) baseStart_5686270 baseEnd_5686270 := by
    simpa [prefixWord, tailWord_5686270, baseEnd_5686270] using wordTrace_append hprefix tailTrace_5686270
  have hstable : (prefixWord ++ tailWord_5686270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5686270).length < 2 ^ (prefixWord ++ tailWord_5686270).sum := by decide
  have hdescent : baseEnd_5686270 < baseStart_5686270 := by decide
  rcases family_descends (prefixWord ++ tailWord_5686270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5686286 : List Nat := [4, 1, 1, 2, 2, 2, 3, 2, 1, 3, 2]
def baseStart_5686286 : Nat := 118140960795 + 5686286 * 2 ^ 59
def prefixEnd_5686286 : Nat := 4983230072969 + 3 ^ 40 * 5686286 * 2
def baseEnd_5686286 : Nat := 2919797856932044613574253

theorem tailTrace_5686286 : CollatzResearch.WordTrace tailWord_5686286 prefixEnd_5686286 2919797856932044613574253 := by
  unfold tailWord_5686286
  simp only [CollatzResearch.WordTrace]
  refine ⟨25924486084695554647184839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138263925785042958118319141 25924486084695554647184839)
  ·
    refine ⟨38886729127043331970777259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25924486084695554647184839 38886729127043331970777259)
    ·
      refine ⟨58330093690564997956165889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38886729127043331970777259 58330093690564997956165889)
      ·
        refine ⟨43747570267923748467124417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58330093690564997956165889 43747570267923748467124417)
        ·
          refine ⟨32810677700942811350343313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43747570267923748467124417 32810677700942811350343313)
          ·
            refine ⟨24608008275707108512757485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32810677700942811350343313 24608008275707108512757485)
            ·
              refine ⟨9228003103390165692284057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24608008275707108512757485 9228003103390165692284057)
              ·
                refine ⟨6921002327542624269213043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9228003103390165692284057 6921002327542624269213043)
                ·
                  refine ⟨10381503491313936403819565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6921002327542624269213043 10381503491313936403819565)
                  ·
                    refine ⟨3893063809242726151432337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10381503491313936403819565 3893063809242726151432337)
                    ·
                      refine ⟨2919797856932044613574253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3893063809242726151432337 2919797856932044613574253)
                      ·
                        rfl

theorem cell23_5686286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 3, 2, 1, 3, 2].length) (baseStart_5686286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5686286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5686286 prefixEnd_5686286 := by exact prefixLift 5686286
  have htrace : WordTrace (prefixWord ++ tailWord_5686286) baseStart_5686286 baseEnd_5686286 := by
    simpa [prefixWord, tailWord_5686286, baseEnd_5686286] using wordTrace_append hprefix tailTrace_5686286
  have hstable : (prefixWord ++ tailWord_5686286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5686286).length < 2 ^ (prefixWord ++ tailWord_5686286).sum := by decide
  have hdescent : baseEnd_5686286 < baseStart_5686286 := by decide
  rcases family_descends (prefixWord ++ tailWord_5686286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5686316 : List Nat := [2, 2, 1, 1, 1, 2, 6, 2, 2, 2, 2]
def baseStart_5686316 : Nat := 118140960795 + 5686316 * 2 ^ 59
def prefixEnd_5686316 : Nat := 4983230072969 + 3 ^ 40 * 5686316 * 2
def baseEnd_5686316 : Nat := 2919813261351679496199115

theorem tailTrace_5686316 : CollatzResearch.WordTrace tailWord_5686316 prefixEnd_5686316 2919813261351679496199115 := by
  unfold tailWord_5686316
  simp only [CollatzResearch.WordTrace]
  refine ⟨103698491433727876150535401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138264655244970501534047201 103698491433727876150535401)
  ·
    refine ⟨77773868575295907112901551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103698491433727876150535401 77773868575295907112901551)
    ·
      refine ⟨116660802862943860669352327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77773868575295907112901551 116660802862943860669352327)
      ·
        refine ⟨174991204294415791004028491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116660802862943860669352327 174991204294415791004028491)
        ·
          refine ⟨262486806441623686506042737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174991204294415791004028491 262486806441623686506042737)
          ·
            refine ⟨196865104831217764879532053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 262486806441623686506042737 196865104831217764879532053)
            ·
              refine ⟨9228051788963332728728065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 196865104831217764879532053 9228051788963332728728065)
              ·
                refine ⟨6921038841722499546546049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9228051788963332728728065 6921038841722499546546049)
                ·
                  refine ⟨5190779131291874659909537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6921038841722499546546049 5190779131291874659909537)
                  ·
                    refine ⟨3893084348468905994932153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5190779131291874659909537 3893084348468905994932153)
                    ·
                      refine ⟨2919813261351679496199115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3893084348468905994932153 2919813261351679496199115)
                      ·
                        rfl

theorem cell23_5686316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 2, 2].length) (baseStart_5686316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5686316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5686316 prefixEnd_5686316 := by exact prefixLift 5686316
  have htrace : WordTrace (prefixWord ++ tailWord_5686316) baseStart_5686316 baseEnd_5686316 := by
    simpa [prefixWord, tailWord_5686316, baseEnd_5686316] using wordTrace_append hprefix tailTrace_5686316
  have hstable : (prefixWord ++ tailWord_5686316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5686316).length < 2 ^ (prefixWord ++ tailWord_5686316).sum := by decide
  have hdescent : baseEnd_5686316 < baseStart_5686316 := by decide
  rcases family_descends (prefixWord ++ tailWord_5686316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5686325 : List Nat := [1, 3, 3, 1, 1, 1, 1, 1, 2, 1, 8]
def baseStart_5686325 : Nat := 118140960795 + 5686325 * 2 ^ 59
def prefixEnd_5686325 : Nat := 4983230072969 + 3 ^ 40 * 5686325 * 2
def baseEnd_5686325 : Nat := 2919817882677569960986573

theorem tailTrace_5686325 : CollatzResearch.WordTrace tailWord_5686325 prefixEnd_5686325 2919817882677569960986573 := by
  unfold tailWord_5686325
  simp only [CollatzResearch.WordTrace]
  refine ⟨207397311124423146838148429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138264874082948764558765619 207397311124423146838148429)
  ·
    refine ⟨77773991671658680064305661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 207397311124423146838148429 77773991671658680064305661)
    ·
      refine ⟨29165246876872005024114623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77773991671658680064305661 29165246876872005024114623)
      ·
        refine ⟨43747870315308007536171935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29165246876872005024114623 43747870315308007536171935)
        ·
          refine ⟨65621805472962011304257903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43747870315308007536171935 65621805472962011304257903)
          ·
            refine ⟨98432708209443016956386855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65621805472962011304257903 98432708209443016956386855)
            ·
              refine ⟨147649062314164525434580283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98432708209443016956386855 147649062314164525434580283)
              ·
                refine ⟨221473593471246788151870425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 147649062314164525434580283 221473593471246788151870425)
                ·
                  refine ⟨166105195103435091113902819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 221473593471246788151870425 166105195103435091113902819)
                  ·
                    refine ⟨249157792655152636670854229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 166105195103435091113902819 249157792655152636670854229)
                    ·
                      refine ⟨2919817882677569960986573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 249157792655152636670854229 2919817882677569960986573)
                      ·
                        rfl

theorem cell23_5686325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 1, 8].length) (baseStart_5686325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5686325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5686325 prefixEnd_5686325 := by exact prefixLift 5686325
  have htrace : WordTrace (prefixWord ++ tailWord_5686325) baseStart_5686325 baseEnd_5686325 := by
    simpa [prefixWord, tailWord_5686325, baseEnd_5686325] using wordTrace_append hprefix tailTrace_5686325
  have hstable : (prefixWord ++ tailWord_5686325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5686325).length < 2 ^ (prefixWord ++ tailWord_5686325).sum := by decide
  have hdescent : baseEnd_5686325 < baseStart_5686325 := by decide
  rcases family_descends (prefixWord ++ tailWord_5686325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5686332 : List Nat := [2, 2, 2, 2, 2, 2, 1, 1, 1, 5, 3]
def baseStart_5686332 : Nat := 118140960795 + 5686332 * 2 ^ 59
def prefixEnd_5686332 : Nat := 4983230072969 + 3 ^ 40 * 5686332 * 2
def baseEnd_5686332 : Nat := 2919821477042151433599041

theorem tailTrace_5686332 : CollatzResearch.WordTrace tailWord_5686332 prefixEnd_5686332 2919821477042151433599041 := by
  unfold tailWord_5686332
  simp only [CollatzResearch.WordTrace]
  refine ⟨103698783217698893516826625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138265044290265191355768833 103698783217698893516826625)
  ·
    refine ⟨77774087413274170137619969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103698783217698893516826625 77774087413274170137619969)
    ·
      refine ⟨58330565559955627603214977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77774087413274170137619969 58330565559955627603214977)
      ·
        refine ⟨43747924169966720702411233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58330565559955627603214977 43747924169966720702411233)
        ·
          refine ⟨32810943127475040526808425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43747924169966720702411233 32810943127475040526808425)
          ·
            refine ⟨24608207345606280395106319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32810943127475040526808425 24608207345606280395106319)
            ·
              refine ⟨36912311018409420592659479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24608207345606280395106319 36912311018409420592659479)
              ·
                refine ⟨55368466527614130888989219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36912311018409420592659479 55368466527614130888989219)
                ·
                  refine ⟨83052699791421196333483829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55368466527614130888989219 83052699791421196333483829)
                  ·
                    refine ⟨7786190605445737156264109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 83052699791421196333483829 7786190605445737156264109)
                    ·
                      refine ⟨2919821477042151433599041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7786190605445737156264109 2919821477042151433599041)
                      ·
                        rfl

theorem cell23_5686332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 1, 1, 5, 3].length) (baseStart_5686332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5686332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5686332 prefixEnd_5686332 := by exact prefixLift 5686332
  have htrace : WordTrace (prefixWord ++ tailWord_5686332) baseStart_5686332 baseEnd_5686332 := by
    simpa [prefixWord, tailWord_5686332, baseEnd_5686332] using wordTrace_append hprefix tailTrace_5686332
  have hstable : (prefixWord ++ tailWord_5686332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5686332).length < 2 ^ (prefixWord ++ tailWord_5686332).sum := by decide
  have hdescent : baseEnd_5686332 < baseStart_5686332 := by decide
  rcases family_descends (prefixWord ++ tailWord_5686332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5686335 : List Nat := [1, 1, 2, 2, 3, 1, 1, 4, 1, 7]
def baseStart_5686335 : Nat := 118140960795 + 5686335 * 2 ^ 59
def prefixEnd_5686335 : Nat := 4983230072969 + 3 ^ 40 * 5686335 * 2
def baseEnd_5686335 : Nat := 973274339161371640620509

theorem tailTrace_5686335 : CollatzResearch.WordTrace tailWord_5686335 prefixEnd_5686335 973274339161371640620509 := by
  unfold tailWord_5686335
  simp only [CollatzResearch.WordTrace]
  refine ⟨207397675854386918546012459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138265117236257945697341639 207397675854386918546012459)
  ·
    refine ⟨311096513781580377819018689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207397675854386918546012459 311096513781580377819018689)
    ·
      refine ⟨233322385336185283364264017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 311096513781580377819018689 233322385336185283364264017)
      ·
        refine ⟨174991789002138962523198013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 233322385336185283364264017 174991789002138962523198013)
        ·
          refine ⟨65621920875802110946199255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 174991789002138962523198013 65621920875802110946199255)
          ·
            refine ⟨98432881313703166419298883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65621920875802110946199255 98432881313703166419298883)
            ·
              refine ⟨147649321970554749628948325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98432881313703166419298883 147649321970554749628948325)
              ·
                refine ⟨27684247869479015555427811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 147649321970554749628948325 27684247869479015555427811)
                ·
                  refine ⟨41526371804218523333141717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27684247869479015555427811 41526371804218523333141717)
                  ·
                    refine ⟨973274339161371640620509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41526371804218523333141717 973274339161371640620509)
                    ·
                      rfl

theorem cell23_5686335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 4, 1, 7].length) (baseStart_5686335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5686335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5686335 prefixEnd_5686335 := by exact prefixLift 5686335
  have htrace : WordTrace (prefixWord ++ tailWord_5686335) baseStart_5686335 baseEnd_5686335 := by
    simpa [prefixWord, tailWord_5686335, baseEnd_5686335] using wordTrace_append hprefix tailTrace_5686335
  have hstable : (prefixWord ++ tailWord_5686335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5686335).length < 2 ^ (prefixWord ++ tailWord_5686335).sum := by decide
  have hdescent : baseEnd_5686335 < baseStart_5686335 := by decide
  rcases family_descends (prefixWord ++ tailWord_5686335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5686345 : List Nat := [1, 2, 1, 1, 2, 2, 2, 2, 3, 2, 5]
def baseStart_5686345 : Nat := 118140960795 + 5686345 * 2 ^ 59
def prefixEnd_5686345 : Nat := 4983230072969 + 3 ^ 40 * 5686345 * 2
def baseEnd_5686345 : Nat := 2919828152290659882736481

theorem tailTrace_5686345 : CollatzResearch.WordTrace tailWord_5686345 prefixEnd_5686345 2919828152290659882736481 := by
  unfold tailWord_5686345
  simp only [CollatzResearch.WordTrace]
  refine ⟨207398040584350690253876489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138265360389567126835917659 207398040584350690253876489)
  ·
    refine ⟨155548530438263017690407367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207398040584350690253876489 155548530438263017690407367)
    ·
      refine ⟨233322795657394526535611051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155548530438263017690407367 233322795657394526535611051)
      ·
        refine ⟨349984193486091789803416577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233322795657394526535611051 349984193486091789803416577)
        ·
          refine ⟨262488145114568842352562433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 349984193486091789803416577 262488145114568842352562433)
          ·
            refine ⟨196866108835926631764421825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 262488145114568842352562433 196866108835926631764421825)
            ·
              refine ⟨147649581626944973823316369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 196866108835926631764421825 147649581626944973823316369)
              ·
                refine ⟨110737186220208730367487277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 147649581626944973823316369 110737186220208730367487277)
                ·
                  refine ⟨41526444832578273887807729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 110737186220208730367487277 41526444832578273887807729)
                  ·
                    refine ⟨31144833624433705415855797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41526444832578273887807729 31144833624433705415855797)
                    ·
                      refine ⟨2919828152290659882736481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31144833624433705415855797 2919828152290659882736481)
                      ·
                        rfl

theorem cell23_5686345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 3, 2, 5].length) (baseStart_5686345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5686345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5686345 prefixEnd_5686345 := by exact prefixLift 5686345
  have htrace : WordTrace (prefixWord ++ tailWord_5686345) baseStart_5686345 baseEnd_5686345 := by
    simpa [prefixWord, tailWord_5686345, baseEnd_5686345] using wordTrace_append hprefix tailTrace_5686345
  have hstable : (prefixWord ++ tailWord_5686345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5686345).length < 2 ^ (prefixWord ++ tailWord_5686345).sum := by decide
  have hdescent : baseEnd_5686345 < baseStart_5686345 := by decide
  rcases family_descends (prefixWord ++ tailWord_5686345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5686372 : List Nat := [2, 3, 1, 1, 2, 1, 1, 3, 4, 1, 4]
def baseStart_5686372 : Nat := 118140960795 + 5686372 * 2 ^ 59
def prefixEnd_5686372 : Nat := 4983230072969 + 3 ^ 40 * 5686372 * 2
def baseEnd_5686372 : Nat := 2919842016268331277098857

theorem tailTrace_5686372 : CollatzResearch.WordTrace tailWord_5686372 prefixEnd_5686372 2919842016268331277098857 := by
  unfold tailWord_5686372
  simp only [CollatzResearch.WordTrace]
  refine ⟨103699512677626436932554685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138266016903501915910072913 103699512677626436932554685)
  ·
    refine ⟨38887317254109913849708007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103699512677626436932554685 38887317254109913849708007)
    ·
      refine ⟨58330975881164870774562011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38887317254109913849708007 58330975881164870774562011)
      ·
        refine ⟨87496463821747306161843017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58330975881164870774562011 87496463821747306161843017)
        ·
          refine ⟨65622347866310479621382263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87496463821747306161843017 65622347866310479621382263)
          ·
            refine ⟨98433521799465719432073395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65622347866310479621382263 98433521799465719432073395)
            ·
              refine ⟨147650282699198579148110093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98433521799465719432073395 147650282699198579148110093)
              ·
                refine ⟨55368856012199467180541285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 147650282699198579148110093 55368856012199467180541285)
                ·
                  refine ⟨10381660502287400096351491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55368856012199467180541285 10381660502287400096351491)
                  ·
                    refine ⟨15572490753431100144527237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10381660502287400096351491 15572490753431100144527237)
                    ·
                      refine ⟨2919842016268331277098857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15572490753431100144527237 2919842016268331277098857)
                      ·
                        rfl

theorem cell23_5686372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 3, 4, 1, 4].length) (baseStart_5686372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5686372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5686372 prefixEnd_5686372 := by exact prefixLift 5686372
  have htrace : WordTrace (prefixWord ++ tailWord_5686372) baseStart_5686372 baseEnd_5686372 := by
    simpa [prefixWord, tailWord_5686372, baseEnd_5686372] using wordTrace_append hprefix tailTrace_5686372
  have hstable : (prefixWord ++ tailWord_5686372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5686372).length < 2 ^ (prefixWord ++ tailWord_5686372).sum := by decide
  have hdescent : baseEnd_5686372 < baseStart_5686372 := by decide
  rcases family_descends (prefixWord ++ tailWord_5686372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5686392 : List Nat := [2, 1, 2, 1, 1, 1, 5, 2, 1, 4, 3]
def baseStart_5686392 : Nat := 118140960795 + 5686392 * 2 ^ 59
def prefixEnd_5686392 : Nat := 4983230072969 + 3 ^ 40 * 5686392 * 2
def baseEnd_5686392 : Nat := 2919852285881421198848765

theorem tailTrace_5686392 : CollatzResearch.WordTrace tailWord_5686392 prefixEnd_5686392 2919852285881421198848765 := by
  unfold tailWord_5686392
  simp only [CollatzResearch.WordTrace]
  refine ⟨103699877407590208640418715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138266503210120278187224953 103699877407590208640418715)
  ·
    refine ⟨155549816111385312960628073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103699877407590208640418715 155549816111385312960628073)
    ·
      refine ⟨116662362083538984720471055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155549816111385312960628073 116662362083538984720471055)
      ·
        refine ⟨174993543125308477080706583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116662362083538984720471055 174993543125308477080706583)
        ·
          refine ⟨262490314687962715621059875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 174993543125308477080706583 262490314687962715621059875)
          ·
            refine ⟨393735472031944073431589813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 262490314687962715621059875 393735472031944073431589813)
            ·
              refine ⟨36912700502994756884211545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 393735472031944073431589813 36912700502994756884211545)
              ·
                refine ⟨27684525377246067663158659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36912700502994756884211545 27684525377246067663158659)
                ·
                  refine ⟨41526788065869101494737989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27684525377246067663158659 41526788065869101494737989)
                  ·
                    refine ⟨7786272762350456530263373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41526788065869101494737989 7786272762350456530263373)
                    ·
                      refine ⟨2919852285881421198848765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7786272762350456530263373 2919852285881421198848765)
                      ·
                        rfl

theorem cell23_5686392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 2, 1, 4, 3].length) (baseStart_5686392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5686392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5686392 prefixEnd_5686392 := by exact prefixLift 5686392
  have htrace : WordTrace (prefixWord ++ tailWord_5686392) baseStart_5686392 baseEnd_5686392 := by
    simpa [prefixWord, tailWord_5686392, baseEnd_5686392] using wordTrace_append hprefix tailTrace_5686392
  have hstable : (prefixWord ++ tailWord_5686392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5686392).length < 2 ^ (prefixWord ++ tailWord_5686392).sum := by decide
  have hdescent : baseEnd_5686392 < baseStart_5686392 := by decide
  rcases family_descends (prefixWord ++ tailWord_5686392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5686426 : List Nat := [3, 1, 1, 5, 1, 2, 1, 2, 2, 2, 3]
def baseStart_5686426 : Nat := 118140960795 + 5686426 * 2 ^ 59
def prefixEnd_5686426 : Nat := 4983230072969 + 3 ^ 40 * 5686426 * 2
def baseEnd_5686426 : Nat := 2919869744223674065823609

theorem tailTrace_5686426 : CollatzResearch.WordTrace tailWord_5686426 prefixEnd_5686426 2919869744223674065823609 := by
  unfold tailWord_5686426
  simp only [CollatzResearch.WordTrace]
  refine ⟨51850248724264310271893783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138267329931371494058383421 51850248724264310271893783)
  ·
    refine ⟨77775373086396465407840675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51850248724264310271893783 77775373086396465407840675)
    ·
      refine ⟨116663059629594698111761013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77775373086396465407840675 116663059629594698111761013)
      ·
        refine ⟨10937161840274502947977595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 116663059629594698111761013 10937161840274502947977595)
        ·
          refine ⟨16405742760411754421966393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10937161840274502947977595 16405742760411754421966393)
          ·
            refine ⟨12304307070308815816474795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16405742760411754421966393 12304307070308815816474795)
            ·
              refine ⟨18456460605463223724712193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12304307070308815816474795 18456460605463223724712193)
              ·
                refine ⟨13842345454097417793534145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18456460605463223724712193 13842345454097417793534145)
                ·
                  refine ⟨10381759090573063345150609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13842345454097417793534145 10381759090573063345150609)
                  ·
                    refine ⟨7786319317929797508862957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10381759090573063345150609 7786319317929797508862957)
                    ·
                      refine ⟨2919869744223674065823609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7786319317929797508862957 2919869744223674065823609)
                      ·
                        rfl

theorem cell23_5686426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_5686426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5686426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5686426 prefixEnd_5686426 := by exact prefixLift 5686426
  have htrace : WordTrace (prefixWord ++ tailWord_5686426) baseStart_5686426 baseEnd_5686426 := by
    simpa [prefixWord, tailWord_5686426, baseEnd_5686426] using wordTrace_append hprefix tailTrace_5686426
  have hstable : (prefixWord ++ tailWord_5686426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5686426).length < 2 ^ (prefixWord ++ tailWord_5686426).sum := by decide
  have hdescent : baseEnd_5686426 < baseStart_5686426 := by decide
  rcases family_descends (prefixWord ++ tailWord_5686426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5686433 : List Nat := [1, 2, 3, 3, 1, 1, 5, 2, 1, 4]
def baseStart_5686433 : Nat := 118140960795 + 5686433 * 2 ^ 59
def prefixEnd_5686433 : Nat := 4983230072969 + 3 ^ 40 * 5686433 * 2
def baseEnd_5686433 : Nat := 973291112862751846145359

theorem tailTrace_5686433 : CollatzResearch.WordTrace tailWord_5686433 prefixEnd_5686433 973291112862751846145359 := by
  unfold tailWord_5686433
  simp only [CollatzResearch.WordTrace]
  refine ⟨207401250208031881283079953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138267500138687920855386635 207401250208031881283079953)
  ·
    refine ⟨155550937656023910962309965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207401250208031881283079953 155550937656023910962309965)
    ·
      refine ⟨58331601621008966610866237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 155550937656023910962309965 58331601621008966610866237)
      ·
        refine ⟨21874350607878362479074839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58331601621008966610866237 21874350607878362479074839)
        ·
          refine ⟨32811525911817543718612259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21874350607878362479074839 32811525911817543718612259)
          ·
            refine ⟨49217288867726315577918389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32811525911817543718612259 49217288867726315577918389)
            ·
              refine ⟨4614120831349342085429849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49217288867726315577918389 4614120831349342085429849)
              ·
                refine ⟨3460590623512006564072387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4614120831349342085429849 3460590623512006564072387)
                ·
                  refine ⟨5190885935268009846108581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3460590623512006564072387 5190885935268009846108581)
                  ·
                    refine ⟨973291112862751846145359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5190885935268009846108581 973291112862751846145359)
                    ·
                      rfl

theorem cell23_5686433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 5, 2, 1, 4].length) (baseStart_5686433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5686433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5686433 prefixEnd_5686433 := by exact prefixLift 5686433
  have htrace : WordTrace (prefixWord ++ tailWord_5686433) baseStart_5686433 baseEnd_5686433 := by
    simpa [prefixWord, tailWord_5686433, baseEnd_5686433] using wordTrace_append hprefix tailTrace_5686433
  have hstable : (prefixWord ++ tailWord_5686433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5686433).length < 2 ^ (prefixWord ++ tailWord_5686433).sum := by decide
  have hdescent : baseEnd_5686433 < baseStart_5686433 := by decide
  rcases family_descends (prefixWord ++ tailWord_5686433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5686472 : List Nat := [2, 1, 3, 1, 2, 1, 3, 1, 3, 6]
def baseStart_5686472 : Nat := 118140960795 + 5686472 * 2 ^ 59
def prefixEnd_5686472 : Nat := 4983230072969 + 3 ^ 40 * 5686472 * 2
def baseEnd_5686472 : Nat := 973297788111260295282799

theorem tailTrace_5686472 : CollatzResearch.WordTrace tailWord_5686472 prefixEnd_5686472 973297788111260295282799 := by
  unfold tailWord_5686472
  simp only [CollatzResearch.WordTrace]
  refine ⟨103701336327445295471874835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138268448436593727295833113 103701336327445295471874835)
  ·
    refine ⟨155552004491167943207812253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103701336327445295471874835 155552004491167943207812253)
    ·
      refine ⟨58332001684187978702929595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 155552004491167943207812253 58332001684187978702929595)
      ·
        refine ⟨87498002526281968054394393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58332001684187978702929595 87498002526281968054394393)
        ·
          refine ⟨65623501894711476040795795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87498002526281968054394393 65623501894711476040795795)
          ·
            refine ⟨98435252842067214061193693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65623501894711476040795795 98435252842067214061193693)
            ·
              refine ⟨36913219815775205272947635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 98435252842067214061193693 36913219815775205272947635)
              ·
                refine ⟨55369829723662807909421453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36913219815775205272947635 55369829723662807909421453)
                ·
                  refine ⟨20763686146373552966033045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55369829723662807909421453 20763686146373552966033045)
                  ·
                    refine ⟨973297788111260295282799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20763686146373552966033045 973297788111260295282799)
                    ·
                      rfl

theorem cell23_5686472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 1, 3, 6].length) (baseStart_5686472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5686472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5686472 prefixEnd_5686472 := by exact prefixLift 5686472
  have htrace : WordTrace (prefixWord ++ tailWord_5686472) baseStart_5686472 baseEnd_5686472 := by
    simpa [prefixWord, tailWord_5686472, baseEnd_5686472] using wordTrace_append hprefix tailTrace_5686472
  have hstable : (prefixWord ++ tailWord_5686472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5686472).length < 2 ^ (prefixWord ++ tailWord_5686472).sum := by decide
  have hdescent : baseEnd_5686472 < baseStart_5686472 := by decide
  rcases family_descends (prefixWord ++ tailWord_5686472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5686484 : List Nat := [2, 4, 1, 4, 2, 1, 2, 2, 1, 4]
def baseStart_5686484 : Nat := 118140960795 + 5686484 * 2 ^ 59
def prefixEnd_5686484 : Nat := 4983230072969 + 3 ^ 40 * 5686484 * 2
def baseEnd_5686484 : Nat := 973299842033878279632781

theorem tailTrace_5686484 : CollatzResearch.WordTrace tailWord_5686484 prefixEnd_5686484 973299842033878279632781 := by
  unfold tailWord_5686484
  simp only [CollatzResearch.WordTrace]
  refine ⟨103701555165423558496593253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138268740220564744662124337 103701555165423558496593253)
  ·
    refine ⟨19444041593516917218111235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103701555165423558496593253 19444041593516917218111235)
    ·
      refine ⟨29166062390275375827166853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19444041593516917218111235 29166062390275375827166853)
      ·
        refine ⟨5468636698176632967593785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29166062390275375827166853 5468636698176632967593785)
        ·
          refine ⟨4101477523632474725695339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5468636698176632967593785 4101477523632474725695339)
          ·
            refine ⟨6152216285448712088543009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4101477523632474725695339 6152216285448712088543009)
            ·
              refine ⟨4614162214086534066407257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6152216285448712088543009 4614162214086534066407257)
              ·
                refine ⟨3460621660564900549805443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4614162214086534066407257 3460621660564900549805443)
                ·
                  refine ⟨5190932490847350824708165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3460621660564900549805443 5190932490847350824708165)
                  ·
                    refine ⟨973299842033878279632781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5190932490847350824708165 973299842033878279632781)
                    ·
                      rfl

theorem cell23_5686484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 2, 2, 1, 4].length) (baseStart_5686484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5686484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5686484 prefixEnd_5686484 := by exact prefixLift 5686484
  have htrace : WordTrace (prefixWord ++ tailWord_5686484) baseStart_5686484 baseEnd_5686484 := by
    simpa [prefixWord, tailWord_5686484, baseEnd_5686484] using wordTrace_append hprefix tailTrace_5686484
  have hstable : (prefixWord ++ tailWord_5686484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5686484).length < 2 ^ (prefixWord ++ tailWord_5686484).sum := by decide
  have hdescent : baseEnd_5686484 < baseStart_5686484 := by decide
  rcases family_descends (prefixWord ++ tailWord_5686484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5686506 : List Nat := [3, 1, 3, 1, 1, 3, 2, 3, 2, 4]
def baseStart_5686506 : Nat := 118140960795 + 5686506 * 2 ^ 59
def prefixEnd_5686506 : Nat := 4983230072969 + 3 ^ 40 * 5686506 * 2
def baseEnd_5686506 : Nat := 973303607558677917607747

theorem tailTrace_5686506 : CollatzResearch.WordTrace tailWord_5686506 prefixEnd_5686506 973303607558677917607747 := by
  unfold tailWord_5686506
  simp only [CollatzResearch.WordTrace]
  refine ⟨51850978184191853687621843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138269275157844943166991581 51850978184191853687621843)
  ·
    refine ⟨77776467276287780531432765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51850978184191853687621843 77776467276287780531432765)
    ·
      refine ⟨29166175228607917699287287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77776467276287780531432765 29166175228607917699287287)
      ·
        refine ⟨43749262842911876548930931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29166175228607917699287287 43749262842911876548930931)
        ·
          refine ⟨65623894264367814823396397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43749262842911876548930931 65623894264367814823396397)
          ·
            refine ⟨24608960349137930558773649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65623894264367814823396397 24608960349137930558773649)
            ·
              refine ⟨18456720261853447919080237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24608960349137930558773649 18456720261853447919080237)
              ·
                refine ⟨6921270098195042969655089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18456720261853447919080237 6921270098195042969655089)
                ·
                  refine ⟨5190952573646282227241317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6921270098195042969655089 5190952573646282227241317)
                  ·
                    refine ⟨973303607558677917607747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5190952573646282227241317 973303607558677917607747)
                    ·
                      rfl

theorem cell23_5686506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 2, 3, 2, 4].length) (baseStart_5686506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5686506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5686506 prefixEnd_5686506 := by exact prefixLift 5686506
  have htrace : WordTrace (prefixWord ++ tailWord_5686506) baseStart_5686506 baseEnd_5686506 := by
    simpa [prefixWord, tailWord_5686506, baseEnd_5686506] using wordTrace_append hprefix tailTrace_5686506
  have hstable : (prefixWord ++ tailWord_5686506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5686506).length < 2 ^ (prefixWord ++ tailWord_5686506).sum := by decide
  have hdescent : baseEnd_5686506 < baseStart_5686506 := by decide
  rcases family_descends (prefixWord ++ tailWord_5686506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5686526 : List Nat := [4, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4]
def baseStart_5686526 : Nat := 118140960795 + 5686526 * 2 ^ 59
def prefixEnd_5686526 : Nat := 4983230072969 + 3 ^ 40 * 5686526 * 2
def baseEnd_5686526 : Nat := 2919921092289123674573149

theorem tailTrace_5686526 : CollatzResearch.WordTrace tailWord_5686526 prefixEnd_5686526 2919921092289123674573149 := by
  unfold tailWord_5686526
  simp only [CollatzResearch.WordTrace]
  refine ⟨25925580274586869770776929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138269761464463305444143621 25925580274586869770776929)
  ·
    refine ⟨19444185205940152328082697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25925580274586869770776929 19444185205940152328082697)
    ·
      refine ⟨14583138904455114246062023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19444185205940152328082697 14583138904455114246062023)
      ·
        refine ⟨21874708356682671369093035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14583138904455114246062023 21874708356682671369093035)
        ·
          refine ⟨32812062535024007053639553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21874708356682671369093035 32812062535024007053639553)
          ·
            refine ⟨24609046901268005290229665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32812062535024007053639553 24609046901268005290229665)
            ·
              refine ⟨18456785175951003967672249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24609046901268005290229665 18456785175951003967672249)
              ·
                refine ⟨13842588881963252975754187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18456785175951003967672249 13842588881963252975754187)
                ·
                  refine ⟨20763883322944879463631281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13842588881963252975754187 20763883322944879463631281)
                  ·
                    refine ⟨15572912492208659597723461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20763883322944879463631281 15572912492208659597723461)
                    ·
                      refine ⟨2919921092289123674573149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15572912492208659597723461 2919921092289123674573149)
                      ·
                        rfl

theorem cell23_5686526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_5686526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5686526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5686526 prefixEnd_5686526 := by exact prefixLift 5686526
  have htrace : WordTrace (prefixWord ++ tailWord_5686526) baseStart_5686526 baseEnd_5686526 := by
    simpa [prefixWord, tailWord_5686526, baseEnd_5686526] using wordTrace_append hprefix tailTrace_5686526
  have hstable : (prefixWord ++ tailWord_5686526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5686526).length < 2 ^ (prefixWord ++ tailWord_5686526).sum := by decide
  have hdescent : baseEnd_5686526 < baseStart_5686526 := by decide
  rcases family_descends (prefixWord ++ tailWord_5686526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5686556 : List Nat := [2, 2, 3, 1, 1, 1, 2, 1, 5, 3, 2]
def baseStart_5686556 : Nat := 118140960795 + 5686556 * 2 ^ 59
def prefixEnd_5686556 : Nat := 4983230072969 + 3 ^ 40 * 5686556 * 2
def baseEnd_5686556 : Nat := 2919936496708758557198011

theorem tailTrace_5686556 : CollatzResearch.WordTrace tailWord_5686556 prefixEnd_5686556 2919936496708758557198011 := by
  unfold tailWord_5686556
  simp only [CollatzResearch.WordTrace]
  refine ⟨103702868193293136644903761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138270490924390848859871681 103702868193293136644903761)
  ·
    refine ⟨77777151144969852483677821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103702868193293136644903761 77777151144969852483677821)
    ·
      refine ⟨29166431679363694681379183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77777151144969852483677821 29166431679363694681379183)
      ·
        refine ⟨43749647519045542022068775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29166431679363694681379183 43749647519045542022068775)
        ·
          refine ⟨65624471278568313033103163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43749647519045542022068775 65624471278568313033103163)
          ·
            refine ⟨98436706917852469549654745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65624471278568313033103163 98436706917852469549654745)
            ·
              refine ⟨73827530188389352162241059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98436706917852469549654745 73827530188389352162241059)
              ·
                refine ⟨110741295282584028243361589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73827530188389352162241059 110741295282584028243361589)
                ·
                  refine ⟨10381996432742252647815149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 110741295282584028243361589 10381996432742252647815149)
                  ·
                    refine ⟨3893248662278344742930681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10381996432742252647815149 3893248662278344742930681)
                    ·
                      refine ⟨2919936496708758557198011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3893248662278344742930681 2919936496708758557198011)
                      ·
                        rfl

theorem cell23_5686556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 5, 3, 2].length) (baseStart_5686556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5686556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5686556 prefixEnd_5686556 := by exact prefixLift 5686556
  have htrace : WordTrace (prefixWord ++ tailWord_5686556) baseStart_5686556 baseEnd_5686556 := by
    simpa [prefixWord, tailWord_5686556, baseEnd_5686556] using wordTrace_append hprefix tailTrace_5686556
  have hstable : (prefixWord ++ tailWord_5686556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5686556).length < 2 ^ (prefixWord ++ tailWord_5686556).sum := by decide
  have hdescent : baseEnd_5686556 < baseStart_5686556 := by decide
  rcases family_descends (prefixWord ++ tailWord_5686556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5686586 : List Nat := [3, 1, 1, 1, 4, 1, 2, 1, 3, 4, 2]
def baseStart_5686586 : Nat := 118140960795 + 5686586 * 2 ^ 59
def prefixEnd_5686586 : Nat := 4983230072969 + 3 ^ 40 * 5686586 * 2
def baseEnd_5686586 : Nat := 2919951901128393439822873

theorem tailTrace_5686586 : CollatzResearch.WordTrace tailWord_5686586 prefixEnd_5686586 2919951901128393439822873 := by
  unfold tailWord_5686586
  simp only [CollatzResearch.WordTrace]
  refine ⟨51851707644119397103349903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138271220384318392275599741 51851707644119397103349903)
  ·
    refine ⟨77777561466179095655024855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51851707644119397103349903 77777561466179095655024855)
    ·
      refine ⟨116666342199268643482537283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77777561466179095655024855 116666342199268643482537283)
      ·
        refine ⟨174999513298902965223805925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116666342199268643482537283 174999513298902965223805925)
        ·
          refine ⟨32812408743544305979463611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 174999513298902965223805925 32812408743544305979463611)
          ·
            refine ⟨49218613115316458969195417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32812408743544305979463611 49218613115316458969195417)
            ·
              refine ⟨36913959836487344226896563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49218613115316458969195417 36913959836487344226896563)
              ·
                refine ⟨55370939754731016340344845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36913959836487344226896563 55370939754731016340344845)
                ·
                  refine ⟨20764102408024131127629317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55370939754731016340344845 20764102408024131127629317)
                  ·
                    refine ⟨3893269201504524586430497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20764102408024131127629317 3893269201504524586430497)
                    ·
                      refine ⟨2919951901128393439822873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3893269201504524586430497 2919951901128393439822873)
                      ·
                        rfl

theorem cell23_5686586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 1, 3, 4, 2].length) (baseStart_5686586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5686586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5686586 prefixEnd_5686586 := by exact prefixLift 5686586
  have htrace : WordTrace (prefixWord ++ tailWord_5686586) baseStart_5686586 baseEnd_5686586 := by
    simpa [prefixWord, tailWord_5686586, baseEnd_5686586] using wordTrace_append hprefix tailTrace_5686586
  have hstable : (prefixWord ++ tailWord_5686586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5686586).length < 2 ^ (prefixWord ++ tailWord_5686586).sum := by decide
  have hdescent : baseEnd_5686586 < baseStart_5686586 := by decide
  rcases family_descends (prefixWord ++ tailWord_5686586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5686598 : List Nat := [6, 1, 1, 3, 1, 1, 3, 2, 1, 2, 2]
def baseStart_5686598 : Nat := 118140960795 + 5686598 * 2 ^ 59
def prefixEnd_5686598 : Nat := 4983230072969 + 3 ^ 40 * 5686598 * 2
def baseEnd_5686598 : Nat := 2919958062896247392872819

theorem tailTrace_5686598 : CollatzResearch.WordTrace tailWord_5686598 prefixEnd_5686598 2919958062896247392872819 := by
  unfold tailWord_5686598
  simp only [CollatzResearch.WordTrace]
  refine ⟨6481477132888566076963639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 138271512168289409641890965 6481477132888566076963639)
  ·
    refine ⟨9722215699332849115445459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6481477132888566076963639 9722215699332849115445459)
    ·
      refine ⟨14583323548999273673168189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9722215699332849115445459 14583323548999273673168189)
      ·
        refine ⟨5468746330874727627438071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14583323548999273673168189 5468746330874727627438071)
        ·
          refine ⟨8203119496312091441157107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5468746330874727627438071 8203119496312091441157107)
          ·
            refine ⟨12304679244468137161735661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8203119496312091441157107 12304679244468137161735661)
            ·
              refine ⟨4614254716675551435650873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12304679244468137161735661 4614254716675551435650873)
              ·
                refine ⟨3460691037506663576738155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4614254716675551435650873 3460691037506663576738155)
                ·
                  refine ⟨5191036556259995365107233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3460691037506663576738155 5191036556259995365107233)
                  ·
                    refine ⟨3893277417194996523830425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5191036556259995365107233 3893277417194996523830425)
                    ·
                      refine ⟨2919958062896247392872819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3893277417194996523830425 2919958062896247392872819)
                      ·
                        rfl

theorem cell23_5686598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_5686598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5686598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5686598 prefixEnd_5686598 := by exact prefixLift 5686598
  have htrace : WordTrace (prefixWord ++ tailWord_5686598) baseStart_5686598 baseEnd_5686598 := by
    simpa [prefixWord, tailWord_5686598, baseEnd_5686598] using wordTrace_append hprefix tailTrace_5686598
  have hstable : (prefixWord ++ tailWord_5686598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5686598).length < 2 ^ (prefixWord ++ tailWord_5686598).sum := by decide
  have hdescent : baseEnd_5686598 < baseStart_5686598 := by decide
  rcases family_descends (prefixWord ++ tailWord_5686598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5686649 : List Nat := [1, 2, 1, 3, 2, 1, 3, 2, 1, 2, 5]
def baseStart_5686649 : Nat := 118140960795 + 5686649 * 2 ^ 59
def prefixEnd_5686649 : Nat := 4983230072969 + 3 ^ 40 * 5686649 * 2
def baseEnd_5686649 : Nat := 2919984250409626693335083

theorem tailTrace_5686649 : CollatzResearch.WordTrace tailWord_5686649 prefixEnd_5686649 2919984250409626693335083 := by
  unfold tailWord_5686649
  simp only [CollatzResearch.WordTrace]
  refine ⟨207409128375249350172943001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138272752250166233448628667 207409128375249350172943001)
  ·
    refine ⟨155556846281437012629707251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207409128375249350172943001 155556846281437012629707251)
    ·
      refine ⟨233335269422155518944560877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155556846281437012629707251 233335269422155518944560877)
      ·
        refine ⟨87500726033308319604210329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 233335269422155518944560877 87500726033308319604210329)
        ·
          refine ⟨65625544524981239703157747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87500726033308319604210329 65625544524981239703157747)
          ·
            refine ⟨98438316787471859554736621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65625544524981239703157747 98438316787471859554736621)
            ·
              refine ⟨36914368795301947333026233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 98438316787471859554736621 36914368795301947333026233)
              ·
                refine ⟨27685776596476460499769675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36914368795301947333026233 27685776596476460499769675)
                ·
                  refine ⟨41528664894714690749654513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27685776596476460499769675 41528664894714690749654513)
                  ·
                    refine ⟨31146498671036018062240885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41528664894714690749654513 31146498671036018062240885)
                    ·
                      refine ⟨2919984250409626693335083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31146498671036018062240885 2919984250409626693335083)
                      ·
                        rfl

theorem cell23_5686649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 2, 1, 2, 5].length) (baseStart_5686649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5686649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5686649 prefixEnd_5686649 := by exact prefixLift 5686649
  have htrace : WordTrace (prefixWord ++ tailWord_5686649) baseStart_5686649 baseEnd_5686649 := by
    simpa [prefixWord, tailWord_5686649, baseEnd_5686649] using wordTrace_append hprefix tailTrace_5686649
  have hstable : (prefixWord ++ tailWord_5686649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5686649).length < 2 ^ (prefixWord ++ tailWord_5686649).sum := by decide
  have hdescent : baseEnd_5686649 < baseStart_5686649 := by decide
  rcases family_descends (prefixWord ++ tailWord_5686649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5686660 : List Nat := [2, 3, 2, 1, 1, 5, 2, 2, 5]
def baseStart_5686660 : Nat := 118140960795 + 5686660 * 2 ^ 59
def prefixEnd_5686660 : Nat := 4983230072969 + 3 ^ 40 * 5686660 * 2
def baseEnd_5686660 : Nat := 324443322077425127810837

theorem tailTrace_5686660 : CollatzResearch.WordTrace tailWord_5686660 prefixEnd_5686660 324443322077425127810837 := by
  unfold tailWord_5686660
  simp only [CollatzResearch.WordTrace]
  refine ⟨103704764789104749525796717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138273019718806332701062289 103704764789104749525796717)
  ·
    refine ⟨38889286795914281072173769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103704764789104749525796717 38889286795914281072173769)
    ·
      refine ⟨29166965096935710804130327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38889286795914281072173769 29166965096935710804130327)
      ·
        refine ⟨43750447645403566206195491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29166965096935710804130327 43750447645403566206195491)
        ·
          refine ⟨65625671468105349309293237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43750447645403566206195491 65625671468105349309293237)
          ·
            refine ⟨6152406700134876497746241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 65625671468105349309293237 6152406700134876497746241)
            ·
              refine ⟨4614305025101157373309681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6152406700134876497746241 4614305025101157373309681)
              ·
                refine ⟨3460728768825868029982261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4614305025101157373309681 3460728768825868029982261)
                ·
                  refine ⟨324443322077425127810837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3460728768825868029982261 324443322077425127810837)
                  ·
                    rfl

theorem cell23_5686660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 2, 2, 5].length) (baseStart_5686660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5686660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5686660 prefixEnd_5686660 := by exact prefixLift 5686660
  have htrace : WordTrace (prefixWord ++ tailWord_5686660) baseStart_5686660 baseEnd_5686660 := by
    simpa [prefixWord, tailWord_5686660, baseEnd_5686660] using wordTrace_append hprefix tailTrace_5686660
  have hstable : (prefixWord ++ tailWord_5686660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5686660).length < 2 ^ (prefixWord ++ tailWord_5686660).sum := by decide
  have hdescent : baseEnd_5686660 < baseStart_5686660 := by decide
  rcases family_descends (prefixWord ++ tailWord_5686660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5686753 : List Nat := [1, 2, 3, 1, 2, 3, 2, 1, 1, 5, 2]
def baseStart_5686753 : Nat := 118140960795 + 5686753 * 2 ^ 59
def prefixEnd_5686753 : Nat := 4983230072969 + 3 ^ 40 * 5686753 * 2
def baseEnd_5686753 : Nat := 2920037652397694286434605

theorem tailTrace_5686753 : CollatzResearch.WordTrace tailWord_5686753 prefixEnd_5686753 2920037652397694286434605 := by
  unfold tailWord_5686753
  simp only [CollatzResearch.WordTrace]
  refine ⟨207412921566872575934728913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138275281044581717289819275 207412921566872575934728913)
  ·
    refine ⟨155559691175154431951046685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207412921566872575934728913 155559691175154431951046685)
    ·
      refine ⟨58334884190682911981642507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 155559691175154431951046685 58334884190682911981642507)
      ·
        refine ⟨87502326286024367972463761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58334884190682911981642507 87502326286024367972463761)
        ·
          refine ⟨65626744714518275979347821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87502326286024367972463761 65626744714518275979347821)
          ·
            refine ⟨24610029267944353492255433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65626744714518275979347821 24610029267944353492255433)
            ·
              refine ⟨18457521950958265119191575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24610029267944353492255433 18457521950958265119191575)
              ·
                refine ⟨27686282926437397678787363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18457521950958265119191575 27686282926437397678787363)
                ·
                  refine ⟨41529424389656096518181045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27686282926437397678787363 41529424389656096518181045)
                  ·
                    refine ⟨3893383536530259048579473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41529424389656096518181045 3893383536530259048579473)
                    ·
                      refine ⟨2920037652397694286434605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3893383536530259048579473 2920037652397694286434605)
                      ·
                        rfl

theorem cell23_5686753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 1, 1, 5, 2].length) (baseStart_5686753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5686753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5686753 prefixEnd_5686753 := by exact prefixLift 5686753
  have htrace : WordTrace (prefixWord ++ tailWord_5686753) baseStart_5686753 baseEnd_5686753 := by
    simpa [prefixWord, tailWord_5686753, baseEnd_5686753] using wordTrace_append hprefix tailTrace_5686753
  have hstable : (prefixWord ++ tailWord_5686753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5686753).length < 2 ^ (prefixWord ++ tailWord_5686753).sum := by decide
  have hdescent : baseEnd_5686753 < baseStart_5686753 := by decide
  rcases family_descends (prefixWord ++ tailWord_5686753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5686770 : List Nat := [3, 2, 1, 4, 1, 1, 1, 1, 4, 3, 2]
def baseStart_5686770 : Nat := 118140960795 + 5686770 * 2 ^ 59
def prefixEnd_5686770 : Nat := 4983230072969 + 3 ^ 40 * 5686770 * 2
def baseEnd_5686770 : Nat := 2920046381568820719922027

theorem tailTrace_5686770 : CollatzResearch.WordTrace tailWord_5686770 prefixEnd_5686770 2920046381568820719922027 := by
  unfold tailWord_5686770
  simp only [CollatzResearch.WordTrace]
  refine ⟨51853385401952746959524441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138275694405207325225398509 51853385401952746959524441)
  ·
    refine ⟨38890039051464560219643331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51853385401952746959524441 38890039051464560219643331)
    ·
      refine ⟨58335058577196840329464997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38890039051464560219643331 58335058577196840329464997)
      ·
        refine ⟨10937823483224407561774687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58335058577196840329464997 10937823483224407561774687)
        ·
          refine ⟨16406735224836611342662031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10937823483224407561774687 16406735224836611342662031)
          ·
            refine ⟨24610102837254917013993047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16406735224836611342662031 24610102837254917013993047)
            ·
              refine ⟨36915154255882375520989571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24610102837254917013993047 36915154255882375520989571)
              ·
                refine ⟨55372731383823563281484357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36915154255882375520989571 55372731383823563281484357)
                ·
                  refine ⟨10382387134466918115278317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55372731383823563281484357 10382387134466918115278317)
                  ·
                    refine ⟨3893395175425094293229369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10382387134466918115278317 3893395175425094293229369)
                    ·
                      refine ⟨2920046381568820719922027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3893395175425094293229369 2920046381568820719922027)
                      ·
                        rfl

theorem cell23_5686770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 1, 4, 3, 2].length) (baseStart_5686770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5686770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5686770 prefixEnd_5686770 := by exact prefixLift 5686770
  have htrace : WordTrace (prefixWord ++ tailWord_5686770) baseStart_5686770 baseEnd_5686770 := by
    simpa [prefixWord, tailWord_5686770, baseEnd_5686770] using wordTrace_append hprefix tailTrace_5686770
  have hstable : (prefixWord ++ tailWord_5686770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5686770).length < 2 ^ (prefixWord ++ tailWord_5686770).sum := by decide
  have hdescent : baseEnd_5686770 < baseStart_5686770 := by decide
  rcases family_descends (prefixWord ++ tailWord_5686770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5686793 : List Nat := [1, 2, 1, 1, 3, 1, 5, 3, 2, 4]
def baseStart_5686793 : Nat := 118140960795 + 5686793 * 2 ^ 59
def prefixEnd_5686793 : Nat := 4983230072969 + 3 ^ 40 * 5686793 * 2
def baseEnd_5686793 : Nat := 973352730541291376644807

theorem tailTrace_5686793 : CollatzResearch.WordTrace tailWord_5686793 prefixEnd_5686793 973352730541291376644807 := by
  unfold tailWord_5686793
  simp only [CollatzResearch.WordTrace]
  refine ⟨207414380486727662766185033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138276253657818441844123355 207414380486727662766185033)
  ·
    refine ⟨155560785365045747074638775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207414380486727662766185033 155560785365045747074638775)
    ·
      refine ⟨233341178047568620611958163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155560785365045747074638775 233341178047568620611958163)
      ·
        refine ⟨350011767071352930917937245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233341178047568620611958163 350011767071352930917937245)
        ·
          refine ⟨131254412651757349094226467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 350011767071352930917937245 131254412651757349094226467)
          ·
            refine ⟨196881618977636023641339701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131254412651757349094226467 196881618977636023641339701)
            ·
              refine ⟨18457651779153377216375597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 196881618977636023641339701 18457651779153377216375597)
              ·
                refine ⟨6921619417182516456140849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18457651779153377216375597 6921619417182516456140849)
                ·
                  refine ⟨5191214562886887342105637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6921619417182516456140849 5191214562886887342105637)
                  ·
                    refine ⟨973352730541291376644807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5191214562886887342105637 973352730541291376644807)
                    ·
                      rfl

theorem cell23_5686793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 5, 3, 2, 4].length) (baseStart_5686793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5686793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5686793 prefixEnd_5686793 := by exact prefixLift 5686793
  have htrace : WordTrace (prefixWord ++ tailWord_5686793) baseStart_5686793 baseEnd_5686793 := by
    simpa [prefixWord, tailWord_5686793, baseEnd_5686793] using wordTrace_append hprefix tailTrace_5686793
  have hstable : (prefixWord ++ tailWord_5686793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5686793).length < 2 ^ (prefixWord ++ tailWord_5686793).sum := by decide
  have hdescent : baseEnd_5686793 < baseStart_5686793 := by decide
  rcases family_descends (prefixWord ++ tailWord_5686793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5686797 : List Nat := [1, 7, 1, 1, 2, 1, 1, 1, 3, 5]
def baseStart_5686797 : Nat := 118140960795 + 5686797 * 2 ^ 59
def prefixEnd_5686797 : Nat := 4983230072969 + 3 ^ 40 * 5686797 * 2
def baseEnd_5686797 : Nat := 973353415182164038094801

theorem tailTrace_5686797 : CollatzResearch.WordTrace tailWord_5686797 prefixEnd_5686797 973353415182164038094801 := by
  unfold tailWord_5686797
  simp only [CollatzResearch.WordTrace]
  refine ⟨207414526378713171449330645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138276350919142114299553763 207414526378713171449330645)
  ·
    refine ⟨4861277962001089955843687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 207414526378713171449330645 4861277962001089955843687)
    ·
      refine ⟨7291916943001634933765531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4861277962001089955843687 7291916943001634933765531)
      ·
        refine ⟨10937875414502452400648297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7291916943001634933765531 10937875414502452400648297)
        ·
          refine ⟨8203406560876839300486223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10937875414502452400648297 8203406560876839300486223)
          ·
            refine ⟨12305109841315258950729335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8203406560876839300486223 12305109841315258950729335)
            ·
              refine ⟨18457664761972888426094003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12305109841315258950729335 18457664761972888426094003)
              ·
                refine ⟨27686497142959332639141005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18457664761972888426094003 27686497142959332639141005)
                ·
                  refine ⟨10382436428609749739677877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27686497142959332639141005 10382436428609749739677877)
                  ·
                    refine ⟨973353415182164038094801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10382436428609749739677877 973353415182164038094801)
                    ·
                      rfl

theorem cell23_5686797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_5686797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5686797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5686797 prefixEnd_5686797 := by exact prefixLift 5686797
  have htrace : WordTrace (prefixWord ++ tailWord_5686797) baseStart_5686797 baseEnd_5686797 := by
    simpa [prefixWord, tailWord_5686797, baseEnd_5686797] using wordTrace_append hprefix tailTrace_5686797
  have hstable : (prefixWord ++ tailWord_5686797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5686797).length < 2 ^ (prefixWord ++ tailWord_5686797).sum := by decide
  have hdescent : baseEnd_5686797 < baseStart_5686797 := by decide
  rcases family_descends (prefixWord ++ tailWord_5686797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5686803 : List Nat := [1, 1, 1, 2, 1, 7, 1, 1, 3, 2, 3]
def baseStart_5686803 : Nat := 118140960795 + 5686803 * 2 ^ 59
def prefixEnd_5686803 : Nat := 4983230072969 + 3 ^ 40 * 5686803 * 2
def baseEnd_5686803 : Nat := 2920063326430419090809375

theorem tailTrace_5686803 : CollatzResearch.WordTrace tailWord_5686803 prefixEnd_5686803 2920063326430419090809375 := by
  unfold tailWord_5686803
  simp only [CollatzResearch.WordTrace]
  refine ⟨207414745216691434474049063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138276496811127622982699375 207414745216691434474049063)
  ·
    refine ⟨311122117825037151711073595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207414745216691434474049063 311122117825037151711073595)
    ·
      refine ⟨466683176737555727566610393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 311122117825037151711073595 466683176737555727566610393)
      ·
        refine ⟨350012382553166795674957795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 466683176737555727566610393 350012382553166795674957795)
        ·
          refine ⟨525018573829750193512436693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 350012382553166795674957795 525018573829750193512436693)
          ·
            refine ⟨12305122824134770160447735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 525018573829750193512436693 12305122824134770160447735)
            ·
              refine ⟨18457684236202155240671603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12305122824134770160447735 18457684236202155240671603)
              ·
                refine ⟨27686526354303232861007405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18457684236202155240671603 27686526354303232861007405)
                ·
                  refine ⟨10382447382863712322877777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27686526354303232861007405 10382447382863712322877777)
                  ·
                    refine ⟨7786835537147784242158333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10382447382863712322877777 7786835537147784242158333)
                    ·
                      refine ⟨2920063326430419090809375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7786835537147784242158333 2920063326430419090809375)
                      ·
                        rfl

theorem cell23_5686803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 1, 3, 2, 3].length) (baseStart_5686803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5686803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5686803 prefixEnd_5686803 := by exact prefixLift 5686803
  have htrace : WordTrace (prefixWord ++ tailWord_5686803) baseStart_5686803 baseEnd_5686803 := by
    simpa [prefixWord, tailWord_5686803, baseEnd_5686803] using wordTrace_append hprefix tailTrace_5686803
  have hstable : (prefixWord ++ tailWord_5686803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5686803).length < 2 ^ (prefixWord ++ tailWord_5686803).sum := by decide
  have hdescent : baseEnd_5686803 < baseStart_5686803 := by decide
  rcases family_descends (prefixWord ++ tailWord_5686803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5686804 : List Nat := [2, 4, 3, 1, 2, 1, 2, 1, 2, 3, 2]
def baseStart_5686804 : Nat := 118140960795 + 5686804 * 2 ^ 59
def prefixEnd_5686804 : Nat := 4983230072969 + 3 ^ 40 * 5686804 * 2
def baseEnd_5686804 : Nat := 2920063839911073586896871

theorem tailTrace_5686804 : CollatzResearch.WordTrace tailWord_5686804 prefixEnd_5686804 2920063839911073586896871 := by
  unfold tailWord_5686804
  simp only [CollatzResearch.WordTrace]
  refine ⟨103707390844843905822417733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138276521126458541096556977 103707390844843905822417733)
  ·
    refine ⟨19445135783408232341703325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103707390844843905822417733 19445135783408232341703325)
    ·
      refine ⟨7291925918778087128138747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19445135783408232341703325 7291925918778087128138747)
      ·
        refine ⟨10937888878167130692208121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7291925918778087128138747 10937888878167130692208121)
        ·
          refine ⟨8203416658625348019156091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10937888878167130692208121 8203416658625348019156091)
          ·
            refine ⟨12305124987938022028734137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8203416658625348019156091 12305124987938022028734137)
            ·
              refine ⟨9228843740953516521550603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12305124987938022028734137 9228843740953516521550603)
              ·
                refine ⟨13843265611430274782325905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9228843740953516521550603 13843265611430274782325905)
                ·
                  refine ⟨10382449208572706086744429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13843265611430274782325905 10382449208572706086744429)
                  ·
                    refine ⟨3893418453214764782529161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10382449208572706086744429 3893418453214764782529161)
                    ·
                      refine ⟨2920063839911073586896871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3893418453214764782529161 2920063839911073586896871)
                      ·
                        rfl

theorem cell23_5686804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 2, 1, 2, 3, 2].length) (baseStart_5686804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5686804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5686804 prefixEnd_5686804 := by exact prefixLift 5686804
  have htrace : WordTrace (prefixWord ++ tailWord_5686804) baseStart_5686804 baseEnd_5686804 := by
    simpa [prefixWord, tailWord_5686804, baseEnd_5686804] using wordTrace_append hprefix tailTrace_5686804
  have hstable : (prefixWord ++ tailWord_5686804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5686804).length < 2 ^ (prefixWord ++ tailWord_5686804).sum := by decide
  have hdescent : baseEnd_5686804 < baseStart_5686804 := by decide
  rcases family_descends (prefixWord ++ tailWord_5686804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5686813 : List Nat := [1, 4, 2, 2, 1, 1, 3, 2, 1, 2, 4]
def baseStart_5686813 : Nat := 118140960795 + 5686813 * 2 ^ 59
def prefixEnd_5686813 : Nat := 4983230072969 + 3 ^ 40 * 5686813 * 2
def baseEnd_5686813 : Nat := 2920068461236964051684329

theorem tailTrace_5686813 : CollatzResearch.WordTrace tailWord_5686813 prefixEnd_5686813 2920068461236964051684329 := by
  unfold tailWord_5686813
  simp only [CollatzResearch.WordTrace]
  refine ⟨207415109946655206181913093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138276739964436804121275395 207415109946655206181913093)
  ·
    refine ⟨38890333114997851159108705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 207415109946655206181913093 38890333114997851159108705)
    ·
      refine ⟨29167749836248388369331529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38890333114997851159108705 29167749836248388369331529)
      ·
        refine ⟨21875812377186291276998647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29167749836248388369331529 21875812377186291276998647)
        ·
          refine ⟨32813718565779436915497971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21875812377186291276998647 32813718565779436915497971)
          ·
            refine ⟨49220577848669155373246957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32813718565779436915497971 49220577848669155373246957)
            ·
              refine ⟨18457716693250933264967609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49220577848669155373246957 18457716693250933264967609)
              ·
                refine ⟨13843287519938199948725707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18457716693250933264967609 13843287519938199948725707)
                ·
                  refine ⟨20764931279907299923088561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13843287519938199948725707 20764931279907299923088561)
                  ·
                    refine ⟨15573698459930474942316421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20764931279907299923088561 15573698459930474942316421)
                    ·
                      refine ⟨2920068461236964051684329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15573698459930474942316421 2920068461236964051684329)
                      ·
                        rfl

theorem cell23_5686813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_5686813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5686813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5686813 prefixEnd_5686813 := by exact prefixLift 5686813
  have htrace : WordTrace (prefixWord ++ tailWord_5686813) baseStart_5686813 baseEnd_5686813 := by
    simpa [prefixWord, tailWord_5686813, baseEnd_5686813] using wordTrace_append hprefix tailTrace_5686813
  have hstable : (prefixWord ++ tailWord_5686813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5686813).length < 2 ^ (prefixWord ++ tailWord_5686813).sum := by decide
  have hdescent : baseEnd_5686813 < baseStart_5686813 := by decide
  rcases family_descends (prefixWord ++ tailWord_5686813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5686860 : List Nat := [2, 2, 1, 3, 1, 3, 2, 1, 3, 3, 2]
def baseStart_5686860 : Nat := 118140960795 + 5686860 * 2 ^ 59
def prefixEnd_5686860 : Nat := 4983230072969 + 3 ^ 40 * 5686860 * 2
def baseEnd_5686860 : Nat := 2920092594827725367796613

theorem tailTrace_5686860 : CollatzResearch.WordTrace tailWord_5686860 prefixEnd_5686860 2920092594827725367796613 := by
  unfold tailWord_5686860
  simp only [CollatzResearch.WordTrace]
  refine ⟨103708412088742466604437017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138277882784989955472582689 103708412088742466604437017)
  ·
    refine ⟨77781309066556849953327763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103708412088742466604437017 77781309066556849953327763)
    ·
      refine ⟨116671963599835274929991645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77781309066556849953327763 116671963599835274929991645)
      ·
        refine ⟨43751986349938228098746867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116671963599835274929991645 43751986349938228098746867)
        ·
          refine ⟨65627979524907342148120301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43751986349938228098746867 65627979524907342148120301)
          ·
            refine ⟨24610492321840253305545113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65627979524907342148120301 24610492321840253305545113)
            ·
              refine ⟨18457869241380189979158835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24610492321840253305545113 18457869241380189979158835)
              ·
                refine ⟨27686803862070284968738253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18457869241380189979158835 27686803862070284968738253)
                ·
                  refine ⟨10382551448276356863276845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27686803862070284968738253 10382551448276356863276845)
                  ·
                    refine ⟨3893456793103633823728817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10382551448276356863276845 3893456793103633823728817)
                    ·
                      refine ⟨2920092594827725367796613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3893456793103633823728817 2920092594827725367796613)
                      ·
                        rfl

theorem cell23_5686860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 1, 3, 3, 2].length) (baseStart_5686860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5686860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5686860 prefixEnd_5686860 := by exact prefixLift 5686860
  have htrace : WordTrace (prefixWord ++ tailWord_5686860) baseStart_5686860 baseEnd_5686860 := by
    simpa [prefixWord, tailWord_5686860, baseEnd_5686860] using wordTrace_append hprefix tailTrace_5686860
  have hstable : (prefixWord ++ tailWord_5686860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5686860).length < 2 ^ (prefixWord ++ tailWord_5686860).sum := by decide
  have hdescent : baseEnd_5686860 < baseStart_5686860 := by decide
  rcases family_descends (prefixWord ++ tailWord_5686860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5686913 : List Nat := [1, 2, 4, 2, 1, 2, 2, 2, 7]
def baseStart_5686913 : Nat := 118140960795 + 5686913 * 2 ^ 59
def prefixEnd_5686913 : Nat := 4983230072969 + 3 ^ 40 * 5686913 * 2
def baseEnd_5686913 : Nat := 324457756589157073381541

theorem tailTrace_5686913 : CollatzResearch.WordTrace tailWord_5686913 prefixEnd_5686913 324457756589157073381541 := by
  unfold tailWord_5686913
  simp only [CollatzResearch.WordTrace]
  refine ⟨207418757246292923260553393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138279171497528615507035595 207418757246292923260553393)
  ·
    refine ⟨155564067934719692445415045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207418757246292923260553393 155564067934719692445415045)
    ·
      refine ⟨29168262737759942333515321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 155564067934719692445415045 29168262737759942333515321)
      ·
        refine ⟨21876197053319956750136491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29168262737759942333515321 21876197053319956750136491)
        ·
          refine ⟨32814295579979935125204737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21876197053319956750136491 32814295579979935125204737)
          ·
            refine ⟨24610721684984951343903553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32814295579979935125204737 24610721684984951343903553)
            ·
              refine ⟨18458041263738713507927665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24610721684984951343903553 18458041263738713507927665)
              ·
                refine ⟨13843530947804035130945749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18458041263738713507927665 13843530947804035130945749)
                ·
                  refine ⟨324457756589157073381541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13843530947804035130945749 324457756589157073381541)
                  ·
                    rfl

theorem cell23_5686913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 2, 7].length) (baseStart_5686913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5686913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5686913 prefixEnd_5686913 := by exact prefixLift 5686913
  have htrace : WordTrace (prefixWord ++ tailWord_5686913) baseStart_5686913 baseEnd_5686913 := by
    simpa [prefixWord, tailWord_5686913, baseEnd_5686913] using wordTrace_append hprefix tailTrace_5686913
  have hstable : (prefixWord ++ tailWord_5686913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5686913).length < 2 ^ (prefixWord ++ tailWord_5686913).sum := by decide
  have hdescent : baseEnd_5686913 < baseStart_5686913 := by decide
  rcases family_descends (prefixWord ++ tailWord_5686913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5686963 : List Nat := [1, 1, 1, 2, 3, 3, 1, 2, 4, 1, 4]
def baseStart_5686963 : Nat := 118140960795 + 5686963 * 2 ^ 59
def prefixEnd_5686963 : Nat := 4983230072969 + 3 ^ 40 * 5686963 * 2
def baseEnd_5686963 : Nat := 2920145483335138464808639

theorem tailTrace_5686963 : CollatzResearch.WordTrace tailWord_5686963 prefixEnd_5686963 2920145483335138464808639 := by
  unfold tailWord_5686963
  simp only [CollatzResearch.WordTrace]
  refine ⟨207420580896111781799873543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138280387264074521199915695 207420580896111781799873543)
  ·
    refine ⟨311130871344167672699810315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207420580896111781799873543 311130871344167672699810315)
    ·
      refine ⟨466696307016251509049715473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 311130871344167672699810315 466696307016251509049715473)
      ·
        refine ⟨350022230262188631787286605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 466696307016251509049715473 350022230262188631787286605)
        ·
          refine ⟨131258336348320736920232477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 350022230262188631787286605 131258336348320736920232477)
          ·
            refine ⟨49221876130620276345087179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 131258336348320736920232477 49221876130620276345087179)
            ·
              refine ⟨73832814195930414517630769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49221876130620276345087179 73832814195930414517630769)
              ·
                refine ⟨55374610646947810888223077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73832814195930414517630769 55374610646947810888223077)
                ·
                  refine ⟨10382739496302714541541827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55374610646947810888223077 10382739496302714541541827)
                  ·
                    refine ⟨15574109244454071812312741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10382739496302714541541827 15574109244454071812312741)
                    ·
                      refine ⟨2920145483335138464808639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15574109244454071812312741 2920145483335138464808639)
                      ·
                        rfl

theorem cell23_5686963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 2, 4, 1, 4].length) (baseStart_5686963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5686963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5686963 prefixEnd_5686963 := by exact prefixLift 5686963
  have htrace : WordTrace (prefixWord ++ tailWord_5686963) baseStart_5686963 baseEnd_5686963 := by
    simpa [prefixWord, tailWord_5686963, baseEnd_5686963] using wordTrace_append hprefix tailTrace_5686963
  have hstable : (prefixWord ++ tailWord_5686963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5686963).length < 2 ^ (prefixWord ++ tailWord_5686963).sum := by decide
  have hdescent : baseEnd_5686963 < baseStart_5686963 := by decide
  rcases family_descends (prefixWord ++ tailWord_5686963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5686998 : List Nat := [5, 2, 1, 3, 1, 2, 2, 2, 5]
def baseStart_5686998 : Nat := 118140960795 + 5686998 * 2 ^ 59
def prefixEnd_5686998 : Nat := 4983230072969 + 3 ^ 40 * 5686998 * 2
def baseEnd_5686998 : Nat := 324462606128671758652331

theorem tailTrace_5686998 : CollatzResearch.WordTrace tailWord_5686998 prefixEnd_5686998 324462606128671758652331 := by
  unfold tailWord_5686998
  simp only [CollatzResearch.WordTrace]
  refine ⟨12963866090686561423587353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 138281238300656655184931765 12963866090686561423587353)
  ·
    refine ⟨9722899568014921067690515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12963866090686561423587353 9722899568014921067690515)
    ·
      refine ⟨14584349352022381601535773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9722899568014921067690515 14584349352022381601535773)
      ·
        refine ⟨5469131007008393100575915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14584349352022381601535773 5469131007008393100575915)
        ·
          refine ⟨8203696510512589650863873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5469131007008393100575915 8203696510512589650863873)
          ·
            refine ⟨6152772382884442238147905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8203696510512589650863873 6152772382884442238147905)
            ·
              refine ⟨4614579287163331678610929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6152772382884442238147905 4614579287163331678610929)
              ·
                refine ⟨3460934465372498758958197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4614579287163331678610929 3460934465372498758958197)
                ·
                  refine ⟨324462606128671758652331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3460934465372498758958197 324462606128671758652331)
                  ·
                    rfl

theorem cell23_5686998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 2, 2, 5].length) (baseStart_5686998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5686998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5686998 prefixEnd_5686998 := by exact prefixLift 5686998
  have htrace : WordTrace (prefixWord ++ tailWord_5686998) baseStart_5686998 baseEnd_5686998 := by
    simpa [prefixWord, tailWord_5686998, baseEnd_5686998] using wordTrace_append hprefix tailTrace_5686998
  have hstable : (prefixWord ++ tailWord_5686998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5686998).length < 2 ^ (prefixWord ++ tailWord_5686998).sum := by decide
  have hdescent : baseEnd_5686998 < baseStart_5686998 := by decide
  rcases family_descends (prefixWord ++ tailWord_5686998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5687000 : List Nat := [2, 1, 2, 2, 3, 1, 1, 4, 2, 2, 3]
def baseStart_5687000 : Nat := 118140960795 + 5687000 * 2 ^ 59
def prefixEnd_5687000 : Nat := 4983230072969 + 3 ^ 40 * 5687000 * 2
def baseEnd_5687000 : Nat := 2920164482119354820045969

theorem tailTrace_5687000 : CollatzResearch.WordTrace tailWord_5687000 prefixEnd_5687000 2920164482119354820045969 := by
  unfold tailWord_5687000
  simp only [CollatzResearch.WordTrace]
  refine ⟨103710965198488868559485227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138281286931318491412646969 103710965198488868559485227)
  ·
    refine ⟨155566447797733302839227841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103710965198488868559485227 155566447797733302839227841)
    ·
      refine ⟨116674835848299977129420881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155566447797733302839227841 116674835848299977129420881)
      ·
        refine ⟨87506126886224982847065661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116674835848299977129420881 87506126886224982847065661)
        ·
          refine ⟨32814797582334368567649623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87506126886224982847065661 32814797582334368567649623)
          ·
            refine ⟨49222196373501552851474435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32814797582334368567649623 49222196373501552851474435)
            ·
              refine ⟨73833294560252329277211653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49222196373501552851474435 73833294560252329277211653)
              ·
                refine ⟨13843742730047311739477185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 73833294560252329277211653 13843742730047311739477185)
                ·
                  refine ⟨10382807047535483804607889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13843742730047311739477185 10382807047535483804607889)
                  ·
                    refine ⟨7787105285651612853455917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10382807047535483804607889 7787105285651612853455917)
                    ·
                      refine ⟨2920164482119354820045969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7787105285651612853455917 2920164482119354820045969)
                      ·
                        rfl

theorem cell23_5687000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 4, 2, 2, 3].length) (baseStart_5687000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5687000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5687000 prefixEnd_5687000 := by exact prefixLift 5687000
  have htrace : WordTrace (prefixWord ++ tailWord_5687000) baseStart_5687000 baseEnd_5687000 := by
    simpa [prefixWord, tailWord_5687000, baseEnd_5687000] using wordTrace_append hprefix tailTrace_5687000
  have hstable : (prefixWord ++ tailWord_5687000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5687000).length < 2 ^ (prefixWord ++ tailWord_5687000).sum := by decide
  have hdescent : baseEnd_5687000 < baseStart_5687000 := by decide
  rcases family_descends (prefixWord ++ tailWord_5687000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5687007 : List Nat := [1, 1, 2, 3, 2, 2, 3, 4, 1, 4]
def baseStart_5687007 : Nat := 118140960795 + 5687007 * 2 ^ 59
def prefixEnd_5687007 : Nat := 4983230072969 + 3 ^ 40 * 5687007 * 2
def baseEnd_5687007 : Nat := 973389358827978764219479

theorem tailTrace_5687007 : CollatzResearch.WordTrace tailWord_5687007 prefixEnd_5687007 973389358827978764219479 := by
  unfold tailWord_5687007
  simp only [CollatzResearch.WordTrace]
  refine ⟨207422185707952377314475275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138281457138634918209650183 207422185707952377314475275)
  ·
    refine ⟨311133278561928565971712913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207422185707952377314475275 311133278561928565971712913)
    ·
      refine ⟨233349958921446424478784685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 311133278561928565971712913 233349958921446424478784685)
      ·
        refine ⟨87506234595542409179544257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 233349958921446424478784685 87506234595542409179544257)
        ·
          refine ⟨65629675946656806884658193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87506234595542409179544257 65629675946656806884658193)
          ·
            refine ⟨49222256959992605163493645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65629675946656806884658193 49222256959992605163493645)
            ·
              refine ⟨18458346359997226936310117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49222256959992605163493645 18458346359997226936310117)
              ·
                refine ⟨3460939942499480050558147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18458346359997226936310117 3460939942499480050558147)
                ·
                  refine ⟨5191409913749220075837221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3460939942499480050558147 5191409913749220075837221)
                  ·
                    refine ⟨973389358827978764219479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5191409913749220075837221 973389358827978764219479)
                    ·
                      rfl

theorem cell23_5687007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 4, 1, 4].length) (baseStart_5687007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5687007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5687007 prefixEnd_5687007 := by exact prefixLift 5687007
  have htrace : WordTrace (prefixWord ++ tailWord_5687007) baseStart_5687007 baseEnd_5687007 := by
    simpa [prefixWord, tailWord_5687007, baseEnd_5687007] using wordTrace_append hprefix tailTrace_5687007
  have hstable : (prefixWord ++ tailWord_5687007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5687007).length < 2 ^ (prefixWord ++ tailWord_5687007).sum := by decide
  have hdescent : baseEnd_5687007 < baseStart_5687007 := by decide
  rcases family_descends (prefixWord ++ tailWord_5687007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5687040 : List Nat := [2, 1, 1, 2, 1, 1, 2, 5, 1, 5, 2]
def baseStart_5687040 : Nat := 118140960795 + 5687040 * 2 ^ 59
def prefixEnd_5687040 : Nat := 4983230072969 + 3 ^ 40 * 5687040 * 2
def baseEnd_5687040 : Nat := 2920185021345534663545785

theorem tailTrace_5687040 : CollatzResearch.WordTrace tailWord_5687040 prefixEnd_5687040 2920185021345534663545785 := by
  unfold tailWord_5687040
  simp only [CollatzResearch.WordTrace]
  refine ⟨103711694658416411975213287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138282259544555215966951049 103711694658416411975213287)
  ·
    refine ⟨155567541987624617962819931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103711694658416411975213287 155567541987624617962819931)
    ·
      refine ⟨233351312981436926944229897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155567541987624617962819931 233351312981436926944229897)
      ·
        refine ⟨175013484736077695208172423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 233351312981436926944229897 175013484736077695208172423)
        ·
          refine ⟨262520227104116542812258635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175013484736077695208172423 262520227104116542812258635)
          ·
            refine ⟨393780340656174814218387953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 262520227104116542812258635 393780340656174814218387953)
            ·
              refine ⟨295335255492131110663790965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 393780340656174814218387953 295335255492131110663790965)
              ·
                refine ⟨27687680202387291624730403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 295335255492131110663790965 27687680202387291624730403)
                ·
                  refine ⟨41531520303580937437095605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27687680202387291624730403 41531520303580937437095605)
                  ·
                    refine ⟨3893580028460712884727713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41531520303580937437095605 3893580028460712884727713)
                    ·
                      refine ⟨2920185021345534663545785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3893580028460712884727713 2920185021345534663545785)
                      ·
                        rfl

theorem cell23_5687040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 5, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 5, 1, 5, 2].length) (baseStart_5687040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5687040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5687040 prefixEnd_5687040 := by exact prefixLift 5687040
  have htrace : WordTrace (prefixWord ++ tailWord_5687040) baseStart_5687040 baseEnd_5687040 := by
    simpa [prefixWord, tailWord_5687040, baseEnd_5687040] using wordTrace_append hprefix tailTrace_5687040
  have hstable : (prefixWord ++ tailWord_5687040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5687040).length < 2 ^ (prefixWord ++ tailWord_5687040).sum := by decide
  have hdescent : baseEnd_5687040 < baseStart_5687040 := by decide
  rcases family_descends (prefixWord ++ tailWord_5687040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5687064 : List Nat := [2, 1, 2, 3, 1, 1, 4, 4, 1, 1, 3]
def baseStart_5687064 : Nat := 118140960795 + 5687064 * 2 ^ 59
def prefixEnd_5687064 : Nat := 4983230072969 + 3 ^ 40 * 5687064 * 2
def baseEnd_5687064 : Nat := 2920197344881242569645675

theorem tailTrace_5687064 : CollatzResearch.WordTrace tailWord_5687064 prefixEnd_5687064 2920197344881242569645675 := by
  unfold tailWord_5687064
  simp only [CollatzResearch.WordTrace]
  refine ⟨103712132334372938024650123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138282843112497250699533497 103712132334372938024650123)
  ·
    refine ⟨155568198501559407036975185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103712132334372938024650123 155568198501559407036975185)
    ·
      refine ⟨116676148876169555277731389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155568198501559407036975185 116676148876169555277731389)
      ·
        refine ⟨43753555828563583229149271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116676148876169555277731389 43753555828563583229149271)
        ·
          refine ⟨65630333742845374843723907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43753555828563583229149271 65630333742845374843723907)
          ·
            refine ⟨98445500614268062265585861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65630333742845374843723907 98445500614268062265585861)
            ·
              refine ⟨18458531365175261674797349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 98445500614268062265585861 18458531365175261674797349)
              ·
                refine ⟨3460974630970361564024503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18458531365175261674797349 3460974630970361564024503)
                ·
                  refine ⟨5191461946455542346036755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3460974630970361564024503 5191461946455542346036755)
                  ·
                    refine ⟨7787192919683313519055133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5191461946455542346036755 7787192919683313519055133)
                    ·
                      refine ⟨2920197344881242569645675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7787192919683313519055133 2920197344881242569645675)
                      ·
                        rfl

theorem cell23_5687064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 4, 1, 1, 3].length) (baseStart_5687064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5687064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5687064 prefixEnd_5687064 := by exact prefixLift 5687064
  have htrace : WordTrace (prefixWord ++ tailWord_5687064) baseStart_5687064 baseEnd_5687064 := by
    simpa [prefixWord, tailWord_5687064, baseEnd_5687064] using wordTrace_append hprefix tailTrace_5687064
  have hstable : (prefixWord ++ tailWord_5687064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5687064).length < 2 ^ (prefixWord ++ tailWord_5687064).sum := by decide
  have hdescent : baseEnd_5687064 < baseStart_5687064 := by decide
  rcases family_descends (prefixWord ++ tailWord_5687064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5687100 : List Nat := [2, 2, 2, 2, 1, 1, 2, 4, 1, 2, 4]
def baseStart_5687100 : Nat := 118140960795 + 5687100 * 2 ^ 59
def prefixEnd_5687100 : Nat := 4983230072969 + 3 ^ 40 * 5687100 * 2
def baseEnd_5687100 : Nat := 2920215830184804428795509

theorem tailTrace_5687100 : CollatzResearch.WordTrace tailWord_5687100 prefixEnd_5687100 2920215830184804428795509 := by
  unfold tailWord_5687100
  simp only [CollatzResearch.WordTrace]
  refine ⟨103712788848307727098805377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138283718464410302798407169 103712788848307727098805377)
  ·
    refine ⟨77784591636230795324104033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103712788848307727098805377 77784591636230795324104033)
    ·
      refine ⟨58338443727173096493078025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77784591636230795324104033 58338443727173096493078025)
      ·
        refine ⟨43753832795379822369808519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58338443727173096493078025 43753832795379822369808519)
        ·
          refine ⟨65630749193069733554712779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43753832795379822369808519 65630749193069733554712779)
          ·
            refine ⟨98446123789604600332069169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65630749193069733554712779 98446123789604600332069169)
            ·
              refine ⟨73834592842203450249051877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98446123789604600332069169 73834592842203450249051877)
              ·
                refine ⟨13843986157913146921697227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 73834592842203450249051877 13843986157913146921697227)
                ·
                  refine ⟨20765979236869720382545841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13843986157913146921697227 20765979236869720382545841)
                  ·
                    refine ⟨15574484427652290286909381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20765979236869720382545841 15574484427652290286909381)
                    ·
                      refine ⟨2920215830184804428795509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15574484427652290286909381 2920215830184804428795509)
                      ·
                        rfl

theorem cell23_5687100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 4, 1, 2, 4].length) (baseStart_5687100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5687100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5687100 prefixEnd_5687100 := by exact prefixLift 5687100
  have htrace : WordTrace (prefixWord ++ tailWord_5687100) baseStart_5687100 baseEnd_5687100 := by
    simpa [prefixWord, tailWord_5687100, baseEnd_5687100] using wordTrace_append hprefix tailTrace_5687100
  have hstable : (prefixWord ++ tailWord_5687100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5687100).length < 2 ^ (prefixWord ++ tailWord_5687100).sum := by decide
  have hdescent : baseEnd_5687100 < baseStart_5687100 := by decide
  rcases family_descends (prefixWord ++ tailWord_5687100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5687107 : List Nat := [1, 1, 1, 3, 1, 5, 2, 3, 1, 2, 3]
def baseStart_5687107 : Nat := 118140960795 + 5687107 * 2 ^ 59
def prefixEnd_5687107 : Nat := 4983230072969 + 3 ^ 40 * 5687107 * 2
def baseEnd_5687107 : Nat := 2920219424549385901407977

theorem tailTrace_5687107 : CollatzResearch.WordTrace tailWord_5687107 prefixEnd_5687107 2920219424549385901407977 := by
  unfold tailWord_5687107
  simp only [CollatzResearch.WordTrace]
  refine ⟨207425833007590094393115575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138283888671726729595410383 207425833007590094393115575)
  ·
    refine ⟨311138749511385141589673363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207425833007590094393115575 311138749511385141589673363)
    ·
      refine ⟨466708124267077712384510045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 311138749511385141589673363 466708124267077712384510045)
      ·
        refine ⟨175015546600154142144191267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 466708124267077712384510045 175015546600154142144191267)
        ·
          refine ⟨262523319900231213216286901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175015546600154142144191267 262523319900231213216286901)
          ·
            refine ⟨24611561240646676239026897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 262523319900231213216286901 24611561240646676239026897)
            ·
              refine ⟨18458670930485007179270173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24611561240646676239026897 18458670930485007179270173)
              ·
                refine ⟨6922001598931877692226315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18458670930485007179270173 6922001598931877692226315)
                ·
                  refine ⟨10383002398397816538339473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6922001598931877692226315 10383002398397816538339473)
                  ·
                    refine ⟨7787251798798362403754605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10383002398397816538339473 7787251798798362403754605)
                    ·
                      refine ⟨2920219424549385901407977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7787251798798362403754605 2920219424549385901407977)
                      ·
                        rfl

theorem cell23_5687107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 3, 1, 2, 3].length) (baseStart_5687107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5687107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5687107 prefixEnd_5687107 := by exact prefixLift 5687107
  have htrace : WordTrace (prefixWord ++ tailWord_5687107) baseStart_5687107 baseEnd_5687107 := by
    simpa [prefixWord, tailWord_5687107, baseEnd_5687107] using wordTrace_append hprefix tailTrace_5687107
  have hstable : (prefixWord ++ tailWord_5687107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5687107).length < 2 ^ (prefixWord ++ tailWord_5687107).sum := by decide
  have hdescent : baseEnd_5687107 < baseStart_5687107 := by decide
  rcases family_descends (prefixWord ++ tailWord_5687107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5687117 : List Nat := [1, 6, 1, 2, 1, 1, 1, 2, 1, 1, 6]
def baseStart_5687117 : Nat := 118140960795 + 5687117 * 2 ^ 59
def prefixEnd_5687117 : Nat := 4983230072969 + 3 ^ 40 * 5687117 * 2
def baseEnd_5687117 : Nat := 2920224559355930862282931

theorem tailTrace_5687117 : CollatzResearch.WordTrace tailWord_5687117 prefixEnd_5687117 2920224559355930862282931 := by
  unfold tailWord_5687117
  simp only [CollatzResearch.WordTrace]
  refine ⟨207426197737553866100979605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138284131825035910733986403 207426197737553866100979605)
  ·
    refine ⟨9723103018947837473483419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 207426197737553866100979605 9723103018947837473483419)
    ·
      refine ⟨14584654528421756210225129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9723103018947837473483419 14584654528421756210225129)
      ·
        refine ⟨10938490896316317157668847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14584654528421756210225129 10938490896316317157668847)
        ·
          refine ⟨16407736344474475736503271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10938490896316317157668847 16407736344474475736503271)
          ·
            refine ⟨24611604516711713604754907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16407736344474475736503271 24611604516711713604754907)
            ·
              refine ⟨36917406775067570407132361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24611604516711713604754907 36917406775067570407132361)
              ·
                refine ⟨27688055081300677805349271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36917406775067570407132361 27688055081300677805349271)
                ·
                  refine ⟨41532082621951016708023907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27688055081300677805349271 41532082621951016708023907)
                  ·
                    refine ⟨62298123932926525062035861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41532082621951016708023907 62298123932926525062035861)
                    ·
                      refine ⟨2920224559355930862282931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62298123932926525062035861 2920224559355930862282931)
                      ·
                        rfl

theorem cell23_5687117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_5687117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5687117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5687117 prefixEnd_5687117 := by exact prefixLift 5687117
  have htrace : WordTrace (prefixWord ++ tailWord_5687117) baseStart_5687117 baseEnd_5687117 := by
    simpa [prefixWord, tailWord_5687117, baseEnd_5687117] using wordTrace_append hprefix tailTrace_5687117
  have hstable : (prefixWord ++ tailWord_5687117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5687117).length < 2 ^ (prefixWord ++ tailWord_5687117).sum := by decide
  have hdescent : baseEnd_5687117 < baseStart_5687117 := by decide
  rcases family_descends (prefixWord ++ tailWord_5687117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5687121 : List Nat := [1, 2, 2, 1, 5, 3, 1, 1, 3, 2, 2]
def baseStart_5687121 : Nat := 118140960795 + 5687121 * 2 ^ 59
def prefixEnd_5687121 : Nat := 4983230072969 + 3 ^ 40 * 5687121 * 2
def baseEnd_5687121 : Nat := 2920226613278548846632913

theorem tailTrace_5687121 : CollatzResearch.WordTrace tailWord_5687121 prefixEnd_5687121 2920226613278548846632913 := by
  unfold tailWord_5687121
  simp only [CollatzResearch.WordTrace]
  refine ⟨207426343629539374784125217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138284229086359583189416811 207426343629539374784125217)
  ·
    refine ⟨155569757722154531088093913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207426343629539374784125217 155569757722154531088093913)
    ·
      refine ⟨116677318291615898316070435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155569757722154531088093913 116677318291615898316070435)
      ·
        refine ⟨175015977437423847474105653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116677318291615898316070435 175015977437423847474105653)
        ·
          refine ⟨16407747884758485700697405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 175015977437423847474105653 16407747884758485700697405)
          ·
            refine ⟨6152905456784432137761527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16407747884758485700697405 6152905456784432137761527)
            ·
              refine ⟨9229358185176648206642291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6152905456784432137761527 9229358185176648206642291)
              ·
                refine ⟨13844037277764972309963437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9229358185176648206642291 13844037277764972309963437)
                ·
                  refine ⟨5191513979161864616236289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13844037277764972309963437 5191513979161864616236289)
                  ·
                    refine ⟨3893635484371398462177217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5191513979161864616236289 3893635484371398462177217)
                    ·
                      refine ⟨2920226613278548846632913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3893635484371398462177217 2920226613278548846632913)
                      ·
                        rfl

theorem cell23_5687121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 1, 1, 3, 2, 2].length) (baseStart_5687121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5687121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5687121 prefixEnd_5687121 := by exact prefixLift 5687121
  have htrace : WordTrace (prefixWord ++ tailWord_5687121) baseStart_5687121 baseEnd_5687121 := by
    simpa [prefixWord, tailWord_5687121, baseEnd_5687121] using wordTrace_append hprefix tailTrace_5687121
  have hstable : (prefixWord ++ tailWord_5687121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5687121).length < 2 ^ (prefixWord ++ tailWord_5687121).sum := by decide
  have hdescent : baseEnd_5687121 < baseStart_5687121 := by decide
  rcases family_descends (prefixWord ++ tailWord_5687121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5687158 : List Nat := [5, 1, 1, 3, 2, 1, 3, 1, 1, 2, 3]
def baseStart_5687158 : Nat := 118140960795 + 5687158 * 2 ^ 59
def prefixEnd_5687158 : Nat := 4983230072969 + 3 ^ 40 * 5687158 * 2
def baseEnd_5687158 : Nat := 2920245612062765201870243

theorem tailTrace_5687158 : CollatzResearch.WordTrace tailWord_5687158 prefixEnd_5687158 2920245612062765201870243 := by
  unfold tailWord_5687158
  simp only [CollatzResearch.WordTrace]
  refine ⟨12964230820650333131451383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 138285128753603553402148085 12964230820650333131451383)
  ·
    refine ⟨19446346230975499697177075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12964230820650333131451383 19446346230975499697177075)
    ·
      refine ⟨29169519346463249545765613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19446346230975499697177075 29169519346463249545765613)
      ·
        refine ⟨10938569754923718579662105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29169519346463249545765613 10938569754923718579662105)
        ·
          refine ⟨8203927316192788934746579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10938569754923718579662105 8203927316192788934746579)
          ·
            refine ⟨12305890974289183402119869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8203927316192788934746579 12305890974289183402119869)
            ·
              refine ⟨4614709115358443775794951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12305890974289183402119869 4614709115358443775794951)
              ·
                refine ⟨6922063673037665663692427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4614709115358443775794951 6922063673037665663692427)
                ·
                  refine ⟨10383095509556498495538641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6922063673037665663692427 10383095509556498495538641)
                  ·
                    refine ⟨7787321632167373871653981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10383095509556498495538641 7787321632167373871653981)
                    ·
                      refine ⟨2920245612062765201870243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7787321632167373871653981 2920245612062765201870243)
                      ·
                        rfl

theorem cell23_5687158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 3, 1, 1, 2, 3].length) (baseStart_5687158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5687158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5687158 prefixEnd_5687158 := by exact prefixLift 5687158
  have htrace : WordTrace (prefixWord ++ tailWord_5687158) baseStart_5687158 baseEnd_5687158 := by
    simpa [prefixWord, tailWord_5687158, baseEnd_5687158] using wordTrace_append hprefix tailTrace_5687158
  have hstable : (prefixWord ++ tailWord_5687158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5687158).length < 2 ^ (prefixWord ++ tailWord_5687158).sum := by decide
  have hdescent : baseEnd_5687158 < baseStart_5687158 := by decide
  rcases family_descends (prefixWord ++ tailWord_5687158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5687177 : List Nat := [1, 2, 1, 1, 5, 1, 1, 2, 3, 4, 2]
def baseStart_5687177 : Nat := 118140960795 + 5687177 * 2 ^ 59
def prefixEnd_5687177 : Nat := 4983230072969 + 3 ^ 40 * 5687177 * 2
def baseEnd_5687177 : Nat := 2920255368195200627532655

theorem tailTrace_5687177 : CollatzResearch.WordTrace tailWord_5687177 prefixEnd_5687177 2920255368195200627532655 := by
  unfold tailWord_5687177
  simp only [CollatzResearch.WordTrace]
  refine ⟨207428386117336496348163785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138285590744890997565442523 207428386117336496348163785)
  ·
    refine ⟨155571289588002372261122839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207428386117336496348163785 155571289588002372261122839)
    ·
      refine ⟨233356934382003558391684259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155571289588002372261122839 233356934382003558391684259)
      ·
        refine ⟨350035401573005337587526389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233356934382003558391684259 350035401573005337587526389)
        ·
          refine ⟨32815818897469250398830599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 350035401573005337587526389 32815818897469250398830599)
          ·
            refine ⟨49223728346203875598245899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32815818897469250398830599 49223728346203875598245899)
            ·
              refine ⟨73835592519305813397368849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49223728346203875598245899 73835592519305813397368849)
              ·
                refine ⟨55376694389479360048026637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73835592519305813397368849 55376694389479360048026637)
                ·
                  refine ⟨20766260396054760018009989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55376694389479360048026637 20766260396054760018009989)
                  ·
                    refine ⟨3893673824260267503376873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20766260396054760018009989 3893673824260267503376873)
                    ·
                      refine ⟨2920255368195200627532655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3893673824260267503376873 2920255368195200627532655)
                      ·
                        rfl

theorem cell23_5687177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 2, 3, 4, 2].length) (baseStart_5687177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5687177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5687177 prefixEnd_5687177 := by exact prefixLift 5687177
  have htrace : WordTrace (prefixWord ++ tailWord_5687177) baseStart_5687177 baseEnd_5687177 := by
    simpa [prefixWord, tailWord_5687177, baseEnd_5687177] using wordTrace_append hprefix tailTrace_5687177
  have hstable : (prefixWord ++ tailWord_5687177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5687177).length < 2 ^ (prefixWord ++ tailWord_5687177).sum := by decide
  have hdescent : baseEnd_5687177 < baseStart_5687177 := by decide
  rcases family_descends (prefixWord ++ tailWord_5687177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5687194 : List Nat := [3, 1, 1, 4, 2, 1, 1, 3, 1, 4, 2]
def baseStart_5687194 : Nat := 118140960795 + 5687194 * 2 ^ 59
def prefixEnd_5687194 : Nat := 4983230072969 + 3 ^ 40 * 5687194 * 2
def baseEnd_5687194 : Nat := 2920264097366327061020077

theorem tailTrace_5687194 : CollatzResearch.WordTrace tailWord_5687194 prefixEnd_5687194 2920264097366327061020077 := by
  unfold tailWord_5687194
  simp only [CollatzResearch.WordTrace]
  refine ⟨51857251539568727062883159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138286004105516605501021757 51857251539568727062883159)
  ·
    refine ⟨77785877309353090594324739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51857251539568727062883159 77785877309353090594324739)
    ·
      refine ⟨116678815964029635891487109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77785877309353090594324739 116678815964029635891487109)
      ·
        refine ⟨21877277993255556729653833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 116678815964029635891487109 21877277993255556729653833)
        ·
          refine ⟨16407958494941667547240375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21877277993255556729653833 16407958494941667547240375)
          ·
            refine ⟨24611937742412501320860563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16407958494941667547240375 24611937742412501320860563)
            ·
              refine ⟨36917906613618751981290845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24611937742412501320860563 36917906613618751981290845)
              ·
                refine ⟨13844214980107031992984067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36917906613618751981290845 13844214980107031992984067)
                ·
                  refine ⟨20766322470160547989476101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13844214980107031992984067 20766322470160547989476101)
                  ·
                    refine ⟨3893685463155102748026769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20766322470160547989476101 3893685463155102748026769)
                    ·
                      refine ⟨2920264097366327061020077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3893685463155102748026769 2920264097366327061020077)
                      ·
                        rfl

theorem cell23_5687194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 3, 1, 4, 2].length) (baseStart_5687194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5687194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5687194 prefixEnd_5687194 := by exact prefixLift 5687194
  have htrace : WordTrace (prefixWord ++ tailWord_5687194) baseStart_5687194 baseEnd_5687194 := by
    simpa [prefixWord, tailWord_5687194, baseEnd_5687194] using wordTrace_append hprefix tailTrace_5687194
  have hstable : (prefixWord ++ tailWord_5687194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5687194).length < 2 ^ (prefixWord ++ tailWord_5687194).sum := by decide
  have hdescent : baseEnd_5687194 < baseStart_5687194 := by decide
  rcases family_descends (prefixWord ++ tailWord_5687194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5687228 : List Nat := [2, 2, 2, 5, 1, 1, 1, 1, 4, 2, 2]
def baseStart_5687228 : Nat := 118140960795 + 5687228 * 2 ^ 59
def prefixEnd_5687228 : Nat := 4983230072969 + 3 ^ 40 * 5687228 * 2
def baseEnd_5687228 : Nat := 2920281555708579927994921

theorem tailTrace_5687228 : CollatzResearch.WordTrace tailWord_5687228 prefixEnd_5687228 2920281555708579927994921 := by
  unfold tailWord_5687228
  simp only [CollatzResearch.WordTrace]
  refine ⟨103715123120075866029135169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138286830826767821372180225 103715123120075866029135169)
  ·
    refine ⟨77786342340056899521851377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103715123120075866029135169 77786342340056899521851377)
    ·
      refine ⟨58339756755042674641388533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77786342340056899521851377 58339756755042674641388533)
      ·
        refine ⟨5469352195785250747630175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 58339756755042674641388533 5469352195785250747630175)
        ·
          refine ⟨8204028293677876121445263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5469352195785250747630175 8204028293677876121445263)
          ·
            refine ⟨12306042440516814182167895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8204028293677876121445263 12306042440516814182167895)
            ·
              refine ⟨18459063660775221273251843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12306042440516814182167895 18459063660775221273251843)
              ·
                refine ⟨27688595491162831909877765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18459063660775221273251843 27688595491162831909877765)
                ·
                  refine ⟨5191611654593030983102081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27688595491162831909877765 5191611654593030983102081)
                  ·
                    refine ⟨3893708740944773237326561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5191611654593030983102081 3893708740944773237326561)
                    ·
                      refine ⟨2920281555708579927994921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3893708740944773237326561 2920281555708579927994921)
                      ·
                        rfl

theorem cell23_5687228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_5687228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5687228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5687228 prefixEnd_5687228 := by exact prefixLift 5687228
  have htrace : WordTrace (prefixWord ++ tailWord_5687228) baseStart_5687228 baseEnd_5687228 := by
    simpa [prefixWord, tailWord_5687228, baseEnd_5687228] using wordTrace_append hprefix tailTrace_5687228
  have hstable : (prefixWord ++ tailWord_5687228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5687228).length < 2 ^ (prefixWord ++ tailWord_5687228).sum := by decide
  have hdescent : baseEnd_5687228 < baseStart_5687228 := by decide
  rcases family_descends (prefixWord ++ tailWord_5687228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5687237 : List Nat := [1, 3, 1, 1, 1, 1, 1, 5, 2, 5, 2]
def baseStart_5687237 : Nat := 118140960795 + 5687237 * 2 ^ 59
def prefixEnd_5687237 : Nat := 4983230072969 + 3 ^ 40 * 5687237 * 2
def baseEnd_5687237 : Nat := 2920286177034470392782379

theorem tailTrace_5687237 : CollatzResearch.WordTrace tailWord_5687237 prefixEnd_5687237 2920286177034470392782379 := by
  unfold tailWord_5687237
  simp only [CollatzResearch.WordTrace]
  refine ⟨207430574497119126595347965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138287049664746084396898643 207430574497119126595347965)
  ·
    refine ⟨77786465436419672473255487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 207430574497119126595347965 77786465436419672473255487)
    ·
      refine ⟨116679698154629508709883231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77786465436419672473255487 116679698154629508709883231)
      ·
        refine ⟨175019547231944263064824847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116679698154629508709883231 175019547231944263064824847)
        ·
          refine ⟨262529320847916394597237271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175019547231944263064824847 262529320847916394597237271)
          ·
            refine ⟨393793981271874591895855907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 262529320847916394597237271 393793981271874591895855907)
            ·
              refine ⟨590690971907811887843783861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 393793981271874591895855907 590690971907811887843783861)
              ·
                refine ⟨55377278616357364485354737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 590690971907811887843783861 55377278616357364485354737)
                ·
                  refine ⟨41532958962268023364016053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55377278616357364485354737 41532958962268023364016053)
                  ·
                    refine ⟨3893714902712627190376505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41532958962268023364016053 3893714902712627190376505)
                    ·
                      refine ⟨2920286177034470392782379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3893714902712627190376505 2920286177034470392782379)
                      ·
                        rfl

theorem cell23_5687237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 5, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 5, 2, 5, 2].length) (baseStart_5687237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5687237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5687237 prefixEnd_5687237 := by exact prefixLift 5687237
  have htrace : WordTrace (prefixWord ++ tailWord_5687237) baseStart_5687237 baseEnd_5687237 := by
    simpa [prefixWord, tailWord_5687237, baseEnd_5687237] using wordTrace_append hprefix tailTrace_5687237
  have hstable : (prefixWord ++ tailWord_5687237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5687237).length < 2 ^ (prefixWord ++ tailWord_5687237).sum := by decide
  have hdescent : baseEnd_5687237 < baseStart_5687237 := by decide
  rcases family_descends (prefixWord ++ tailWord_5687237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5687267 : List Nat := [1, 1, 1, 6, 1, 2, 2, 1, 1, 3, 4]
def baseStart_5687267 : Nat := 118140960795 + 5687267 * 2 ^ 59
def prefixEnd_5687267 : Nat := 4983230072969 + 3 ^ 40 * 5687267 * 2
def baseEnd_5687267 : Nat := 2920301581454105275407241

theorem tailTrace_5687267 : CollatzResearch.WordTrace tailWord_5687267 prefixEnd_5687267 2920301581454105275407241 := by
  unfold tailWord_5687267
  simp only [CollatzResearch.WordTrace]
  refine ⟨207431668687010441718940055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138287779124673627812626703 207431668687010441718940055)
  ·
    refine ⟨311147503030515662578410083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207431668687010441718940055 311147503030515662578410083)
    ·
      refine ⟨466721254545773493867615125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 311147503030515662578410083 466721254545773493867615125)
      ·
        refine ⟨21877558806833132525044459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 466721254545773493867615125 21877558806833132525044459)
        ·
          refine ⟨32816338210249698787566689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21877558806833132525044459 32816338210249698787566689)
          ·
            refine ⟨24612253657687274090675017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32816338210249698787566689 24612253657687274090675017)
            ·
              refine ⟨18459190243265455568006263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24612253657687274090675017 18459190243265455568006263)
              ·
                refine ⟨27688785364898183352009395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18459190243265455568006263 27688785364898183352009395)
                ·
                  refine ⟨41533178047347275028014093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27688785364898183352009395 41533178047347275028014093)
                  ·
                    refine ⟨15574941767755228135505285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41533178047347275028014093 15574941767755228135505285)
                    ·
                      refine ⟨2920301581454105275407241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15574941767755228135505285 2920301581454105275407241)
                      ·
                        rfl

theorem cell23_5687267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_5687267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5687267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5687267 prefixEnd_5687267 := by exact prefixLift 5687267
  have htrace : WordTrace (prefixWord ++ tailWord_5687267) baseStart_5687267 baseEnd_5687267 := by
    simpa [prefixWord, tailWord_5687267, baseEnd_5687267] using wordTrace_append hprefix tailTrace_5687267
  have hstable : (prefixWord ++ tailWord_5687267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5687267).length < 2 ^ (prefixWord ++ tailWord_5687267).sum := by decide
  have hdescent : baseEnd_5687267 < baseStart_5687267 := by decide
  rcases family_descends (prefixWord ++ tailWord_5687267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5687280 : List Nat := [2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 6]
def baseStart_5687280 : Nat := 118140960795 + 5687280 * 2 ^ 59
def prefixEnd_5687280 : Nat := 4983230072969 + 3 ^ 40 * 5687280 * 2
def baseEnd_5687280 : Nat := 2920308256702613724544681

theorem tailTrace_5687280 : CollatzResearch.WordTrace tailWord_5687280 prefixEnd_5687280 2920308256702613724544681 := by
  unfold tailWord_5687280
  simp only [CollatzResearch.WordTrace]
  refine ⟨103716071417981672469581647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138288095223975563292775529 103716071417981672469581647)
  ·
    refine ⟨155574107126972508704372471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103716071417981672469581647 155574107126972508704372471)
    ·
      refine ⟨233361160690458763056558707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155574107126972508704372471 233361160690458763056558707)
      ·
        refine ⟨350041741035688144584838061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233361160690458763056558707 350041741035688144584838061)
        ·
          refine ⟨131265652888383054219314273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 350041741035688144584838061 131265652888383054219314273)
          ·
            refine ⟨98449239666287290664485705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131265652888383054219314273 98449239666287290664485705)
            ·
              refine ⟨73836929749715467998364279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98449239666287290664485705 73836929749715467998364279)
              ·
                refine ⟨110755394624573201997546419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73836929749715467998364279 110755394624573201997546419)
                ·
                  refine ⟨166133091936859802996319629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 110755394624573201997546419 166133091936859802996319629)
                  ·
                    refine ⟨62299909476322426123619861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 166133091936859802996319629 62299909476322426123619861)
                    ·
                      refine ⟨2920308256702613724544681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62299909476322426123619861 2920308256702613724544681)
                      ·
                        rfl

theorem cell23_5687280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 6].length) (baseStart_5687280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5687280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5687280 prefixEnd_5687280 := by exact prefixLift 5687280
  have htrace : WordTrace (prefixWord ++ tailWord_5687280) baseStart_5687280 baseEnd_5687280 := by
    simpa [prefixWord, tailWord_5687280, baseEnd_5687280] using wordTrace_append hprefix tailTrace_5687280
  have hstable : (prefixWord ++ tailWord_5687280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5687280).length < 2 ^ (prefixWord ++ tailWord_5687280).sum := by decide
  have hdescent : baseEnd_5687280 < baseStart_5687280 := by decide
  rcases family_descends (prefixWord ++ tailWord_5687280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5687307 : List Nat := [1, 1, 1, 1, 6, 1, 3, 3, 6]
def baseStart_5687307 : Nat := 118140960795 + 5687307 * 2 ^ 59
def prefixEnd_5687307 : Nat := 4983230072969 + 3 ^ 40 * 5687307 * 2
def baseEnd_5687307 : Nat := 324480235631142790989673

theorem tailTrace_5687307 : CollatzResearch.WordTrace tailWord_5687307 prefixEnd_5687307 324480235631142790989673 := by
  unfold tailWord_5687307
  simp only [CollatzResearch.WordTrace]
  refine ⟨207433127606865528550396175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138288751737910352366930783 207433127606865528550396175)
  ·
    refine ⟨311149691410298292825594263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207433127606865528550396175 311149691410298292825594263)
    ·
      refine ⟨466724537115447439238391395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 311149691410298292825594263 466724537115447439238391395)
      ·
        refine ⟨700086805673171158857587093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 466724537115447439238391395 700086805673171158857587093)
        ·
          refine ⟨32816569015929898071449395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 700086805673171158857587093 32816569015929898071449395)
          ·
            refine ⟨49224853523894847107174093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32816569015929898071449395 49224853523894847107174093)
            ·
              refine ⟨18459320071460567665190285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49224853523894847107174093 18459320071460567665190285)
              ·
                refine ⟨6922245026797712874446357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18459320071460567665190285 6922245026797712874446357)
                ·
                  refine ⟨324480235631142790989673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6922245026797712874446357 324480235631142790989673)
                  ·
                    rfl

theorem cell23_5687307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 3, 6].length) (baseStart_5687307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5687307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5687307 prefixEnd_5687307 := by exact prefixLift 5687307
  have htrace : WordTrace (prefixWord ++ tailWord_5687307) baseStart_5687307 baseEnd_5687307 := by
    simpa [prefixWord, tailWord_5687307, baseEnd_5687307] using wordTrace_append hprefix tailTrace_5687307
  have hstable : (prefixWord ++ tailWord_5687307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5687307).length < 2 ^ (prefixWord ++ tailWord_5687307).sum := by decide
  have hdescent : baseEnd_5687307 < baseStart_5687307 := by decide
  rcases family_descends (prefixWord ++ tailWord_5687307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5687374 : List Nat := [4, 1, 1, 1, 1, 4, 2, 1, 3, 1, 4]
def baseStart_5687374 : Nat := 118140960795 + 5687374 * 2 ^ 59
def prefixEnd_5687374 : Nat := 4983230072969 + 3 ^ 40 * 5687374 * 2
def baseEnd_5687374 : Nat := 2920356523884136356769249

theorem tailTrace_5687374 : CollatzResearch.WordTrace tailWord_5687374 prefixEnd_5687374 2920356523884136356769249 := by
  unfold tailWord_5687374
  simp only [CollatzResearch.WordTrace]
  refine ⟨25929446412202849874135647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138290380865081865995390117 25929446412202849874135647)
  ·
    refine ⟨38894169618304274811203471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25929446412202849874135647 38894169618304274811203471)
    ·
      refine ⟨58341254427456412216805207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38894169618304274811203471 58341254427456412216805207)
      ·
        refine ⟨87511881641184618325207811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58341254427456412216805207 87511881641184618325207811)
        ·
          refine ⟨131267822461776927487811717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87511881641184618325207811 131267822461776927487811717)
          ·
            refine ⟨24612716711583173903964697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 131267822461776927487811717 24612716711583173903964697)
            ·
              refine ⟨18459537533687380427973523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24612716711583173903964697 18459537533687380427973523)
              ·
                refine ⟨27689306300531070641960285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18459537533687380427973523 27689306300531070641960285)
                ·
                  refine ⟨10383489862699151490735107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27689306300531070641960285 10383489862699151490735107)
                  ·
                    refine ⟨15575234794048727236102661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10383489862699151490735107 15575234794048727236102661)
                    ·
                      refine ⟨2920356523884136356769249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15575234794048727236102661 2920356523884136356769249)
                      ·
                        rfl

theorem cell23_5687374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 1, 3, 1, 4].length) (baseStart_5687374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5687374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5687374 prefixEnd_5687374 := by exact prefixLift 5687374
  have htrace : WordTrace (prefixWord ++ tailWord_5687374) baseStart_5687374 baseEnd_5687374 := by
    simpa [prefixWord, tailWord_5687374, baseEnd_5687374] using wordTrace_append hprefix tailTrace_5687374
  have hstable : (prefixWord ++ tailWord_5687374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5687374).length < 2 ^ (prefixWord ++ tailWord_5687374).sum := by decide
  have hdescent : baseEnd_5687374 < baseStart_5687374 := by decide
  rcases family_descends (prefixWord ++ tailWord_5687374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5687388 : List Nat := [2, 2, 4, 1, 1, 4, 2, 1, 1, 5]
def baseStart_5687388 : Nat := 118140960795 + 5687388 * 2 ^ 59
def prefixEnd_5687388 : Nat := 4983230072969 + 3 ^ 40 * 5687388 * 2
def baseEnd_5687388 : Nat := 973454570871099767331395

theorem tailTrace_5687388 : CollatzResearch.WordTrace tailWord_5687388 prefixEnd_5687388 973454570871099767331395 := by
  unfold tailWord_5687388
  simp only [CollatzResearch.WordTrace]
  refine ⟨103718040959786039692047409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138290721279714719589396545 103718040959786039692047409)
  ·
    refine ⟨77788530719839529769035557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103718040959786039692047409 77788530719839529769035557)
    ·
      refine ⟨14585349509969911831694167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 77788530719839529769035557 14585349509969911831694167)
      ·
        refine ⟨21878024264954867747541251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14585349509969911831694167 21878024264954867747541251)
        ·
          refine ⟨32817036397432301621311877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21878024264954867747541251 32817036397432301621311877)
          ·
            refine ⟨6153194324518556553995977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32817036397432301621311877 6153194324518556553995977)
            ·
              refine ⟨4614895743388917415496983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6153194324518556553995977 4614895743388917415496983)
              ·
                refine ⟨6922343615083376123245475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4614895743388917415496983 6922343615083376123245475)
                ·
                  refine ⟨10383515422625064184868213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6922343615083376123245475 10383515422625064184868213)
                  ·
                    refine ⟨973454570871099767331395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10383515422625064184868213 973454570871099767331395)
                    ·
                      rfl

theorem cell23_5687388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 2, 1, 1, 5].length) (baseStart_5687388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5687388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5687388 prefixEnd_5687388 := by exact prefixLift 5687388
  have htrace : WordTrace (prefixWord ++ tailWord_5687388) baseStart_5687388 baseEnd_5687388 := by
    simpa [prefixWord, tailWord_5687388, baseEnd_5687388] using wordTrace_append hprefix tailTrace_5687388
  have hstable : (prefixWord ++ tailWord_5687388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5687388).length < 2 ^ (prefixWord ++ tailWord_5687388).sum := by decide
  have hdescent : baseEnd_5687388 < baseStart_5687388 := by decide
  rcases family_descends (prefixWord ++ tailWord_5687388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5687397 : List Nat := [1, 3, 1, 3, 2, 3, 10]
def baseStart_5687397 : Nat := 118140960795 + 5687397 * 2 ^ 59
def prefixEnd_5687397 : Nat := 4983230072969 + 3 ^ 40 * 5687397 * 2
def baseEnd_5687397 : Nat := 36053930048631972429403

theorem tailTrace_5687397 : CollatzResearch.WordTrace tailWord_5687397 prefixEnd_5687397 36053930048631972429403 := by
  unfold tailWord_5687397
  simp only [CollatzResearch.WordTrace]
  refine ⟨207436410176539473921172445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138290940117692982614114963 207436410176539473921172445)
  ·
    refine ⟨77788653816202302720439667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 207436410176539473921172445 77788653816202302720439667)
    ·
      refine ⟨116682980724303454080659501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77788653816202302720439667 116682980724303454080659501)
      ·
        refine ⟨43756117771613795280247313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116682980724303454080659501 43756117771613795280247313)
        ·
          refine ⟨32817088328710346460185485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43756117771613795280247313 32817088328710346460185485)
          ·
            refine ⟨12306408123266379922569557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32817088328710346460185485 12306408123266379922569557)
            ·
              refine ⟨36053930048631972429403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 12306408123266379922569557 36053930048631972429403)
              ·
                rfl

theorem cell23_5687397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 10].length) (baseStart_5687397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5687397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5687397 prefixEnd_5687397 := by exact prefixLift 5687397
  have htrace : WordTrace (prefixWord ++ tailWord_5687397) baseStart_5687397 baseEnd_5687397 := by
    simpa [prefixWord, tailWord_5687397, baseEnd_5687397] using wordTrace_append hprefix tailTrace_5687397
  have hstable : (prefixWord ++ tailWord_5687397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5687397).length < 2 ^ (prefixWord ++ tailWord_5687397).sum := by decide
  have hdescent : baseEnd_5687397 < baseStart_5687397 := by decide
  rcases family_descends (prefixWord ++ tailWord_5687397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5687408 : List Nat := [2, 1, 1, 1, 5, 3, 2, 1, 3, 2, 2]
def baseStart_5687408 : Nat := 118140960795 + 5687408 * 2 ^ 59
def prefixEnd_5687408 : Nat := 4983230072969 + 3 ^ 40 * 5687408 * 2
def baseEnd_5687408 : Nat := 2920373982226389223744093

theorem tailTrace_5687408 : CollatzResearch.WordTrace tailWord_5687408 prefixEnd_5687408 2920373982226389223744093 := by
  unfold tailWord_5687408
  simp only [CollatzResearch.WordTrace]
  refine ⟨103718405689749811399911439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138291207586333081866548585 103718405689749811399911439)
  ·
    refine ⟨155577608534624717099867159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103718405689749811399911439 155577608534624717099867159)
    ·
      refine ⟨233366412801937075649800739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155577608534624717099867159 233366412801937075649800739)
      ·
        refine ⟨350049619202905613474701109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233366412801937075649800739 350049619202905613474701109)
        ·
          refine ⟨32817151800272401263253229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 350049619202905613474701109 32817151800272401263253229)
          ·
            refine ⟨12306431925102150473719961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32817151800272401263253229 12306431925102150473719961)
            ·
              refine ⟨9229823943826612855289971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12306431925102150473719961 9229823943826612855289971)
              ·
                refine ⟨13844735915739919282934957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9229823943826612855289971 13844735915739919282934957)
                ·
                  refine ⟨5191775968402469731100609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13844735915739919282934957 5191775968402469731100609)
                  ·
                    refine ⟨3893831976301852298325457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5191775968402469731100609 3893831976301852298325457)
                    ·
                      refine ⟨2920373982226389223744093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3893831976301852298325457 2920373982226389223744093)
                      ·
                        rfl

theorem cell23_5687408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 2, 1, 3, 2, 2].length) (baseStart_5687408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5687408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5687408 prefixEnd_5687408 := by exact prefixLift 5687408
  have htrace : WordTrace (prefixWord ++ tailWord_5687408) baseStart_5687408 baseEnd_5687408 := by
    simpa [prefixWord, tailWord_5687408, baseEnd_5687408] using wordTrace_append hprefix tailTrace_5687408
  have hstable : (prefixWord ++ tailWord_5687408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5687408).length < 2 ^ (prefixWord ++ tailWord_5687408).sum := by decide
  have hdescent : baseEnd_5687408 < baseStart_5687408 := by decide
  rcases family_descends (prefixWord ++ tailWord_5687408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5687421 : List Nat := [1, 4, 1, 1, 3, 4, 1, 1, 1, 2, 4]
def baseStart_5687421 : Nat := 118140960795 + 5687421 * 2 ^ 59
def prefixEnd_5687421 : Nat := 4983230072969 + 3 ^ 40 * 5687421 * 2
def baseEnd_5687421 : Nat := 2920380657474897672881533

theorem tailTrace_5687421 : CollatzResearch.WordTrace tailWord_5687421 prefixEnd_5687421 2920380657474897672881533 := by
  unfold tailWord_5687421
  simp only [CollatzResearch.WordTrace]
  refine ⟨207437285528452526020046117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138291523685635017346697411 207437285528452526020046117)
  ·
    refine ⟨38894491036584848628758647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 207437285528452526020046117 38894491036584848628758647)
    ·
      refine ⟨58341736554877272943137971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38894491036584848628758647 58341736554877272943137971)
      ·
        refine ⟨87512604832315909414706957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58341736554877272943137971 87512604832315909414706957)
        ·
          refine ⟨32817226812118466030515109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87512604832315909414706957 32817226812118466030515109)
          ·
            refine ⟨6153230027272212380721583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32817226812118466030515109 6153230027272212380721583)
            ·
              refine ⟨9229845040908318571082375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6153230027272212380721583 9229845040908318571082375)
              ·
                refine ⟨13844767561362477856623563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9229845040908318571082375 13844767561362477856623563)
                ·
                  refine ⟨20767151342043716784935345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13844767561362477856623563 20767151342043716784935345)
                  ·
                    refine ⟨15575363506532787588701509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20767151342043716784935345 15575363506532787588701509)
                    ·
                      refine ⟨2920380657474897672881533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15575363506532787588701509 2920380657474897672881533)
                      ·
                        rfl

theorem cell23_5687421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 1, 1, 1, 2, 4].length) (baseStart_5687421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5687421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5687421 prefixEnd_5687421 := by exact prefixLift 5687421
  have htrace : WordTrace (prefixWord ++ tailWord_5687421) baseStart_5687421 baseEnd_5687421 := by
    simpa [prefixWord, tailWord_5687421, baseEnd_5687421] using wordTrace_append hprefix tailTrace_5687421
  have hstable : (prefixWord ++ tailWord_5687421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5687421).length < 2 ^ (prefixWord ++ tailWord_5687421).sum := by decide
  have hdescent : baseEnd_5687421 < baseStart_5687421 := by decide
  rcases family_descends (prefixWord ++ tailWord_5687421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5687451 : List Nat := [1, 1, 1, 1, 1, 1, 2, 9, 1, 3, 2]
def baseStart_5687451 : Nat := 118140960795 + 5687451 * 2 ^ 59
def prefixEnd_5687451 : Nat := 4983230072969 + 3 ^ 40 * 5687451 * 2
def baseEnd_5687451 : Nat := 2920396061894532555506395

theorem tailTrace_5687451 : CollatzResearch.WordTrace tailWord_5687451 prefixEnd_5687451 2920396061894532555506395 := by
  unfold tailWord_5687451
  simp only [CollatzResearch.WordTrace]
  refine ⟨207438379718343841143638207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138292253145562560762425471 207438379718343841143638207)
  ·
    refine ⟨311157569577515761715457311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207438379718343841143638207 311157569577515761715457311)
    ·
      refine ⟨466736354366273642573185967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 311157569577515761715457311 466736354366273642573185967)
      ·
        refine ⟨700104531549410463859778951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 466736354366273642573185967 700104531549410463859778951)
        ·
          refine ⟨1050156797324115695789668427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 700104531549410463859778951 1050156797324115695789668427)
          ·
            refine ⟨1575235195986173543684502641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1050156797324115695789668427 1575235195986173543684502641)
            ·
              refine ⟨1181426396989630157763376981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1575235195986173543684502641 1181426396989630157763376981)
              ·
                refine ⟨6922420294861114205644787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1181426396989630157763376981 6922420294861114205644787)
                ·
                  refine ⟨10383630442291671308467181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6922420294861114205644787 10383630442291671308467181)
                  ·
                    refine ⟨3893861415859376740675193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10383630442291671308467181 3893861415859376740675193)
                    ·
                      refine ⟨2920396061894532555506395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3893861415859376740675193 2920396061894532555506395)
                      ·
                        rfl

theorem cell23_5687451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 9, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 9, 1, 3, 2].length) (baseStart_5687451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5687451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5687451 prefixEnd_5687451 := by exact prefixLift 5687451
  have htrace : WordTrace (prefixWord ++ tailWord_5687451) baseStart_5687451 baseEnd_5687451 := by
    simpa [prefixWord, tailWord_5687451, baseEnd_5687451] using wordTrace_append hprefix tailTrace_5687451
  have hstable : (prefixWord ++ tailWord_5687451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5687451).length < 2 ^ (prefixWord ++ tailWord_5687451).sum := by decide
  have hdescent : baseEnd_5687451 < baseStart_5687451 := by decide
  rcases family_descends (prefixWord ++ tailWord_5687451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5687458 : List Nat := [3, 3, 1, 3, 1, 1, 2, 1, 4, 1, 3]
def baseStart_5687458 : Nat := 118140960795 + 5687458 * 2 ^ 59
def prefixEnd_5687458 : Nat := 4983230072969 + 3 ^ 40 * 5687458 * 2
def baseEnd_5687458 : Nat := 2920399656259114028118863

theorem tailTrace_5687458 : CollatzResearch.WordTrace tailWord_5687458 prefixEnd_5687458 2920399656259114028118863 := by
  unfold tailWord_5687458
  simp only [CollatzResearch.WordTrace]
  refine ⟨51859658757329620334785757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138292423352878987559428685 51859658757329620334785757)
  ·
    refine ⟨19447372033998607625544659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51859658757329620334785757 19447372033998607625544659)
    ·
      refine ⟨29171058050997911438316989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19447372033998607625544659 29171058050997911438316989)
      ·
        refine ⟨10939146769124216789368871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29171058050997911438316989 10939146769124216789368871)
        ·
          refine ⟨16408720153686325184053307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10939146769124216789368871 16408720153686325184053307)
          ·
            refine ⟨24613080230529487776079961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16408720153686325184053307 24613080230529487776079961)
            ·
              refine ⟨18459810172897115832059971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24613080230529487776079961 18459810172897115832059971)
              ·
                refine ⟨27689715259345673748089957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18459810172897115832059971 27689715259345673748089957)
                ·
                  refine ⟨5191821611127313827766867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27689715259345673748089957 5191821611127313827766867)
                  ·
                    refine ⟨7787732416690970741650301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5191821611127313827766867 7787732416690970741650301)
                    ·
                      refine ⟨2920399656259114028118863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7787732416690970741650301 2920399656259114028118863)
                      ·
                        rfl

theorem cell23_5687458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_5687458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5687458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5687458 prefixEnd_5687458 := by exact prefixLift 5687458
  have htrace : WordTrace (prefixWord ++ tailWord_5687458) baseStart_5687458 baseEnd_5687458 := by
    simpa [prefixWord, tailWord_5687458, baseEnd_5687458] using wordTrace_append hprefix tailTrace_5687458
  have hstable : (prefixWord ++ tailWord_5687458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5687458).length < 2 ^ (prefixWord ++ tailWord_5687458).sum := by decide
  have hdescent : baseEnd_5687458 < baseStart_5687458 := by decide
  rcases family_descends (prefixWord ++ tailWord_5687458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5687481 : List Nat := [1, 2, 1, 4, 1, 2, 2, 3, 1, 4, 2]
def baseStart_5687481 : Nat := 118140960795 + 5687481 * 2 ^ 59
def prefixEnd_5687481 : Nat := 4983230072969 + 3 ^ 40 * 5687481 * 2
def baseEnd_5687481 : Nat := 2920411466314167438131257

theorem tailTrace_5687481 : CollatzResearch.WordTrace tailWord_5687481 prefixEnd_5687481 2920411466314167438131257 := by
  unfold tailWord_5687481
  simp only [CollatzResearch.WordTrace]
  refine ⟨207439473908235156267230297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138292982605490104178153531 207439473908235156267230297)
  ·
    refine ⟨155579605431176367200422723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207439473908235156267230297 155579605431176367200422723)
    ·
      refine ⟨233369408146764550800634085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155579605431176367200422723 233369408146764550800634085)
      ·
        refine ⟨43756764027518353275118891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 233369408146764550800634085 43756764027518353275118891)
        ·
          refine ⟨65635146041277529912678337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43756764027518353275118891 65635146041277529912678337)
          ·
            refine ⟨49226359530958147434508753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65635146041277529912678337 49226359530958147434508753)
            ·
              refine ⟨36919769648218610575881565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49226359530958147434508753 36919769648218610575881565)
              ·
                refine ⟨13844913618081978965955587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36919769648218610575881565 13844913618081978965955587)
                ·
                  refine ⟨20767370427122968448933381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13844913618081978965955587 20767370427122968448933381)
                  ·
                    refine ⟨3893881955085556584175009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20767370427122968448933381 3893881955085556584175009)
                    ·
                      refine ⟨2920411466314167438131257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3893881955085556584175009 2920411466314167438131257)
                      ·
                        rfl

theorem cell23_5687481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 3, 1, 4, 2].length) (baseStart_5687481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5687481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5687481 prefixEnd_5687481 := by exact prefixLift 5687481
  have htrace : WordTrace (prefixWord ++ tailWord_5687481) baseStart_5687481 baseEnd_5687481 := by
    simpa [prefixWord, tailWord_5687481, baseEnd_5687481] using wordTrace_append hprefix tailTrace_5687481
  have hstable : (prefixWord ++ tailWord_5687481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5687481).length < 2 ^ (prefixWord ++ tailWord_5687481).sum := by decide
  have hdescent : baseEnd_5687481 < baseStart_5687481 := by decide
  rcases family_descends (prefixWord ++ tailWord_5687481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5687487 : List Nat := [1, 1, 2, 2, 2, 2, 1, 3, 9]
def baseStart_5687487 : Nat := 118140960795 + 5687487 * 2 ^ 59
def prefixEnd_5687487 : Nat := 4983230072969 + 3 ^ 40 * 5687487 * 2
def baseEnd_5687487 : Nat := 324490505244232712739581

theorem tailTrace_5687487 : CollatzResearch.WordTrace tailWord_5687487 prefixEnd_5687487 324490505244232712739581 := by
  unfold tailWord_5687487
  simp only [CollatzResearch.WordTrace]
  refine ⟨207439692746213419291948715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138293128497475612861299143 207439692746213419291948715)
  ·
    refine ⟨311159539119320128937923073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207439692746213419291948715 311159539119320128937923073)
    ·
      refine ⟨233369654339490096703442305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 311159539119320128937923073 233369654339490096703442305)
      ·
        refine ⟨175027240754617572527581729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 233369654339490096703442305 175027240754617572527581729)
        ·
          refine ⟨131270430565963179395686297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175027240754617572527581729 131270430565963179395686297)
          ·
            refine ⟨98452822924472384546764723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131270430565963179395686297 98452822924472384546764723)
            ·
              refine ⟨147679234386708576820147085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98452822924472384546764723 147679234386708576820147085)
              ·
                refine ⟨55379712895015716307555157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 147679234386708576820147085 55379712895015716307555157)
                ·
                  refine ⟨324490505244232712739581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 55379712895015716307555157 324490505244232712739581)
                  ·
                    rfl

theorem cell23_5687487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 3, 9].length) (baseStart_5687487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5687487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5687487 prefixEnd_5687487 := by exact prefixLift 5687487
  have htrace : WordTrace (prefixWord ++ tailWord_5687487) baseStart_5687487 baseEnd_5687487 := by
    simpa [prefixWord, tailWord_5687487, baseEnd_5687487] using wordTrace_append hprefix tailTrace_5687487
  have hstable : (prefixWord ++ tailWord_5687487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5687487).length < 2 ^ (prefixWord ++ tailWord_5687487).sum := by decide
  have hdescent : baseEnd_5687487 < baseStart_5687487 := by decide
  rcases family_descends (prefixWord ++ tailWord_5687487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5687497 : List Nat := [1, 2, 1, 1, 2, 1, 1, 4, 1, 2, 7]
def baseStart_5687497 : Nat := 118140960795 + 5687497 * 2 ^ 59
def prefixEnd_5687497 : Nat := 4983230072969 + 3 ^ 40 * 5687497 * 2
def baseEnd_5687497 : Nat := 2920419682004639375531183

theorem tailTrace_5687497 : CollatzResearch.WordTrace tailWord_5687497 prefixEnd_5687497 2920419682004639375531183 := by
  unfold tailWord_5687497
  simp only [CollatzResearch.WordTrace]
  refine ⟨207440057476177190999812745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138293371650784793999875163 207440057476177190999812745)
  ·
    refine ⟨155580043107132893249859559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207440057476177190999812745 155580043107132893249859559)
    ·
      refine ⟨233370064660699339874789339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155580043107132893249859559 233370064660699339874789339)
      ·
        refine ⟨350055096991049009812184009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233370064660699339874789339 350055096991049009812184009)
        ·
          refine ⟨262541322743286757359138007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 350055096991049009812184009 262541322743286757359138007)
          ·
            refine ⟨393811984114930136038707011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 262541322743286757359138007 393811984114930136038707011)
            ·
              refine ⟨590717976172395204058060517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 393811984114930136038707011 590717976172395204058060517)
              ·
                refine ⟨110759620532324100760886347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 590717976172395204058060517 110759620532324100760886347)
                ·
                  refine ⟨166139430798486151141329521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 110759620532324100760886347 166139430798486151141329521)
                  ·
                    refine ⟨124604573098864613355997141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 166139430798486151141329521 124604573098864613355997141)
                    ·
                      refine ⟨2920419682004639375531183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 124604573098864613355997141 2920419682004639375531183)
                      ·
                        rfl

theorem cell23_5687497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 2, 7].length) (baseStart_5687497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5687497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5687497 prefixEnd_5687497 := by exact prefixLift 5687497
  have htrace : WordTrace (prefixWord ++ tailWord_5687497) baseStart_5687497 baseEnd_5687497 := by
    simpa [prefixWord, tailWord_5687497, baseEnd_5687497] using wordTrace_append hprefix tailTrace_5687497
  have hstable : (prefixWord ++ tailWord_5687497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5687497).length < 2 ^ (prefixWord ++ tailWord_5687497).sum := by decide
  have hdescent : baseEnd_5687497 < baseStart_5687497 := by decide
  rcases family_descends (prefixWord ++ tailWord_5687497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5687507 : List Nat := [1, 1, 1, 2, 1, 1, 1, 3, 2, 4, 6]
def baseStart_5687507 : Nat := 118140960795 + 5687507 * 2 ^ 59
def prefixEnd_5687507 : Nat := 4983230072969 + 3 ^ 40 * 5687507 * 2
def baseEnd_5687507 : Nat := 2920424816811184336406137

theorem tailTrace_5687507 : CollatzResearch.WordTrace tailWord_5687507 prefixEnd_5687507 2920424816811184336406137 := by
  unfold tailWord_5687507
  simp only [CollatzResearch.WordTrace]
  refine ⟨207440422206140962707676775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138293614804093975138451183 207440422206140962707676775)
  ·
    refine ⟨311160633309211444061515163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207440422206140962707676775 311160633309211444061515163)
    ·
      refine ⟨466740949963817166092272745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 311160633309211444061515163 466740949963817166092272745)
      ·
        refine ⟨350055712472862874569204559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 466740949963817166092272745 350055712472862874569204559)
        ·
          refine ⟨525083568709294311853806839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 350055712472862874569204559 525083568709294311853806839)
          ·
            refine ⟨787625353063941467780710259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 525083568709294311853806839 787625353063941467780710259)
            ·
              refine ⟨1181438029595912201671065389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 787625353063941467780710259 1181438029595912201671065389)
              ·
                refine ⟨443039261098467075626649521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1181438029595912201671065389 443039261098467075626649521)
                ·
                  refine ⟨332279445823850306719987141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 443039261098467075626649521 332279445823850306719987141)
                  ·
                    refine ⟨62302396091971932509997589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 332279445823850306719987141 62302396091971932509997589)
                    ·
                      refine ⟨2920424816811184336406137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62302396091971932509997589 2920424816811184336406137)
                      ·
                        rfl

theorem cell23_5687507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 4, 6].length) (baseStart_5687507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5687507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5687507 prefixEnd_5687507 := by exact prefixLift 5687507
  have htrace : WordTrace (prefixWord ++ tailWord_5687507) baseStart_5687507 baseEnd_5687507 := by
    simpa [prefixWord, tailWord_5687507, baseEnd_5687507] using wordTrace_append hprefix tailTrace_5687507
  have hstable : (prefixWord ++ tailWord_5687507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5687507).length < 2 ^ (prefixWord ++ tailWord_5687507).sum := by decide
  have hdescent : baseEnd_5687507 < baseStart_5687507 := by decide
  rcases family_descends (prefixWord ++ tailWord_5687507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5687521 : List Nat := [1, 2, 3, 1, 3, 1, 3, 4, 5]
def baseStart_5687521 : Nat := 118140960795 + 5687521 * 2 ^ 59
def prefixEnd_5687521 : Nat := 4983230072969 + 3 ^ 40 * 5687521 * 2
def baseEnd_5687521 : Nat := 324492445060038586847897

theorem tailTrace_5687521 : CollatzResearch.WordTrace tailWord_5687521 prefixEnd_5687521 324492445060038586847897 := by
  unfold tailWord_5687521
  simp only [CollatzResearch.WordTrace]
  refine ⟨207440932828090243098686417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138293955218726828732457611 207440932828090243098686417)
  ·
    refine ⟨155580699621067682324014813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207440932828090243098686417 155580699621067682324014813)
    ·
      refine ⟨58342762357900380871505555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 155580699621067682324014813 58342762357900380871505555)
      ·
        refine ⟨87514143536850571307258333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58342762357900380871505555 87514143536850571307258333)
        ·
          refine ⟨32817803826318964240221875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87514143536850571307258333 32817803826318964240221875)
          ·
            refine ⟨49226705739478446360332813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32817803826318964240221875 49226705739478446360332813)
            ·
              refine ⟨18460014652304417385124805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49226705739478446360332813 18460014652304417385124805)
              ·
                refine ⟨3461252747307078259710901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18460014652304417385124805 3461252747307078259710901)
                ·
                  refine ⟨324492445060038586847897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3461252747307078259710901 324492445060038586847897)
                  ·
                    rfl

theorem cell23_5687521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 4, 5].length) (baseStart_5687521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5687521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5687521 prefixEnd_5687521 := by exact prefixLift 5687521
  have htrace : WordTrace (prefixWord ++ tailWord_5687521) baseStart_5687521 baseEnd_5687521 := by
    simpa [prefixWord, tailWord_5687521, baseEnd_5687521] using wordTrace_append hprefix tailTrace_5687521
  have hstable : (prefixWord ++ tailWord_5687521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5687521).length < 2 ^ (prefixWord ++ tailWord_5687521).sum := by decide
  have hdescent : baseEnd_5687521 < baseStart_5687521 := by decide
  rcases family_descends (prefixWord ++ tailWord_5687521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5687534 : List Nat := [4, 1, 2, 1, 1, 1, 1, 4, 1, 7]
def baseStart_5687534 : Nat := 118140960795 + 5687534 * 2 ^ 59
def prefixEnd_5687534 : Nat := 4983230072969 + 3 ^ 40 * 5687534 * 2
def baseEnd_5687534 : Nat := 973479560262951910256171

theorem tailTrace_5687534 : CollatzResearch.WordTrace tailWord_5687534 prefixEnd_5687534 973479560262951910256171 := by
  unfold tailWord_5687534
  simp only [CollatzResearch.WordTrace]
  refine ⟨25930175872130393289863707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138294271318028764212606437 25930175872130393289863707)
  ·
    refine ⟨38895263808195589934795561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25930175872130393289863707 38895263808195589934795561)
    ·
      refine ⟨29171447856146692451096671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38895263808195589934795561 29171447856146692451096671)
      ·
        refine ⟨43757171784220038676645007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29171447856146692451096671 43757171784220038676645007)
        ·
          refine ⟨65635757676330058014967511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43757171784220038676645007 65635757676330058014967511)
          ·
            refine ⟨98453636514495087022451267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65635757676330058014967511 98453636514495087022451267)
            ·
              refine ⟨147680454771742630533676901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98453636514495087022451267 147680454771742630533676901)
              ·
                refine ⟨27690085269701743225064419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 147680454771742630533676901 27690085269701743225064419)
                ·
                  refine ⟨41535127904552614837596629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27690085269701743225064419 41535127904552614837596629)
                  ·
                    refine ⟨973479560262951910256171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41535127904552614837596629 973479560262951910256171)
                    ·
                      rfl

theorem cell23_5687534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 4, 1, 7].length) (baseStart_5687534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5687534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5687534 prefixEnd_5687534 := by exact prefixLift 5687534
  have htrace : WordTrace (prefixWord ++ tailWord_5687534) baseStart_5687534 baseEnd_5687534 := by
    simpa [prefixWord, tailWord_5687534, baseEnd_5687534] using wordTrace_append hprefix tailTrace_5687534
  have hstable : (prefixWord ++ tailWord_5687534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5687534).length < 2 ^ (prefixWord ++ tailWord_5687534).sum := by decide
  have hdescent : baseEnd_5687534 < baseStart_5687534 := by decide
  rcases family_descends (prefixWord ++ tailWord_5687534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5687588 : List Nat := [2, 3, 1, 3, 1, 2, 2, 1, 2, 4, 2]
def baseStart_5687588 : Nat := 118140960795 + 5687588 * 2 ^ 59
def prefixEnd_5687588 : Nat := 4983230072969 + 3 ^ 40 * 5687588 * 2
def baseEnd_5687588 : Nat := 2920466408744198519493265

theorem tailTrace_5687588 : CollatzResearch.WordTrace tailWord_5687588 prefixEnd_5687588 2920466408744198519493265 := by
  unfold tailWord_5687588
  simp only [CollatzResearch.WordTrace]
  refine ⟨103721688259423756770687709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138295584345898342360916945 103721688259423756770687709)
  ·
    refine ⟨38895633097283908789007891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103721688259423756770687709 38895633097283908789007891)
    ·
      refine ⟨58343449645925863183511837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38895633097283908789007891 58343449645925863183511837)
      ·
        refine ⟨21878793617222198693816939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58343449645925863183511837 21878793617222198693816939)
        ·
          refine ⟨32818190425833298040725409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21878793617222198693816939 32818190425833298040725409)
          ·
            refine ⟨24613642819374973530544057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32818190425833298040725409 24613642819374973530544057)
            ·
              refine ⟨18460232114531230147908043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24613642819374973530544057 18460232114531230147908043)
              ·
                refine ⟨27690348171796845221862065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18460232114531230147908043 27690348171796845221862065)
                ·
                  refine ⟨20767761128847633916396549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27690348171796845221862065 20767761128847633916396549)
                  ·
                    refine ⟨3893955211658931359324353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20767761128847633916396549 3893955211658931359324353)
                    ·
                      refine ⟨2920466408744198519493265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3893955211658931359324353 2920466408744198519493265)
                      ·
                        rfl

theorem cell23_5687588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 1, 2, 4, 2].length) (baseStart_5687588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5687588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5687588 prefixEnd_5687588 := by exact prefixLift 5687588
  have htrace : WordTrace (prefixWord ++ tailWord_5687588) baseStart_5687588 baseEnd_5687588 := by
    simpa [prefixWord, tailWord_5687588, baseEnd_5687588] using wordTrace_append hprefix tailTrace_5687588
  have hstable : (prefixWord ++ tailWord_5687588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5687588).length < 2 ^ (prefixWord ++ tailWord_5687588).sum := by decide
  have hdescent : baseEnd_5687588 < baseStart_5687588 := by decide
  rcases family_descends (prefixWord ++ tailWord_5687588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5687631 : List Nat := [1, 1, 2, 1, 1, 2, 1, 4, 3, 5, 2]
def baseStart_5687631 : Nat := 118140960795 + 5687631 * 2 ^ 59
def prefixEnd_5687631 : Nat := 4983230072969 + 3 ^ 40 * 5687631 * 2
def baseEnd_5687631 : Nat := 2920488488412341851255567

theorem tailTrace_5687631 : CollatzResearch.WordTrace tailWord_5687631 prefixEnd_5687631 2920488488412341851255567 := by
  unfold tailWord_5687631
  simp only [CollatzResearch.WordTrace]
  refine ⟨207444944857691731885190747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138296629905127821256793831 207444944857691731885190747)
  ·
    refine ⟨311167417286537597827786121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207444944857691731885190747 311167417286537597827786121)
    ·
      refine ⟨233375562964903198370839591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 311167417286537597827786121 233375562964903198370839591)
      ·
        refine ⟨350063344447354797556259387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233375562964903198370839591 350063344447354797556259387)
        ·
          refine ⟨525095016671032196334389081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 350063344447354797556259387 525095016671032196334389081)
          ·
            refine ⟨393821262503274147250791811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 525095016671032196334389081 393821262503274147250791811)
            ·
              refine ⟨590731893754911220876187717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 393821262503274147250791811 590731893754911220876187717)
              ·
                refine ⟨110762230079045853914285197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 590731893754911220876187717 110762230079045853914285197)
                ·
                  refine ⟨41535836279642195217856949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 110762230079045853914285197 41535836279642195217856949)
                  ·
                    refine ⟨3893984651216455801674089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41535836279642195217856949 3893984651216455801674089)
                    ·
                      refine ⟨2920488488412341851255567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3893984651216455801674089 2920488488412341851255567)
                      ·
                        rfl

theorem cell23_5687631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 3, 5, 2].length) (baseStart_5687631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5687631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5687631 prefixEnd_5687631 := by exact prefixLift 5687631
  have htrace : WordTrace (prefixWord ++ tailWord_5687631) baseStart_5687631 baseEnd_5687631 := by
    simpa [prefixWord, tailWord_5687631, baseEnd_5687631] using wordTrace_append hprefix tailTrace_5687631
  have hstable : (prefixWord ++ tailWord_5687631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5687631).length < 2 ^ (prefixWord ++ tailWord_5687631).sum := by decide
  have hdescent : baseEnd_5687631 < baseStart_5687631 := by decide
  rcases family_descends (prefixWord ++ tailWord_5687631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5687658 : List Nat := [3, 1, 3, 3, 1, 2, 1, 1, 3, 5]
def baseStart_5687658 : Nat := 118140960795 + 5687658 * 2 ^ 59
def prefixEnd_5687658 : Nat := 4983230072969 + 3 ^ 40 * 5687658 * 2
def baseEnd_5687658 : Nat := 973500784130004415205981

theorem tailTrace_5687658 : CollatzResearch.WordTrace tailWord_5687658 prefixEnd_5687658 973500784130004415205981 := by
  unfold tailWord_5687658
  simp only [CollatzResearch.WordTrace]
  refine ⟨51861482407148478874105907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138297286419062610330949085 51861482407148478874105907)
  ·
    refine ⟨77792223610722718311158861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51861482407148478874105907 77792223610722718311158861)
    ·
      refine ⟨29172083854021019366684573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77792223610722718311158861 29172083854021019366684573)
      ·
        refine ⟨10939531445257882262506715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29172083854021019366684573 10939531445257882262506715)
        ·
          refine ⟨16409297167886823393760073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10939531445257882262506715 16409297167886823393760073)
          ·
            refine ⟨12306972875915117545320055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16409297167886823393760073 12306972875915117545320055)
            ·
              refine ⟨18460459313872676317980083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12306972875915117545320055 18460459313872676317980083)
              ·
                refine ⟨27690688970809014476970125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18460459313872676317980083 27690688970809014476970125)
                ·
                  refine ⟨10384008364053380428863797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27690688970809014476970125 10384008364053380428863797)
                  ·
                    refine ⟨973500784130004415205981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10384008364053380428863797 973500784130004415205981)
                    ·
                      rfl

theorem cell23_5687658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 1, 3, 5].length) (baseStart_5687658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5687658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5687658 prefixEnd_5687658 := by exact prefixLift 5687658
  have htrace : WordTrace (prefixWord ++ tailWord_5687658) baseStart_5687658 baseEnd_5687658 := by
    simpa [prefixWord, tailWord_5687658, baseEnd_5687658] using wordTrace_append hprefix tailTrace_5687658
  have hstable : (prefixWord ++ tailWord_5687658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5687658).length < 2 ^ (prefixWord ++ tailWord_5687658).sum := by decide
  have hdescent : baseEnd_5687658 < baseStart_5687658 := by decide
  rcases family_descends (prefixWord ++ tailWord_5687658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5687671 : List Nat := [1, 1, 3, 1, 1, 2, 2, 4, 4, 4]
def baseStart_5687671 : Nat := 118140960795 + 5687671 * 2 ^ 59
def prefixEnd_5687671 : Nat := 4983230072969 + 3 ^ 40 * 5687671 * 2
def baseEnd_5687671 : Nat := 973503009212840564918461

theorem tailTrace_5687671 : CollatzResearch.WordTrace tailWord_5687671 prefixEnd_5687671 973503009212840564918461 := by
  unfold tailWord_5687671
  simp only [CollatzResearch.WordTrace]
  refine ⟨207446403777546818716646867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138297602518364545811097911 207446403777546818716646867)
  ·
    refine ⟨311169605666320228074970301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207446403777546818716646867 311169605666320228074970301)
    ·
      refine ⟨116688602124870085528113863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 311169605666320228074970301 116688602124870085528113863)
      ·
        refine ⟨175032903187305128292170795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116688602124870085528113863 175032903187305128292170795)
        ·
          refine ⟨262549354780957692438256193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175032903187305128292170795 262549354780957692438256193)
          ·
            refine ⟨196912016085718269328692145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 262549354780957692438256193 196912016085718269328692145)
            ·
              refine ⟨147684012064288701996519109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 196912016085718269328692145 147684012064288701996519109)
              ·
                refine ⟨27690752262054131624347333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 147684012064288701996519109 27690752262054131624347333)
                ·
                  refine ⟨5192016049135149679565125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27690752262054131624347333 5192016049135149679565125)
                  ·
                    refine ⟨973503009212840564918461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5192016049135149679565125 973503009212840564918461)
                    ·
                      rfl

theorem cell23_5687671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 4, 4, 4].length) (baseStart_5687671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5687671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5687671 prefixEnd_5687671 := by exact prefixLift 5687671
  have htrace : WordTrace (prefixWord ++ tailWord_5687671) baseStart_5687671 baseEnd_5687671 := by
    simpa [prefixWord, tailWord_5687671, baseEnd_5687671] using wordTrace_append hprefix tailTrace_5687671
  have hstable : (prefixWord ++ tailWord_5687671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5687671).length < 2 ^ (prefixWord ++ tailWord_5687671).sum := by decide
  have hdescent : baseEnd_5687671 < baseStart_5687671 := by decide
  rcases family_descends (prefixWord ++ tailWord_5687671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5687689 : List Nat := [1, 2, 1, 1, 6, 3, 2, 2, 1, 1, 3]
def baseStart_5687689 : Nat := 118140960795 + 5687689 * 2 ^ 59
def prefixEnd_5687689 : Nat := 4983230072969 + 3 ^ 40 * 5687689 * 2
def baseEnd_5687689 : Nat := 2920518270290302624330301

theorem tailTrace_5687689 : CollatzResearch.WordTrace tailWord_5687689 prefixEnd_5687689 2920518270290302624330301 := by
  unfold tailWord_5687689
  simp only [CollatzResearch.WordTrace]
  refine ⟨207447060291481607790802121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138298040194321071860534747 207447060291481607790802121)
  ·
    refine ⟨155585295218611205843101591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207447060291481607790802121 155585295218611205843101591)
    ·
      refine ⟨233377942827916808764652387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155585295218611205843101591 233377942827916808764652387)
      ·
        refine ⟨350066914241875213146978581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233377942827916808764652387 350066914241875213146978581)
        ·
          refine ⟨16409386605087900616264621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 350066914241875213146978581 16409386605087900616264621)
          ·
            refine ⟨6153519976907962731099233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16409386605087900616264621 6153519976907962731099233)
            ·
              refine ⟨4615139982680972048324425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6153519976907962731099233 4615139982680972048324425)
              ·
                refine ⟨3461354987010729036243319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4615139982680972048324425 3461354987010729036243319)
                ·
                  refine ⟨5192032480516093554364979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3461354987010729036243319 5192032480516093554364979)
                  ·
                    refine ⟨7788048720774140331547469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5192032480516093554364979 7788048720774140331547469)
                    ·
                      refine ⟨2920518270290302624330301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7788048720774140331547469 2920518270290302624330301)
                      ·
                        rfl

theorem cell23_5687689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 2, 2, 1, 1, 3].length) (baseStart_5687689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5687689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5687689 prefixEnd_5687689 := by exact prefixLift 5687689
  have htrace : WordTrace (prefixWord ++ tailWord_5687689) baseStart_5687689 baseEnd_5687689 := by
    simpa [prefixWord, tailWord_5687689, baseEnd_5687689] using wordTrace_append hprefix tailTrace_5687689
  have hstable : (prefixWord ++ tailWord_5687689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5687689).length < 2 ^ (prefixWord ++ tailWord_5687689).sum := by decide
  have hdescent : baseEnd_5687689 < baseStart_5687689 := by decide
  rcases family_descends (prefixWord ++ tailWord_5687689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5687729 : List Nat := [1, 2, 2, 4, 1, 3, 2, 3, 1, 2, 2]
def baseStart_5687729 : Nat := 118140960795 + 5687729 * 2 ^ 59
def prefixEnd_5687729 : Nat := 4983230072969 + 3 ^ 40 * 5687729 * 2
def baseEnd_5687729 : Nat := 2920538809516482467830117

theorem tailTrace_5687729 : CollatzResearch.WordTrace tailWord_5687729 prefixEnd_5687729 2920538809516482467830117 := by
  unfold tailWord_5687729
  simp only [CollatzResearch.WordTrace]
  refine ⟨207448519211336694622258241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138299012807557796414838827 207448519211336694622258241)
  ·
    refine ⟨155586389408502520966693681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207448519211336694622258241 155586389408502520966693681)
    ·
      refine ⟨116689792056376890725020261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155586389408502520966693681 116689792056376890725020261)
      ·
        refine ⟨21879336010570667010941299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 116689792056376890725020261 21879336010570667010941299)
        ·
          refine ⟨32819004015856000516411949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21879336010570667010941299 32819004015856000516411949)
          ·
            refine ⟨12307126505946000193654481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32819004015856000516411949 12307126505946000193654481)
            ·
              refine ⟨9230344879459500145240861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12307126505946000193654481 9230344879459500145240861)
              ·
                refine ⟨3461379329797312554465323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9230344879459500145240861 3461379329797312554465323)
                ·
                  refine ⟨5192068994695968831697985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3461379329797312554465323 5192068994695968831697985)
                  ·
                    refine ⟨3894051746021976623773489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5192068994695968831697985 3894051746021976623773489)
                    ·
                      refine ⟨2920538809516482467830117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3894051746021976623773489 2920538809516482467830117)
                      ·
                        rfl

theorem cell23_5687729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 2, 3, 1, 2, 2].length) (baseStart_5687729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5687729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5687729 prefixEnd_5687729 := by exact prefixLift 5687729
  have htrace : WordTrace (prefixWord ++ tailWord_5687729) baseStart_5687729 baseEnd_5687729 := by
    simpa [prefixWord, tailWord_5687729, baseEnd_5687729] using wordTrace_append hprefix tailTrace_5687729
  have hstable : (prefixWord ++ tailWord_5687729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5687729).length < 2 ^ (prefixWord ++ tailWord_5687729).sum := by decide
  have hdescent : baseEnd_5687729 < baseStart_5687729 := by decide
  rcases family_descends (prefixWord ++ tailWord_5687729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5687818 : List Nat := [3, 1, 2, 2, 2, 1, 2, 1, 1, 5, 3]
def baseStart_5687818 : Nat := 118140960795 + 5687818 * 2 ^ 59
def prefixEnd_5687818 : Nat := 4983230072969 + 3 ^ 40 * 5687818 * 2
def baseEnd_5687818 : Nat := 2920584509294732619617207

theorem tailTrace_5687818 : CollatzResearch.WordTrace tailWord_5687818 prefixEnd_5687818 2920584509294732619617207 := by
  unfold tailWord_5687818
  simp only [CollatzResearch.WordTrace]
  refine ⟨51862941327003565705562027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138301176872009508548165405 51862941327003565705562027)
  ·
    refine ⟨77794411990505348558343041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51862941327003565705562027 77794411990505348558343041)
    ·
      refine ⟨58345808992879011418757281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77794411990505348558343041 58345808992879011418757281)
      ·
        refine ⟨43759356744659258564067961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58345808992879011418757281 43759356744659258564067961)
        ·
          refine ⟨32819517558494443923050971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43759356744659258564067961 32819517558494443923050971)
          ·
            refine ⟨49229276337741665884576457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32819517558494443923050971 49229276337741665884576457)
            ·
              refine ⟨36921957253306249413432343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49229276337741665884576457 36921957253306249413432343)
              ·
                refine ⟨55382935879959374120148515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36921957253306249413432343 55382935879959374120148515)
                ·
                  refine ⟨83074403819939061180222773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55382935879959374120148515 83074403819939061180222773)
                  ·
                    refine ⟨7788225358119286985645885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 83074403819939061180222773 7788225358119286985645885)
                    ·
                      refine ⟨2920584509294732619617207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7788225358119286985645885 2920584509294732619617207)
                      ·
                        rfl

theorem cell23_5687818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 1, 1, 5, 3].length) (baseStart_5687818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5687818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5687818 prefixEnd_5687818 := by exact prefixLift 5687818
  have htrace : WordTrace (prefixWord ++ tailWord_5687818) baseStart_5687818 baseEnd_5687818 := by
    simpa [prefixWord, tailWord_5687818, baseEnd_5687818] using wordTrace_append hprefix tailTrace_5687818
  have hstable : (prefixWord ++ tailWord_5687818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5687818).length < 2 ^ (prefixWord ++ tailWord_5687818).sum := by decide
  have hdescent : baseEnd_5687818 < baseStart_5687818 := by decide
  rcases family_descends (prefixWord ++ tailWord_5687818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5687819 : List Nat := [1, 1, 1, 1, 7, 1, 4, 1, 2, 2, 2]
def baseStart_5687819 : Nat := 118140960795 + 5687819 * 2 ^ 59
def prefixEnd_5687819 : Nat := 4983230072969 + 3 ^ 40 * 5687819 * 2
def baseEnd_5687819 : Nat := 2920585022775387115704703

theorem tailTrace_5687819 : CollatzResearch.WordTrace tailWord_5687819 prefixEnd_5687819 2920585022775387115704703 := by
  unfold tailWord_5687819
  simp only [CollatzResearch.WordTrace]
  refine ⟨207451801781010639993034511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138301201187340426662023007 207451801781010639993034511)
  ·
    refine ⟨311177702671515959989551767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207451801781010639993034511 311177702671515959989551767)
    ·
      refine ⟨466766554007273939984327651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 311177702671515959989551767 466766554007273939984327651)
      ·
        refine ⟨700149831010910909976491477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 466766554007273939984327651 700149831010910909976491477)
        ·
          refine ⟨16409761664318224452574019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 700149831010910909976491477 16409761664318224452574019)
          ·
            refine ⟨24614642496477336678861029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16409761664318224452574019 24614642496477336678861029)
            ·
              refine ⟨4615245468089500627286443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24614642496477336678861029 4615245468089500627286443)
              ·
                refine ⟨6922868202134250940929665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4615245468089500627286443 6922868202134250940929665)
                ·
                  refine ⟨5192151151600688205697249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6922868202134250940929665 5192151151600688205697249)
                  ·
                    refine ⟨3894113363700516154272937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5192151151600688205697249 3894113363700516154272937)
                    ·
                      refine ⟨2920585022775387115704703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3894113363700516154272937 2920585022775387115704703)
                      ·
                        rfl

theorem cell23_5687819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 4, 1, 2, 2, 2].length) (baseStart_5687819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5687819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5687819 prefixEnd_5687819 := by exact prefixLift 5687819
  have htrace : WordTrace (prefixWord ++ tailWord_5687819) baseStart_5687819 baseEnd_5687819 := by
    simpa [prefixWord, tailWord_5687819, baseEnd_5687819] using wordTrace_append hprefix tailTrace_5687819
  have hstable : (prefixWord ++ tailWord_5687819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5687819).length < 2 ^ (prefixWord ++ tailWord_5687819).sum := by decide
  have hdescent : baseEnd_5687819 < baseStart_5687819 := by decide
  rcases family_descends (prefixWord ++ tailWord_5687819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5687862 : List Nat := [5, 1, 2, 1, 2, 1, 1, 1, 2, 5, 2]
def baseStart_5687862 : Nat := 118140960795 + 5687862 * 2 ^ 59
def prefixEnd_5687862 : Nat := 4983230072969 + 3 ^ 40 * 5687862 * 2
def baseEnd_5687862 : Nat := 2920607102443530447467005

theorem tailTrace_5687862 : CollatzResearch.WordTrace tailWord_5687862 prefixEnd_5687862 2920607102443530447467005 := by
  unfold tailWord_5687862
  simp only [CollatzResearch.WordTrace]
  refine ⟨12965835632490928646053115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 138302246746569905557899893 12965835632490928646053115)
  ·
    refine ⟨19448753448736392969079673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12965835632490928646053115 19448753448736392969079673)
    ·
      refine ⟨14586565086552294726809755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19448753448736392969079673 14586565086552294726809755)
      ·
        refine ⟨21879847629828442090214633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14586565086552294726809755 21879847629828442090214633)
        ·
          refine ⟨16409885722371331567660975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21879847629828442090214633 16409885722371331567660975)
          ·
            refine ⟨24614828583556997351491463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16409885722371331567660975 24614828583556997351491463)
            ·
              refine ⟨36922242875335496027237195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24614828583556997351491463 36922242875335496027237195)
              ·
                refine ⟨55383364313003244040855793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36922242875335496027237195 55383364313003244040855793)
                ·
                  refine ⟨41537523234752433030641845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55383364313003244040855793 41537523234752433030641845)
                  ·
                    refine ⟨3894142803258040596622673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41537523234752433030641845 3894142803258040596622673)
                    ·
                      refine ⟨2920607102443530447467005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3894142803258040596622673 2920607102443530447467005)
                      ·
                        rfl

theorem cell23_5687862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 1, 2, 5, 2].length) (baseStart_5687862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5687862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5687862 prefixEnd_5687862 := by exact prefixLift 5687862
  have htrace : WordTrace (prefixWord ++ tailWord_5687862) baseStart_5687862 baseEnd_5687862 := by
    simpa [prefixWord, tailWord_5687862, baseEnd_5687862] using wordTrace_append hprefix tailTrace_5687862
  have hstable : (prefixWord ++ tailWord_5687862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5687862).length < 2 ^ (prefixWord ++ tailWord_5687862).sum := by decide
  have hdescent : baseEnd_5687862 < baseStart_5687862 := by decide
  rcases family_descends (prefixWord ++ tailWord_5687862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5687881 : List Nat := [1, 2, 1, 1, 2, 2, 1, 1, 12]
def baseStart_5687881 : Nat := 118140960795 + 5687881 * 2 ^ 59
def prefixEnd_5687881 : Nat := 4983230072969 + 3 ^ 40 * 5687881 * 2
def baseEnd_5687881 : Nat := 324512984286218430347713

theorem tailTrace_5687881 : CollatzResearch.WordTrace tailWord_5687881 prefixEnd_5687881 324512984286218430347713 := by
  unfold tailWord_5687881
  simp only [CollatzResearch.WordTrace]
  refine ⟨207454063106786024581791497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138302708737857349721194331 207454063106786024581791497)
  ·
    refine ⟨155590547330089518436343623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207454063106786024581791497 155590547330089518436343623)
    ·
      refine ⟨233385820995134277654515435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155590547330089518436343623 233385820995134277654515435)
      ·
        refine ⟨350078731492701416481773153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233385820995134277654515435 350078731492701416481773153)
        ·
          refine ⟨262559048619526062361329865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 350078731492701416481773153 262559048619526062361329865)
          ·
            refine ⟨196919286464644546770997399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 262559048619526062361329865 196919286464644546770997399)
            ·
              refine ⟨295378929696966820156496099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 196919286464644546770997399 295378929696966820156496099)
              ·
                refine ⟨443068394545450230234744149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 295378929696966820156496099 443068394545450230234744149)
                ·
                  refine ⟨324512984286218430347713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 443068394545450230234744149 324512984286218430347713)
                  ·
                    rfl

theorem cell23_5687881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 12].length) (baseStart_5687881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5687881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5687881 prefixEnd_5687881 := by exact prefixLift 5687881
  have htrace : WordTrace (prefixWord ++ tailWord_5687881) baseStart_5687881 baseEnd_5687881 := by
    simpa [prefixWord, tailWord_5687881, baseEnd_5687881] using wordTrace_append hprefix tailTrace_5687881
  have hstable : (prefixWord ++ tailWord_5687881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5687881).length < 2 ^ (prefixWord ++ tailWord_5687881).sum := by decide
  have hdescent : baseEnd_5687881 < baseStart_5687881 := by decide
  rcases family_descends (prefixWord ++ tailWord_5687881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5687891 : List Nat := [1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 9]
def baseStart_5687891 : Nat := 118140960795 + 5687891 * 2 ^ 59
def prefixEnd_5687891 : Nat := 4983230072969 + 3 ^ 40 * 5687891 * 2
def baseEnd_5687891 : Nat := 2920621993382510834004371

theorem tailTrace_5687891 : CollatzResearch.WordTrace tailWord_5687891 prefixEnd_5687891 2920621993382510834004371 := by
  unfold tailWord_5687891
  simp only [CollatzResearch.WordTrace]
  refine ⟨207454427836749796289655527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138302951891166530859770351 207454427836749796289655527)
  ·
    refine ⟨311181641755124694434483291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207454427836749796289655527 311181641755124694434483291)
    ·
      refine ⟨466772462632687041651724937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 311181641755124694434483291 466772462632687041651724937)
      ·
        refine ⟨350079346974515281238793703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 466772462632687041651724937 350079346974515281238793703)
        ·
          refine ⟨525119020461772921858190555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 350079346974515281238793703 525119020461772921858190555)
          ·
            refine ⟨787678530692659382787285833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 525119020461772921858190555 787678530692659382787285833)
            ·
              refine ⟨590758898019494537090464375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 787678530692659382787285833 590758898019494537090464375)
              ·
                refine ⟨886138347029241805635696563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 590758898019494537090464375 886138347029241805635696563)
                ·
                  refine ⟨1329207520543862708453544845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 886138347029241805635696563 1329207520543862708453544845)
                  ·
                    refine ⟨498452820203948515670079317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1329207520543862708453544845 498452820203948515670079317)
                    ·
                      refine ⟨2920621993382510834004371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 498452820203948515670079317 2920621993382510834004371)
                      ·
                        rfl

theorem cell23_5687891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 9].length) (baseStart_5687891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5687891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5687891 prefixEnd_5687891 := by exact prefixLift 5687891
  have htrace : WordTrace (prefixWord ++ tailWord_5687891) baseStart_5687891 baseEnd_5687891 := by
    simpa [prefixWord, tailWord_5687891, baseEnd_5687891] using wordTrace_append hprefix tailTrace_5687891
  have hstable : (prefixWord ++ tailWord_5687891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5687891).length < 2 ^ (prefixWord ++ tailWord_5687891).sum := by decide
  have hdescent : baseEnd_5687891 < baseStart_5687891 := by decide
  rcases family_descends (prefixWord ++ tailWord_5687891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5687892 : List Nat := [2, 4, 1, 1, 1, 5, 1, 1, 2, 1, 4]
def baseStart_5687892 : Nat := 118140960795 + 5687892 * 2 ^ 59
def prefixEnd_5687892 : Nat := 4983230072969 + 3 ^ 40 * 5687892 * 2
def baseEnd_5687892 : Nat := 2920622506863165330091867

theorem tailTrace_5687892 : CollatzResearch.WordTrace tailWord_5687892 prefixEnd_5687892 2920622506863165330091867 := by
  unfold tailWord_5687892
  simp only [CollatzResearch.WordTrace]
  refine ⟨103727232154873086730220965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138302976206497448973627953 103727232154873086730220965)
  ·
    refine ⟨19448856029038703761916431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103727232154873086730220965 19448856029038703761916431)
    ·
      refine ⟨29173284043558055642874647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19448856029038703761916431 29173284043558055642874647)
      ·
        refine ⟨43759926065337083464311971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29173284043558055642874647 43759926065337083464311971)
        ·
          refine ⟨65639889098005625196467957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43759926065337083464311971 65639889098005625196467957)
          ·
            refine ⟨6153739602938027362168871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 65639889098005625196467957 6153739602938027362168871)
            ·
              refine ⟨9230609404407041043253307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6153739602938027362168871 9230609404407041043253307)
              ·
                refine ⟨13845914106610561564879961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9230609404407041043253307 13845914106610561564879961)
                ·
                  refine ⟨10384435579957921173659971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13845914106610561564879961 10384435579957921173659971)
                  ·
                    refine ⟨15576653369936881760489957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10384435579957921173659971 15576653369936881760489957)
                    ·
                      refine ⟨2920622506863165330091867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15576653369936881760489957 2920622506863165330091867)
                      ·
                        rfl

theorem cell23_5687892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 1, 1, 2, 1, 4].length) (baseStart_5687892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5687892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5687892 prefixEnd_5687892 := by exact prefixLift 5687892
  have htrace : WordTrace (prefixWord ++ tailWord_5687892) baseStart_5687892 baseEnd_5687892 := by
    simpa [prefixWord, tailWord_5687892, baseEnd_5687892] using wordTrace_append hprefix tailTrace_5687892
  have hstable : (prefixWord ++ tailWord_5687892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5687892).length < 2 ^ (prefixWord ++ tailWord_5687892).sum := by decide
  have hdescent : baseEnd_5687892 < baseStart_5687892 := by decide
  rcases family_descends (prefixWord ++ tailWord_5687892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5687935 : List Nat := [1, 1, 2, 2, 1, 1, 1, 3, 6, 3, 2]
def baseStart_5687935 : Nat := 118140960795 + 5687935 * 2 ^ 59
def prefixEnd_5687935 : Nat := 4983230072969 + 3 ^ 40 * 5687935 * 2
def baseEnd_5687935 : Nat := 2920644586531308661854169

theorem tailTrace_5687935 : CollatzResearch.WordTrace tailWord_5687935 prefixEnd_5687935 2920644586531308661854169 := by
  unfold tailWord_5687935
  simp only [CollatzResearch.WordTrace]
  refine ⟨207456032648590391804257259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138304021765726927869504839 207456032648590391804257259)
  ·
    refine ⟨311184048972885587706385889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207456032648590391804257259 311184048972885587706385889)
    ·
      refine ⟨233388036729664190779789417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 311184048972885587706385889 233388036729664190779789417)
      ·
        refine ⟨175041027547248143084842063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 233388036729664190779789417 175041027547248143084842063)
        ·
          refine ⟨262561541320872214627263095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175041027547248143084842063 262561541320872214627263095)
          ·
            refine ⟨393842311981308321940894643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 262561541320872214627263095 393842311981308321940894643)
            ·
              refine ⟨590763467971962482911341965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 393842311981308321940894643 590763467971962482911341965)
              ·
                refine ⟨221536300489485931091753237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 590763467971962482911341965 221536300489485931091753237)
                ·
                  refine ⟨10384514085444653019925933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 221536300489485931091753237 10384514085444653019925933)
                  ·
                    refine ⟨3894192782041744882472225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10384514085444653019925933 3894192782041744882472225)
                    ·
                      refine ⟨2920644586531308661854169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3894192782041744882472225 2920644586531308661854169)
                      ·
                        rfl

theorem cell23_5687935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 6, 3, 2].length) (baseStart_5687935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5687935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5687935 prefixEnd_5687935 := by exact prefixLift 5687935
  have htrace : WordTrace (prefixWord ++ tailWord_5687935) baseStart_5687935 baseEnd_5687935 := by
    simpa [prefixWord, tailWord_5687935, baseEnd_5687935] using wordTrace_append hprefix tailTrace_5687935
  have hstable : (prefixWord ++ tailWord_5687935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5687935).length < 2 ^ (prefixWord ++ tailWord_5687935).sum := by decide
  have hdescent : baseEnd_5687935 < baseStart_5687935 := by decide
  rcases family_descends (prefixWord ++ tailWord_5687935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5687969 : List Nat := [1, 2, 3, 3, 3, 1, 1, 2, 2, 3, 2]
def baseStart_5687969 : Nat := 118140960795 + 5687969 * 2 ^ 59
def prefixEnd_5687969 : Nat := 4983230072969 + 3 ^ 40 * 5687969 * 2
def baseEnd_5687969 : Nat := 2920662044873561528829013

theorem tailTrace_5687969 : CollatzResearch.WordTrace tailWord_5687969 prefixEnd_5687969 2920662044873561528829013 := by
  unfold tailWord_5687969
  simp only [CollatzResearch.WordTrace]
  refine ⟨207457272730467215610994961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138304848486978143740663307 207457272730467215610994961)
  ·
    refine ⟨155592954547850411708246221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207457272730467215610994961 155592954547850411708246221)
    ·
      refine ⟨58347357955443904390592333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 155592954547850411708246221 58347357955443904390592333)
      ·
        refine ⟨21880259233291464146472125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58347357955443904390592333 21880259233291464146472125)
        ·
          refine ⟨8205097212484299054927047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21880259233291464146472125 8205097212484299054927047)
          ·
            refine ⟨12307645818726448582390571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8205097212484299054927047 12307645818726448582390571)
            ·
              refine ⟨18461468728089672873585857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12307645818726448582390571 18461468728089672873585857)
              ·
                refine ⟨13846101546067254655189393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18461468728089672873585857 13846101546067254655189393)
                ·
                  refine ⟨10384576159550440991392045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13846101546067254655189393 10384576159550440991392045)
                  ·
                    refine ⟨3894216059831415371772017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10384576159550440991392045 3894216059831415371772017)
                    ·
                      refine ⟨2920662044873561528829013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3894216059831415371772017 2920662044873561528829013)
                      ·
                        rfl

theorem cell23_5687969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 2, 2, 3, 2].length) (baseStart_5687969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5687969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5687969 prefixEnd_5687969 := by exact prefixLift 5687969
  have htrace : WordTrace (prefixWord ++ tailWord_5687969) baseStart_5687969 baseEnd_5687969 := by
    simpa [prefixWord, tailWord_5687969, baseEnd_5687969] using wordTrace_append hprefix tailTrace_5687969
  have hstable : (prefixWord ++ tailWord_5687969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5687969).length < 2 ^ (prefixWord ++ tailWord_5687969).sum := by decide
  have hdescent : baseEnd_5687969 < baseStart_5687969 := by decide
  rcases family_descends (prefixWord ++ tailWord_5687969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5688012 : List Nat := [2, 2, 1, 5, 1, 2, 1, 2, 1, 2, 4]
def baseStart_5688012 : Nat := 118140960795 + 5688012 * 2 ^ 59
def prefixEnd_5688012 : Nat := 4983230072969 + 3 ^ 40 * 5688012 * 2
def baseEnd_5688012 : Nat := 2920684124541704860591315

theorem tailTrace_5688012 : CollatzResearch.WordTrace tailWord_5688012 prefixEnd_5688012 2920684124541704860591315 := by
  unfold tailWord_5688012
  simp only [CollatzResearch.WordTrace]
  refine ⟨103729420534655716977405145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138305894046207622636540193 103729420534655716977405145)
  ·
    refine ⟨77797065400991787733053859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103729420534655716977405145 77797065400991787733053859)
    ·
      refine ⟨116695598101487681599580789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77797065400991787733053859 116695598101487681599580789)
      ·
        refine ⟨10940212322014470149960699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 116695598101487681599580789 10940212322014470149960699)
        ·
          refine ⟨16410318483021705224941049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10940212322014470149960699 16410318483021705224941049)
          ·
            refine ⟨12307738862266278918705787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16410318483021705224941049 12307738862266278918705787)
            ·
              refine ⟨18461608293399418378058681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12307738862266278918705787 18461608293399418378058681)
              ·
                refine ⟨13846206220049563783544011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18461608293399418378058681 13846206220049563783544011)
                ·
                  refine ⟨20769309330074345675316017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13846206220049563783544011 20769309330074345675316017)
                  ·
                    refine ⟨15576981997555759256487013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20769309330074345675316017 15576981997555759256487013)
                    ·
                      refine ⟨2920684124541704860591315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15576981997555759256487013 2920684124541704860591315)
                      ·
                        rfl

theorem cell23_5688012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_5688012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5688012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5688012 prefixEnd_5688012 := by exact prefixLift 5688012
  have htrace : WordTrace (prefixWord ++ tailWord_5688012) baseStart_5688012 baseEnd_5688012 := by
    simpa [prefixWord, tailWord_5688012, baseEnd_5688012] using wordTrace_append hprefix tailTrace_5688012
  have hstable : (prefixWord ++ tailWord_5688012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5688012).length < 2 ^ (prefixWord ++ tailWord_5688012).sum := by decide
  have hdescent : baseEnd_5688012 < baseStart_5688012 := by decide
  rcases family_descends (prefixWord ++ tailWord_5688012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5688033 : List Nat := [1, 2, 3, 1, 4, 1, 4, 2, 1, 2, 2]
def baseStart_5688033 : Nat := 118140960795 + 5688033 * 2 ^ 59
def prefixEnd_5688033 : Nat := 4983230072969 + 3 ^ 40 * 5688033 * 2
def baseEnd_5688033 : Nat := 2920694907635449278428719

theorem tailTrace_5688033 : CollatzResearch.WordTrace tailWord_5688033 prefixEnd_5688033 2920694907635449278428719 := by
  unfold tailWord_5688033
  simp only [CollatzResearch.WordTrace]
  refine ⟨207459607002235354541324753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138306404668156903027549835 207459607002235354541324753)
  ·
    refine ⟨155594705251676515905993565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207459607002235354541324753 155594705251676515905993565)
    ·
      refine ⟨58348014469378693464747587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 155594705251676515905993565 58348014469378693464747587)
      ·
        refine ⟨87522021704068040197121381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58348014469378693464747587 87522021704068040197121381)
        ·
          refine ⟨16410379069512757536960259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87522021704068040197121381 16410379069512757536960259)
          ·
            refine ⟨24615568604269136305440389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16410379069512757536960259 24615568604269136305440389)
            ·
              refine ⟨4615419113300463057270073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24615568604269136305440389 4615419113300463057270073)
              ·
                refine ⟨3461564334975347292952555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4615419113300463057270073 3461564334975347292952555)
                ·
                  refine ⟨5192346502463020939428833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3461564334975347292952555 5192346502463020939428833)
                  ·
                    refine ⟨3894259876847265704571625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5192346502463020939428833 3894259876847265704571625)
                    ·
                      refine ⟨2920694907635449278428719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3894259876847265704571625 2920694907635449278428719)
                      ·
                        rfl

theorem cell23_5688033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 4, 2, 1, 2, 2].length) (baseStart_5688033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5688033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5688033 prefixEnd_5688033 := by exact prefixLift 5688033
  have htrace : WordTrace (prefixWord ++ tailWord_5688033) baseStart_5688033 baseEnd_5688033 := by
    simpa [prefixWord, tailWord_5688033, baseEnd_5688033] using wordTrace_append hprefix tailTrace_5688033
  have hstable : (prefixWord ++ tailWord_5688033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5688033).length < 2 ^ (prefixWord ++ tailWord_5688033).sum := by decide
  have hdescent : baseEnd_5688033 < baseStart_5688033 := by decide
  rcases family_descends (prefixWord ++ tailWord_5688033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5688035 : List Nat := [1, 1, 1, 7, 1, 1, 1, 1, 2, 7]
def baseStart_5688035 : Nat := 118140960795 + 5688035 * 2 ^ 59
def prefixEnd_5688035 : Nat := 4983230072969 + 3 ^ 40 * 5688035 * 2
def baseEnd_5688035 : Nat := 973565311532252756867903

theorem tailTrace_5688035 : CollatzResearch.WordTrace tailWord_5688035 prefixEnd_5688035 973565311532252756867903 := by
  unfold tailWord_5688035
  simp only [CollatzResearch.WordTrace]
  refine ⟨207459679948228108882897559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138306453298818739255265039 207459679948228108882897559)
  ·
    refine ⟨311189519922342163324346339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207459679948228108882897559 311189519922342163324346339)
    ·
      refine ⟨466784279883513244986519509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 311189519922342163324346339 466784279883513244986519509)
      ·
        refine ⟨10940256559769841679371551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 466784279883513244986519509 10940256559769841679371551)
        ·
          refine ⟨16410384839654762519057327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10940256559769841679371551 16410384839654762519057327)
          ·
            refine ⟨24615577259482143778585991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16410384839654762519057327 24615577259482143778585991)
            ·
              refine ⟨36923365889223215667878987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24615577259482143778585991 36923365889223215667878987)
              ·
                refine ⟨55385048833834823501818481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36923365889223215667878987 55385048833834823501818481)
                ·
                  refine ⟨41538786625376117626363861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55385048833834823501818481 41538786625376117626363861)
                  ·
                    refine ⟨973565311532252756867903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41538786625376117626363861 973565311532252756867903)
                    ·
                      rfl

theorem cell23_5688035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 1, 2, 7].length) (baseStart_5688035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5688035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5688035 prefixEnd_5688035 := by exact prefixLift 5688035
  have htrace : WordTrace (prefixWord ++ tailWord_5688035) baseStart_5688035 baseEnd_5688035 := by
    simpa [prefixWord, tailWord_5688035, baseEnd_5688035] using wordTrace_append hprefix tailTrace_5688035
  have hstable : (prefixWord ++ tailWord_5688035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5688035).length < 2 ^ (prefixWord ++ tailWord_5688035).sum := by decide
  have hdescent : baseEnd_5688035 < baseStart_5688035 := by decide
  rcases family_descends (prefixWord ++ tailWord_5688035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5688085 : List Nat := [1, 3, 2, 1, 2, 2, 1, 1, 4, 2, 4]
def baseStart_5688085 : Nat := 118140960795 + 5688085 * 2 ^ 59
def prefixEnd_5688085 : Nat := 4983230072969 + 3 ^ 40 * 5688085 * 2
def baseEnd_5688085 : Nat := 2920721608629483074978479

theorem tailTrace_5688085 : CollatzResearch.WordTrace tailWord_5688085 prefixEnd_5688085 2920721608629483074978479 := by
  unfold tailWord_5688085
  simp only [CollatzResearch.WordTrace]
  refine ⟨207461503598046967422217709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138307669065364644948145139 207461503598046967422217709)
  ·
    refine ⟨77798063849267612783331641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 207461503598046967422217709 77798063849267612783331641)
    ·
      refine ⟨58348547886950709587498731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77798063849267612783331641 58348547886950709587498731)
      ·
        refine ⟨87522821830426064381248097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58348547886950709587498731 87522821830426064381248097)
        ·
          refine ⟨65642116372819548285936073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87522821830426064381248097 65642116372819548285936073)
          ·
            refine ⟨49231587279614661214452055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65642116372819548285936073 49231587279614661214452055)
            ·
              refine ⟨73847380919421991821678083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49231587279614661214452055 73847380919421991821678083)
              ·
                refine ⟨110771071379132987732517125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73847380919421991821678083 110771071379132987732517125)
                ·
                  refine ⟨20769575883587435199846961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 110771071379132987732517125 20769575883587435199846961)
                  ·
                    refine ⟨15577181912690576399885221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20769575883587435199846961 15577181912690576399885221)
                    ·
                      refine ⟨2920721608629483074978479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15577181912690576399885221 2920721608629483074978479)
                      ·
                        rfl

theorem cell23_5688085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 4, 2, 4].length) (baseStart_5688085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5688085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5688085 prefixEnd_5688085 := by exact prefixLift 5688085
  have htrace : WordTrace (prefixWord ++ tailWord_5688085) baseStart_5688085 baseEnd_5688085 := by
    simpa [prefixWord, tailWord_5688085, baseEnd_5688085] using wordTrace_append hprefix tailTrace_5688085
  have hstable : (prefixWord ++ tailWord_5688085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5688085).length < 2 ^ (prefixWord ++ tailWord_5688085).sum := by decide
  have hdescent : baseEnd_5688085 < baseStart_5688085 := by decide
  rcases family_descends (prefixWord ++ tailWord_5688085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5688089 : List Nat := [1, 2, 1, 2, 1, 1, 1, 8, 2, 2, 2]
def baseStart_5688089 : Nat := 118140960795 + 5688089 * 2 ^ 59
def prefixEnd_5688089 : Nat := 4983230072969 + 3 ^ 40 * 5688089 * 2
def baseEnd_5688089 : Nat := 2920723662552101059328461

theorem tailTrace_5688089 : CollatzResearch.WordTrace tailWord_5688089 prefixEnd_5688089 2920723662552101059328461 := by
  unfold tailWord_5688089
  simp only [CollatzResearch.WordTrace]
  refine ⟨207461649490032476105363321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138307766326688317403575547 207461649490032476105363321)
  ·
    refine ⟨155596237117524357079022491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207461649490032476105363321 155596237117524357079022491)
    ·
      refine ⟨233394355676286535618533737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155596237117524357079022491 233394355676286535618533737)
      ·
        refine ⟨175045766757214901713900303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 233394355676286535618533737 175045766757214901713900303)
        ·
          refine ⟨262568650135822352570850455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175045766757214901713900303 262568650135822352570850455)
          ·
            refine ⟨393852975203733528856275683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 262568650135822352570850455 393852975203733528856275683)
            ·
              refine ⟨590779462805600293284413525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 393852975203733528856275683 590779462805600293284413525)
              ·
                refine ⟨6923196829753128436926721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 590779462805600293284413525 6923196829753128436926721)
                ·
                  refine ⟨5192397622314846327695041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6923196829753128436926721 5192397622314846327695041)
                  ·
                    refine ⟨3894298216736134745771281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5192397622314846327695041 3894298216736134745771281)
                    ·
                      refine ⟨2920723662552101059328461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3894298216736134745771281 2920723662552101059328461)
                      ·
                        rfl

theorem cell23_5688089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 8, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 8, 2, 2, 2].length) (baseStart_5688089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5688089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5688089 prefixEnd_5688089 := by exact prefixLift 5688089
  have htrace : WordTrace (prefixWord ++ tailWord_5688089) baseStart_5688089 baseEnd_5688089 := by
    simpa [prefixWord, tailWord_5688089, baseEnd_5688089] using wordTrace_append hprefix tailTrace_5688089
  have hstable : (prefixWord ++ tailWord_5688089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5688089).length < 2 ^ (prefixWord ++ tailWord_5688089).sum := by decide
  have hdescent : baseEnd_5688089 < baseStart_5688089 := by decide
  rcases family_descends (prefixWord ++ tailWord_5688089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5688095 : List Nat := [1, 1, 2, 4, 2, 2, 1, 3, 7]
def baseStart_5688095 : Nat := 118140960795 + 5688095 * 2 ^ 59
def prefixEnd_5688095 : Nat := 4983230072969 + 3 ^ 40 * 5688095 * 2
def baseEnd_5688095 : Nat := 324525193715114226205937

theorem tailTrace_5688095 : CollatzResearch.WordTrace tailWord_5688095 prefixEnd_5688095 324525193715114226205937 := by
  unfold tailWord_5688095
  simp only [CollatzResearch.WordTrace]
  refine ⟨207461868328010739130081739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138307912218673826086721159 207461868328010739130081739)
  ·
    refine ⟨311192802492016108695122609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207461868328010739130081739 311192802492016108695122609)
    ·
      refine ⟨233394601869012081521341957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 311192802492016108695122609 233394601869012081521341957)
      ·
        refine ⟨43761487850439765285251617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 233394601869012081521341957 43761487850439765285251617)
        ·
          refine ⟨32821115887829823963938713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43761487850439765285251617 32821115887829823963938713)
          ·
            refine ⟨24615836915872367972954035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32821115887829823963938713 24615836915872367972954035)
            ·
              refine ⟨36923755373808551959431053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24615836915872367972954035 36923755373808551959431053)
              ·
                refine ⟨13846408265178206984786645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36923755373808551959431053 13846408265178206984786645)
                ·
                  refine ⟨324525193715114226205937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13846408265178206984786645 324525193715114226205937)
                  ·
                    rfl

theorem cell23_5688095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 3, 7].length) (baseStart_5688095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5688095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5688095 prefixEnd_5688095 := by exact prefixLift 5688095
  have htrace : WordTrace (prefixWord ++ tailWord_5688095) baseStart_5688095 baseEnd_5688095 := by
    simpa [prefixWord, tailWord_5688095, baseEnd_5688095] using wordTrace_append hprefix tailTrace_5688095
  have hstable : (prefixWord ++ tailWord_5688095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5688095).length < 2 ^ (prefixWord ++ tailWord_5688095).sum := by decide
  have hdescent : baseEnd_5688095 < baseStart_5688095 := by decide
  rcases family_descends (prefixWord ++ tailWord_5688095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5688135 : List Nat := [1, 1, 4, 1, 2, 1, 1, 4, 1, 2, 5]
def baseStart_5688135 : Nat := 118140960795 + 5688135 * 2 ^ 59
def prefixEnd_5688135 : Nat := 4983230072969 + 3 ^ 40 * 5688135 * 2
def baseEnd_5688135 : Nat := 2920747282662207879353249

theorem tailTrace_5688135 : CollatzResearch.WordTrace tailWord_5688135 prefixEnd_5688135 2920747282662207879353249 := by
  unfold tailWord_5688135
  simp only [CollatzResearch.WordTrace]
  refine ⟨207463327247865825961537859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138308884831910550641025239 207463327247865825961537859)
  ·
    refine ⟨311194990871798738942306789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207463327247865825961537859 311194990871798738942306789)
    ·
      refine ⟨58349060788462263551682523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 311194990871798738942306789 58349060788462263551682523)
      ·
        refine ⟨87523591182693395327523785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58349060788462263551682523 87523591182693395327523785)
        ·
          refine ⟨65642693387020046495642839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87523591182693395327523785 65642693387020046495642839)
          ·
            refine ⟨98464040080530069743464259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65642693387020046495642839 98464040080530069743464259)
            ·
              refine ⟨147696060120795104615196389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98464040080530069743464259 147696060120795104615196389)
              ·
                refine ⟨27693011272649082115349323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 147696060120795104615196389 27693011272649082115349323)
                ·
                  refine ⟨41539516908973623173023985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27693011272649082115349323 41539516908973623173023985)
                  ·
                    refine ⟨31154637681730217379767989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41539516908973623173023985 31154637681730217379767989)
                    ·
                      refine ⟨2920747282662207879353249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31154637681730217379767989 2920747282662207879353249)
                      ·
                        rfl

theorem cell23_5688135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 4, 1, 2, 5].length) (baseStart_5688135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5688135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5688135 prefixEnd_5688135 := by exact prefixLift 5688135
  have htrace : WordTrace (prefixWord ++ tailWord_5688135) baseStart_5688135 baseEnd_5688135 := by
    simpa [prefixWord, tailWord_5688135, baseEnd_5688135] using wordTrace_append hprefix tailTrace_5688135
  have hstable : (prefixWord ++ tailWord_5688135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5688135).length < 2 ^ (prefixWord ++ tailWord_5688135).sum := by decide
  have hdescent : baseEnd_5688135 < baseStart_5688135 := by decide
  rcases family_descends (prefixWord ++ tailWord_5688135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5688172 : List Nat := [2, 2, 1, 1, 4, 1, 2, 1, 5, 4]
def baseStart_5688172 : Nat := 118140960795 + 5688172 * 2 ^ 59
def prefixEnd_5688172 : Nat := 4983230072969 + 3 ^ 40 * 5688172 * 2
def baseEnd_5688172 : Nat := 973588760482141411530193

theorem tailTrace_5688172 : CollatzResearch.WordTrace tailWord_5688172 prefixEnd_5688172 973588760482141411530193 := by
  unfold tailWord_5688172
  simp only [CollatzResearch.WordTrace]
  refine ⟨103732338374365890640317385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138309784499154520853756513 103732338374365890640317385)
  ·
    refine ⟨77799253780774417980238039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103732338374365890640317385 77799253780774417980238039)
    ·
      refine ⟨116698880671161626970357059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77799253780774417980238039 116698880671161626970357059)
      ·
        refine ⟨175048321006742440455535589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116698880671161626970357059 175048321006742440455535589)
        ·
          refine ⟨32821560188764207585412923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 175048321006742440455535589 32821560188764207585412923)
          ·
            refine ⟨49232340283146311378119385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32821560188764207585412923 49232340283146311378119385)
            ·
              refine ⟨36924255212359733533589539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49232340283146311378119385 36924255212359733533589539)
              ·
                refine ⟨55386382818539600300384309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36924255212359733533589539 55386382818539600300384309)
                ·
                  refine ⟨5192473389238087528161029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 55386382818539600300384309 5192473389238087528161029)
                  ·
                    refine ⟨973588760482141411530193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5192473389238087528161029 973588760482141411530193)
                    ·
                      rfl

theorem cell23_5688172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 4].length) (baseStart_5688172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5688172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5688172 prefixEnd_5688172 := by exact prefixLift 5688172
  have htrace : WordTrace (prefixWord ++ tailWord_5688172) baseStart_5688172 baseEnd_5688172 := by
    simpa [prefixWord, tailWord_5688172, baseEnd_5688172] using wordTrace_append hprefix tailTrace_5688172
  have hstable : (prefixWord ++ tailWord_5688172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5688172).length < 2 ^ (prefixWord ++ tailWord_5688172).sum := by decide
  have hdescent : baseEnd_5688172 < baseStart_5688172 := by decide
  rcases family_descends (prefixWord ++ tailWord_5688172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5688175 : List Nat := [1, 1, 2, 1, 3, 1, 1, 3, 2, 4, 4]
def baseStart_5688175 : Nat := 118140960795 + 5688175 * 2 ^ 59
def prefixEnd_5688175 : Nat := 4983230072969 + 3 ^ 40 * 5688175 * 2
def baseEnd_5688175 : Nat := 2920767821888387722853065

theorem tailTrace_5688175 : CollatzResearch.WordTrace tailWord_5688175 prefixEnd_5688175 2920767821888387722853065 := by
  unfold tailWord_5688175
  simp only [CollatzResearch.WordTrace]
  refine ⟨207464786167720912792993979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138309857445147275195329319 207464786167720912792993979)
  ·
    refine ⟨311197179251581369189490969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207464786167720912792993979 311197179251581369189490969)
    ·
      refine ⟨233397884438686026892118227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 311197179251581369189490969 233397884438686026892118227)
      ·
        refine ⟨350096826658029040338177341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233397884438686026892118227 350096826658029040338177341)
        ·
          refine ⟨131286309996760890126816503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 350096826658029040338177341 131286309996760890126816503)
          ·
            refine ⟨196929464995141335190224755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131286309996760890126816503 196929464995141335190224755)
            ·
              refine ⟨295394197492712002785337133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 196929464995141335190224755 295394197492712002785337133)
              ·
                refine ⟨110772824059767001044501425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 295394197492712002785337133 110772824059767001044501425)
                ·
                  refine ⟨83079618044825250783376069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 110772824059767001044501425 83079618044825250783376069)
                  ·
                    refine ⟨15577428383404734521883013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 83079618044825250783376069 15577428383404734521883013)
                    ·
                      refine ⟨2920767821888387722853065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15577428383404734521883013 2920767821888387722853065)
                      ·
                        rfl

theorem cell23_5688175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 2, 4, 4].length) (baseStart_5688175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5688175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5688175 prefixEnd_5688175 := by exact prefixLift 5688175
  have htrace : WordTrace (prefixWord ++ tailWord_5688175) baseStart_5688175 baseEnd_5688175 := by
    simpa [prefixWord, tailWord_5688175, baseEnd_5688175] using wordTrace_append hprefix tailTrace_5688175
  have hstable : (prefixWord ++ tailWord_5688175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5688175).length < 2 ^ (prefixWord ++ tailWord_5688175).sum := by decide
  have hdescent : baseEnd_5688175 < baseStart_5688175 := by decide
  rcases family_descends (prefixWord ++ tailWord_5688175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5688199 : List Nat := [1, 1, 4, 2, 3, 1, 2, 2, 2, 2, 3]
def baseStart_5688199 : Nat := 118140960795 + 5688199 * 2 ^ 59
def prefixEnd_5688199 : Nat := 4983230072969 + 3 ^ 40 * 5688199 * 2
def baseEnd_5688199 : Nat := 2920780145424095628952955

theorem tailTrace_5688199 : CollatzResearch.WordTrace tailWord_5688199 prefixEnd_5688199 2920780145424095628952955 := by
  unfold tailWord_5688199
  simp only [CollatzResearch.WordTrace]
  refine ⟨207465661519633964891867651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138310441013089309927911767 207465661519633964891867651)
  ·
    refine ⟨311198492279450947337801477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207465661519633964891867651 311198492279450947337801477)
    ·
      refine ⟨58349717302397052625837777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 311198492279450947337801477 58349717302397052625837777)
      ·
        refine ⟨43762287976797789469378333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58349717302397052625837777 43762287976797789469378333)
        ·
          refine ⟨16410857991299171051016875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43762287976797789469378333 16410857991299171051016875)
          ·
            refine ⟨24616286986948756576525313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16410857991299171051016875 24616286986948756576525313)
            ·
              refine ⟨18462215240211567432393985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24616286986948756576525313 18462215240211567432393985)
              ·
                refine ⟨13846661430158675574295489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18462215240211567432393985 13846661430158675574295489)
                ·
                  refine ⟨10384996072619006680721617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13846661430158675574295489 10384996072619006680721617)
                  ·
                    refine ⟨7788747054464255010541213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10384996072619006680721617 7788747054464255010541213)
                    ·
                      refine ⟨2920780145424095628952955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7788747054464255010541213 2920780145424095628952955)
                      ·
                        rfl

theorem cell23_5688199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 2, 2, 2, 3].length) (baseStart_5688199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5688199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5688199 prefixEnd_5688199 := by exact prefixLift 5688199
  have htrace : WordTrace (prefixWord ++ tailWord_5688199) baseStart_5688199 baseEnd_5688199 := by
    simpa [prefixWord, tailWord_5688199, baseEnd_5688199] using wordTrace_append hprefix tailTrace_5688199
  have hstable : (prefixWord ++ tailWord_5688199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5688199).length < 2 ^ (prefixWord ++ tailWord_5688199).sum := by decide
  have hdescent : baseEnd_5688199 < baseStart_5688199 := by decide
  rcases family_descends (prefixWord ++ tailWord_5688199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5688239 : List Nat := [1, 1, 2, 1, 2, 2, 2, 5, 2, 3, 2]
def baseStart_5688239 : Nat := 118140960795 + 5688239 * 2 ^ 59
def prefixEnd_5688239 : Nat := 4983230072969 + 3 ^ 40 * 5688239 * 2
def baseEnd_5688239 : Nat := 2920800684650275472452771

theorem tailTrace_5688239 : CollatzResearch.WordTrace tailWord_5688239 prefixEnd_5688239 2920800684650275472452771 := by
  unfold tailWord_5688239
  simp only [CollatzResearch.WordTrace]
  refine ⟨207467120439489051723323771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138311413626326034482215847 207467120439489051723323771)
  ·
    refine ⟨311200680659233577584985657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207467120439489051723323771 311200680659233577584985657)
    ·
      refine ⟨233400510494425183188739243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 311200680659233577584985657 233400510494425183188739243)
      ·
        refine ⟨350100765741637774783108865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233400510494425183188739243 350100765741637774783108865)
        ·
          refine ⟨262575574306228331087331649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 350100765741637774783108865 262575574306228331087331649)
          ·
            refine ⟨196931680729671248315498737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 262575574306228331087331649 196931680729671248315498737)
            ·
              refine ⟨147698760547253436236624053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 196931680729671248315498737 147698760547253436236624053)
              ·
                refine ⟨13846758801305009647183505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 147698760547253436236624053 13846758801305009647183505)
                ·
                  refine ⟨10385069100978757235387629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13846758801305009647183505 10385069100978757235387629)
                  ·
                    refine ⟨3894400912867033963270361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10385069100978757235387629 3894400912867033963270361)
                    ·
                      refine ⟨2920800684650275472452771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3894400912867033963270361 2920800684650275472452771)
                      ·
                        rfl

theorem cell23_5688239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 5, 2, 3, 2].length) (baseStart_5688239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5688239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5688239 prefixEnd_5688239 := by exact prefixLift 5688239
  have htrace : WordTrace (prefixWord ++ tailWord_5688239) baseStart_5688239 baseEnd_5688239 := by
    simpa [prefixWord, tailWord_5688239, baseEnd_5688239] using wordTrace_append hprefix tailTrace_5688239
  have hstable : (prefixWord ++ tailWord_5688239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5688239).length < 2 ^ (prefixWord ++ tailWord_5688239).sum := by decide
  have hdescent : baseEnd_5688239 < baseStart_5688239 := by decide
  rcases family_descends (prefixWord ++ tailWord_5688239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5688249 : List Nat := [1, 2, 1, 4, 2, 3, 1, 3, 1, 5]
def baseStart_5688249 : Nat := 118140960795 + 5688249 * 2 ^ 59
def prefixEnd_5688249 : Nat := 4983230072969 + 3 ^ 40 * 5688249 * 2
def baseEnd_5688249 : Nat := 973601939818940144442575

theorem tailTrace_5688249 : CollatzResearch.WordTrace tailWord_5688249 prefixEnd_5688249 973601939818940144442575 := by
  unfold tailWord_5688249
  simp only [CollatzResearch.WordTrace]
  refine ⟨207467485169452823431187801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138311656779635215620791867 207467485169452823431187801)
  ·
    refine ⟨155600613877089617573390851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207467485169452823431187801 155600613877089617573390851)
    ·
      refine ⟨233400920815634426360086277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155600613877089617573390851 233400920815634426360086277)
      ·
        refine ⟨43762672652931454942516177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 233400920815634426360086277 43762672652931454942516177)
        ·
          refine ⟨32822004489698591206887133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43762672652931454942516177 32822004489698591206887133)
          ·
            refine ⟨12308251683636971702582675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32822004489698591206887133 12308251683636971702582675)
            ·
              refine ⟨18462377525455457553874013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12308251683636971702582675 18462377525455457553874013)
              ·
                refine ⟨6923391572045796582702755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18462377525455457553874013 6923391572045796582702755)
                ·
                  refine ⟨10385087358068694874054133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6923391572045796582702755 10385087358068694874054133)
                  ·
                    refine ⟨973601939818940144442575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10385087358068694874054133 973601939818940144442575)
                    ·
                      rfl

theorem cell23_5688249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 3, 1, 5].length) (baseStart_5688249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5688249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5688249 prefixEnd_5688249 := by exact prefixLift 5688249
  have htrace : WordTrace (prefixWord ++ tailWord_5688249) baseStart_5688249 baseEnd_5688249 := by
    simpa [prefixWord, tailWord_5688249, baseEnd_5688249] using wordTrace_append hprefix tailTrace_5688249
  have hstable : (prefixWord ++ tailWord_5688249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5688249).length < 2 ^ (prefixWord ++ tailWord_5688249).sum := by decide
  have hdescent : baseEnd_5688249 < baseStart_5688249 := by decide
  rcases family_descends (prefixWord ++ tailWord_5688249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5688346 : List Nat := [3, 1, 1, 3, 1, 2, 3, 1, 3, 3, 2]
def baseStart_5688346 : Nat := 118140960795 + 5688346 * 2 ^ 59
def prefixEnd_5688346 : Nat := 4983230072969 + 3 ^ 40 * 5688346 * 2
def baseEnd_5688346 : Nat := 2920855627080306553814779

theorem tailTrace_5688346 : CollatzResearch.WordTrace tailWord_5688346 prefixEnd_5688346 2920855627080306553814779 := by
  unfold tailWord_5688346
  simp only [CollatzResearch.WordTrace]
  refine ⟨51867755762525352249367223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138314015366734272664979261 51867755762525352249367223)
  ·
    refine ⟨77801633643788028374050835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51867755762525352249367223 77801633643788028374050835)
    ·
      refine ⟨116702450465682042561076253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77801633643788028374050835 116702450465682042561076253)
      ·
        refine ⟨43763418924630765960403595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116702450465682042561076253 43763418924630765960403595)
        ·
          refine ⟨65645128386946148940605393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43763418924630765960403595 65645128386946148940605393)
          ·
            refine ⟨49233846290209611705454045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65645128386946148940605393 49233846290209611705454045)
            ·
              refine ⟨18462692358828604389545267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49233846290209611705454045 18462692358828604389545267)
              ·
                refine ⟨27694038538242906584317901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18462692358828604389545267 27694038538242906584317901)
                ·
                  refine ⟨10385264451841089969119213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27694038538242906584317901 10385264451841089969119213)
                  ·
                    refine ⟨3894474169440408738419705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10385264451841089969119213 3894474169440408738419705)
                    ·
                      refine ⟨2920855627080306553814779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3894474169440408738419705 2920855627080306553814779)
                      ·
                        rfl

theorem cell23_5688346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 1, 3, 3, 2].length) (baseStart_5688346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5688346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5688346 prefixEnd_5688346 := by exact prefixLift 5688346
  have htrace : WordTrace (prefixWord ++ tailWord_5688346) baseStart_5688346 baseEnd_5688346 := by
    simpa [prefixWord, tailWord_5688346, baseEnd_5688346] using wordTrace_append hprefix tailTrace_5688346
  have hstable : (prefixWord ++ tailWord_5688346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5688346).length < 2 ^ (prefixWord ++ tailWord_5688346).sum := by decide
  have hdescent : baseEnd_5688346 < baseStart_5688346 := by decide
  rcases family_descends (prefixWord ++ tailWord_5688346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5688363 : List Nat := [1, 1, 1, 1, 2, 1, 9, 1, 1, 3, 2]
def baseStart_5688363 : Nat := 118140960795 + 5688363 * 2 ^ 59
def prefixEnd_5688363 : Nat := 4983230072969 + 3 ^ 40 * 5688363 * 2
def baseEnd_5688363 : Nat := 2920864356251432987302201

theorem tailTrace_5688363 : CollatzResearch.WordTrace tailWord_5688363 prefixEnd_5688363 2920864356251432987302201 := by
  unfold tailWord_5688363
  simp only [CollatzResearch.WordTrace]
  refine ⟨207471643091039820900837743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138314428727359880600558495 207471643091039820900837743)
  ·
    refine ⟨311207464636559731351256615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207471643091039820900837743 311207464636559731351256615)
    ·
      refine ⟨466811196954839597026884923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 311207464636559731351256615 466811196954839597026884923)
      ·
        refine ⟨700216795432259395540327385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 466811196954839597026884923 700216795432259395540327385)
        ·
          refine ⟨525162596574194546655245539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 700216795432259395540327385 525162596574194546655245539)
          ·
            refine ⟨787743894861291819982868309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 525162596574194546655245539 787743894861291819982868309)
            ·
              refine ⟨4615686883952881757712119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 787743894861291819982868309 4615686883952881757712119)
              ·
                refine ⟨6923530325929322636568179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4615686883952881757712119 6923530325929322636568179)
                ·
                  refine ⟨10385295488893983954852269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6923530325929322636568179 10385295488893983954852269)
                  ·
                    refine ⟨3894485808335243983069601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10385295488893983954852269 3894485808335243983069601)
                    ·
                      refine ⟨2920864356251432987302201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3894485808335243983069601 2920864356251432987302201)
                      ·
                        rfl

theorem cell23_5688363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 9, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 9, 1, 1, 3, 2].length) (baseStart_5688363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5688363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5688363 prefixEnd_5688363 := by exact prefixLift 5688363
  have htrace : WordTrace (prefixWord ++ tailWord_5688363) baseStart_5688363 baseEnd_5688363 := by
    simpa [prefixWord, tailWord_5688363, baseEnd_5688363] using wordTrace_append hprefix tailTrace_5688363
  have hstable : (prefixWord ++ tailWord_5688363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5688363).length < 2 ^ (prefixWord ++ tailWord_5688363).sum := by decide
  have hdescent : baseEnd_5688363 < baseStart_5688363 := by decide
  rcases family_descends (prefixWord ++ tailWord_5688363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5688414 : List Nat := [4, 4, 1, 1, 1, 1, 4, 1, 1, 3, 2]
def baseStart_5688414 : Nat := 118140960795 + 5688414 * 2 ^ 59
def prefixEnd_5688414 : Nat := 4983230072969 + 3 ^ 40 * 5688414 * 2
def baseEnd_5688414 : Nat := 2920890543764812287764467

theorem tailTrace_5688414 : CollatzResearch.WordTrace tailWord_5688414 prefixEnd_5688414 2920890543764812287764467 := by
  unfold tailWord_5688414
  simp only [CollatzResearch.WordTrace]
  refine ⟨25934187901731882076368037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138315668809236704407296197 25934187901731882076368037)
  ·
    refine ⟨4862660231574727889319007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25934187901731882076368037 4862660231574727889319007)
    ·
      refine ⟨7293990347362091833978511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4862660231574727889319007 7293990347362091833978511)
      ·
        refine ⟨10940985521043137750967767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7293990347362091833978511 10940985521043137750967767)
        ·
          refine ⟨16411478281564706626451651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10940985521043137750967767 16411478281564706626451651)
          ·
            refine ⟨24617217422347059939677477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16411478281564706626451651 24617217422347059939677477)
            ·
              refine ⟨4615728266690073738689527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24617217422347059939677477 4615728266690073738689527)
              ·
                refine ⟨6923592400035110608034291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4615728266690073738689527 6923592400035110608034291)
                ·
                  refine ⟨10385388600052665912051437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6923592400035110608034291 10385388600052665912051437)
                  ·
                    refine ⟨3894520725019749717019289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10385388600052665912051437 3894520725019749717019289)
                    ·
                      refine ⟨2920890543764812287764467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3894520725019749717019289 2920890543764812287764467)
                      ·
                        rfl

theorem cell23_5688414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 4, 1, 1, 3, 2].length) (baseStart_5688414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5688414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5688414 prefixEnd_5688414 := by exact prefixLift 5688414
  have htrace : WordTrace (prefixWord ++ tailWord_5688414) baseStart_5688414 baseEnd_5688414 := by
    simpa [prefixWord, tailWord_5688414, baseEnd_5688414] using wordTrace_append hprefix tailTrace_5688414
  have hstable : (prefixWord ++ tailWord_5688414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5688414).length < 2 ^ (prefixWord ++ tailWord_5688414).sum := by decide
  have hdescent : baseEnd_5688414 < baseStart_5688414 := by decide
  rcases family_descends (prefixWord ++ tailWord_5688414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5688416 : List Nat := [2, 1, 1, 3, 2, 2, 4, 3, 5]
def baseStart_5688416 : Nat := 118140960795 + 5688416 * 2 ^ 59
def prefixEnd_5688416 : Nat := 4983230072969 + 3 ^ 40 * 5688416 * 2
def baseEnd_5688416 : Nat := 324543507858457919993273

theorem tailTrace_5688416 : CollatzResearch.WordTrace tailWord_5688416 prefixEnd_5688416 324543507858457919993273 := by
  unfold tailWord_5688416
  simp only [CollatzResearch.WordTrace]
  refine ⟨103736788079923905476258551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138315717439898540635011401 103736788079923905476258551)
  ·
    refine ⟨155605182119885858214387827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103736788079923905476258551 155605182119885858214387827)
    ·
      refine ⟨233407773179828787321581741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155605182119885858214387827 233407773179828787321581741)
      ·
        refine ⟨87527914942435795245593153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 233407773179828787321581741 87527914942435795245593153)
        ·
          refine ⟨65645936206826846434194865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87527914942435795245593153 65645936206826846434194865)
          ·
            refine ⟨49234452155120134825646149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65645936206826846434194865 49234452155120134825646149)
            ·
              refine ⟨9231459779085025279808653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49234452155120134825646149 9231459779085025279808653)
              ·
                refine ⟨3461797417156884479928245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9231459779085025279808653 3461797417156884479928245)
                ·
                  refine ⟨324543507858457919993273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3461797417156884479928245 324543507858457919993273)
                  ·
                    rfl

theorem cell23_5688416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 4, 3, 5].length) (baseStart_5688416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5688416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5688416 prefixEnd_5688416 := by exact prefixLift 5688416
  have htrace : WordTrace (prefixWord ++ tailWord_5688416) baseStart_5688416 baseEnd_5688416 := by
    simpa [prefixWord, tailWord_5688416, baseEnd_5688416] using wordTrace_append hprefix tailTrace_5688416
  have hstable : (prefixWord ++ tailWord_5688416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5688416).length < 2 ^ (prefixWord ++ tailWord_5688416).sum := by decide
  have hdescent : baseEnd_5688416 < baseStart_5688416 := by decide
  rcases family_descends (prefixWord ++ tailWord_5688416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5688426 : List Nat := [3, 1, 3, 2, 2, 1, 1, 2, 2, 3, 3]
def baseStart_5688426 : Nat := 118140960795 + 5688426 * 2 ^ 59
def prefixEnd_5688426 : Nat := 4983230072969 + 3 ^ 40 * 5688426 * 2
def baseEnd_5688426 : Nat := 2920896705532666240814411

theorem tailTrace_5688426 : CollatzResearch.WordTrace tailWord_5688426 prefixEnd_5688426 2920896705532666240814411 := by
  unfold tailWord_5688426
  simp only [CollatzResearch.WordTrace]
  refine ⟨51868485222452895665095283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138315960593207721773587421 51868485222452895665095283)
  ·
    refine ⟨77802727833679343497642925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51868485222452895665095283 77802727833679343497642925)
    ·
      refine ⟨29176022937629753811616097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77802727833679343497642925 29176022937629753811616097)
      ·
        refine ⟨21882017203222315358712073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29176022937629753811616097 21882017203222315358712073)
        ·
          refine ⟨16411512902416736519034055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21882017203222315358712073 16411512902416736519034055)
          ·
            refine ⟨24617269353625104778551083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16411512902416736519034055 24617269353625104778551083)
            ·
              refine ⟨36925904030437657167826625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24617269353625104778551083 36925904030437657167826625)
              ·
                refine ⟨27694428022828242875869969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36925904030437657167826625 27694428022828242875869969)
                ·
                  refine ⟨20770821017121182156902477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27694428022828242875869969 20770821017121182156902477)
                  ·
                    refine ⟨7789057881420443308838429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20770821017121182156902477 7789057881420443308838429)
                    ·
                      refine ⟨2920896705532666240814411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7789057881420443308838429 2920896705532666240814411)
                      ·
                        rfl

theorem cell23_5688426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 2, 2, 3, 3].length) (baseStart_5688426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5688426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5688426 prefixEnd_5688426 := by exact prefixLift 5688426
  have htrace : WordTrace (prefixWord ++ tailWord_5688426) baseStart_5688426 baseEnd_5688426 := by
    simpa [prefixWord, tailWord_5688426, baseEnd_5688426] using wordTrace_append hprefix tailTrace_5688426
  have hstable : (prefixWord ++ tailWord_5688426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5688426).length < 2 ^ (prefixWord ++ tailWord_5688426).sum := by decide
  have hdescent : baseEnd_5688426 < baseStart_5688426 := by decide
  rcases family_descends (prefixWord ++ tailWord_5688426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5688466 : List Nat := [3, 2, 3, 1, 1, 2, 2, 1, 1, 3, 4]
def baseStart_5688466 : Nat := 118140960795 + 5688466 * 2 ^ 59
def prefixEnd_5688466 : Nat := 4983230072969 + 3 ^ 40 * 5688466 * 2
def baseEnd_5688466 : Nat := 2920917244758846084314227

theorem tailTrace_5688466 : CollatzResearch.WordTrace tailWord_5688466 prefixEnd_5688466 2920917244758846084314227 := by
  unfold tailWord_5688466
  simp only [CollatzResearch.WordTrace]
  refine ⟨51868849952416667372959313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138316933206444446327891501 51868849952416667372959313)
  ·
    refine ⟨38901637464312500529719485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51868849952416667372959313 38901637464312500529719485)
    ·
      refine ⟨14588114049117187698644807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38901637464312500529719485 14588114049117187698644807)
      ·
        refine ⟨21882171073675781547967211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14588114049117187698644807 21882171073675781547967211)
        ·
          refine ⟨32823256610513672321950817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21882171073675781547967211 32823256610513672321950817)
          ·
            refine ⟨24617442457885254241463113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32823256610513672321950817 24617442457885254241463113)
            ·
              refine ⟨18463081843413940681097335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24617442457885254241463113 18463081843413940681097335)
              ·
                refine ⟨27694622765120911021646003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18463081843413940681097335 27694622765120911021646003)
                ·
                  refine ⟨41541934147681366532469005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27694622765120911021646003 41541934147681366532469005)
                  ·
                    refine ⟨15578225305380512449675877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41541934147681366532469005 15578225305380512449675877)
                    ·
                      refine ⟨2920917244758846084314227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15578225305380512449675877 2920917244758846084314227)
                      ·
                        rfl

theorem cell23_5688466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_5688466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5688466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5688466 prefixEnd_5688466 := by exact prefixLift 5688466
  have htrace : WordTrace (prefixWord ++ tailWord_5688466) baseStart_5688466 baseEnd_5688466 := by
    simpa [prefixWord, tailWord_5688466, baseEnd_5688466] using wordTrace_append hprefix tailTrace_5688466
  have hstable : (prefixWord ++ tailWord_5688466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5688466).length < 2 ^ (prefixWord ++ tailWord_5688466).sum := by decide
  have hdescent : baseEnd_5688466 < baseStart_5688466 := by decide
  rcases family_descends (prefixWord ++ tailWord_5688466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5688509 : List Nat := [1, 4, 1, 2, 1, 1, 2, 2, 1, 2, 6]
def baseStart_5688509 : Nat := 118140960795 + 5688509 * 2 ^ 59
def prefixEnd_5688509 : Nat := 4983230072969 + 3 ^ 40 * 5688509 * 2
def baseEnd_5688509 : Nat := 2920939324426989416076529

theorem tailTrace_5688509 : CollatzResearch.WordTrace tailWord_5688509 prefixEnd_5688509 2920939324426989416076529 := by
  unfold tailWord_5688509
  simp only [CollatzResearch.WordTrace]
  refine ⟨207476968148510887835652581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138317978765673925223768387 207476968148510887835652581)
  ·
    refine ⟨38901931527845791469184859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 207476968148510887835652581 38901931527845791469184859)
    ·
      refine ⟨58352897291768687203777289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38901931527845791469184859 58352897291768687203777289)
      ·
        refine ⟨43764672968826515402832967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58352897291768687203777289 43764672968826515402832967)
        ·
          refine ⟨65647009453239773104249451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43764672968826515402832967 65647009453239773104249451)
          ·
            refine ⟨98470514179859659656374177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65647009453239773104249451 98470514179859659656374177)
            ·
              refine ⟨73852885634894744742280633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98470514179859659656374177 73852885634894744742280633)
              ·
                refine ⟨55389664226171058556710475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73852885634894744742280633 55389664226171058556710475)
                ·
                  refine ⟨83084496339256587835065713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55389664226171058556710475 83084496339256587835065713)
                  ·
                    refine ⟨62313372254442440876299285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 83084496339256587835065713 62313372254442440876299285)
                    ·
                      refine ⟨2920939324426989416076529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62313372254442440876299285 2920939324426989416076529)
                      ·
                        rfl

theorem cell23_5688509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 2, 1, 2, 6].length) (baseStart_5688509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5688509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5688509 prefixEnd_5688509 := by exact prefixLift 5688509
  have htrace : WordTrace (prefixWord ++ tailWord_5688509) baseStart_5688509 baseEnd_5688509 := by
    simpa [prefixWord, tailWord_5688509, baseEnd_5688509] using wordTrace_append hprefix tailTrace_5688509
  have hstable : (prefixWord ++ tailWord_5688509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5688509).length < 2 ^ (prefixWord ++ tailWord_5688509).sum := by decide
  have hdescent : baseEnd_5688509 < baseStart_5688509 := by decide
  rcases family_descends (prefixWord ++ tailWord_5688509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5688543 : List Nat := [1, 1, 2, 3, 2, 1, 4, 2, 2, 3, 2]
def baseStart_5688543 : Nat := 118140960795 + 5688543 * 2 ^ 59
def prefixEnd_5688543 : Nat := 4983230072969 + 3 ^ 40 * 5688543 * 2
def baseEnd_5688543 : Nat := 2920956782769242283051373

theorem tailTrace_5688543 : CollatzResearch.WordTrace tailWord_5688543 prefixEnd_5688543 2920956782769242283051373 := by
  unfold tailWord_5688543
  simp only [CollatzResearch.WordTrace]
  refine ⟨207478208230387711642390283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138318805486925141094926855 207478208230387711642390283)
  ·
    refine ⟨311217312345581567463585425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207478208230387711642390283 311217312345581567463585425)
    ·
      refine ⟨233412984259186175597689069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 311217312345581567463585425 233412984259186175597689069)
      ·
        refine ⟨87529869097194815849133401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 233412984259186175597689069 87529869097194815849133401)
        ·
          refine ⟨65647401822896111886850051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87529869097194815849133401 65647401822896111886850051)
          ·
            refine ⟨98471102734344167830275077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65647401822896111886850051 98471102734344167830275077)
            ·
              refine ⟨18463331762689531468176577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 98471102734344167830275077 18463331762689531468176577)
              ·
                refine ⟨13847498822017148601132433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18463331762689531468176577 13847498822017148601132433)
                ·
                  refine ⟨10385624116512861450849325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13847498822017148601132433 10385624116512861450849325)
                  ·
                    refine ⟨3894609043692323044068497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10385624116512861450849325 3894609043692323044068497)
                    ·
                      refine ⟨2920956782769242283051373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3894609043692323044068497 2920956782769242283051373)
                      ·
                        rfl

theorem cell23_5688543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 2, 2, 3, 2].length) (baseStart_5688543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5688543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5688543 prefixEnd_5688543 := by exact prefixLift 5688543
  have htrace : WordTrace (prefixWord ++ tailWord_5688543) baseStart_5688543 baseEnd_5688543 := by
    simpa [prefixWord, tailWord_5688543, baseEnd_5688543] using wordTrace_append hprefix tailTrace_5688543
  have hstable : (prefixWord ++ tailWord_5688543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5688543).length < 2 ^ (prefixWord ++ tailWord_5688543).sum := by decide
  have hdescent : baseEnd_5688543 < baseStart_5688543 := by decide
  rcases family_descends (prefixWord ++ tailWord_5688543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5688556 : List Nat := [2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 4]
def baseStart_5688556 : Nat := 118140960795 + 5688556 * 2 ^ 59
def prefixEnd_5688556 : Nat := 4983230072969 + 3 ^ 40 * 5688556 * 2
def baseEnd_5688556 : Nat := 2920963458017750732188813

theorem tailTrace_5688556 : CollatzResearch.WordTrace tailWord_5688556 prefixEnd_5688556 2920963458017750732188813 := by
  unfold tailWord_5688556
  simp only [CollatzResearch.WordTrace]
  refine ⟨103739341189670307431306761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138319121586227076575075681 103739341189670307431306761)
  ·
    refine ⟨77804505892252730573480071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103739341189670307431306761 77804505892252730573480071)
    ·
      refine ⟨116706758838379095860220107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77804505892252730573480071 116706758838379095860220107)
      ·
        refine ⟨175060138257568643790330161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116706758838379095860220107 175060138257568643790330161)
        ·
          refine ⟨131295103693176482842747621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175060138257568643790330161 131295103693176482842747621)
          ·
            refine ⟨24617831942470590533015179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 131295103693176482842747621 24617831942470590533015179)
            ·
              refine ⟨36926747913705885799522769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24617831942470590533015179 36926747913705885799522769)
              ·
                refine ⟨27695060935279414349642077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36926747913705885799522769 27695060935279414349642077)
                ·
                  refine ⟨10385647850729780381115779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27695060935279414349642077 10385647850729780381115779)
                  ·
                    refine ⟨15578471776094670571673669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10385647850729780381115779 15578471776094670571673669)
                    ·
                      refine ⟨2920963458017750732188813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15578471776094670571673669 2920963458017750732188813)
                      ·
                        rfl

theorem cell23_5688556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 4].length) (baseStart_5688556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5688556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5688556 prefixEnd_5688556 := by exact prefixLift 5688556
  have htrace : WordTrace (prefixWord ++ tailWord_5688556) baseStart_5688556 baseEnd_5688556 := by
    simpa [prefixWord, tailWord_5688556, baseEnd_5688556] using wordTrace_append hprefix tailTrace_5688556
  have hstable : (prefixWord ++ tailWord_5688556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5688556).length < 2 ^ (prefixWord ++ tailWord_5688556).sum := by decide
  have hdescent : baseEnd_5688556 < baseStart_5688556 := by decide
  rcases family_descends (prefixWord ++ tailWord_5688556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5688590 : List Nat := [4, 1, 1, 2, 1, 3, 4, 1, 1, 1, 4]
def baseStart_5688590 : Nat := 118140960795 + 5688590 * 2 ^ 59
def prefixEnd_5688590 : Nat := 4983230072969 + 3 ^ 40 * 5688590 * 2
def baseEnd_5688590 : Nat := 2920980916360003599163657

theorem tailTrace_5688590 : CollatzResearch.WordTrace tailWord_5688590 prefixEnd_5688590 2920980916360003599163657 := by
  unfold tailWord_5688590
  simp only [CollatzResearch.WordTrace]
  refine ⟨25934990307652179833668903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138319948307478292446234149 25934990307652179833668903)
  ·
    refine ⟨38902485461478269750503355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25934990307652179833668903 38902485461478269750503355)
    ·
      refine ⟨58353728192217404625755033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38902485461478269750503355 58353728192217404625755033)
      ·
        refine ⟨43765296144163053469316275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58353728192217404625755033 43765296144163053469316275)
        ·
          refine ⟨65647944216244580203974413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43765296144163053469316275 65647944216244580203974413)
          ·
            refine ⟨24617979081091717576490405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65647944216244580203974413 24617979081091717576490405)
            ·
              refine ⟨4615871077704697045591951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24617979081091717576490405 4615871077704697045591951)
              ·
                refine ⟨6923806616557045568387927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4615871077704697045591951 6923806616557045568387927)
                ·
                  refine ⟨10385709924835568352581891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6923806616557045568387927 10385709924835568352581891)
                  ·
                    refine ⟨15578564887253352528872837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10385709924835568352581891 15578564887253352528872837)
                    ·
                      refine ⟨2920980916360003599163657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15578564887253352528872837 2920980916360003599163657)
                      ·
                        rfl

theorem cell23_5688590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 4, 1, 1, 1, 4].length) (baseStart_5688590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5688590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5688590 prefixEnd_5688590 := by exact prefixLift 5688590
  have htrace : WordTrace (prefixWord ++ tailWord_5688590) baseStart_5688590 baseEnd_5688590 := by
    simpa [prefixWord, tailWord_5688590, baseEnd_5688590] using wordTrace_append hprefix tailTrace_5688590
  have hstable : (prefixWord ++ tailWord_5688590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5688590).length < 2 ^ (prefixWord ++ tailWord_5688590).sum := by decide
  have hdescent : baseEnd_5688590 < baseStart_5688590 := by decide
  rcases family_descends (prefixWord ++ tailWord_5688590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5688593 : List Nat := [1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 3]
def baseStart_5688593 : Nat := 118140960795 + 5688593 * 2 ^ 59
def prefixEnd_5688593 : Nat := 4983230072969 + 3 ^ 40 * 5688593 * 2
def baseEnd_5688593 : Nat := 2920982456801967087426143

theorem tailTrace_5688593 : CollatzResearch.WordTrace tailWord_5688593 prefixEnd_5688593 2920982456801967087426143 := by
  unfold tailWord_5688593
  simp only [CollatzResearch.WordTrace]
  refine ⟨207480031880206570181710433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138320021253471046787806955 207480031880206570181710433)
  ·
    refine ⟨155610023910154927636282825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207480031880206570181710433 155610023910154927636282825)
    ·
      refine ⟨116707517932616195727212119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155610023910154927636282825 116707517932616195727212119)
      ·
        refine ⟨175061276898924293590818179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116707517932616195727212119 175061276898924293590818179)
        ·
          refine ⟨262591915348386440386227269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175061276898924293590818179 262591915348386440386227269)
          ·
            refine ⟨49235984127822457572417613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 262591915348386440386227269 49235984127822457572417613)
            ·
              refine ⟨18463494047933421589656605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49235984127822457572417613 18463494047933421589656605)
              ·
                refine ⟨6923810267975033096121227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18463494047933421589656605 6923810267975033096121227)
                ·
                  refine ⟨10385715401962549644181841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6923810267975033096121227 10385715401962549644181841)
                  ·
                    refine ⟨7789286551471912233136381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10385715401962549644181841 7789286551471912233136381)
                    ·
                      refine ⟨2920982456801967087426143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7789286551471912233136381 2920982456801967087426143)
                      ·
                        rfl

theorem cell23_5688593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 3].length) (baseStart_5688593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5688593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5688593 prefixEnd_5688593 := by exact prefixLift 5688593
  have htrace : WordTrace (prefixWord ++ tailWord_5688593) baseStart_5688593 baseEnd_5688593 := by
    simpa [prefixWord, tailWord_5688593, baseEnd_5688593] using wordTrace_append hprefix tailTrace_5688593
  have hstable : (prefixWord ++ tailWord_5688593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5688593).length < 2 ^ (prefixWord ++ tailWord_5688593).sum := by decide
  have hdescent : baseEnd_5688593 < baseStart_5688593 := by decide
  rcases family_descends (prefixWord ++ tailWord_5688593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5688600 : List Nat := [2, 1, 2, 3, 1, 5, 1, 2, 2, 4]
def baseStart_5688600 : Nat := 118140960795 + 5688600 * 2 ^ 59
def prefixEnd_5688600 : Nat := 4983230072969 + 3 ^ 40 * 5688600 * 2
def baseEnd_5688600 : Nat := 973662017055516186679537

theorem tailTrace_5688600 : CollatzResearch.WordTrace tailWord_5688600 prefixEnd_5688600 973662017055516186679537 := by
  unfold tailWord_5688600
  simp only [CollatzResearch.WordTrace]
  refine ⟨103740143595590605188607627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138320191460787473584810169 103740143595590605188607627)
  ·
    refine ⟨155610215393385907782911441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103740143595590605188607627 155610215393385907782911441)
    ·
      refine ⟨116707661545039430837183581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155610215393385907782911441 116707661545039430837183581)
      ·
        refine ⟨43765373079389786563943843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116707661545039430837183581 43765373079389786563943843)
        ·
          refine ⟨65648059619084679845915765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43765373079389786563943843 65648059619084679845915765)
          ·
            refine ⟨6154505589289188735554603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 65648059619084679845915765 6154505589289188735554603)
            ·
              refine ⟨9231758383933783103331905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6154505589289188735554603 9231758383933783103331905)
              ·
                refine ⟨6923818787950337327498929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9231758383933783103331905 6923818787950337327498929)
                ·
                  refine ⟨5192864090962752995624197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6923818787950337327498929 5192864090962752995624197)
                  ·
                    refine ⟨973662017055516186679537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5192864090962752995624197 973662017055516186679537)
                    ·
                      rfl

theorem cell23_5688600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 1, 2, 2, 4].length) (baseStart_5688600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5688600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5688600 prefixEnd_5688600 := by exact prefixLift 5688600
  have htrace : WordTrace (prefixWord ++ tailWord_5688600) baseStart_5688600 baseEnd_5688600 := by
    simpa [prefixWord, tailWord_5688600, baseEnd_5688600] using wordTrace_append hprefix tailTrace_5688600
  have hstable : (prefixWord ++ tailWord_5688600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5688600).length < 2 ^ (prefixWord ++ tailWord_5688600).sum := by decide
  have hdescent : baseEnd_5688600 < baseStart_5688600 := by decide
  rcases family_descends (prefixWord ++ tailWord_5688600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5688607 : List Nat := [1, 1, 2, 4, 4, 1, 2, 1, 3, 2, 2]
def baseStart_5688607 : Nat := 118140960795 + 5688607 * 2 ^ 59
def prefixEnd_5688607 : Nat := 4983230072969 + 3 ^ 40 * 5688607 * 2
def baseEnd_5688607 : Nat := 2920989645531130032651079

theorem tailTrace_5688607 : CollatzResearch.WordTrace tailWord_5688607 prefixEnd_5688607 2920989645531130032651079 := by
  unfold tailWord_5688607
  simp only [CollatzResearch.WordTrace]
  refine ⟨207480542502155850572720075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138320361668103900381813383 207480542502155850572720075)
  ·
    refine ⟨311220813753233775859080113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207480542502155850572720075 311220813753233775859080113)
    ·
      refine ⟨233415610314925331894310085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 311220813753233775859080113 233415610314925331894310085)
      ·
        refine ⟨43765426934048499730183141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 233415610314925331894310085 43765426934048499730183141)
        ·
          refine ⟨8206017550134093699409339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43765426934048499730183141 8206017550134093699409339)
          ·
            refine ⟨12309026325201140549114009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8206017550134093699409339 12309026325201140549114009)
            ·
              refine ⟨9231769743900855411835507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12309026325201140549114009 9231769743900855411835507)
              ·
                refine ⟨13847654615851283117753261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9231769743900855411835507 13847654615851283117753261)
                ·
                  refine ⟨5192870480944231169157473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13847654615851283117753261 5192870480944231169157473)
                  ·
                    refine ⟨3894652860708173376868105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5192870480944231169157473 3894652860708173376868105)
                    ·
                      refine ⟨2920989645531130032651079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3894652860708173376868105 2920989645531130032651079)
                      ·
                        rfl

theorem cell23_5688607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 2, 1, 3, 2, 2].length) (baseStart_5688607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5688607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5688607 prefixEnd_5688607 := by exact prefixLift 5688607
  have htrace : WordTrace (prefixWord ++ tailWord_5688607) baseStart_5688607 baseEnd_5688607 := by
    simpa [prefixWord, tailWord_5688607, baseEnd_5688607] using wordTrace_append hprefix tailTrace_5688607
  have hstable : (prefixWord ++ tailWord_5688607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5688607).length < 2 ^ (prefixWord ++ tailWord_5688607).sum := by decide
  have hdescent : baseEnd_5688607 < baseStart_5688607 := by decide
  rcases family_descends (prefixWord ++ tailWord_5688607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5688630 : List Nat := [5, 1, 2, 3, 1, 1, 1, 9]
def baseStart_5688630 : Nat := 118140960795 + 5688630 * 2 ^ 59
def prefixEnd_5688630 : Nat := 4983230072969 + 3 ^ 40 * 5688630 * 2
def baseEnd_5688630 : Nat := 108185239095784571950499

theorem tailTrace_5688630 : CollatzResearch.WordTrace tailWord_5688630 prefixEnd_5688630 108185239095784571950499 := by
  unfold tailWord_5688630
  simp only [CollatzResearch.WordTrace]
  refine ⟨12967586336317032843800459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 138320920920715017000538229 12967586336317032843800459)
  ·
    refine ⟨19451379504475549265700689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12967586336317032843800459 19451379504475549265700689)
    ·
      refine ⟨14588534628356661949275517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19451379504475549265700689 14588534628356661949275517)
      ·
        refine ⟨5470700485633748230978319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14588534628356661949275517 5470700485633748230978319)
        ·
          refine ⟨8206050728450622346467479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5470700485633748230978319 8206050728450622346467479)
          ·
            refine ⟨12309076092675933519701219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8206050728450622346467479 12309076092675933519701219)
            ·
              refine ⟨18463614139013900279551829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12309076092675933519701219 18463614139013900279551829)
              ·
                refine ⟨108185239095784571950499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18463614139013900279551829 108185239095784571950499)
                ·
                  rfl

theorem cell23_5688630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 9].length) (baseStart_5688630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5688630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5688630 prefixEnd_5688630 := by exact prefixLift 5688630
  have htrace : WordTrace (prefixWord ++ tailWord_5688630) baseStart_5688630 baseEnd_5688630 := by
    simpa [prefixWord, tailWord_5688630, baseEnd_5688630] using wordTrace_append hprefix tailTrace_5688630
  have hstable : (prefixWord ++ tailWord_5688630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5688630).length < 2 ^ (prefixWord ++ tailWord_5688630).sum := by decide
  have hdescent : baseEnd_5688630 < baseStart_5688630 := by decide
  rcases family_descends (prefixWord ++ tailWord_5688630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5688636 : List Nat := [2, 2, 2, 2, 1, 3, 1, 1, 2, 2, 5]
def baseStart_5688636 : Nat := 118140960795 + 5688636 * 2 ^ 59
def prefixEnd_5688636 : Nat := 4983230072969 + 3 ^ 40 * 5688636 * 2
def baseEnd_5688636 : Nat := 2921004536470110419188445

theorem tailTrace_5688636 : CollatzResearch.WordTrace tailWord_5688636 prefixEnd_5688636 2921004536470110419188445 := by
  unfold tailWord_5688636
  simp only [CollatzResearch.WordTrace]
  refine ⟨103740800109525394262762881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138321066812700525683683841 103740800109525394262762881)
  ·
    refine ⟨77805600082144045697072161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103740800109525394262762881 77805600082144045697072161)
    ·
      refine ⟨58354200061608034272804121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77805600082144045697072161 58354200061608034272804121)
      ·
        refine ⟨43765650046206025704603091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58354200061608034272804121 43765650046206025704603091)
        ·
          refine ⟨65648475069309038556904637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43765650046206025704603091 65648475069309038556904637)
          ·
            refine ⟨24618178150990889458839239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65648475069309038556904637 24618178150990889458839239)
            ·
              refine ⟨36927267226486334188258859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24618178150990889458839239 36927267226486334188258859)
              ·
                refine ⟨55390900839729501282388289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36927267226486334188258859 55390900839729501282388289)
                ·
                  refine ⟨41543175629797125961791217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55390900839729501282388289 41543175629797125961791217)
                  ·
                    refine ⟨31157381722347844471343413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41543175629797125961791217 31157381722347844471343413)
                    ·
                      refine ⟨2921004536470110419188445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31157381722347844471343413 2921004536470110419188445)
                      ·
                        rfl

theorem cell23_5688636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 1, 2, 2, 5].length) (baseStart_5688636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5688636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5688636 prefixEnd_5688636 := by exact prefixLift 5688636
  have htrace : WordTrace (prefixWord ++ tailWord_5688636) baseStart_5688636 baseEnd_5688636 := by
    simpa [prefixWord, tailWord_5688636, baseEnd_5688636] using wordTrace_append hprefix tailTrace_5688636
  have hstable : (prefixWord ++ tailWord_5688636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5688636).length < 2 ^ (prefixWord ++ tailWord_5688636).sum := by decide
  have hdescent : baseEnd_5688636 < baseStart_5688636 := by decide
  rcases family_descends (prefixWord ++ tailWord_5688636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5688641 : List Nat := [1, 2, 5, 2, 1, 3, 1, 3, 1, 2, 2]
def baseStart_5688641 : Nat := 118140960795 + 5688641 * 2 ^ 59
def prefixEnd_5688641 : Nat := 4983230072969 + 3 ^ 40 * 5688641 * 2
def baseEnd_5688641 : Nat := 2921007103873382899625923

theorem tailTrace_5688641 : CollatzResearch.WordTrace tailWord_5688641 prefixEnd_5688641 2921007103873382899625923 := by
  unfold tailWord_5688641
  simp only [CollatzResearch.WordTrace]
  refine ⟨207481782584032674379457777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138321188389355116252971851 207481782584032674379457777)
  ·
    refine ⟨155611336938024505784593333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207481782584032674379457777 155611336938024505784593333)
    ·
      refine ⟨14588562837939797417305625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 155611336938024505784593333 14588562837939797417305625)
      ·
        refine ⟨10941422128454848062979219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14588562837939797417305625 10941422128454848062979219)
        ·
          refine ⟨16412133192682272094468829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10941422128454848062979219 16412133192682272094468829)
          ·
            refine ⟨6154549947255852035425811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16412133192682272094468829 6154549947255852035425811)
            ·
              refine ⟨9231824920883778053138717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6154549947255852035425811 9231824920883778053138717)
              ·
                refine ⟨3461934345331416769927019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9231824920883778053138717 3461934345331416769927019)
                ·
                  refine ⟨5192901517997125154890529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3461934345331416769927019 5192901517997125154890529)
                  ·
                    refine ⟨3894676138497843866167897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5192901517997125154890529 3894676138497843866167897)
                    ·
                      refine ⟨2921007103873382899625923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3894676138497843866167897 2921007103873382899625923)
                      ·
                        rfl

theorem cell23_5688641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 1, 3, 1, 2, 2].length) (baseStart_5688641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5688641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5688641 prefixEnd_5688641 := by exact prefixLift 5688641
  have htrace : WordTrace (prefixWord ++ tailWord_5688641) baseStart_5688641 baseEnd_5688641 := by
    simpa [prefixWord, tailWord_5688641, baseEnd_5688641] using wordTrace_append hprefix tailTrace_5688641
  have hstable : (prefixWord ++ tailWord_5688641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5688641).length < 2 ^ (prefixWord ++ tailWord_5688641).sum := by decide
  have hdescent : baseEnd_5688641 < baseStart_5688641 := by decide
  rcases family_descends (prefixWord ++ tailWord_5688641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5688753 : List Nat := [1, 2, 2, 4, 1, 1, 3, 1, 1, 3, 4]
def baseStart_5688753 : Nat := 118140960795 + 5688753 * 2 ^ 59
def prefixEnd_5688753 : Nat := 4983230072969 + 3 ^ 40 * 5688753 * 2
def baseEnd_5688753 : Nat := 2921064613706686461425407

theorem tailTrace_5688753 : CollatzResearch.WordTrace tailWord_5688753 prefixEnd_5688753 2921064613706686461425407 := by
  unfold tailWord_5688753
  simp only [CollatzResearch.WordTrace]
  refine ⟨207485867559626917507534913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138323911706417945005023275 207485867559626917507534913)
  ·
    refine ⟨155614400669720188130651185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207485867559626917507534913 155614400669720188130651185)
    ·
      refine ⟨116710800502290141097988389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155614400669720188130651185 116710800502290141097988389)
      ·
        refine ⟨21883275094179401455872823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 116710800502290141097988389 21883275094179401455872823)
        ·
          refine ⟨32824912641269102183809235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21883275094179401455872823 32824912641269102183809235)
          ·
            refine ⟨49237368961903653275713853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32824912641269102183809235 49237368961903653275713853)
            ·
              refine ⟨18464013360713869978392695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49237368961903653275713853 18464013360713869978392695)
              ·
                refine ⟨27696020041070804967589043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18464013360713869978392695 27696020041070804967589043)
                ·
                  refine ⟨41544030061606207451383565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27696020041070804967589043 41544030061606207451383565)
                  ·
                    refine ⟨15579011273102327794268837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41544030061606207451383565 15579011273102327794268837)
                    ·
                      refine ⟨2921064613706686461425407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15579011273102327794268837 2921064613706686461425407)
                      ·
                        rfl

theorem cell23_5688753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_5688753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5688753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5688753 prefixEnd_5688753 := by exact prefixLift 5688753
  have htrace : WordTrace (prefixWord ++ tailWord_5688753) baseStart_5688753 baseEnd_5688753 := by
    simpa [prefixWord, tailWord_5688753, baseEnd_5688753] using wordTrace_append hprefix tailTrace_5688753
  have hstable : (prefixWord ++ tailWord_5688753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5688753).length < 2 ^ (prefixWord ++ tailWord_5688753).sum := by decide
  have hdescent : baseEnd_5688753 < baseStart_5688753 := by decide
  rcases family_descends (prefixWord ++ tailWord_5688753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5688780 : List Nat := [2, 2, 1, 4, 2, 1, 1, 3, 3, 4]
def baseStart_5688780 : Nat := 118140960795 + 5688780 * 2 ^ 59
def prefixEnd_5688780 : Nat := 4983230072969 + 3 ^ 40 * 5688780 * 2
def baseEnd_5688780 : Nat := 973692825894785951929261

theorem tailTrace_5688780 : CollatzResearch.WordTrace tailWord_5688780 prefixEnd_5688780 973692825894785951929261 := by
  unfold tailWord_5688780
  simp only [CollatzResearch.WordTrace]
  refine ⟨103743426165264550559383897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138324568220352734079178529 103743426165264550559383897)
  ·
    refine ⟨77807569623948412919537923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103743426165264550559383897 77807569623948412919537923)
    ·
      refine ⟨116711354435922619379306885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77807569623948412919537923 116711354435922619379306885)
      ·
        refine ⟨21883378956735491133620041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 116711354435922619379306885 21883378956735491133620041)
        ·
          refine ⟨16412534217551618350215031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21883378956735491133620041 16412534217551618350215031)
          ·
            refine ⟨24618801326327427525322547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16412534217551618350215031 24618801326327427525322547)
            ·
              refine ⟨36928201989491141287983821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24618801326327427525322547 36928201989491141287983821)
              ·
                refine ⟨13848075746059177982993933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36928201989491141287983821 13848075746059177982993933)
                ·
                  refine ⟨5193028404772191743622725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13848075746059177982993933 5193028404772191743622725)
                  ·
                    refine ⟨973692825894785951929261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5193028404772191743622725 973692825894785951929261)
                    ·
                      rfl

theorem cell23_5688780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 3, 3, 4].length) (baseStart_5688780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5688780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5688780 prefixEnd_5688780 := by exact prefixLift 5688780
  have htrace : WordTrace (prefixWord ++ tailWord_5688780) baseStart_5688780 baseEnd_5688780 := by
    simpa [prefixWord, tailWord_5688780, baseEnd_5688780] using wordTrace_append hprefix tailTrace_5688780
  have hstable : (prefixWord ++ tailWord_5688780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5688780).length < 2 ^ (prefixWord ++ tailWord_5688780).sum := by decide
  have hdescent : baseEnd_5688780 < baseStart_5688780 := by decide
  rcases family_descends (prefixWord ++ tailWord_5688780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5688844 : List Nat := [2, 2, 1, 2, 6, 1, 2, 1, 6]
def baseStart_5688844 : Nat := 118140960795 + 5688844 * 2 ^ 59
def prefixEnd_5688844 : Nat := 4983230072969 + 3 ^ 40 * 5688844 * 2
def baseEnd_5688844 : Nat := 324567926716249511709721

theorem tailTrace_5688844 : CollatzResearch.WordTrace tailWord_5688844 prefixEnd_5688844 324567926716249511709721 := by
  unfold tailWord_5688844
  simp only [CollatzResearch.WordTrace]
  refine ⟨103744593301148620024548793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138326124401531493366065057 103744593301148620024548793)
  ·
    refine ⟨77808444975861465018411595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103744593301148620024548793 77808444975861465018411595)
    ·
      refine ⟨116712667463792197527617393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77808444975861465018411595 116712667463792197527617393)
      ·
        refine ⟨87534500597844148145713045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116712667463792197527617393 87534500597844148145713045)
        ·
          refine ⟨4103179715523944444330299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 87534500597844148145713045 4103179715523944444330299)
          ·
            refine ⟨6154769573285916666495449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4103179715523944444330299 6154769573285916666495449)
            ·
              refine ⟨4616077179964437499871587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6154769573285916666495449 4616077179964437499871587)
              ·
                refine ⟨6924115769946656249807381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4616077179964437499871587 6924115769946656249807381)
                ·
                  refine ⟨324567926716249511709721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6924115769946656249807381 324567926716249511709721)
                  ·
                    rfl

theorem cell23_5688844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 2, 1, 6].length) (baseStart_5688844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5688844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5688844 prefixEnd_5688844 := by exact prefixLift 5688844
  have htrace : WordTrace (prefixWord ++ tailWord_5688844) baseStart_5688844 baseEnd_5688844 := by
    simpa [prefixWord, tailWord_5688844, baseEnd_5688844] using wordTrace_append hprefix tailTrace_5688844
  have hstable : (prefixWord ++ tailWord_5688844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5688844).length < 2 ^ (prefixWord ++ tailWord_5688844).sum := by decide
  have hdescent : baseEnd_5688844 < baseStart_5688844 := by decide
  rcases family_descends (prefixWord ++ tailWord_5688844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5688860 : List Nat := [2, 2, 3, 1, 2, 1, 3, 1, 3, 1, 4]
def baseStart_5688860 : Nat := 118140960795 + 5688860 * 2 ^ 59
def prefixEnd_5688860 : Nat := 4983230072969 + 3 ^ 40 * 5688860 * 2
def baseEnd_5688860 : Nat := 2921119556136717542787415

theorem tailTrace_5688860 : CollatzResearch.WordTrace tailWord_5688860 prefixEnd_5688860 2921119556136717542787415 := by
  unfold tailWord_5688860
  simp only [CollatzResearch.WordTrace]
  refine ⟨103744885085119637390840017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138326513446826183187786689 103744885085119637390840017)
  ·
    refine ⟨77808663813839728043130013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103744885085119637390840017 77808663813839728043130013)
    ·
      refine ⟨29178248930189898016173755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 77808663813839728043130013 29178248930189898016173755)
      ·
        refine ⟨43767373395284847024260633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29178248930189898016173755 43767373395284847024260633)
        ·
          refine ⟨32825530046463635268195475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43767373395284847024260633 32825530046463635268195475)
          ·
            refine ⟨49238295069695452902293213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32825530046463635268195475 49238295069695452902293213)
            ·
              refine ⟨18464360651135794838359955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49238295069695452902293213 18464360651135794838359955)
              ·
                refine ⟨27696540976703692257539933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18464360651135794838359955 27696540976703692257539933)
                ·
                  refine ⟨10386202866263884596577475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27696540976703692257539933 10386202866263884596577475)
                  ·
                    refine ⟨15579304299395826894866213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10386202866263884596577475 15579304299395826894866213)
                    ·
                      refine ⟨2921119556136717542787415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15579304299395826894866213 2921119556136717542787415)
                      ·
                        rfl

theorem cell23_5688860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 1, 3, 1, 4].length) (baseStart_5688860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5688860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5688860 prefixEnd_5688860 := by exact prefixLift 5688860
  have htrace : WordTrace (prefixWord ++ tailWord_5688860) baseStart_5688860 baseEnd_5688860 := by
    simpa [prefixWord, tailWord_5688860, baseEnd_5688860] using wordTrace_append hprefix tailTrace_5688860
  have hstable : (prefixWord ++ tailWord_5688860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5688860).length < 2 ^ (prefixWord ++ tailWord_5688860).sum := by decide
  have hdescent : baseEnd_5688860 < baseStart_5688860 := by decide
  rcases family_descends (prefixWord ++ tailWord_5688860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5688863 : List Nat := [1, 1, 2, 4, 1, 1, 2, 2, 3, 1, 5]
def baseStart_5688863 : Nat := 118140960795 + 5688863 * 2 ^ 59
def prefixEnd_5688863 : Nat := 4983230072969 + 3 ^ 40 * 5688863 * 2
def baseEnd_5688863 : Nat := 2921121096578681031049901

theorem tailTrace_5688863 : CollatzResearch.WordTrace tailWord_5688863 prefixEnd_5688863 2921121096578681031049901 := by
  unfold tailWord_5688863
  simp only [CollatzResearch.WordTrace]
  refine ⟨207489879589228406294039243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138326586392818937529359495 207489879589228406294039243)
  ·
    refine ⟨311234819383842609441058865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207489879589228406294039243 311234819383842609441058865)
    ·
      refine ⟨233426114537881957080794149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 311234819383842609441058865 233426114537881957080794149)
      ·
        refine ⟨43767396475852866952648903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 233426114537881957080794149 43767396475852866952648903)
        ·
          refine ⟨65651094713779300428973355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43767396475852866952648903 65651094713779300428973355)
          ·
            refine ⟨98476642070668950643460033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65651094713779300428973355 98476642070668950643460033)
            ·
              refine ⟨73857481553001712982595025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98476642070668950643460033 73857481553001712982595025)
              ·
                refine ⟨55393111164751284736946269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73857481553001712982595025 55393111164751284736946269)
                ·
                  refine ⟨20772416686781731776354851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55393111164751284736946269 20772416686781731776354851)
                  ·
                    refine ⟨31158625030172597664532277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20772416686781731776354851 31158625030172597664532277)
                    ·
                      refine ⟨2921121096578681031049901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31158625030172597664532277 2921121096578681031049901)
                      ·
                        rfl

theorem cell23_5688863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 2, 3, 1, 5].length) (baseStart_5688863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5688863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5688863 prefixEnd_5688863 := by exact prefixLift 5688863
  have htrace : WordTrace (prefixWord ++ tailWord_5688863) baseStart_5688863 baseEnd_5688863 := by
    simpa [prefixWord, tailWord_5688863, baseEnd_5688863] using wordTrace_append hprefix tailTrace_5688863
  have hstable : (prefixWord ++ tailWord_5688863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5688863).length < 2 ^ (prefixWord ++ tailWord_5688863).sum := by decide
  have hdescent : baseEnd_5688863 < baseStart_5688863 := by decide
  rcases family_descends (prefixWord ++ tailWord_5688863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5688864 : List Nat := [2, 1, 1, 6, 1, 2, 2, 1, 2, 3, 2]
def baseStart_5688864 : Nat := 118140960795 + 5688864 * 2 ^ 59
def prefixEnd_5688864 : Nat := 4983230072969 + 3 ^ 40 * 5688864 * 2
def baseEnd_5688864 : Nat := 2921121610059335527137397

theorem tailTrace_5688864 : CollatzResearch.WordTrace tailWord_5688864 prefixEnd_5688864 2921121610059335527137397 := by
  unfold tailWord_5688864
  simp only [CollatzResearch.WordTrace]
  refine ⟨103744958031112391732412823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138326610708149855643217097 103744958031112391732412823)
  ·
    refine ⟨155617437046668587598619235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103744958031112391732412823 155617437046668587598619235)
    ·
      refine ⟨233426155570002881397928853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155617437046668587598619235 233426155570002881397928853)
      ·
        refine ⟨10941851042343885065527915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 233426155570002881397928853 10941851042343885065527915)
        ·
          refine ⟨16412776563515827598291873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10941851042343885065527915 16412776563515827598291873)
          ·
            refine ⟨12309582422636870698718905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16412776563515827598291873 12309582422636870698718905)
            ·
              refine ⟨9232186816977653024039179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12309582422636870698718905 9232186816977653024039179)
              ·
                refine ⟨13848280225466479536058769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9232186816977653024039179 13848280225466479536058769)
                ·
                  refine ⟨10386210169099859652044077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13848280225466479536058769 10386210169099859652044077)
                  ·
                    refine ⟨3894828813412447369516529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10386210169099859652044077 3894828813412447369516529)
                    ·
                      refine ⟨2921121610059335527137397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3894828813412447369516529 2921121610059335527137397)
                      ·
                        rfl

theorem cell23_5688864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 2, 1, 2, 3, 2].length) (baseStart_5688864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5688864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5688864 prefixEnd_5688864 := by exact prefixLift 5688864
  have htrace : WordTrace (prefixWord ++ tailWord_5688864) baseStart_5688864 baseEnd_5688864 := by
    simpa [prefixWord, tailWord_5688864, baseEnd_5688864] using wordTrace_append hprefix tailTrace_5688864
  have hstable : (prefixWord ++ tailWord_5688864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5688864).length < 2 ^ (prefixWord ++ tailWord_5688864).sum := by decide
  have hdescent : baseEnd_5688864 < baseStart_5688864 := by decide
  rcases family_descends (prefixWord ++ tailWord_5688864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5688887 : List Nat := [1, 1, 3, 1, 2, 5, 2, 2, 2, 4]
def baseStart_5688887 : Nat := 118140960795 + 5688887 * 2 ^ 59
def prefixEnd_5688887 : Nat := 4983230072969 + 3 ^ 40 * 5688887 * 2
def baseEnd_5688887 : Nat := 973711140038129645716597

theorem tailTrace_5688887 : CollatzResearch.WordTrace tailWord_5688887 prefixEnd_5688887 973711140038129645716597 := by
  unfold tailWord_5688887
  simp only [CollatzResearch.WordTrace]
  refine ⟨207490754941141458392912915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138327169960760972261941943 207490754941141458392912915)
  ·
    refine ⟨311236132411712187589369373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207490754941141458392912915 311236132411712187589369373)
    ·
      refine ⟨116713549654392070346013515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 311236132411712187589369373 116713549654392070346013515)
      ·
        refine ⟨175070324481588105519020273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116713549654392070346013515 175070324481588105519020273)
        ·
          refine ⟨131302743361191079139265205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175070324481588105519020273 131302743361191079139265205)
          ·
            refine ⟨12309632190111663669306113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 131302743361191079139265205 12309632190111663669306113)
            ·
              refine ⟨9232224142583747751979585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12309632190111663669306113 9232224142583747751979585)
              ·
                refine ⟨6924168106937810813984689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9232224142583747751979585 6924168106937810813984689)
                ·
                  refine ⟨5193126080203358110488517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6924168106937810813984689 5193126080203358110488517)
                  ·
                    refine ⟨973711140038129645716597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5193126080203358110488517 973711140038129645716597)
                    ·
                      rfl

theorem cell23_5688887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 2, 2, 2, 4].length) (baseStart_5688887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5688887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5688887 prefixEnd_5688887 := by exact prefixLift 5688887
  have htrace : WordTrace (prefixWord ++ tailWord_5688887) baseStart_5688887 baseEnd_5688887 := by
    simpa [prefixWord, tailWord_5688887, baseEnd_5688887] using wordTrace_append hprefix tailTrace_5688887
  have hstable : (prefixWord ++ tailWord_5688887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5688887).length < 2 ^ (prefixWord ++ tailWord_5688887).sum := by decide
  have hdescent : baseEnd_5688887 < baseStart_5688887 := by decide
  rcases family_descends (prefixWord ++ tailWord_5688887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5688913 : List Nat := [1, 2, 2, 1, 3, 2, 1, 2, 2, 7]
def baseStart_5688913 : Nat := 118140960795 + 5688913 * 2 ^ 59
def prefixEnd_5688913 : Nat := 4983230072969 + 3 ^ 40 * 5688913 * 2
def baseEnd_5688913 : Nat := 973715590203801945141557

theorem tailTrace_5688913 : CollatzResearch.WordTrace tailWord_5688913 prefixEnd_5688913 973715590203801945141557 := by
  unfold tailWord_5688913
  simp only [CollatzResearch.WordTrace]
  refine ⟨207491703239047264833359393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138327802159364843222239595 207491703239047264833359393)
  ·
    refine ⟨155618777429285448625019545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207491703239047264833359393 155618777429285448625019545)
    ·
      refine ⟨116714083071964086468764659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155618777429285448625019545 116714083071964086468764659)
      ·
        refine ⟨175071124607946129703146989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116714083071964086468764659 175071124607946129703146989)
        ·
          refine ⟨65651671727979798638680121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 175071124607946129703146989 65651671727979798638680121)
          ·
            refine ⟨49238753795984848979010091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65651671727979798638680121 49238753795984848979010091)
            ·
              refine ⟨73858130693977273468515137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49238753795984848979010091 73858130693977273468515137)
              ·
                refine ⟨55393598020482955101386353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73858130693977273468515137 55393598020482955101386353)
                ·
                  refine ⟨41545198515362216326039765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55393598020482955101386353 41545198515362216326039765)
                  ·
                    refine ⟨973715590203801945141557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41545198515362216326039765 973715590203801945141557)
                    ·
                      rfl

theorem cell23_5688913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 2, 2, 7].length) (baseStart_5688913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5688913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5688913 prefixEnd_5688913 := by exact prefixLift 5688913
  have htrace : WordTrace (prefixWord ++ tailWord_5688913) baseStart_5688913 baseEnd_5688913 := by
    simpa [prefixWord, tailWord_5688913, baseEnd_5688913] using wordTrace_append hprefix tailTrace_5688913
  have hstable : (prefixWord ++ tailWord_5688913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5688913).length < 2 ^ (prefixWord ++ tailWord_5688913).sum := by decide
  have hdescent : baseEnd_5688913 < baseStart_5688913 := by decide
  rcases family_descends (prefixWord ++ tailWord_5688913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5688944 : List Nat := [2, 1, 1, 1, 6, 1, 3, 2, 2, 1, 3]
def baseStart_5688944 : Nat := 118140960795 + 5688944 * 2 ^ 59
def prefixEnd_5688944 : Nat := 4983230072969 + 3 ^ 40 * 5688944 * 2
def baseEnd_5688944 : Nat := 2921162688511695214137029

theorem tailTrace_5688944 : CollatzResearch.WordTrace tailWord_5688944 prefixEnd_5688944 2921162688511695214137029 := by
  unfold tailWord_5688944
  simp only [CollatzResearch.WordTrace]
  refine ⟨103746416950967478563868943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138328555934623304751825257 103746416950967478563868943)
  ·
    refine ⟨155619625426451217845803415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103746416950967478563868943 155619625426451217845803415)
    ·
      refine ⟨233429438139676826768705123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155619625426451217845803415 233429438139676826768705123)
      ·
        refine ⟨350144157209515240153057685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233429438139676826768705123 350144157209515240153057685)
        ·
          refine ⟨16413007369196026882174579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 350144157209515240153057685 16413007369196026882174579)
          ·
            refine ⟨24619511053794040323261869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16413007369196026882174579 24619511053794040323261869)
            ·
              refine ⟨9232316645172765121223201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24619511053794040323261869 9232316645172765121223201)
              ·
                refine ⟨6924237483879573840917401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9232316645172765121223201 6924237483879573840917401)
                ·
                  refine ⟨5193178112909680380688051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6924237483879573840917401 5193178112909680380688051)
                  ·
                    refine ⟨7789767169364520571032077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5193178112909680380688051 7789767169364520571032077)
                    ·
                      refine ⟨2921162688511695214137029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7789767169364520571032077 2921162688511695214137029)
                      ·
                        rfl

theorem cell23_5688944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 3, 2, 2, 1, 3].length) (baseStart_5688944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5688944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5688944 prefixEnd_5688944 := by exact prefixLift 5688944
  have htrace : WordTrace (prefixWord ++ tailWord_5688944) baseStart_5688944 baseEnd_5688944 := by
    simpa [prefixWord, tailWord_5688944, baseEnd_5688944] using wordTrace_append hprefix tailTrace_5688944
  have hstable : (prefixWord ++ tailWord_5688944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5688944).length < 2 ^ (prefixWord ++ tailWord_5688944).sum := by decide
  have hdescent : baseEnd_5688944 < baseStart_5688944 := by decide
  rcases family_descends (prefixWord ++ tailWord_5688944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5688961 : List Nat := [1, 2, 4, 2, 1, 3, 3, 1, 2, 1, 3]
def baseStart_5688961 : Nat := 118140960795 + 5688961 * 2 ^ 59
def prefixEnd_5688961 : Nat := 4983230072969 + 3 ^ 40 * 5688961 * 2
def baseEnd_5688961 : Nat := 2921171417682821647624451

theorem tailTrace_5688961 : CollatzResearch.WordTrace tailWord_5688961 prefixEnd_5688961 2921171417682821647624451 := by
  unfold tailWord_5688961
  simp only [CollatzResearch.WordTrace]
  refine ⟨207493453942873369031106737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138328969295248912687404491 207493453942873369031106737)
  ·
    refine ⟨155620090457155026773330053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207493453942873369031106737 155620090457155026773330053)
    ·
      refine ⟨29178766960716567519999385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 155620090457155026773330053 29178766960716567519999385)
      ·
        refine ⟨21884075220537425639999539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29178766960716567519999385 21884075220537425639999539)
        ·
          refine ⟨32826112830806138459999309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21884075220537425639999539 32826112830806138459999309)
          ·
            refine ⟨12309792311552301922499741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32826112830806138459999309 12309792311552301922499741)
            ·
              refine ⟨4616172116832113220937403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12309792311552301922499741 4616172116832113220937403)
              ·
                refine ⟨6924258175248169831406105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4616172116832113220937403 6924258175248169831406105)
                ·
                  refine ⟨5193193631436127373554579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6924258175248169831406105 5193193631436127373554579)
                  ·
                    refine ⟨7789790447154191060331869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5193193631436127373554579 7789790447154191060331869)
                    ·
                      refine ⟨2921171417682821647624451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7789790447154191060331869 2921171417682821647624451)
                      ·
                        rfl

theorem cell23_5688961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 3, 1, 2, 1, 3].length) (baseStart_5688961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5688961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5688961 prefixEnd_5688961 := by exact prefixLift 5688961
  have htrace : WordTrace (prefixWord ++ tailWord_5688961) baseStart_5688961 baseEnd_5688961 := by
    simpa [prefixWord, tailWord_5688961, baseEnd_5688961] using wordTrace_append hprefix tailTrace_5688961
  have hstable : (prefixWord ++ tailWord_5688961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5688961).length < 2 ^ (prefixWord ++ tailWord_5688961).sum := by decide
  have hdescent : baseEnd_5688961 < baseStart_5688961 := by decide
  rcases family_descends (prefixWord ++ tailWord_5688961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5688984 : List Nat := [2, 1, 2, 4, 1, 2, 1, 2, 4, 2, 2]
def baseStart_5688984 : Nat := 118140960795 + 5688984 * 2 ^ 59
def prefixEnd_5688984 : Nat := 4983230072969 + 3 ^ 40 * 5688984 * 2
def baseEnd_5688984 : Nat := 2921183227737875057636845

theorem tailTrace_5688984 : CollatzResearch.WordTrace tailWord_5688984 prefixEnd_5688984 2921183227737875057636845 := by
  unfold tailWord_5688984
  simp only [CollatzResearch.WordTrace]
  refine ⟨103747146410895021979597003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138329528547860029306129337 103747146410895021979597003)
  ·
    refine ⟨155620719616342532969395505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103747146410895021979597003 155620719616342532969395505)
    ·
      refine ⟨116715539712256899727046629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155620719616342532969395505 116715539712256899727046629)
      ·
        refine ⟨21884163696048168698821243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 116715539712256899727046629 21884163696048168698821243)
        ·
          refine ⟨32826245544072253048231865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21884163696048168698821243 32826245544072253048231865)
          ·
            refine ⟨24619684158054189786173899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32826245544072253048231865 24619684158054189786173899)
            ·
              refine ⟨36929526237081284679260849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24619684158054189786173899 36929526237081284679260849)
              ·
                refine ⟨27697144677810963509445637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36929526237081284679260849 27697144677810963509445637)
                ·
                  refine ⟨5193214627089555658021057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27697144677810963509445637 5193214627089555658021057)
                  ·
                    refine ⟨3894910970317166743515793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5193214627089555658021057 3894910970317166743515793)
                    ·
                      refine ⟨2921183227737875057636845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3894910970317166743515793 2921183227737875057636845)
                      ·
                        rfl

theorem cell23_5688984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 2, 4, 2, 2].length) (baseStart_5688984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5688984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5688984 prefixEnd_5688984 := by exact prefixLift 5688984
  have htrace : WordTrace (prefixWord ++ tailWord_5688984) baseStart_5688984 baseEnd_5688984 := by
    simpa [prefixWord, tailWord_5688984, baseEnd_5688984] using wordTrace_append hprefix tailTrace_5688984
  have hstable : (prefixWord ++ tailWord_5688984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5688984).length < 2 ^ (prefixWord ++ tailWord_5688984).sum := by decide
  have hdescent : baseEnd_5688984 < baseStart_5688984 := by decide
  rcases family_descends (prefixWord ++ tailWord_5688984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5689003 : List Nat := [1, 1, 1, 1, 2, 1, 1, 1, 1, 13]
def baseStart_5689003 : Nat := 118140960795 + 5689003 * 2 ^ 59
def prefixEnd_5689003 : Nat := 4983230072969 + 3 ^ 40 * 5689003 * 2
def baseEnd_5689003 : Nat := 973730994623436827766419

theorem tailTrace_5689003 : CollatzResearch.WordTrace tailWord_5689003 prefixEnd_5689003 973730994623436827766419 := by
  unfold tailWord_5689003
  simp only [CollatzResearch.WordTrace]
  refine ⟨207494985808721210204135663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138329990539147473469423775 207494985808721210204135663)
  ·
    refine ⟨311242478713081815306203495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207494985808721210204135663 311242478713081815306203495)
    ·
      refine ⟨466863718069622722959305243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 311242478713081815306203495 466863718069622722959305243)
      ·
        refine ⟨700295577104434084438957865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 466863718069622722959305243 700295577104434084438957865)
        ·
          refine ⟨525221682828325563329218399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 700295577104434084438957865 525221682828325563329218399)
          ·
            refine ⟨787832524242488344993827599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 525221682828325563329218399 787832524242488344993827599)
            ·
              refine ⟨1181748786363732517490741399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 787832524242488344993827599 1181748786363732517490741399)
              ·
                refine ⟨1772623179545598776236112099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1181748786363732517490741399 1772623179545598776236112099)
                ·
                  refine ⟨2658934769318398164354168149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1772623179545598776236112099 2658934769318398164354168149)
                  ·
                    refine ⟨973730994623436827766419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 13 2658934769318398164354168149 973730994623436827766419)
                    ·
                      rfl

theorem cell23_5689003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 13].length) (baseStart_5689003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5689003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5689003 prefixEnd_5689003 := by exact prefixLift 5689003
  have htrace : WordTrace (prefixWord ++ tailWord_5689003) baseStart_5689003 baseEnd_5689003 := by
    simpa [prefixWord, tailWord_5689003, baseEnd_5689003] using wordTrace_append hprefix tailTrace_5689003
  have hstable : (prefixWord ++ tailWord_5689003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5689003).length < 2 ^ (prefixWord ++ tailWord_5689003).sum := by decide
  have hdescent : baseEnd_5689003 < baseStart_5689003 := by decide
  rcases family_descends (prefixWord ++ tailWord_5689003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5689018 : List Nat := [3, 1, 1, 1, 2, 6, 2, 1, 2, 2, 2]
def baseStart_5689018 : Nat := 118140960795 + 5689018 * 2 ^ 59
def prefixEnd_5689018 : Nat := 4983230072969 + 3 ^ 40 * 5689018 * 2
def baseEnd_5689018 : Nat := 2921200686080127924611689

theorem tailTrace_5689018 : CollatzResearch.WordTrace tailWord_5689018 prefixEnd_5689018 2921200686080127924611689 := by
  unfold tailWord_5689018
  simp only [CollatzResearch.WordTrace]
  refine ⟨51873883225916716941482927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138330355269111245177287805 51873883225916716941482927)
  ·
    refine ⟨77810824838875075412224391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51873883225916716941482927 77810824838875075412224391)
    ·
      refine ⟨116716237258312613118336587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77810824838875075412224391 116716237258312613118336587)
      ·
        refine ⟨175074355887468919677504881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116716237258312613118336587 175074355887468919677504881)
        ·
          refine ⟨131305766915601689758128661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175074355887468919677504881 131305766915601689758128661)
          ·
            refine ⟨6154957824168829207412281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 131305766915601689758128661 6154957824168829207412281)
            ·
              refine ⟨4616218368126621905559211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6154957824168829207412281 4616218368126621905559211)
              ·
                refine ⟨6924327552189932858338817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4616218368126621905559211 6924327552189932858338817)
                ·
                  refine ⟨5193245664142449643754113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6924327552189932858338817 5193245664142449643754113)
                  ·
                    refine ⟨3894934248106837232815585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5193245664142449643754113 3894934248106837232815585)
                    ·
                      refine ⟨2921200686080127924611689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3894934248106837232815585 2921200686080127924611689)
                      ·
                        rfl

theorem cell23_5689018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 2, 1, 2, 2, 2].length) (baseStart_5689018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5689018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5689018 prefixEnd_5689018 := by exact prefixLift 5689018
  have htrace : WordTrace (prefixWord ++ tailWord_5689018) baseStart_5689018 baseEnd_5689018 := by
    simpa [prefixWord, tailWord_5689018, baseEnd_5689018] using wordTrace_append hprefix tailTrace_5689018
  have hstable : (prefixWord ++ tailWord_5689018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5689018).length < 2 ^ (prefixWord ++ tailWord_5689018).sum := by decide
  have hdescent : baseEnd_5689018 < baseStart_5689018 := by decide
  rcases family_descends (prefixWord ++ tailWord_5689018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5689060 : List Nat := [2, 3, 1, 1, 1, 3, 1, 1, 2, 3, 5]
def baseStart_5689060 : Nat := 118140960795 + 5689060 * 2 ^ 59
def prefixEnd_5689060 : Nat := 4983230072969 + 3 ^ 40 * 5689060 * 2
def baseEnd_5689060 : Nat := 2921222252267616760286495

theorem tailTrace_5689060 : CollatzResearch.WordTrace tailWord_5689060 prefixEnd_5689060 2921222252267616760286495 := by
  unfold tailWord_5689060
  simp only [CollatzResearch.WordTrace]
  refine ⟨103748532384757354469480317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138331376513009805959307089 103748532384757354469480317)
  ·
    refine ⟨38905699644284007926055119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103748532384757354469480317 38905699644284007926055119)
    ·
      refine ⟨58358549466426011889082679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38905699644284007926055119 58358549466426011889082679)
      ·
        refine ⟨87537824199639017833624019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58358549466426011889082679 87537824199639017833624019)
        ·
          refine ⟨131306736299458526750436029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87537824199639017833624019 131306736299458526750436029)
          ·
            refine ⟨49240026112296947531413511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 131306736299458526750436029 49240026112296947531413511)
            ·
              refine ⟨73860039168445421297120267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49240026112296947531413511 73860039168445421297120267)
              ·
                refine ⟨110790058752668131945680401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73860039168445421297120267 110790058752668131945680401)
                ·
                  refine ⟨83092544064501098959260301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 110790058752668131945680401 83092544064501098959260301)
                  ·
                    refine ⟨31159704024187912109722613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 83092544064501098959260301 31159704024187912109722613)
                    ·
                      refine ⟨2921222252267616760286495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31159704024187912109722613 2921222252267616760286495)
                      ·
                        rfl

theorem cell23_5689060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 2, 3, 5].length) (baseStart_5689060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5689060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5689060 prefixEnd_5689060 := by exact prefixLift 5689060
  have htrace : WordTrace (prefixWord ++ tailWord_5689060) baseStart_5689060 baseEnd_5689060 := by
    simpa [prefixWord, tailWord_5689060, baseEnd_5689060] using wordTrace_append hprefix tailTrace_5689060
  have hstable : (prefixWord ++ tailWord_5689060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5689060).length < 2 ^ (prefixWord ++ tailWord_5689060).sum := by decide
  have hdescent : baseEnd_5689060 < baseStart_5689060 := by decide
  rcases family_descends (prefixWord ++ tailWord_5689060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5689074 : List Nat := [3, 2, 1, 3, 1, 1, 3, 1, 2, 4, 2]
def baseStart_5689074 : Nat := 118140960795 + 5689074 * 2 ^ 59
def prefixEnd_5689074 : Nat := 4983230072969 + 3 ^ 40 * 5689074 * 2
def baseEnd_5689074 : Nat := 2921229440996779705511431

theorem tailTrace_5689074 : CollatzResearch.WordTrace tailWord_5689074 prefixEnd_5689074 2921229440996779705511431 := by
  unfold tailWord_5689074
  simp only [CollatzResearch.WordTrace]
  refine ⟨51874393847865997332492569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138331716927642659553313517 51874393847865997332492569)
  ·
    refine ⟨38905795385899497999369427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51874393847865997332492569 38905795385899497999369427)
    ·
      refine ⟨58358693078849246999054141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38905795385899497999369427 58358693078849246999054141)
      ·
        refine ⟨21884509904568467624645303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58358693078849246999054141 21884509904568467624645303)
        ·
          refine ⟨32826764856852701436967955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21884509904568467624645303 32826764856852701436967955)
          ·
            refine ⟨49240147285279052155451933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32826764856852701436967955 49240147285279052155451933)
            ·
              refine ⟨18465055231979644558294475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49240147285279052155451933 18465055231979644558294475)
              ·
                refine ⟨27697582847969466837441713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18465055231979644558294475 27697582847969466837441713)
                ·
                  refine ⟨20773187135977100128081285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27697582847969466837441713 20773187135977100128081285)
                  ·
                    refine ⟨3894972587995706274015241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20773187135977100128081285 3894972587995706274015241)
                    ·
                      refine ⟨2921229440996779705511431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3894972587995706274015241 2921229440996779705511431)
                      ·
                        rfl

theorem cell23_5689074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 1, 2, 4, 2].length) (baseStart_5689074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5689074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5689074 prefixEnd_5689074 := by exact prefixLift 5689074
  have htrace : WordTrace (prefixWord ++ tailWord_5689074) baseStart_5689074 baseEnd_5689074 := by
    simpa [prefixWord, tailWord_5689074, baseEnd_5689074] using wordTrace_append hprefix tailTrace_5689074
  have hstable : (prefixWord ++ tailWord_5689074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5689074).length < 2 ^ (prefixWord ++ tailWord_5689074).sum := by decide
  have hdescent : baseEnd_5689074 < baseStart_5689074 := by decide
  rcases family_descends (prefixWord ++ tailWord_5689074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5689114 : List Nat := [3, 1, 1, 3, 2, 4, 1, 2, 6]
def baseStart_5689114 : Nat := 118140960795 + 5689114 * 2 ^ 59
def prefixEnd_5689114 : Nat := 4983230072969 + 3 ^ 40 * 5689114 * 2
def baseEnd_5689114 : Nat := 324583331135884394334583

theorem tailTrace_5689114 : CollatzResearch.WordTrace tailWord_5689114 prefixEnd_5689114 324583331135884394334583 := by
  unfold tailWord_5689114
  simp only [CollatzResearch.WordTrace]
  refine ⟨51874758577829769040356599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138332689540879384107617597 51874758577829769040356599)
  ·
    refine ⟨77812137866744653560534899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51874758577829769040356599 77812137866744653560534899)
    ·
      refine ⟨116718206800116980340802349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77812137866744653560534899 116718206800116980340802349)
      ·
        refine ⟨43769327550043867627800881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116718206800116980340802349 43769327550043867627800881)
        ·
          refine ⟨32826995662532900720850661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43769327550043867627800881 32826995662532900720850661)
          ·
            refine ⟨6155061686724918885159499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32826995662532900720850661 6155061686724918885159499)
            ·
              refine ⟨9232592530087378327739249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6155061686724918885159499 9232592530087378327739249)
              ·
                refine ⟨6924444397565533745804437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9232592530087378327739249 6924444397565533745804437)
                ·
                  refine ⟨324583331135884394334583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6924444397565533745804437 324583331135884394334583)
                  ·
                    rfl

theorem cell23_5689114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 1, 2, 6].length) (baseStart_5689114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5689114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5689114 prefixEnd_5689114 := by exact prefixLift 5689114
  have htrace : WordTrace (prefixWord ++ tailWord_5689114) baseStart_5689114 baseEnd_5689114 := by
    simpa [prefixWord, tailWord_5689114, baseEnd_5689114] using wordTrace_append hprefix tailTrace_5689114
  have hstable : (prefixWord ++ tailWord_5689114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5689114).length < 2 ^ (prefixWord ++ tailWord_5689114).sum := by decide
  have hdescent : baseEnd_5689114 < baseStart_5689114 := by decide
  rcases family_descends (prefixWord ++ tailWord_5689114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5689144 : List Nat := [2, 1, 2, 1, 3, 4, 2, 2, 1, 5]
def baseStart_5689144 : Nat := 118140960795 + 5689144 * 2 ^ 59
def prefixEnd_5689144 : Nat := 4983230072969 + 3 ^ 40 * 5689144 * 2
def baseEnd_5689144 : Nat := 973755128214198143878703

theorem tailTrace_5689144 : CollatzResearch.WordTrace tailWord_5689144 prefixEnd_5689144 973755128214198143878703 := by
  unfold tailWord_5689144
  simp only [CollatzResearch.WordTrace]
  refine ⟨103750064250605195642509243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138333419000806927523345657 103750064250605195642509243)
  ·
    refine ⟨155625096375907793463763865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103750064250605195642509243 155625096375907793463763865)
    ·
      refine ⟨116718822281930845097822899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155625096375907793463763865 116718822281930845097822899)
      ·
        refine ⟨175078233422896267646734349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116718822281930845097822899 175078233422896267646734349)
        ·
          refine ⟨65654337533586100367525381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 175078233422896267646734349 65654337533586100367525381)
          ·
            refine ⟨12310188287547393818911009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65654337533586100367525381 12310188287547393818911009)
            ·
              refine ⟨9232641215660545364183257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12310188287547393818911009 9232641215660545364183257)
              ·
                refine ⟨6924480911745409023137443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9232641215660545364183257 6924480911745409023137443)
                ·
                  refine ⟨10386721367618113534706165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6924480911745409023137443 10386721367618113534706165)
                  ·
                    refine ⟨973755128214198143878703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10386721367618113534706165 973755128214198143878703)
                    ·
                      rfl

theorem cell23_5689144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 2, 2, 1, 5].length) (baseStart_5689144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5689144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5689144 prefixEnd_5689144 := by exact prefixLift 5689144
  have htrace : WordTrace (prefixWord ++ tailWord_5689144) baseStart_5689144 baseEnd_5689144 := by
    simpa [prefixWord, tailWord_5689144, baseEnd_5689144] using wordTrace_append hprefix tailTrace_5689144
  have hstable : (prefixWord ++ tailWord_5689144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5689144).length < 2 ^ (prefixWord ++ tailWord_5689144).sum := by decide
  have hdescent : baseEnd_5689144 < baseStart_5689144 := by decide
  rcases family_descends (prefixWord ++ tailWord_5689144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5689157 : List Nat := [1, 3, 1, 1, 1, 2, 3, 1, 6, 4]
def baseStart_5689157 : Nat := 118140960795 + 5689157 * 2 ^ 59
def prefixEnd_5689157 : Nat := 4983230072969 + 3 ^ 40 * 5689157 * 2
def baseEnd_5689157 : Nat := 973757353297034293591183

theorem tailTrace_5689157 : CollatzResearch.WordTrace tailWord_5689157 prefixEnd_5689157 973757353297034293591183 := by
  unfold tailWord_5689157
  simp only [CollatzResearch.WordTrace]
  refine ⟨207500602650163294505241725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138333735100108863003494483 207500602650163294505241725)
  ·
    refine ⟨77812725993811235439465647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 207500602650163294505241725 77812725993811235439465647)
    ·
      refine ⟨116719088990716853159198471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77812725993811235439465647 116719088990716853159198471)
      ·
        refine ⟨175078633486075279738797707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116719088990716853159198471 175078633486075279738797707)
        ·
          refine ⟨262617950229112919608196561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175078633486075279738797707 262617950229112919608196561)
          ·
            refine ⟨196963462671834689706147421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 262617950229112919608196561 196963462671834689706147421)
            ·
              refine ⟨73861298501938008639805283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 196963462671834689706147421 73861298501938008639805283)
              ·
                refine ⟨110791947752907012959707925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73861298501938008639805283 110791947752907012959707925)
                ·
                  refine ⟨5193372550917516232486309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 110791947752907012959707925 5193372550917516232486309)
                  ·
                    refine ⟨973757353297034293591183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5193372550917516232486309 973757353297034293591183)
                    ·
                      rfl

theorem cell23_5689157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 6, 4].length) (baseStart_5689157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5689157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5689157 prefixEnd_5689157 := by exact prefixLift 5689157
  have htrace : WordTrace (prefixWord ++ tailWord_5689157) baseStart_5689157 baseEnd_5689157 := by
    simpa [prefixWord, tailWord_5689157, baseEnd_5689157] using wordTrace_append hprefix tailTrace_5689157
  have hstable : (prefixWord ++ tailWord_5689157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5689157).length < 2 ^ (prefixWord ++ tailWord_5689157).sum := by decide
  have hdescent : baseEnd_5689157 < baseStart_5689157 := by decide
  rcases family_descends (prefixWord ++ tailWord_5689157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5689175 : List Nat := [1, 1, 3, 2, 5, 1, 3, 2, 1, 1, 3]
def baseStart_5689175 : Nat := 118140960795 + 5689175 * 2 ^ 59
def prefixEnd_5689175 : Nat := 4983230072969 + 3 ^ 40 * 5689175 * 2
def baseEnd_5689175 : Nat := 2921281302542883810348467

theorem tailTrace_5689175 : CollatzResearch.WordTrace tailWord_5689175 prefixEnd_5689175 2921281302542883810348467 := by
  unfold tailWord_5689175
  simp only [CollatzResearch.WordTrace]
  refine ⟨207501259164098083579396979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138334172776065389052931319 207501259164098083579396979)
  ·
    refine ⟨311251888746147125369095469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207501259164098083579396979 311251888746147125369095469)
    ·
      refine ⟨116719458279805172013410801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 311251888746147125369095469 116719458279805172013410801)
      ·
        refine ⟨87539593709853879010058101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116719458279805172013410801 87539593709853879010058101)
        ·
          refine ⟨8206836910298801157192947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 87539593709853879010058101 8206836910298801157192947)
          ·
            refine ⟨12310255365448201735789421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8206836910298801157192947 12310255365448201735789421)
            ·
              refine ⟨4616345762043075650921033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12310255365448201735789421 4616345762043075650921033)
              ·
                refine ⟨3462259321532306738190775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4616345762043075650921033 3462259321532306738190775)
                ·
                  refine ⟨5193388982298460107286163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3462259321532306738190775 5193388982298460107286163)
                  ·
                    refine ⟨7790083473447690160929245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5193388982298460107286163 7790083473447690160929245)
                    ·
                      refine ⟨2921281302542883810348467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7790083473447690160929245 2921281302542883810348467)
                      ·
                        rfl

theorem cell23_5689175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 3, 2, 1, 1, 3].length) (baseStart_5689175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5689175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5689175 prefixEnd_5689175 := by exact prefixLift 5689175
  have htrace : WordTrace (prefixWord ++ tailWord_5689175) baseStart_5689175 baseEnd_5689175 := by
    simpa [prefixWord, tailWord_5689175, baseEnd_5689175] using wordTrace_append hprefix tailTrace_5689175
  have hstable : (prefixWord ++ tailWord_5689175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5689175).length < 2 ^ (prefixWord ++ tailWord_5689175).sum := by decide
  have hdescent : baseEnd_5689175 < baseStart_5689175 := by decide
  rcases family_descends (prefixWord ++ tailWord_5689175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5689198 : List Nat := [4, 1, 2, 3, 1, 3, 1, 2, 1, 1, 4]
def baseStart_5689198 : Nat := 118140960795 + 5689198 * 2 ^ 59
def prefixEnd_5689198 : Nat := 4983230072969 + 3 ^ 40 * 5689198 * 2
def baseEnd_5689198 : Nat := 2921293112597937220360861

theorem tailTrace_5689198 : CollatzResearch.WordTrace tailWord_5689198 prefixEnd_5689198 2921293112597937220360861 := by
  unfold tailWord_5689198
  simp only [CollatzResearch.WordTrace]
  refine ⟨25937762255376844813435531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138334732028676505671656165 25937762255376844813435531)
  ·
    refine ⟨38906643383065267220153297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25937762255376844813435531 38906643383065267220153297)
    ·
      refine ⟨29179982537298950415114973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38906643383065267220153297 29179982537298950415114973)
      ·
        refine ⟨10942493451487106405668115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29179982537298950415114973 10942493451487106405668115)
        ·
          refine ⟨16413740177230659608502173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10942493451487106405668115 16413740177230659608502173)
          ·
            refine ⟨6155152566461497353188315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16413740177230659608502173 6155152566461497353188315)
            ·
              refine ⟨9232728849692246029782473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6155152566461497353188315 9232728849692246029782473)
              ·
                refine ⟨6924546637269184522336855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9232728849692246029782473 6924546637269184522336855)
                ·
                  refine ⟨10386819955903776783505283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6924546637269184522336855 10386819955903776783505283)
                  ·
                    refine ⟨15580229933855665175257925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10386819955903776783505283 15580229933855665175257925)
                    ·
                      refine ⟨2921293112597937220360861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15580229933855665175257925 2921293112597937220360861)
                      ·
                        rfl

theorem cell23_5689198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_5689198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5689198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5689198 prefixEnd_5689198 := by exact prefixLift 5689198
  have htrace : WordTrace (prefixWord ++ tailWord_5689198) baseStart_5689198 baseEnd_5689198 := by
    simpa [prefixWord, tailWord_5689198, baseEnd_5689198] using wordTrace_append hprefix tailTrace_5689198
  have hstable : (prefixWord ++ tailWord_5689198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5689198).length < 2 ^ (prefixWord ++ tailWord_5689198).sum := by decide
  have hdescent : baseEnd_5689198 < baseStart_5689198 := by decide
  rcases family_descends (prefixWord ++ tailWord_5689198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5689234 : List Nat := [3, 2, 3, 2, 1, 1, 1, 1, 2, 7]
def baseStart_5689234 : Nat := 118140960795 + 5689234 * 2 ^ 59
def prefixEnd_5689234 : Nat := 4983230072969 + 3 ^ 40 * 5689234 * 2
def baseEnd_5689234 : Nat := 973770532633833026503565

theorem tailTrace_5689234 : CollatzResearch.WordTrace tailWord_5689234 prefixEnd_5689234 973770532633833026503565 := by
  unfold tailWord_5689234
  simp only [CollatzResearch.WordTrace]
  refine ⟨51875852767721084163948689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138335607380589557770529837 51875852767721084163948689)
  ·
    refine ⟨38906889575790813122961517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51875852767721084163948689 38906889575790813122961517)
    ·
      refine ⟨14590083590921554921110569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38906889575790813122961517 14590083590921554921110569)
      ·
        refine ⟨10942562693191166190832927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14590083590921554921110569 10942562693191166190832927)
        ·
          refine ⟨16413844039786749286249391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10942562693191166190832927 16413844039786749286249391)
          ·
            refine ⟨24620766059680123929374087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16413844039786749286249391 24620766059680123929374087)
            ·
              refine ⟨36931149089520185894061131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24620766059680123929374087 36931149089520185894061131)
              ·
                refine ⟨55396723634280278841091697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36931149089520185894061131 55396723634280278841091697)
                ·
                  refine ⟨41547542725710209130818773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55396723634280278841091697 41547542725710209130818773)
                  ·
                    refine ⟨973770532633833026503565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41547542725710209130818773 973770532633833026503565)
                    ·
                      rfl

theorem cell23_5689234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 1, 2, 7].length) (baseStart_5689234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5689234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5689234 prefixEnd_5689234 := by exact prefixLift 5689234
  have htrace : WordTrace (prefixWord ++ tailWord_5689234) baseStart_5689234 baseEnd_5689234 := by
    simpa [prefixWord, tailWord_5689234, baseEnd_5689234] using wordTrace_append hprefix tailTrace_5689234
  have hstable : (prefixWord ++ tailWord_5689234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5689234).length < 2 ^ (prefixWord ++ tailWord_5689234).sum := by decide
  have hdescent : baseEnd_5689234 < baseStart_5689234 := by decide
  rcases family_descends (prefixWord ++ tailWord_5689234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5689237 : List Nat := [1, 3, 2, 1, 1, 3, 1, 1, 1, 5, 4]
def baseStart_5689237 : Nat := 118140960795 + 5689237 * 2 ^ 59
def prefixEnd_5689237 : Nat := 4983230072969 + 3 ^ 40 * 5689237 * 2
def baseEnd_5689237 : Nat := 2921313138343462567773181

theorem tailTrace_5689237 : CollatzResearch.WordTrace tailWord_5689237 prefixEnd_5689237 2921313138343462567773181 := by
  unfold tailWord_5689237
  simp only [CollatzResearch.WordTrace]
  refine ⟨207503520489873468168153965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138335680326582312112102643 207503520489873468168153965)
  ·
    refine ⟨77813820183702550563057737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 207503520489873468168153965 77813820183702550563057737)
    ·
      refine ⟨58360365137776912922293303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77813820183702550563057737 58360365137776912922293303)
      ·
        refine ⟨87540547706665369383439955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58360365137776912922293303 87540547706665369383439955)
        ·
          refine ⟨131310821559998054075159933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87540547706665369383439955 131310821559998054075159933)
          ·
            refine ⟨49241558084999270278184975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 131310821559998054075159933 49241558084999270278184975)
            ·
              refine ⟨73862337127498905417277463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49241558084999270278184975 73862337127498905417277463)
              ·
                refine ⟨110793505691248358125916195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73862337127498905417277463 110793505691248358125916195)
                ·
                  refine ⟨166190258536872537188874293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 110793505691248358125916195 166190258536872537188874293)
                  ·
                    refine ⟨15580336737831800361456965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 166190258536872537188874293 15580336737831800361456965)
                    ·
                      refine ⟨2921313138343462567773181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15580336737831800361456965 2921313138343462567773181)
                      ·
                        rfl

theorem cell23_5689237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 5, 4].length) (baseStart_5689237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5689237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5689237 prefixEnd_5689237 := by exact prefixLift 5689237
  have htrace : WordTrace (prefixWord ++ tailWord_5689237) baseStart_5689237 baseEnd_5689237 := by
    simpa [prefixWord, tailWord_5689237, baseEnd_5689237] using wordTrace_append hprefix tailTrace_5689237
  have hstable : (prefixWord ++ tailWord_5689237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5689237).length < 2 ^ (prefixWord ++ tailWord_5689237).sum := by decide
  have hdescent : baseEnd_5689237 < baseStart_5689237 := by decide
  rcases family_descends (prefixWord ++ tailWord_5689237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5689257 : List Nat := [1, 2, 1, 1, 1, 1, 4, 4, 2, 1, 5]
def baseStart_5689257 : Nat := 118140960795 + 5689257 * 2 ^ 59
def prefixEnd_5689257 : Nat := 4983230072969 + 3 ^ 40 * 5689257 * 2
def baseEnd_5689257 : Nat := 2921323407956552489523089

theorem tailTrace_5689257 : CollatzResearch.WordTrace tailWord_5689257 prefixEnd_5689257 2921323407956552489523089 := by
  unfold tailWord_5689257
  simp only [CollatzResearch.WordTrace]
  refine ⟨207504249949801011583882025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138336166633200674389254683 207504249949801011583882025)
  ·
    refine ⟨155628187462350758687911519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207504249949801011583882025 155628187462350758687911519)
    ·
      refine ⟨233442281193526138031867279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155628187462350758687911519 233442281193526138031867279)
      ·
        refine ⟨350163421790289207047800919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233442281193526138031867279 350163421790289207047800919)
        ·
          refine ⟨525245132685433810571701379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 350163421790289207047800919 525245132685433810571701379)
          ·
            refine ⟨787867699028150715857552069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 525245132685433810571701379 787867699028150715857552069)
            ·
              refine ⟨147725193567778259223291013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 787867699028150715857552069 147725193567778259223291013)
              ·
                refine ⟨27698473793958423604367065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 147725193567778259223291013 27698473793958423604367065)
                ·
                  refine ⟨20773855345468817703275299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27698473793958423604367065 20773855345468817703275299)
                  ·
                    refine ⟨31160783018203226554912949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20773855345468817703275299 31160783018203226554912949)
                    ·
                      refine ⟨2921323407956552489523089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31160783018203226554912949 2921323407956552489523089)
                      ·
                        rfl

theorem cell23_5689257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 4, 2, 1, 5].length) (baseStart_5689257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5689257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5689257 prefixEnd_5689257 := by exact prefixLift 5689257
  have htrace : WordTrace (prefixWord ++ tailWord_5689257) baseStart_5689257 baseEnd_5689257 := by
    simpa [prefixWord, tailWord_5689257, baseEnd_5689257] using wordTrace_append hprefix tailTrace_5689257
  have hstable : (prefixWord ++ tailWord_5689257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5689257).length < 2 ^ (prefixWord ++ tailWord_5689257).sum := by decide
  have hdescent : baseEnd_5689257 < baseStart_5689257 := by decide
  rcases family_descends (prefixWord ++ tailWord_5689257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5689267 : List Nat := [1, 1, 1, 2, 3, 1, 3, 2, 1, 4, 4]
def baseStart_5689267 : Nat := 118140960795 + 5689267 * 2 ^ 59
def prefixEnd_5689267 : Nat := 4983230072969 + 3 ^ 40 * 5689267 * 2
def baseEnd_5689267 : Nat := 2921328542763097450398043

theorem tailTrace_5689267 : CollatzResearch.WordTrace tailWord_5689267 prefixEnd_5689267 2921328542763097450398043 := by
  unfold tailWord_5689267
  simp only [CollatzResearch.WordTrace]
  refine ⟨207504614679764783291746055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138336409786509855527830703 207504614679764783291746055)
  ·
    refine ⟨311256922019647174937619083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207504614679764783291746055 311256922019647174937619083)
    ·
      refine ⟨466885383029470762406428625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 311256922019647174937619083 466885383029470762406428625)
      ·
        refine ⟨350164037272103071804821469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 466885383029470762406428625 350164037272103071804821469)
        ·
          refine ⟨131311513977038651926808051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 350164037272103071804821469 131311513977038651926808051)
          ·
            refine ⟨196967270965557977890212077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131311513977038651926808051 196967270965557977890212077)
            ·
              refine ⟨73862726612084241708829529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 196967270965557977890212077 73862726612084241708829529)
              ·
                refine ⟨55397044959063181281622147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 73862726612084241708829529 55397044959063181281622147)
                ·
                  refine ⟨83095567438594771922433221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55397044959063181281622147 83095567438594771922433221)
                  ·
                    refine ⟨15580418894736519735456229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 83095567438594771922433221 15580418894736519735456229)
                    ·
                      refine ⟨2921328542763097450398043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15580418894736519735456229 2921328542763097450398043)
                      ·
                        rfl

theorem cell23_5689267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 2, 1, 4, 4].length) (baseStart_5689267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5689267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5689267 prefixEnd_5689267 := by exact prefixLift 5689267
  have htrace : WordTrace (prefixWord ++ tailWord_5689267) baseStart_5689267 baseEnd_5689267 := by
    simpa [prefixWord, tailWord_5689267, baseEnd_5689267] using wordTrace_append hprefix tailTrace_5689267
  have hstable : (prefixWord ++ tailWord_5689267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5689267).length < 2 ^ (prefixWord ++ tailWord_5689267).sum := by decide
  have hdescent : baseEnd_5689267 < baseStart_5689267 := by decide
  rcases family_descends (prefixWord ++ tailWord_5689267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5689271 : List Nat := [1, 1, 3, 1, 3, 1, 1, 4, 4, 2, 2]
def baseStart_5689271 : Nat := 118140960795 + 5689271 * 2 ^ 59
def prefixEnd_5689271 : Nat := 4983230072969 + 3 ^ 40 * 5689271 * 2
def baseEnd_5689271 : Nat := 2921330596685715434748025

theorem tailTrace_5689271 : CollatzResearch.WordTrace tailWord_5689271 prefixEnd_5689271 2921330596685715434748025 := by
  unfold tailWord_5689271
  simp only [CollatzResearch.WordTrace]
  refine ⟨207504760571750291974891667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138336507047833527983261111 207504760571750291974891667)
  ·
    refine ⟨311257140857625437962337501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207504760571750291974891667 311257140857625437962337501)
    ·
      refine ⟨116721427821609539235876563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 311257140857625437962337501 116721427821609539235876563)
      ·
        refine ⟨175082141732414308853814845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116721427821609539235876563 175082141732414308853814845)
        ·
          refine ⟨65655803149655365820180567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 175082141732414308853814845 65655803149655365820180567)
          ·
            refine ⟨98483704724483048730270851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65655803149655365820180567 98483704724483048730270851)
            ·
              refine ⟨147725557086724573095406277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98483704724483048730270851 147725557086724573095406277)
              ·
                refine ⟨27698541953760857455388677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 147725557086724573095406277 27698541953760857455388677)
                ·
                  refine ⟨5193476616330160772885377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27698541953760857455388677 5193476616330160772885377)
                  ·
                    refine ⟨3895107462247620579664033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5193476616330160772885377 3895107462247620579664033)
                    ·
                      refine ⟨2921330596685715434748025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3895107462247620579664033 2921330596685715434748025)
                      ·
                        rfl

theorem cell23_5689271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 4, 4, 2, 2].length) (baseStart_5689271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5689271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5689271 prefixEnd_5689271 := by exact prefixLift 5689271
  have htrace : WordTrace (prefixWord ++ tailWord_5689271) baseStart_5689271 baseEnd_5689271 := by
    simpa [prefixWord, tailWord_5689271, baseEnd_5689271] using wordTrace_append hprefix tailTrace_5689271
  have hstable : (prefixWord ++ tailWord_5689271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5689271).length < 2 ^ (prefixWord ++ tailWord_5689271).sum := by decide
  have hdescent : baseEnd_5689271 < baseStart_5689271 := by decide
  rcases family_descends (prefixWord ++ tailWord_5689271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5689288 : List Nat := [2, 1, 3, 1, 4, 2, 1, 1, 4, 2, 2]
def baseStart_5689288 : Nat := 118140960795 + 5689288 * 2 ^ 59
def prefixEnd_5689288 : Nat := 4983230072969 + 3 ^ 40 * 5689288 * 2
def baseEnd_5689288 : Nat := 2921339325856841868235447

theorem tailTrace_5689288 : CollatzResearch.WordTrace tailWord_5689288 prefixEnd_5689288 2921339325856841868235447 := by
  unfold tailWord_5689288
  simp only [CollatzResearch.WordTrace]
  refine ⟨103752690306344351939130259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138336920408459135918840345 103752690306344351939130259)
  ·
    refine ⟨155629035459516527908695389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103752690306344351939130259 155629035459516527908695389)
    ·
      refine ⟨58360888297318697965760771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 155629035459516527908695389 58360888297318697965760771)
      ·
        refine ⟨87541332445978046948641157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58360888297318697965760771 87541332445978046948641157)
        ·
          refine ⟨16413999833620883802870217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87541332445978046948641157 16413999833620883802870217)
          ·
            refine ⟨12310499875215662852152663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16413999833620883802870217 12310499875215662852152663)
            ·
              refine ⟨18465749812823494278228995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12310499875215662852152663 18465749812823494278228995)
              ·
                refine ⟨27698624719235241417343493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18465749812823494278228995 27698624719235241417343493)
                ·
                  refine ⟨5193492134856607765751905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27698624719235241417343493 5193492134856607765751905)
                  ·
                    refine ⟨3895119101142455824313929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5193492134856607765751905 3895119101142455824313929)
                    ·
                      refine ⟨2921339325856841868235447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3895119101142455824313929 2921339325856841868235447)
                      ·
                        rfl

theorem cell23_5689288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 1, 4, 2, 2].length) (baseStart_5689288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5689288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5689288 prefixEnd_5689288 := by exact prefixLift 5689288
  have htrace : WordTrace (prefixWord ++ tailWord_5689288) baseStart_5689288 baseEnd_5689288 := by
    simpa [prefixWord, tailWord_5689288, baseEnd_5689288] using wordTrace_append hprefix tailTrace_5689288
  have hstable : (prefixWord ++ tailWord_5689288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5689288).length < 2 ^ (prefixWord ++ tailWord_5689288).sum := by decide
  have hdescent : baseEnd_5689288 < baseStart_5689288 := by decide
  rcases family_descends (prefixWord ++ tailWord_5689288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5689294 : List Nat := [4, 1, 1, 1, 2, 2, 4, 1, 7]
def baseStart_5689294 : Nat := 118140960795 + 5689294 * 2 ^ 59
def prefixEnd_5689294 : Nat := 4983230072969 + 3 ^ 40 * 5689294 * 2
def baseEnd_5689294 : Nat := 324593600748974316084491

theorem tailTrace_5689294 : CollatzResearch.WordTrace tailWord_5689294 prefixEnd_5689294 324593600748974316084491 := by
  unfold tailWord_5689294
  simp only [CollatzResearch.WordTrace]
  refine ⟨25938199931333370862872367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138337066300444644601985957 25938199931333370862872367)
  ·
    refine ⟨38907299897000056294308551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25938199931333370862872367 38907299897000056294308551)
    ·
      refine ⟨58360949845500084441462827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38907299897000056294308551 58360949845500084441462827)
      ·
        refine ⟨87541424768250126662194241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58360949845500084441462827 87541424768250126662194241)
        ·
          refine ⟨65656068576187594996645681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87541424768250126662194241 65656068576187594996645681)
          ·
            refine ⟨49242051432140696247484261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65656068576187594996645681 49242051432140696247484261)
            ·
              refine ⟨9232884643526380546403299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49242051432140696247484261 9232884643526380546403299)
              ·
                refine ⟨13849326965289570819604949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9232884643526380546403299 13849326965289570819604949)
                ·
                  refine ⟨324593600748974316084491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13849326965289570819604949 324593600748974316084491)
                  ·
                    rfl

theorem cell23_5689294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 4, 1, 7].length) (baseStart_5689294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5689294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5689294 prefixEnd_5689294 := by exact prefixLift 5689294
  have htrace : WordTrace (prefixWord ++ tailWord_5689294) baseStart_5689294 baseEnd_5689294 := by
    simpa [prefixWord, tailWord_5689294, baseEnd_5689294] using wordTrace_append hprefix tailTrace_5689294
  have hstable : (prefixWord ++ tailWord_5689294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5689294).length < 2 ^ (prefixWord ++ tailWord_5689294).sum := by decide
  have hdescent : baseEnd_5689294 < baseStart_5689294 := by decide
  rcases family_descends (prefixWord ++ tailWord_5689294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5689304 : List Nat := [2, 1, 2, 2, 2, 2, 1, 3, 2, 3, 3]
def baseStart_5689304 : Nat := 118140960795 + 5689304 * 2 ^ 59
def prefixEnd_5689304 : Nat := 4983230072969 + 3 ^ 40 * 5689304 * 2
def baseEnd_5689304 : Nat := 2921347541547313805635373

theorem tailTrace_5689304 : CollatzResearch.WordTrace tailWord_5689304 prefixEnd_5689304 2921347541547313805635373 := by
  unfold tailWord_5689304
  simp only [CollatzResearch.WordTrace]
  refine ⟨103752982090315369305421483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138337309453753825740561977 103752982090315369305421483)
  ·
    refine ⟨155629473135473053958132225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103752982090315369305421483 155629473135473053958132225)
    ·
      refine ⟨116722104851604790468599169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155629473135473053958132225 116722104851604790468599169)
      ·
        refine ⟨87541578638703592851449377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116722104851604790468599169 87541578638703592851449377)
        ·
          refine ⟨65656183979027694638587033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87541578638703592851449377 65656183979027694638587033)
          ·
            refine ⟨49242137984270770978940275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65656183979027694638587033 49242137984270770978940275)
            ·
              refine ⟨73863206976406156468410413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49242137984270770978940275 73863206976406156468410413)
              ·
                refine ⟨27698702616152308675653905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 73863206976406156468410413 27698702616152308675653905)
                ·
                  refine ⟨20774026962114231506740429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27698702616152308675653905 20774026962114231506740429)
                  ·
                    refine ⟨7790260110792836815027661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20774026962114231506740429 7790260110792836815027661)
                    ·
                      refine ⟨2921347541547313805635373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7790260110792836815027661 2921347541547313805635373)
                      ·
                        rfl

theorem cell23_5689304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 3, 2, 3, 3].length) (baseStart_5689304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5689304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5689304 prefixEnd_5689304 := by exact prefixLift 5689304
  have htrace : WordTrace (prefixWord ++ tailWord_5689304) baseStart_5689304 baseEnd_5689304 := by
    simpa [prefixWord, tailWord_5689304, baseEnd_5689304] using wordTrace_append hprefix tailTrace_5689304
  have hstable : (prefixWord ++ tailWord_5689304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5689304).length < 2 ^ (prefixWord ++ tailWord_5689304).sum := by decide
  have hdescent : baseEnd_5689304 < baseStart_5689304 := by decide
  rcases family_descends (prefixWord ++ tailWord_5689304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5689305 : List Nat := [1, 2, 1, 2, 7, 1, 1, 1, 1, 4, 2]
def baseStart_5689305 : Nat := 118140960795 + 5689305 * 2 ^ 59
def prefixEnd_5689305 : Nat := 4983230072969 + 3 ^ 40 * 5689305 * 2
def baseEnd_5689305 : Nat := 2921348055027968301722869

theorem tailTrace_5689305 : CollatzResearch.WordTrace tailWord_5689305 prefixEnd_5689305 2921348055027968301722869 := by
  unfold tailWord_5689305
  simp only [CollatzResearch.WordTrace]
  refine ⟨207506000653627115781629369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138337333769084743854419579 207506000653627115781629369)
  ·
    refine ⟨155629500490220336836222027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207506000653627115781629369 155629500490220336836222027)
    ·
      refine ⟨233444250735330505254333041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155629500490220336836222027 233444250735330505254333041)
      ·
        refine ⟨175083188051497878940749781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 233444250735330505254333041 175083188051497878940749781)
        ·
          refine ⟨4103512219956981537673823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 175083188051497878940749781 4103512219956981537673823)
          ·
            refine ⟨6155268329935472306510735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4103512219956981537673823 6155268329935472306510735)
            ·
              refine ⟨9232902494903208459766103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6155268329935472306510735 9232902494903208459766103)
              ·
                refine ⟨13849353742354812689649155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9232902494903208459766103 13849353742354812689649155)
                ·
                  refine ⟨20774030613532219034473733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13849353742354812689649155 20774030613532219034473733)
                  ·
                    refine ⟨3895130740037291068963825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20774030613532219034473733 3895130740037291068963825)
                    ·
                      refine ⟨2921348055027968301722869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3895130740037291068963825 2921348055027968301722869)
                      ·
                        rfl

theorem cell23_5689305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 1, 1, 1, 4, 2].length) (baseStart_5689305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5689305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5689305 prefixEnd_5689305 := by exact prefixLift 5689305
  have htrace : WordTrace (prefixWord ++ tailWord_5689305) baseStart_5689305 baseEnd_5689305 := by
    simpa [prefixWord, tailWord_5689305, baseEnd_5689305] using wordTrace_append hprefix tailTrace_5689305
  have hstable : (prefixWord ++ tailWord_5689305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5689305).length < 2 ^ (prefixWord ++ tailWord_5689305).sum := by decide
  have hdescent : baseEnd_5689305 < baseStart_5689305 := by decide
  rcases family_descends (prefixWord ++ tailWord_5689305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5689381 : List Nat := [1, 3, 1, 2, 2, 3, 1, 3, 2, 2, 3]
def baseStart_5689381 : Nat := 118140960795 + 5689381 * 2 ^ 59
def prefixEnd_5689381 : Nat := 4983230072969 + 3 ^ 40 * 5689381 * 2
def baseEnd_5689381 : Nat := 2921387079557710004372519

theorem tailTrace_5689381 : CollatzResearch.WordTrace tailWord_5689381 prefixEnd_5689381 2921387079557710004372519 := by
  unfold tailWord_5689381
  simp only [CollatzResearch.WordTrace]
  refine ⟨207508772601351780761395997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138339181734234520507597331 207508772601351780761395997)
  ·
    refine ⟨77815789725506917785523499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 207508772601351780761395997 77815789725506917785523499)
    ·
      refine ⟨116723684588260376678285249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77815789725506917785523499 116723684588260376678285249)
      ·
        refine ⟨87542763441195282508713937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116723684588260376678285249 87542763441195282508713937)
        ·
          refine ⟨65657072580896461881535453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87542763441195282508713937 65657072580896461881535453)
          ·
            refine ⟨24621402217836173205575795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65657072580896461881535453 24621402217836173205575795)
            ·
              refine ⟨36932103326754259808363693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24621402217836173205575795 36932103326754259808363693)
              ·
                refine ⟨13849538747532847428136385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36932103326754259808363693 13849538747532847428136385)
                ·
                  refine ⟨10387154060649635571102289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13849538747532847428136385 10387154060649635571102289)
                  ·
                    refine ⟨7790365545487226678326717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10387154060649635571102289 7790365545487226678326717)
                    ·
                      refine ⟨2921387079557710004372519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7790365545487226678326717 2921387079557710004372519)
                      ·
                        rfl

theorem cell23_5689381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 3, 2, 2, 3].length) (baseStart_5689381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5689381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5689381 prefixEnd_5689381 := by exact prefixLift 5689381
  have htrace : WordTrace (prefixWord ++ tailWord_5689381) baseStart_5689381 baseEnd_5689381 := by
    simpa [prefixWord, tailWord_5689381, baseEnd_5689381] using wordTrace_append hprefix tailTrace_5689381
  have hstable : (prefixWord ++ tailWord_5689381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5689381).length < 2 ^ (prefixWord ++ tailWord_5689381).sum := by decide
  have hdescent : baseEnd_5689381 < baseStart_5689381 := by decide
  rcases family_descends (prefixWord ++ tailWord_5689381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5689398 : List Nat := [5, 1, 2, 1, 1, 1, 1, 4, 2, 2, 3]
def baseStart_5689398 : Nat := 118140960795 + 5689398 * 2 ^ 59
def prefixEnd_5689398 : Nat := 4983230072969 + 3 ^ 40 * 5689398 * 2
def baseEnd_5689398 : Nat := 2921395808728836437859941

theorem tailTrace_5689398 : CollatzResearch.WordTrace tailWord_5689398 prefixEnd_5689398 2921395808728836437859941 := by
  unfold tailWord_5689398
  simp only [CollatzResearch.WordTrace]
  refine ⟨12969337040143137041547803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 138339595094860128443176565 12969337040143137041547803)
  ·
    refine ⟨19454005560214705562321705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12969337040143137041547803 19454005560214705562321705)
    ·
      refine ⟨14590504170161029171741279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19454005560214705562321705 14590504170161029171741279)
      ·
        refine ⟨21885756255241543757611919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14590504170161029171741279 21885756255241543757611919)
        ·
          refine ⟨32828634382862315636417879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21885756255241543757611919 32828634382862315636417879)
          ·
            refine ⟨49242951574293473454626819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32828634382862315636417879 49242951574293473454626819)
            ·
              refine ⟨73864427361440210181940229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49242951574293473454626819 73864427361440210181940229)
              ·
                refine ⟨13849580130270039409113793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 73864427361440210181940229 13849580130270039409113793)
                ·
                  refine ⟨10387185097702529556835345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13849580130270039409113793 10387185097702529556835345)
                  ·
                    refine ⟨7790388823276897167626509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10387185097702529556835345 7790388823276897167626509)
                    ·
                      refine ⟨2921395808728836437859941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7790388823276897167626509 2921395808728836437859941)
                      ·
                        rfl

theorem cell23_5689398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 4, 2, 2, 3].length) (baseStart_5689398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5689398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5689398 prefixEnd_5689398 := by exact prefixLift 5689398
  have htrace : WordTrace (prefixWord ++ tailWord_5689398) baseStart_5689398 baseEnd_5689398 := by
    simpa [prefixWord, tailWord_5689398, baseEnd_5689398] using wordTrace_append hprefix tailTrace_5689398
  have hstable : (prefixWord ++ tailWord_5689398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5689398).length < 2 ^ (prefixWord ++ tailWord_5689398).sum := by decide
  have hdescent : baseEnd_5689398 < baseStart_5689398 := by decide
  rcases family_descends (prefixWord ++ tailWord_5689398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5689404 : List Nat := [2, 2, 2, 2, 2, 1, 2, 1, 1, 2, 6]
def baseStart_5689404 : Nat := 118140960795 + 5689404 * 2 ^ 59
def prefixEnd_5689404 : Nat := 4983230072969 + 3 ^ 40 * 5689404 * 2
def baseEnd_5689404 : Nat := 2921398889612763414384913

theorem tailTrace_5689404 : CollatzResearch.WordTrace tailWord_5689404 prefixEnd_5689404 2921398889612763414384913 := by
  unfold tailWord_5689404
  simp only [CollatzResearch.WordTrace]
  refine ⟨103754805740134227844741633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138339740986845637126322177 103754805740134227844741633)
  ·
    refine ⟨77816104305100670883556225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103754805740134227844741633 77816104305100670883556225)
    ·
      refine ⟨58362078228825503162667169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77816104305100670883556225 58362078228825503162667169)
      ·
        refine ⟨43771558671619127372000377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58362078228825503162667169 43771558671619127372000377)
        ·
          refine ⟨32828669003714345529000283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43771558671619127372000377 32828669003714345529000283)
          ·
            refine ⟨49243003505571518293500425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32828669003714345529000283 49243003505571518293500425)
            ·
              refine ⟨36932252629178638720125319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49243003505571518293500425 36932252629178638720125319)
              ·
                refine ⟨55398378943767958080187979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36932252629178638720125319 55398378943767958080187979)
                ·
                  refine ⟨83097568415651937120281969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55398378943767958080187979 83097568415651937120281969)
                  ·
                    refine ⟨62323176311738952840211477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 83097568415651937120281969 62323176311738952840211477)
                    ·
                      refine ⟨2921398889612763414384913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62323176311738952840211477 2921398889612763414384913)
                      ·
                        rfl

theorem cell23_5689404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 1, 1, 2, 6].length) (baseStart_5689404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5689404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5689404 prefixEnd_5689404 := by exact prefixLift 5689404
  have htrace : WordTrace (prefixWord ++ tailWord_5689404) baseStart_5689404 baseEnd_5689404 := by
    simpa [prefixWord, tailWord_5689404, baseEnd_5689404] using wordTrace_append hprefix tailTrace_5689404
  have hstable : (prefixWord ++ tailWord_5689404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5689404).length < 2 ^ (prefixWord ++ tailWord_5689404).sum := by decide
  have hdescent : baseEnd_5689404 < baseStart_5689404 := by decide
  rcases family_descends (prefixWord ++ tailWord_5689404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5689445 : List Nat := [1, 3, 1, 3, 2, 2, 1, 5, 1, 1, 3]
def baseStart_5689445 : Nat := 118140960795 + 5689445 * 2 ^ 59
def prefixEnd_5689445 : Nat := 4983230072969 + 3 ^ 40 * 5689445 * 2
def baseEnd_5689445 : Nat := 2921419942319597753972225

theorem tailTrace_5689445 : CollatzResearch.WordTrace tailWord_5689445 prefixEnd_5689445 2921419942319597753972225 := by
  unfold tailWord_5689445
  simp only [CollatzResearch.WordTrace]
  refine ⟨207511106873119919691725789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138340737915413279794483859 207511106873119919691725789)
  ·
    refine ⟨77816665077419969884397171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 207511106873119919691725789 77816665077419969884397171)
    ·
      refine ⟨116724997616129954826595757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77816665077419969884397171 116724997616129954826595757)
      ·
        refine ⟨43771874106048733059973409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116724997616129954826595757 43771874106048733059973409)
        ·
          refine ⟨32828905579536549794980057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43771874106048733059973409 32828905579536549794980057)
          ·
            refine ⟨24621679184652412346235043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32828905579536549794980057 24621679184652412346235043)
            ·
              refine ⟨36932518776978618519352565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24621679184652412346235043 36932518776978618519352565)
              ·
                refine ⟨3462423635341745486189303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36932518776978618519352565 3462423635341745486189303)
                ·
                  refine ⟨5193635453012618229283955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3462423635341745486189303 5193635453012618229283955)
                  ·
                    refine ⟨7790453179518927343925933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5193635453012618229283955 7790453179518927343925933)
                    ·
                      refine ⟨2921419942319597753972225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7790453179518927343925933 2921419942319597753972225)
                      ·
                        rfl

theorem cell23_5689445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 5, 1, 1, 3].length) (baseStart_5689445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5689445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5689445 prefixEnd_5689445 := by exact prefixLift 5689445
  have htrace : WordTrace (prefixWord ++ tailWord_5689445) baseStart_5689445 baseEnd_5689445 := by
    simpa [prefixWord, tailWord_5689445, baseEnd_5689445] using wordTrace_append hprefix tailTrace_5689445
  have hstable : (prefixWord ++ tailWord_5689445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5689445).length < 2 ^ (prefixWord ++ tailWord_5689445).sum := by decide
  have hdescent : baseEnd_5689445 < baseStart_5689445 := by decide
  rcases family_descends (prefixWord ++ tailWord_5689445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5689462 : List Nat := [5, 1, 1, 2, 1, 2, 2, 4, 1, 1, 3]
def baseStart_5689462 : Nat := 118140960795 + 5689462 * 2 ^ 59
def prefixEnd_5689462 : Nat := 4983230072969 + 3 ^ 40 * 5689462 * 2
def baseEnd_5689462 : Nat := 2921428671490724187459647

theorem tailTrace_5689462 : CollatzResearch.WordTrace tailWord_5689462 prefixEnd_5689462 2921428671490724187459647 := by
  unfold tailWord_5689462
  simp only [CollatzResearch.WordTrace]
  refine ⟨12969482932128645724693415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 138341151276038887730063093 12969482932128645724693415)
  ·
    refine ⟨19454224398192968587040123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12969482932128645724693415 19454224398192968587040123)
    ·
      refine ⟨29181336597289452880560185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19454224398192968587040123 29181336597289452880560185)
      ·
        refine ⟨21886002447967089660420139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29181336597289452880560185 21886002447967089660420139)
        ·
          refine ⟨32829003671950634490630209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21886002447967089660420139 32829003671950634490630209)
          ·
            refine ⟨24621752753962975867972657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32829003671950634490630209 24621752753962975867972657)
            ·
              refine ⟨18466314565472231900979493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24621752753962975867972657 18466314565472231900979493)
              ·
                refine ⟨3462433981026043481433655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18466314565472231900979493 3462433981026043481433655)
                ·
                  refine ⟨5193650971539065222150483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3462433981026043481433655 5193650971539065222150483)
                  ·
                    refine ⟨7790476457308597833225725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5193650971539065222150483 7790476457308597833225725)
                    ·
                      refine ⟨2921428671490724187459647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7790476457308597833225725 2921428671490724187459647)
                      ·
                        rfl

theorem cell23_5689462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 4, 1, 1, 3].length) (baseStart_5689462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5689462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5689462 prefixEnd_5689462 := by exact prefixLift 5689462
  have htrace : WordTrace (prefixWord ++ tailWord_5689462) baseStart_5689462 baseEnd_5689462 := by
    simpa [prefixWord, tailWord_5689462, baseEnd_5689462] using wordTrace_append hprefix tailTrace_5689462
  have hstable : (prefixWord ++ tailWord_5689462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5689462).length < 2 ^ (prefixWord ++ tailWord_5689462).sum := by decide
  have hdescent : baseEnd_5689462 < baseStart_5689462 := by decide
  rcases family_descends (prefixWord ++ tailWord_5689462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5689464 : List Nat := [2, 1, 2, 1, 1, 1, 3, 4, 1, 1, 6]
def baseStart_5689464 : Nat := 118140960795 + 5689464 * 2 ^ 59
def prefixEnd_5689464 : Nat := 4983230072969 + 3 ^ 40 * 5689464 * 2
def baseEnd_5689464 : Nat := 2921429698452033179634637

theorem tailTrace_5689464 : CollatzResearch.WordTrace tailWord_5689464 prefixEnd_5689464 2921429698452033179634637 := by
  unfold tailWord_5689464
  simp only [CollatzResearch.WordTrace]
  refine ⟨103755899930025542968333723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138341199906700723957778297 103755899930025542968333723)
  ·
    refine ⟨155633849895038314452500585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103755899930025542968333723 155633849895038314452500585)
    ·
      refine ⟨116725387421278735839375439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155633849895038314452500585 116725387421278735839375439)
      ·
        refine ⟨175088081131918103759063159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116725387421278735839375439 175088081131918103759063159)
        ·
          refine ⟨262632121697877155638594739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175088081131918103759063159 262632121697877155638594739)
          ·
            refine ⟨393948182546815733457892109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 262632121697877155638594739 393948182546815733457892109)
            ·
              refine ⟨147730568455055900046709541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 393948182546815733457892109 147730568455055900046709541)
              ·
                refine ⟨27699481585322981258758039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 147730568455055900046709541 27699481585322981258758039)
                ·
                  refine ⟨41549222377984471888137059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27699481585322981258758039 41549222377984471888137059)
                  ·
                    refine ⟨62323833566976707832205589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41549222377984471888137059 62323833566976707832205589)
                    ·
                      refine ⟨2921429698452033179634637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 62323833566976707832205589 2921429698452033179634637)
                      ·
                        rfl

theorem cell23_5689464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 4, 1, 1, 6].length) (baseStart_5689464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5689464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5689464 prefixEnd_5689464 := by exact prefixLift 5689464
  have htrace : WordTrace (prefixWord ++ tailWord_5689464) baseStart_5689464 baseEnd_5689464 := by
    simpa [prefixWord, tailWord_5689464, baseEnd_5689464] using wordTrace_append hprefix tailTrace_5689464
  have hstable : (prefixWord ++ tailWord_5689464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5689464).length < 2 ^ (prefixWord ++ tailWord_5689464).sum := by decide
  have hdescent : baseEnd_5689464 < baseStart_5689464 := by decide
  rcases family_descends (prefixWord ++ tailWord_5689464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5689488 : List Nat := [2, 1, 1, 1, 1, 1, 8, 2, 1, 2, 3]
def baseStart_5689488 : Nat := 118140960795 + 5689488 * 2 ^ 59
def prefixEnd_5689488 : Nat := 4983230072969 + 3 ^ 40 * 5689488 * 2
def baseEnd_5689488 : Nat := 2921442021987741085734527

theorem tailTrace_5689488 : CollatzResearch.WordTrace tailWord_5689488 prefixEnd_5689488 2921442021987741085734527 := by
  unfold tailWord_5689488
  simp only [CollatzResearch.WordTrace]
  refine ⟨103756337605982069017770559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138341783474642758690360745 103756337605982069017770559)
  ·
    refine ⟨155634506408973103526655839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103756337605982069017770559 155634506408973103526655839)
    ·
      refine ⟨233451759613459655289983759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155634506408973103526655839 233451759613459655289983759)
      ·
        refine ⟨350177639420189482934975639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233451759613459655289983759 350177639420189482934975639)
        ·
          refine ⟨525266459130284224402463459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 350177639420189482934975639 525266459130284224402463459)
          ·
            refine ⟨787899688695426336603695189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 525266459130284224402463459 787899688695426336603695189)
            ·
              refine ⟨9233199476899527382074553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 787899688695426336603695189 9233199476899527382074553)
              ·
                refine ⟨6924899607674645536555915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9233199476899527382074553 6924899607674645536555915)
                ·
                  refine ⟨10387349411511968304833873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6924899607674645536555915 10387349411511968304833873)
                  ·
                    refine ⟨7790512058633976228625405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10387349411511968304833873 7790512058633976228625405)
                    ·
                      refine ⟨2921442021987741085734527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7790512058633976228625405 2921442021987741085734527)
                      ·
                        rfl

theorem cell23_5689488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 8, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 8, 2, 1, 2, 3].length) (baseStart_5689488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5689488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5689488 prefixEnd_5689488 := by exact prefixLift 5689488
  have htrace : WordTrace (prefixWord ++ tailWord_5689488) baseStart_5689488 baseEnd_5689488 := by
    simpa [prefixWord, tailWord_5689488, baseEnd_5689488] using wordTrace_append hprefix tailTrace_5689488
  have hstable : (prefixWord ++ tailWord_5689488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5689488).length < 2 ^ (prefixWord ++ tailWord_5689488).sum := by decide
  have hdescent : baseEnd_5689488 < baseStart_5689488 := by decide
  rcases family_descends (prefixWord ++ tailWord_5689488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5689508 : List Nat := [2, 3, 1, 2, 5, 1, 9]
def baseStart_5689508 : Nat := 118140960795 + 5689508 * 2 ^ 59
def prefixEnd_5689508 : Nat := 4983230072969 + 3 ^ 40 * 5689508 * 2
def baseEnd_5689508 : Nat := 36067312241985567993635

theorem tailTrace_5689508 : CollatzResearch.WordTrace tailWord_5689508 prefixEnd_5689508 36067312241985567993635 := by
  unfold tailWord_5689508
  simp only [CollatzResearch.WordTrace]
  refine ⟨103756702335945840725634589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138342269781261120967512785 103756702335945840725634589)
  ·
    refine ⟨38908763375979690272112971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 103756702335945840725634589 38908763375979690272112971)
    ·
      refine ⟨58363145063969535408169457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38908763375979690272112971 58363145063969535408169457)
      ·
        refine ⟨43772358797977151556127093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58363145063969535408169457 43772358797977151556127093)
        ·
          refine ⟨4103658637310357958386915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 43772358797977151556127093 4103658637310357958386915)
          ·
            refine ⟨6155487955965536937580373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4103658637310357958386915 6155487955965536937580373)
            ·
              refine ⟨36067312241985567993635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6155487955965536937580373 36067312241985567993635)
              ·
                rfl

theorem cell23_5689508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 9].length) (baseStart_5689508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5689508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5689508 prefixEnd_5689508 := by exact prefixLift 5689508
  have htrace : WordTrace (prefixWord ++ tailWord_5689508) baseStart_5689508 baseEnd_5689508 := by
    simpa [prefixWord, tailWord_5689508, baseEnd_5689508] using wordTrace_append hprefix tailTrace_5689508
  have hstable : (prefixWord ++ tailWord_5689508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5689508).length < 2 ^ (prefixWord ++ tailWord_5689508).sum := by decide
  have hdescent : baseEnd_5689508 < baseStart_5689508 := by decide
  rcases family_descends (prefixWord ++ tailWord_5689508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5689528 : List Nat := [2, 1, 2, 1, 2, 1, 4, 2, 3, 3, 2]
def baseStart_5689528 : Nat := 118140960795 + 5689528 * 2 ^ 59
def prefixEnd_5689528 : Nat := 4983230072969 + 3 ^ 40 * 5689528 * 2
def baseEnd_5689528 : Nat := 2921462561213920929234343

theorem tailTrace_5689528 : CollatzResearch.WordTrace tailWord_5689528 prefixEnd_5689528 2921462561213920929234343 := by
  unfold tailWord_5689528
  simp only [CollatzResearch.WordTrace]
  refine ⟨103757067065909612433498619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138342756087879483244664825 103757067065909612433498619)
  ·
    refine ⟨155635600598864418650247929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103757067065909612433498619 155635600598864418650247929)
    ·
      refine ⟨116726700449148313987685947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 155635600598864418650247929 116726700449148313987685947)
      ·
        refine ⟨175090050673722470981528921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 116726700449148313987685947 175090050673722470981528921)
        ·
          refine ⟨131317538005291853236146691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175090050673722470981528921 131317538005291853236146691)
          ·
            refine ⟨196976307007937779854220037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131317538005291853236146691 196976307007937779854220037)
            ·
              refine ⟨36933057563988333722666257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 196976307007937779854220037 36933057563988333722666257)
              ·
                refine ⟨27699793172991250291999693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36933057563988333722666257 27699793172991250291999693)
                ·
                  refine ⟨10387422439871718859499885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27699793172991250291999693 10387422439871718859499885)
                  ·
                    refine ⟨3895283414951894572312457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10387422439871718859499885 3895283414951894572312457)
                    ·
                      refine ⟨2921462561213920929234343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3895283414951894572312457 2921462561213920929234343)
                      ·
                        rfl

theorem cell23_5689528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 2, 3, 3, 2].length) (baseStart_5689528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5689528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5689528 prefixEnd_5689528 := by exact prefixLift 5689528
  have htrace : WordTrace (prefixWord ++ tailWord_5689528) baseStart_5689528 baseEnd_5689528 := by
    simpa [prefixWord, tailWord_5689528, baseEnd_5689528] using wordTrace_append hprefix tailTrace_5689528
  have hstable : (prefixWord ++ tailWord_5689528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5689528).length < 2 ^ (prefixWord ++ tailWord_5689528).sum := by decide
  have hdescent : baseEnd_5689528 < baseStart_5689528 := by decide
  rcases family_descends (prefixWord ++ tailWord_5689528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5689561 : List Nat := [1, 2, 1, 2, 3, 1, 4, 1, 2, 1, 5]
def baseStart_5689561 : Nat := 118140960795 + 5689561 * 2 ^ 59
def prefixEnd_5689561 : Nat := 4983230072969 + 3 ^ 40 * 5689561 * 2
def baseEnd_5689561 : Nat := 2921479506075519300121691

theorem tailTrace_5689561 : CollatzResearch.WordTrace tailWord_5689561 prefixEnd_5689561 2921479506075519300121691 := by
  unfold tailWord_5689561
  simp only [CollatzResearch.WordTrace]
  refine ⟨207515337740699671502948537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138343558493799781001965691 207515337740699671502948537)
  ·
    refine ⟨155636503305524753627211403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207515337740699671502948537 155636503305524753627211403)
    ·
      refine ⟨233454754958287130440817105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155636503305524753627211403 233454754958287130440817105)
      ·
        refine ⟨175091066218715347830612829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 233454754958287130440817105 175091066218715347830612829)
        ·
          refine ⟨65659149832018255436479811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 175091066218715347830612829 65659149832018255436479811)
          ·
            refine ⟨98488724748027383154719717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65659149832018255436479811 98488724748027383154719717)
            ·
              refine ⟨18466635890255134341509947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 98488724748027383154719717 18466635890255134341509947)
              ·
                refine ⟨27699953835382701512264921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18466635890255134341509947 27699953835382701512264921)
                ·
                  refine ⟨20774965376537026134198691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27699953835382701512264921 20774965376537026134198691)
                  ·
                    refine ⟨31162448064805539201298037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20774965376537026134198691 31162448064805539201298037)
                    ·
                      refine ⟨2921479506075519300121691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31162448064805539201298037 2921479506075519300121691)
                      ·
                        rfl

theorem cell23_5689561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 1, 2, 1, 5].length) (baseStart_5689561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5689561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5689561 prefixEnd_5689561 := by exact prefixLift 5689561
  have htrace : WordTrace (prefixWord ++ tailWord_5689561) baseStart_5689561 baseEnd_5689561 := by
    simpa [prefixWord, tailWord_5689561, baseEnd_5689561] using wordTrace_append hprefix tailTrace_5689561
  have hstable : (prefixWord ++ tailWord_5689561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5689561).length < 2 ^ (prefixWord ++ tailWord_5689561).sum := by decide
  have hdescent : baseEnd_5689561 < baseStart_5689561 := by decide
  rcases family_descends (prefixWord ++ tailWord_5689561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5689598 : List Nat := [4, 2, 2, 1, 1, 1, 3, 2, 7]
def baseStart_5689598 : Nat := 118140960795 + 5689598 * 2 ^ 59
def prefixEnd_5689598 : Nat := 4983230072969 + 3 ^ 40 * 5689598 * 2
def baseEnd_5689598 : Nat := 324610944984415072817669

theorem tailTrace_5689598 : CollatzResearch.WordTrace tailWord_5689598 prefixEnd_5689598 324610944984415072817669 := by
  unfold tailWord_5689598
  simp only [CollatzResearch.WordTrace]
  refine ⟨25939585905195703352755681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138344458161043751214696965 25939585905195703352755681)
  ·
    refine ⟨19454689428896777514566761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25939585905195703352755681 19454689428896777514566761)
    ·
      refine ⟨14591017071672583135925071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19454689428896777514566761 14591017071672583135925071)
      ·
        refine ⟨21886525607508874703887607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14591017071672583135925071 21886525607508874703887607)
        ·
          refine ⟨32829788411263312055831411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21886525607508874703887607 32829788411263312055831411)
          ·
            refine ⟨49244682616894968083747117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32829788411263312055831411 49244682616894968083747117)
            ·
              refine ⟨18466755981335613031405169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49244682616894968083747117 18466755981335613031405169)
              ·
                refine ⟨13850066986001709773553877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18466755981335613031405169 13850066986001709773553877)
                ·
                  refine ⟨324610944984415072817669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13850066986001709773553877 324610944984415072817669)
                  ·
                    rfl

theorem cell23_5689598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 2, 7].length) (baseStart_5689598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5689598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5689598 prefixEnd_5689598 := by exact prefixLift 5689598
  have htrace : WordTrace (prefixWord ++ tailWord_5689598) baseStart_5689598 baseEnd_5689598 := by
    simpa [prefixWord, tailWord_5689598, baseEnd_5689598] using wordTrace_append hprefix tailTrace_5689598
  have hstable : (prefixWord ++ tailWord_5689598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5689598).length < 2 ^ (prefixWord ++ tailWord_5689598).sum := by decide
  have hdescent : baseEnd_5689598 < baseStart_5689598 := by decide
  rcases family_descends (prefixWord ++ tailWord_5689598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5689611 : List Nat := [1, 1, 1, 1, 5, 2, 3, 1, 1, 7]
def baseStart_5689611 : Nat := 118140960795 + 5689611 * 2 ^ 59
def prefixEnd_5689611 : Nat := 4983230072969 + 3 ^ 40 * 5689611 * 2
def baseEnd_5689611 : Nat := 973835060036081368165487

theorem tailTrace_5689611 : CollatzResearch.WordTrace tailWord_5689611 prefixEnd_5689611 973835060036081368165487 := by
  unfold tailWord_5689611
  simp only [CollatzResearch.WordTrace]
  refine ⟨207517161390518530042268687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138344774260345686694845791 207517161390518530042268687)
  ·
    refine ⟨311275742085777795063403031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207517161390518530042268687 311275742085777795063403031)
    ·
      refine ⟨466913613128666692595104547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 311275742085777795063403031 466913613128666692595104547)
      ·
        refine ⟨700370419693000038892656821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 466913613128666692595104547 700370419693000038892656821)
        ·
          refine ⟨65659726846218753646186577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 700370419693000038892656821 65659726846218753646186577)
          ·
            refine ⟨49244795134664065234639933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65659726846218753646186577 49244795134664065234639933)
            ·
              refine ⟨18466798175499024462989975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49244795134664065234639933 18466798175499024462989975)
              ·
                refine ⟨27700197263248536694484963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18466798175499024462989975 27700197263248536694484963)
                ·
                  refine ⟨41550295894872805041727445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27700197263248536694484963 41550295894872805041727445)
                  ·
                    refine ⟨973835060036081368165487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41550295894872805041727445 973835060036081368165487)
                    ·
                      rfl

theorem cell23_5689611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 1, 1, 7].length) (baseStart_5689611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5689611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5689611 prefixEnd_5689611 := by exact prefixLift 5689611
  have htrace : WordTrace (prefixWord ++ tailWord_5689611) baseStart_5689611 baseEnd_5689611 := by
    simpa [prefixWord, tailWord_5689611, baseEnd_5689611] using wordTrace_append hprefix tailTrace_5689611
  have hstable : (prefixWord ++ tailWord_5689611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5689611).length < 2 ^ (prefixWord ++ tailWord_5689611).sum := by decide
  have hdescent : baseEnd_5689611 < baseStart_5689611 := by decide
  rcases family_descends (prefixWord ++ tailWord_5689611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5689621 : List Nat := [1, 3, 2, 1, 2, 1, 2, 1, 3, 2, 5]
def baseStart_5689621 : Nat := 118140960795 + 5689621 * 2 ^ 59
def prefixEnd_5689621 : Nat := 4983230072969 + 3 ^ 40 * 5689621 * 2
def baseEnd_5689621 : Nat := 2921510314914789065371415

theorem tailTrace_5689621 : CollatzResearch.WordTrace tailWord_5689621 prefixEnd_5689621 2921510314914789065371415 := by
  unfold tailWord_5689621
  simp only [CollatzResearch.WordTrace]
  refine ⟨207517526120482301750132717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138345017413654867833421811 207517526120482301750132717)
  ·
    refine ⟨77819072295180863156299769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 207517526120482301750132717 77819072295180863156299769)
    ·
      refine ⟨58364304221385647367224827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77819072295180863156299769 58364304221385647367224827)
      ·
        refine ⟨87546456332078471050837241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58364304221385647367224827 87546456332078471050837241)
        ·
          refine ⟨65659842249058853288127931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87546456332078471050837241 65659842249058853288127931)
          ·
            refine ⟨98489763373588279932191897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65659842249058853288127931 98489763373588279932191897)
            ·
              refine ⟨73867322530191209949143923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98489763373588279932191897 73867322530191209949143923)
              ·
                refine ⟨110800983795286814923715885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73867322530191209949143923 110800983795286814923715885)
                ·
                  refine ⟨41550368923232555596393457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 110800983795286814923715885 41550368923232555596393457)
                  ·
                    refine ⟨31162776692424416697295093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41550368923232555596393457 31162776692424416697295093)
                    ·
                      refine ⟨2921510314914789065371415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31162776692424416697295093 2921510314914789065371415)
                      ·
                        rfl

theorem cell23_5689621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 3, 2, 5].length) (baseStart_5689621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5689621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5689621 prefixEnd_5689621 := by exact prefixLift 5689621
  have htrace : WordTrace (prefixWord ++ tailWord_5689621) baseStart_5689621 baseEnd_5689621 := by
    simpa [prefixWord, tailWord_5689621, baseEnd_5689621] using wordTrace_append hprefix tailTrace_5689621
  have hstable : (prefixWord ++ tailWord_5689621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5689621).length < 2 ^ (prefixWord ++ tailWord_5689621).sum := by decide
  have hdescent : baseEnd_5689621 < baseStart_5689621 := by decide
  rcases family_descends (prefixWord ++ tailWord_5689621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5689626 : List Nat := [3, 1, 1, 3, 5, 1, 1, 2, 2, 2, 2]
def baseStart_5689626 : Nat := 118140960795 + 5689626 * 2 ^ 59
def prefixEnd_5689626 : Nat := 4983230072969 + 3 ^ 40 * 5689626 * 2
def baseEnd_5689626 : Nat := 2921512882318061545808893

theorem tailTrace_5689626 : CollatzResearch.WordTrace tailWord_5689626 prefixEnd_5689626 2921512882318061545808893 := by
  unfold tailWord_5689626
  simp only [CollatzResearch.WordTrace]
  refine ⟨51879427121366046901016183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 138345138990309458402709821 51879427121366046901016183)
  ·
    refine ⟨77819140682049070351524275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51879427121366046901016183 77819140682049070351524275)
    ·
      refine ⟨116728711023073605527286413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77819140682049070351524275 116728711023073605527286413)
      ·
        refine ⟨43773266633652602072732405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 116728711023073605527286413 43773266633652602072732405)
        ·
          refine ⟨4103743746904931444318663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 43773266633652602072732405 4103743746904931444318663)
          ·
            refine ⟨6155615620357397166477995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4103743746904931444318663 6155615620357397166477995)
            ·
              refine ⟨9233423430536095749716993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6155615620357397166477995 9233423430536095749716993)
              ·
                refine ⟨6925067572902071812287745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9233423430536095749716993 6925067572902071812287745)
                ·
                  refine ⟨5193800679676553859215809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6925067572902071812287745 5193800679676553859215809)
                  ·
                    refine ⟨3895350509757415394411857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5193800679676553859215809 3895350509757415394411857)
                    ·
                      refine ⟨2921512882318061545808893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3895350509757415394411857 2921512882318061545808893)
                      ·
                        rfl

theorem cell23_5689626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 1, 2, 2, 2, 2].length) (baseStart_5689626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5689626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5689626 prefixEnd_5689626 := by exact prefixLift 5689626
  have htrace : WordTrace (prefixWord ++ tailWord_5689626) baseStart_5689626 baseEnd_5689626 := by
    simpa [prefixWord, tailWord_5689626, baseEnd_5689626] using wordTrace_append hprefix tailTrace_5689626
  have hstable : (prefixWord ++ tailWord_5689626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5689626).length < 2 ^ (prefixWord ++ tailWord_5689626).sum := by decide
  have hdescent : baseEnd_5689626 < baseStart_5689626 := by decide
  rcases family_descends (prefixWord ++ tailWord_5689626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5689648 : List Nat := [2, 1, 1, 1, 2, 2, 2, 3, 1, 6, 2]
def baseStart_5689648 : Nat := 118140960795 + 5689648 * 2 ^ 59
def prefixEnd_5689648 : Nat := 4983230072969 + 3 ^ 40 * 5689648 * 2
def baseEnd_5689648 : Nat := 2921524178892460459733791

theorem tailTrace_5689648 : CollatzResearch.WordTrace tailWord_5689648 prefixEnd_5689648 2921524178892460459733791 := by
  unfold tailWord_5689648
  simp only [CollatzResearch.WordTrace]
  refine ⟨103759255445692242680682799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 138345673927589656907577065 103759255445692242680682799)
  ·
    refine ⟨155638883168538364021024199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 103759255445692242680682799 155638883168538364021024199)
    ·
      refine ⟨233458324752807546031536299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155638883168538364021024199 233458324752807546031536299)
      ·
        refine ⟨350187487129211319047304449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233458324752807546031536299 350187487129211319047304449)
        ·
          refine ⟨262640615346908489285478337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 350187487129211319047304449 262640615346908489285478337)
          ·
            refine ⟨196980461510181366964108753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 262640615346908489285478337 196980461510181366964108753)
            ·
              refine ⟨147735346132636025223081565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 196980461510181366964108753 147735346132636025223081565)
              ·
                refine ⟨55400754799738509458655587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 147735346132636025223081565 55400754799738509458655587)
                ·
                  refine ⟨83101132199607764187983381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55400754799738509458655587 83101132199607764187983381)
                  ·
                    refine ⟨3895365571856613946311721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 83101132199607764187983381 3895365571856613946311721)
                    ·
                      refine ⟨2921524178892460459733791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3895365571856613946311721 2921524178892460459733791)
                      ·
                        rfl

theorem cell23_5689648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 3, 1, 6, 2].length) (baseStart_5689648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5689648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5689648 prefixEnd_5689648 := by exact prefixLift 5689648
  have htrace : WordTrace (prefixWord ++ tailWord_5689648) baseStart_5689648 baseEnd_5689648 := by
    simpa [prefixWord, tailWord_5689648, baseEnd_5689648] using wordTrace_append hprefix tailTrace_5689648
  have hstable : (prefixWord ++ tailWord_5689648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5689648).length < 2 ^ (prefixWord ++ tailWord_5689648).sum := by decide
  have hdescent : baseEnd_5689648 < baseStart_5689648 := by decide
  rcases family_descends (prefixWord ++ tailWord_5689648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5689671 : List Nat := [1, 1, 4, 1, 2, 2, 1, 1, 10]
def baseStart_5689671 : Nat := 118140960795 + 5689671 * 2 ^ 59
def prefixEnd_5689671 : Nat := 4983230072969 + 3 ^ 40 * 5689671 * 2
def baseEnd_5689671 : Nat := 324615109883057096638465

theorem tailTrace_5689671 : CollatzResearch.WordTrace tailWord_5689671 prefixEnd_5689671 324615109883057096638465 := by
  unfold tailWord_5689671
  simp only [CollatzResearch.WordTrace]
  refine ⟨207519349770301160289452867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138346233180200773526301911 207519349770301160289452867)
  ·
    refine ⟨311279024655451740434179301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207519349770301160289452867 311279024655451740434179301)
    ·
      refine ⟨58364817122897201331408619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 311279024655451740434179301 58364817122897201331408619)
      ·
        refine ⟨87547225684345801997112929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58364817122897201331408619 87547225684345801997112929)
        ·
          refine ⟨65660419263259351497834697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87547225684345801997112929 65660419263259351497834697)
          ·
            refine ⟨49245314447444513623376023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65660419263259351497834697 49245314447444513623376023)
            ·
              refine ⟨73867971671166770435064035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49245314447444513623376023 73867971671166770435064035)
              ·
                refine ⟨110801957506750155652596053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 73867971671166770435064035 110801957506750155652596053)
                ·
                  refine ⟨324615109883057096638465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 110801957506750155652596053 324615109883057096638465)
                  ·
                    rfl

theorem cell23_5689671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 10].length) (baseStart_5689671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5689671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5689671 prefixEnd_5689671 := by exact prefixLift 5689671
  have htrace : WordTrace (prefixWord ++ tailWord_5689671) baseStart_5689671 baseEnd_5689671 := by
    simpa [prefixWord, tailWord_5689671, baseEnd_5689671] using wordTrace_append hprefix tailTrace_5689671
  have hstable : (prefixWord ++ tailWord_5689671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5689671).length < 2 ^ (prefixWord ++ tailWord_5689671).sum := by decide
  have hdescent : baseEnd_5689671 < baseStart_5689671 := by decide
  rcases family_descends (prefixWord ++ tailWord_5689671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5689675 : List Nat := [1, 1, 1, 1, 3, 1, 1, 9, 1, 4]
def baseStart_5689675 : Nat := 118140960795 + 5689675 * 2 ^ 59
def prefixEnd_5689675 : Nat := 4983230072969 + 3 ^ 40 * 5689675 * 2
def baseEnd_5689675 : Nat := 973846014290043951365389

theorem tailTrace_5689675 : CollatzResearch.WordTrace tailWord_5689675 prefixEnd_5689675 973846014290043951365389 := by
  unfold tailWord_5689675
  simp only [CollatzResearch.WordTrace]
  refine ⟨207519495662286668972598479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138346330441524445981732319 207519495662286668972598479)
  ·
    refine ⟨311279243493430003458897719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207519495662286668972598479 311279243493430003458897719)
    ·
      refine ⟨466918865240145005188346579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 311279243493430003458897719 466918865240145005188346579)
      ·
        refine ⟨700378297860217507782519869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 466918865240145005188346579 700378297860217507782519869)
        ·
          refine ⟨262641861697581565418444951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 700378297860217507782519869 262641861697581565418444951)
          ·
            refine ⟨393962792546372348127667427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 262641861697581565418444951 393962792546372348127667427)
            ·
              refine ⟨590944188819558522191501141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 393962792546372348127667427 590944188819558522191501141)
              ·
                refine ⟨3462563606364600715965827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 590944188819558522191501141 3462563606364600715965827)
                ·
                  refine ⟨5193845409546901073948741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3462563606364600715965827 5193845409546901073948741)
                  ·
                    refine ⟨973846014290043951365389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5193845409546901073948741 973846014290043951365389)
                    ·
                      rfl

theorem cell23_5689675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 9, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 9, 1, 4].length) (baseStart_5689675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5689675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5689675 prefixEnd_5689675 := by exact prefixLift 5689675
  have htrace : WordTrace (prefixWord ++ tailWord_5689675) baseStart_5689675 baseEnd_5689675 := by
    simpa [prefixWord, tailWord_5689675, baseEnd_5689675] using wordTrace_append hprefix tailTrace_5689675
  have hstable : (prefixWord ++ tailWord_5689675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5689675).length < 2 ^ (prefixWord ++ tailWord_5689675).sum := by decide
  have hdescent : baseEnd_5689675 < baseStart_5689675 := by decide
  rcases family_descends (prefixWord ++ tailWord_5689675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5689694 : List Nat := [4, 4, 2, 1, 2, 1, 2, 1, 2, 2, 2]
def baseStart_5689694 : Nat := 118140960795 + 5689694 * 2 ^ 59
def prefixEnd_5689694 : Nat := 4983230072969 + 3 ^ 40 * 5689694 * 2
def baseEnd_5689694 : Nat := 2921547799002567279758581

theorem tailTrace_5689694 : CollatzResearch.WordTrace tailWord_5689694 prefixEnd_5689694 2921547799002567279758581 := by
  unfold tailWord_5689694
  simp only [CollatzResearch.WordTrace]
  refine ⟨25940023581152229402192517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 138346792432811890145026757 25940023581152229402192517)
  ·
    refine ⟨4863754421466043012911097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25940023581152229402192517 4863754421466043012911097)
    ·
      refine ⟨3647815816099532259683323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4863754421466043012911097 3647815816099532259683323)
      ·
        refine ⟨5471723724149298389524985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3647815816099532259683323 5471723724149298389524985)
        ·
          refine ⟨4103792793111973792143739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5471723724149298389524985 4103792793111973792143739)
          ·
            refine ⟨6155689189667960688215609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4103792793111973792143739 6155689189667960688215609)
            ·
              refine ⟨4616766892250970516161707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6155689189667960688215609 4616766892250970516161707)
              ·
                refine ⟨6925150338376455774242561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4616766892250970516161707 6925150338376455774242561)
                ·
                  refine ⟨5193862753782341830681921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6925150338376455774242561 5193862753782341830681921)
                  ·
                    refine ⟨3895397065336756373011441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5193862753782341830681921 3895397065336756373011441)
                    ·
                      refine ⟨2921547799002567279758581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3895397065336756373011441 2921547799002567279758581)
                      ·
                        rfl

theorem cell23_5689694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_5689694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5689694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5689694 prefixEnd_5689694 := by exact prefixLift 5689694
  have htrace : WordTrace (prefixWord ++ tailWord_5689694) baseStart_5689694 baseEnd_5689694 := by
    simpa [prefixWord, tailWord_5689694, baseEnd_5689694] using wordTrace_append hprefix tailTrace_5689694
  have hstable : (prefixWord ++ tailWord_5689694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5689694).length < 2 ^ (prefixWord ++ tailWord_5689694).sum := by decide
  have hdescent : baseEnd_5689694 < baseStart_5689694 := by decide
  rcases family_descends (prefixWord ++ tailWord_5689694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5689711 : List Nat := [1, 1, 2, 1, 3, 1, 2, 1, 1, 3, 7]
def baseStart_5689711 : Nat := 118140960795 + 5689711 * 2 ^ 59
def prefixEnd_5689711 : Nat := 4983230072969 + 3 ^ 40 * 5689711 * 2
def baseEnd_5689711 : Nat := 2921556528173693713246001

theorem tailTrace_5689711 : CollatzResearch.WordTrace tailWord_5689711 prefixEnd_5689711 2921556528173693713246001 := by
  unfold tailWord_5689711
  simp only [CollatzResearch.WordTrace]
  refine ⟨207520808690156247120908987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138347205793437498080605991 207520808690156247120908987)
  ·
    refine ⟨311281213035234370681363481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 207520808690156247120908987 311281213035234370681363481)
    ·
      refine ⟨233460909776425778011022611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 311281213035234370681363481 233460909776425778011022611)
      ·
        refine ⟨350191364664638667016533917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233460909776425778011022611 350191364664638667016533917)
        ·
          refine ⟨131321761749239500131200219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 350191364664638667016533917 131321761749239500131200219)
          ·
            refine ⟨196982642623859250196800329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131321761749239500131200219 196982642623859250196800329)
            ·
              refine ⟨147736981967894437647600247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 196982642623859250196800329 147736981967894437647600247)
              ·
                refine ⟨221605472951841656471400371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 147736981967894437647600247 221605472951841656471400371)
                ·
                  refine ⟨332408209427762484707100557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 221605472951841656471400371 332408209427762484707100557)
                  ·
                    refine ⟨124653078535410931765162709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 332408209427762484707100557 124653078535410931765162709)
                    ·
                      refine ⟨2921556528173693713246001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 124653078535410931765162709 2921556528173693713246001)
                      ·
                        rfl

theorem cell23_5689711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 3, 7].length) (baseStart_5689711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5689711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5689711 prefixEnd_5689711 := by exact prefixLift 5689711
  have htrace : WordTrace (prefixWord ++ tailWord_5689711) baseStart_5689711 baseEnd_5689711 := by
    simpa [prefixWord, tailWord_5689711, baseEnd_5689711] using wordTrace_append hprefix tailTrace_5689711
  have hstable : (prefixWord ++ tailWord_5689711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5689711).length < 2 ^ (prefixWord ++ tailWord_5689711).sum := by decide
  have hdescent : baseEnd_5689711 < baseStart_5689711 := by decide
  rcases family_descends (prefixWord ++ tailWord_5689711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5689765 : List Nat := [1, 3, 1, 2, 1, 1, 3, 5, 2, 4]
def baseStart_5689765 : Nat := 118140960795 + 5689765 * 2 ^ 59
def prefixEnd_5689765 : Nat := 4983230072969 + 3 ^ 40 * 5689765 * 2
def baseEnd_5689765 : Nat := 973861418709678833990251

theorem tailTrace_5689765 : CollatzResearch.WordTrace tailWord_5689765 prefixEnd_5689765 973861418709678833990251 := by
  unfold tailWord_5689765
  simp only [CollatzResearch.WordTrace]
  refine ⟨207522778231960614343374749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138348518821307076228916499 207522778231960614343374749)
  ·
    refine ⟨77821041836985230378765531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 207522778231960614343374749 77821041836985230378765531)
    ·
      refine ⟨116731562755477845568148297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77821041836985230378765531 116731562755477845568148297)
      ·
        refine ⟨87548672066608384176111223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 116731562755477845568148297 87548672066608384176111223)
        ·
          refine ⟨131323008099912576264166835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87548672066608384176111223 131323008099912576264166835)
          ·
            refine ⟨196984512149868864396250253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131323008099912576264166835 196984512149868864396250253)
            ·
              refine ⟨73869192056200824148593845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 196984512149868864396250253 73869192056200824148593845)
              ·
                refine ⟨6925236755268827263930673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 73869192056200824148593845 6925236755268827263930673)
                ·
                  refine ⟨5193927566451620447948005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6925236755268827263930673 5193927566451620447948005)
                  ·
                    refine ⟨973861418709678833990251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5193927566451620447948005 973861418709678833990251)
                    ·
                      rfl

theorem cell23_5689765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 5, 2, 4].length) (baseStart_5689765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5689765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5689765 prefixEnd_5689765 := by exact prefixLift 5689765
  have htrace : WordTrace (prefixWord ++ tailWord_5689765) baseStart_5689765 baseEnd_5689765 := by
    simpa [prefixWord, tailWord_5689765, baseEnd_5689765] using wordTrace_append hprefix tailTrace_5689765
  have hstable : (prefixWord ++ tailWord_5689765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5689765).length < 2 ^ (prefixWord ++ tailWord_5689765).sum := by decide
  have hdescent : baseEnd_5689765 < baseStart_5689765 := by decide
  rcases family_descends (prefixWord ++ tailWord_5689765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5689785 : List Nat := [1, 2, 1, 4, 3, 1, 2, 2, 1, 2, 4]
def baseStart_5689785 : Nat := 118140960795 + 5689785 * 2 ^ 59
def prefixEnd_5689785 : Nat := 4983230072969 + 3 ^ 40 * 5689785 * 2
def baseEnd_5689785 : Nat := 2921594525742126423720661

theorem tailTrace_5689785 : CollatzResearch.WordTrace tailWord_5689785 prefixEnd_5689785 2921594525742126423720661 := by
  unfold tailWord_5689785
  simp only [CollatzResearch.WordTrace]
  refine ⟨207523507691888157759102809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138349005127925438506068539 207523507691888157759102809)
  ·
    refine ⟨155642630768916118319327107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 207523507691888157759102809 155642630768916118319327107)
    ·
      refine ⟨233463946153374177478990661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 155642630768916118319327107 233463946153374177478990661)
      ·
        refine ⟨43774489903757658277310749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 233463946153374177478990661 43774489903757658277310749)
        ·
          refine ⟨16415433713909121853991531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43774489903757658277310749 16415433713909121853991531)
          ·
            refine ⟨24623150570863682780987297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16415433713909121853991531 24623150570863682780987297)
            ·
              refine ⟨18467362928147762085740473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24623150570863682780987297 18467362928147762085740473)
              ·
                refine ⟨13850522196110821564305355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18467362928147762085740473 13850522196110821564305355)
                ·
                  refine ⟨20775783294166232346458033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13850522196110821564305355 20775783294166232346458033)
                  ·
                    refine ⟨15581837470624674259843525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20775783294166232346458033 15581837470624674259843525)
                    ·
                      refine ⟨2921594525742126423720661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15581837470624674259843525 2921594525742126423720661)
                      ·
                        rfl

theorem cell23_5689785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 2, 1, 2, 4].length) (baseStart_5689785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5689785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5689785 prefixEnd_5689785 := by exact prefixLift 5689785
  have htrace : WordTrace (prefixWord ++ tailWord_5689785) baseStart_5689785 baseEnd_5689785 := by
    simpa [prefixWord, tailWord_5689785, baseEnd_5689785] using wordTrace_append hprefix tailTrace_5689785
  have hstable : (prefixWord ++ tailWord_5689785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5689785).length < 2 ^ (prefixWord ++ tailWord_5689785).sum := by decide
  have hdescent : baseEnd_5689785 < baseStart_5689785 := by decide
  rcases family_descends (prefixWord ++ tailWord_5689785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5689789 : List Nat := [1, 4, 1, 2, 2, 4, 2, 1, 1, 1, 4]
def baseStart_5689789 : Nat := 118140960795 + 5689789 * 2 ^ 59
def prefixEnd_5689789 : Nat := 4983230072969 + 3 ^ 40 * 5689789 * 2
def baseEnd_5689789 : Nat := 2921596579664744408070643

theorem tailTrace_5689789 : CollatzResearch.WordTrace tailWord_5689789 prefixEnd_5689789 2921596579664744408070643 := by
  unfold tailWord_5689789
  simp only [CollatzResearch.WordTrace]
  refine ⟨207523653583873666442248421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138349102389249110961498947 207523653583873666442248421)
  ·
    refine ⟨38910685046976312457921579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 207523653583873666442248421 38910685046976312457921579)
    ·
      refine ⟨58366027570464468686882369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38910685046976312457921579 58366027570464468686882369)
      ·
        refine ⟨43774520677848351515161777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58366027570464468686882369 43774520677848351515161777)
        ·
          refine ⟨32830890508386263636371333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43774520677848351515161777 32830890508386263636371333)
          ·
            refine ⟨6155791970322424431819625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32830890508386263636371333 6155791970322424431819625)
            ·
              refine ⟨4616843977741818323864719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6155791970322424431819625 4616843977741818323864719)
              ·
                refine ⟨6925265966612727485797079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4616843977741818323864719 6925265966612727485797079)
                ·
                  refine ⟨10387898949919091228695619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6925265966612727485797079 10387898949919091228695619)
                  ·
                    refine ⟨15581848424878636843043429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10387898949919091228695619 15581848424878636843043429)
                    ·
                      refine ⟨2921596579664744408070643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15581848424878636843043429 2921596579664744408070643)
                      ·
                        rfl

theorem cell23_5689789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 2, 1, 1, 1, 4].length) (baseStart_5689789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5689789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5689789 prefixEnd_5689789 := by exact prefixLift 5689789
  have htrace : WordTrace (prefixWord ++ tailWord_5689789) baseStart_5689789 baseEnd_5689789 := by
    simpa [prefixWord, tailWord_5689789, baseEnd_5689789] using wordTrace_append hprefix tailTrace_5689789
  have hstable : (prefixWord ++ tailWord_5689789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5689789).length < 2 ^ (prefixWord ++ tailWord_5689789).sum := by decide
  have hdescent : baseEnd_5689789 < baseStart_5689789 := by decide
  rcases family_descends (prefixWord ++ tailWord_5689789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5689829 : List Nat := [1, 3, 1, 5, 3, 1, 2, 7]
def baseStart_5689829 : Nat := 118140960795 + 5689829 * 2 ^ 59
def prefixEnd_5689829 : Nat := 4983230072969 + 3 ^ 40 * 5689829 * 2
def baseEnd_5689829 : Nat := 108208041440404601910017

theorem tailTrace_5689829 : CollatzResearch.WordTrace tailWord_5689829 prefixEnd_5689829 108208041440404601910017 := by
  unfold tailWord_5689829
  simp only [CollatzResearch.WordTrace]
  refine ⟨207525112503728753273704541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 138350075002485835515803027 207525112503728753273704541)
  ·
    refine ⟨77821917188898282477639203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 207525112503728753273704541 77821917188898282477639203)
    ·
      refine ⟨116732875783347423716458805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 77821917188898282477639203 116732875783347423716458805)
      ·
        refine ⟨10943707104688820973418013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 116732875783347423716458805 10943707104688820973418013)
        ·
          refine ⟨4103890164258307865031755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10943707104688820973418013 4103890164258307865031755)
          ·
            refine ⟨6155835246387461797547633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4103890164258307865031755 6155835246387461797547633)
            ·
              refine ⟨4616876434790596348160725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6155835246387461797547633 4616876434790596348160725)
              ·
                refine ⟨108208041440404601910017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4616876434790596348160725 108208041440404601910017)
                ·
                  rfl

theorem cell23_5689829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 2, 7].length) (baseStart_5689829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5689829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5689829 prefixEnd_5689829 := by exact prefixLift 5689829
  have htrace : WordTrace (prefixWord ++ tailWord_5689829) baseStart_5689829 baseEnd_5689829 := by
    simpa [prefixWord, tailWord_5689829, baseEnd_5689829] using wordTrace_append hprefix tailTrace_5689829
  have hstable : (prefixWord ++ tailWord_5689829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5689829).length < 2 ^ (prefixWord ++ tailWord_5689829).sum := by decide
  have hdescent : baseEnd_5689829 < baseStart_5689829 := by decide
  rcases family_descends (prefixWord ++ tailWord_5689829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
