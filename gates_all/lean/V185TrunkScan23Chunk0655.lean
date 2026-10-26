import V185TrunkScan23Chunk0654

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3873027 : List Nat := [1, 1, 1, 3, 2, 3, 1, 3, 4, 1, 3]
def baseStart_3873027 : Nat := 118140960795 + 3873027 * 2 ^ 59
def prefixEnd_3873027 : Nat := 4983230072969 + 3 ^ 40 * 3873027 * 2
def baseEnd_3873027 : Nat := 1988724438841123497750779

theorem tailTrace_3873027 : CollatzResearch.WordTrace tailWord_3873027 prefixEnd_3873027 1988724438841123497750779 := by
  unfold tailWord_3873027
  simp only [CollatzResearch.WordTrace]
  refine ⟨141260899739692114195161335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94173933159794742796774223 141260899739692114195161335)
  ·
    refine ⟨211891349609538171292742003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141260899739692114195161335 211891349609538171292742003)
    ·
      refine ⟨317837024414307256939113005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211891349609538171292742003 317837024414307256939113005)
      ·
        refine ⟨119188884155365221352167377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 317837024414307256939113005 119188884155365221352167377)
        ·
          refine ⟨89391663116523916014125533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119188884155365221352167377 89391663116523916014125533)
          ·
            refine ⟨33521873668696468505297075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89391663116523916014125533 33521873668696468505297075)
            ·
              refine ⟨50282810503044702757945613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33521873668696468505297075 50282810503044702757945613)
              ·
                refine ⟨18856053938641763534229605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50282810503044702757945613 18856053938641763534229605)
                ·
                  refine ⟨3535510113495330662668051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18856053938641763534229605 3535510113495330662668051)
                  ·
                    refine ⟨5303265170242995994002077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3535510113495330662668051 5303265170242995994002077)
                    ·
                      refine ⟨1988724438841123497750779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5303265170242995994002077 1988724438841123497750779)
                      ·
                        rfl

theorem cell23_3873027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 3, 4, 1, 3].length) (baseStart_3873027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3873027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3873027 prefixEnd_3873027 := by exact prefixLift 3873027
  have htrace : WordTrace (prefixWord ++ tailWord_3873027) baseStart_3873027 baseEnd_3873027 := by
    simpa [prefixWord, tailWord_3873027, baseEnd_3873027] using wordTrace_append hprefix tailTrace_3873027
  have hstable : (prefixWord ++ tailWord_3873027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3873027).length < 2 ^ (prefixWord ++ tailWord_3873027).sum := by decide
  have hdescent : baseEnd_3873027 < baseStart_3873027 := by decide
  rcases family_descends (prefixWord ++ tailWord_3873027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3873028 : List Nat := [2, 3, 2, 2, 3, 2, 1, 1, 3, 2, 2]
def baseStart_3873028 : Nat := 118140960795 + 3873028 * 2 ^ 59
def prefixEnd_3873028 : Nat := 4983230072969 + 3 ^ 40 * 3873028 * 2
def baseEnd_3873028 : Nat := 1988724952321777993838275

theorem tailTrace_3873028 : CollatzResearch.WordTrace tailWord_3873028 prefixEnd_3873028 1988724952321777993838275 := by
  unfold tailWord_3873028
  simp only [CollatzResearch.WordTrace]
  refine ⟨70630468106344245682973869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94173957475125660910631825 70630468106344245682973869)
  ·
    refine ⟨26486425539879092131115201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70630468106344245682973869 26486425539879092131115201)
    ·
      refine ⟨19864819154909319098336401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26486425539879092131115201 19864819154909319098336401)
      ·
        refine ⟨14898614366181989323752301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19864819154909319098336401 14898614366181989323752301)
        ·
          refine ⟨5586980387318245996407113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14898614366181989323752301 5586980387318245996407113)
          ·
            refine ⟨4190235290488684497305335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5586980387318245996407113 4190235290488684497305335)
            ·
              refine ⟨6285352935733026745958003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4190235290488684497305335 6285352935733026745958003)
              ·
                refine ⟨9428029403599540118937005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6285352935733026745958003 9428029403599540118937005)
                ·
                  refine ⟨3535511026349827544601377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9428029403599540118937005 3535511026349827544601377)
                  ·
                    refine ⟨2651633269762370658451033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3535511026349827544601377 2651633269762370658451033)
                    ·
                      refine ⟨1988724952321777993838275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2651633269762370658451033 1988724952321777993838275)
                      ·
                        rfl

theorem cell23_3873028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 1, 1, 3, 2, 2].length) (baseStart_3873028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3873028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3873028 prefixEnd_3873028 := by exact prefixLift 3873028
  have htrace : WordTrace (prefixWord ++ tailWord_3873028) baseStart_3873028 baseEnd_3873028 := by
    simpa [prefixWord, tailWord_3873028, baseEnd_3873028] using wordTrace_append hprefix tailTrace_3873028
  have hstable : (prefixWord ++ tailWord_3873028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3873028).length < 2 ^ (prefixWord ++ tailWord_3873028).sum := by decide
  have hdescent : baseEnd_3873028 < baseStart_3873028 := by decide
  rcases family_descends (prefixWord ++ tailWord_3873028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3873124 : List Nat := [2, 3, 1, 1, 3, 1, 4, 3, 5]
def baseStart_3873124 : Nat := 118140960795 + 3873124 * 2 ^ 59
def prefixEnd_3873124 : Nat := 4983230072969 + 3 ^ 40 * 3873124 * 2
def baseEnd_3873124 : Nat := 220974916273845513137537

theorem tailTrace_3873124 : CollatzResearch.WordTrace tailWord_3873124 prefixEnd_3873124 220974916273845513137537 := by
  unfold tailWord_3873124
  simp only [CollatzResearch.WordTrace]
  refine ⟨70632218810170349880721213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94176291746893799840961617 70632218810170349880721213)
  ·
    refine ⟨26487082053813881205270455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70632218810170349880721213 26487082053813881205270455)
    ·
      refine ⟨39730623080720821807905683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26487082053813881205270455 39730623080720821807905683)
      ·
        refine ⟨59595934621081232711858525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39730623080720821807905683 59595934621081232711858525)
        ·
          refine ⟨22348475482905462266946947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59595934621081232711858525 22348475482905462266946947)
          ·
            refine ⟨33522713224358193400420421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22348475482905462266946947 33522713224358193400420421)
            ·
              refine ⟨6285508729567161262578829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33522713224358193400420421 6285508729567161262578829)
              ·
                refine ⟨2357065773587685473467061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6285508729567161262578829 2357065773587685473467061)
                ·
                  refine ⟨220974916273845513137537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2357065773587685473467061 220974916273845513137537)
                  ·
                    rfl

theorem cell23_3873124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 4, 3, 5].length) (baseStart_3873124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3873124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3873124 prefixEnd_3873124 := by exact prefixLift 3873124
  have htrace : WordTrace (prefixWord ++ tailWord_3873124) baseStart_3873124 baseEnd_3873124 := by
    simpa [prefixWord, tailWord_3873124, baseEnd_3873124] using wordTrace_append hprefix tailTrace_3873124
  have hstable : (prefixWord ++ tailWord_3873124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3873124).length < 2 ^ (prefixWord ++ tailWord_3873124).sum := by decide
  have hdescent : baseEnd_3873124 < baseStart_3873124 := by decide
  rcases family_descends (prefixWord ++ tailWord_3873124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3873177 : List Nat := [1, 2, 1, 2, 1, 4, 1, 3, 1, 4, 3]
def baseStart_3873177 : Nat := 118140960795 + 3873177 * 2 ^ 59
def prefixEnd_3873177 : Nat := 4983230072969 + 3 ^ 40 * 3873177 * 2
def baseEnd_3873177 : Nat := 1988801460939297910875089

theorem tailTrace_3873177 : CollatzResearch.WordTrace tailWord_3873177 prefixEnd_3873177 1988801460939297910875089 := by
  unfold tailWord_3873177
  simp only [CollatzResearch.WordTrace]
  refine ⟨141266370689148689813121785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94177580459432459875414523 141266370689148689813121785)
  ·
    refine ⟨105949778016861517359841339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141266370689148689813121785 105949778016861517359841339)
    ·
      refine ⟨158924667025292276039762009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105949778016861517359841339 158924667025292276039762009)
      ·
        refine ⟨119193500268969207029821507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158924667025292276039762009 119193500268969207029821507)
        ·
          refine ⟨178790250403453810544732261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119193500268969207029821507 178790250403453810544732261)
          ·
            refine ⟨33523171950647589477137299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 178790250403453810544732261 33523171950647589477137299)
            ·
              refine ⟨50284757925971384215705949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33523171950647589477137299 50284757925971384215705949)
              ·
                refine ⟨18856784222239269080889731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50284757925971384215705949 18856784222239269080889731)
                ·
                  refine ⟨28285176333358903621334597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18856784222239269080889731 28285176333358903621334597)
                  ·
                    refine ⟨5303470562504794429000237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28285176333358903621334597 5303470562504794429000237)
                    ·
                      refine ⟨1988801460939297910875089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5303470562504794429000237 1988801460939297910875089)
                      ·
                        rfl

theorem cell23_3873177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 3, 1, 4, 3].length) (baseStart_3873177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3873177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3873177 prefixEnd_3873177 := by exact prefixLift 3873177
  have htrace : WordTrace (prefixWord ++ tailWord_3873177) baseStart_3873177 baseEnd_3873177 := by
    simpa [prefixWord, tailWord_3873177, baseEnd_3873177] using wordTrace_append hprefix tailTrace_3873177
  have hstable : (prefixWord ++ tailWord_3873177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3873177).length < 2 ^ (prefixWord ++ tailWord_3873177).sum := by decide
  have hdescent : baseEnd_3873177 < baseStart_3873177 := by decide
  rcases family_descends (prefixWord ++ tailWord_3873177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3873201 : List Nat := [1, 2, 2, 4, 1, 4, 1, 1, 3, 4]
def baseStart_3873201 : Nat := 118140960795 + 3873201 * 2 ^ 59
def prefixEnd_3873201 : Nat := 4983230072969 + 3 ^ 40 * 3873201 * 2
def baseEnd_3873201 : Nat := 662937928158335272324993

theorem tailTrace_3873201 : CollatzResearch.WordTrace tailWord_3873201 prefixEnd_3873201 662937928158335272324993 := by
  unfold tailWord_3873201
  simp only [CollatzResearch.WordTrace]
  refine ⟨141267246041061741911995457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94178164027374494607996971 141267246041061741911995457)
  ·
    refine ⟨105950434530796306433996593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141267246041061741911995457 105950434530796306433996593)
    ·
      refine ⟨79462825898097229825497445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105950434530796306433996593 79462825898097229825497445)
      ·
        refine ⟨14899279855893230592280771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79462825898097229825497445 14899279855893230592280771)
        ·
          refine ⟨22348919783839845888421157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14899279855893230592280771 22348919783839845888421157)
          ·
            refine ⟨4190422459469971104078967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22348919783839845888421157 4190422459469971104078967)
            ·
              refine ⟨6285633689204956656118451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4190422459469971104078967 6285633689204956656118451)
              ·
                refine ⟨9428450533807434984177677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6285633689204956656118451 9428450533807434984177677)
                ·
                  refine ⟨3535668950177788119066629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9428450533807434984177677 3535668950177788119066629)
                  ·
                    refine ⟨662937928158335272324993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3535668950177788119066629 662937928158335272324993)
                    ·
                      rfl

theorem cell23_3873201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 1, 1, 3, 4].length) (baseStart_3873201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3873201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3873201 prefixEnd_3873201 := by exact prefixLift 3873201
  have htrace : WordTrace (prefixWord ++ tailWord_3873201) baseStart_3873201 baseEnd_3873201 := by
    simpa [prefixWord, tailWord_3873201, baseEnd_3873201] using wordTrace_append hprefix tailTrace_3873201
  have hstable : (prefixWord ++ tailWord_3873201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3873201).length < 2 ^ (prefixWord ++ tailWord_3873201).sum := by decide
  have hdescent : baseEnd_3873201 < baseStart_3873201 := by decide
  rcases family_descends (prefixWord ++ tailWord_3873201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3873267 : List Nat := [1, 1, 1, 2, 2, 2, 4, 1, 3, 1, 5]
def baseStart_3873267 : Nat := 118140960795 + 3873267 * 2 ^ 59
def prefixEnd_3873267 : Nat := 4983230072969 + 3 ^ 40 * 3873267 * 2
def baseEnd_3873267 : Nat := 1988847674198202558749675

theorem tailTrace_3873267 : CollatzResearch.WordTrace tailWord_3873267 prefixEnd_3873267 1988847674198202558749675 := by
  unfold tailWord_3873267
  simp only [CollatzResearch.WordTrace]
  refine ⟨141269653258822635183898055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94179768839215090122598703 141269653258822635183898055)
  ·
    refine ⟨211904479888233952775847083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141269653258822635183898055 211904479888233952775847083)
    ·
      refine ⟨317856719832350929163770625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211904479888233952775847083 317856719832350929163770625)
      ·
        refine ⟨238392539874263196872827969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 317856719832350929163770625 238392539874263196872827969)
        ·
          refine ⟨178794404905697397654620977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238392539874263196872827969 178794404905697397654620977)
          ·
            refine ⟨134095803679273048240965733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178794404905697397654620977 134095803679273048240965733)
            ·
              refine ⟨25142963189863696545181075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 134095803679273048240965733 25142963189863696545181075)
              ·
                refine ⟨37714444784795544817771613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25142963189863696545181075 37714444784795544817771613)
                ·
                  refine ⟨14142916794298329306664355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37714444784795544817771613 14142916794298329306664355)
                  ·
                    refine ⟨21214375191447493959996533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14142916794298329306664355 21214375191447493959996533)
                    ·
                      refine ⟨1988847674198202558749675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21214375191447493959996533 1988847674198202558749675)
                      ·
                        rfl

theorem cell23_3873267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 1, 3, 1, 5].length) (baseStart_3873267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3873267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3873267 prefixEnd_3873267 := by exact prefixLift 3873267
  have htrace : WordTrace (prefixWord ++ tailWord_3873267) baseStart_3873267 baseEnd_3873267 := by
    simpa [prefixWord, tailWord_3873267, baseEnd_3873267] using wordTrace_append hprefix tailTrace_3873267
  have hstable : (prefixWord ++ tailWord_3873267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3873267).length < 2 ^ (prefixWord ++ tailWord_3873267).sum := by decide
  have hdescent : baseEnd_3873267 < baseStart_3873267 := by decide
  rcases family_descends (prefixWord ++ tailWord_3873267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3873301 : List Nat := [1, 3, 2, 1, 3, 1, 3, 3, 1, 2, 3]
def baseStart_3873301 : Nat := 118140960795 + 3873301 * 2 ^ 59
def prefixEnd_3873301 : Nat := 4983230072969 + 3 ^ 40 * 3873301 * 2
def baseEnd_3873301 : Nat := 1988865132540455425724519

theorem tailTrace_3873301 : CollatzResearch.WordTrace tailWord_3873301 prefixEnd_3873301 1988865132540455425724519 := by
  unfold tailWord_3873301
  simp only [CollatzResearch.WordTrace]
  refine ⟨141270893340699458990635757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94180595560466305993757171 141270893340699458990635757)
  ·
    refine ⟨52976585002762297121488409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141270893340699458990635757 52976585002762297121488409)
    ·
      refine ⟨39732438752071722841116307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52976585002762297121488409 39732438752071722841116307)
      ·
        refine ⟨59598658128107584261674461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39732438752071722841116307 59598658128107584261674461)
        ·
          refine ⟨22349496798040344098127923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59598658128107584261674461 22349496798040344098127923)
          ·
            refine ⟨33524245197060516147191885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22349496798040344098127923 33524245197060516147191885)
            ·
              refine ⟨12571591948897693555196957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33524245197060516147191885 12571591948897693555196957)
              ·
                refine ⟨4714346980836635083198859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12571591948897693555196957 4714346980836635083198859)
                ·
                  refine ⟨7071520471254952624798289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4714346980836635083198859 7071520471254952624798289)
                  ·
                    refine ⟨5303640353441214468598717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7071520471254952624798289 5303640353441214468598717)
                    ·
                      refine ⟨1988865132540455425724519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5303640353441214468598717 1988865132540455425724519)
                      ·
                        rfl

theorem cell23_3873301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 3, 1, 2, 3].length) (baseStart_3873301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3873301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3873301 prefixEnd_3873301 := by exact prefixLift 3873301
  have htrace : WordTrace (prefixWord ++ tailWord_3873301) baseStart_3873301 baseEnd_3873301 := by
    simpa [prefixWord, tailWord_3873301, baseEnd_3873301] using wordTrace_append hprefix tailTrace_3873301
  have hstable : (prefixWord ++ tailWord_3873301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3873301).length < 2 ^ (prefixWord ++ tailWord_3873301).sum := by decide
  have hdescent : baseEnd_3873301 < baseStart_3873301 := by decide
  rcases family_descends (prefixWord ++ tailWord_3873301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3873308 : List Nat := [2, 2, 3, 1, 2, 4, 1, 2, 2, 4]
def baseStart_3873308 : Nat := 118140960795 + 3873308 * 2 ^ 59
def prefixEnd_3873308 : Nat := 4983230072969 + 3 ^ 40 * 3873308 * 2
def baseEnd_3873308 : Nat := 662956242301678966112329

theorem tailTrace_3873308 : CollatzResearch.WordTrace tailWord_3873308 prefixEnd_3873308 662956242301678966112329 := by
  unfold tailWord_3873308
  simp only [CollatzResearch.WordTrace]
  refine ⟨70635574325837049593070289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94180765767782732790760385 70635574325837049593070289)
  ·
    refine ⟨52976680744377787194802717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70635574325837049593070289 52976680744377787194802717)
    ·
      refine ⟨19866255279141670198051019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52976680744377787194802717 19866255279141670198051019)
      ·
        refine ⟨29799382918712505297076529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19866255279141670198051019 29799382918712505297076529)
        ·
          refine ⟨22349537189034378972807397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29799382918712505297076529 22349537189034378972807397)
          ·
            refine ⟨4190538222943946057401387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22349537189034378972807397 4190538222943946057401387)
            ·
              refine ⟨6285807334415919086102081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4190538222943946057401387 6285807334415919086102081)
              ·
                refine ⟨4714355500811939314576561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6285807334415919086102081 4714355500811939314576561)
                ·
                  refine ⟨3535766625608954485932421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4714355500811939314576561 3535766625608954485932421)
                  ·
                    refine ⟨662956242301678966112329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3535766625608954485932421 662956242301678966112329)
                    ·
                      rfl

theorem cell23_3873308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 1, 2, 2, 4].length) (baseStart_3873308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3873308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3873308 prefixEnd_3873308 := by exact prefixLift 3873308
  have htrace : WordTrace (prefixWord ++ tailWord_3873308) baseStart_3873308 baseEnd_3873308 := by
    simpa [prefixWord, tailWord_3873308, baseEnd_3873308] using wordTrace_append hprefix tailTrace_3873308
  have hstable : (prefixWord ++ tailWord_3873308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3873308).length < 2 ^ (prefixWord ++ tailWord_3873308).sum := by decide
  have hdescent : baseEnd_3873308 < baseStart_3873308 := by decide
  rcases family_descends (prefixWord ++ tailWord_3873308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3873315 : List Nat := [1, 1, 1, 4, 4, 1, 2, 4, 1, 2, 2]
def baseStart_3873315 : Nat := 118140960795 + 3873315 * 2 ^ 59
def prefixEnd_3873315 : Nat := 4983230072969 + 3 ^ 40 * 3873315 * 2
def baseEnd_3873315 : Nat := 1988872321269618370949455

theorem tailTrace_3873315 : CollatzResearch.WordTrace tailWord_3873315 prefixEnd_3873315 1988872321269618370949455 := by
  unfold tailWord_3873315
  simp only [CollatzResearch.WordTrace]
  refine ⟨141271403962648739381645399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94180935975099159587763599 141271403962648739381645399)
  ·
    refine ⟨211907105943973109072468099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141271403962648739381645399 211907105943973109072468099)
    ·
      refine ⟨317860658915959663608702149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211907105943973109072468099 317860658915959663608702149)
      ·
        refine ⟨59598873546742436926631653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 317860658915959663608702149 59598873546742436926631653)
        ·
          refine ⟨11174788790014206923743435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59598873546742436926631653 11174788790014206923743435)
          ·
            refine ⟨16762183185021310385615153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11174788790014206923743435 16762183185021310385615153)
            ·
              refine ⟨12571637388765982789211365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16762183185021310385615153 12571637388765982789211365)
              ·
                refine ⟨2357182010393621772977131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12571637388765982789211365 2357182010393621772977131)
                ·
                  refine ⟨3535773015590432659465697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2357182010393621772977131 3535773015590432659465697)
                  ·
                    refine ⟨2651829761692824494599273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3535773015590432659465697 2651829761692824494599273)
                    ·
                      refine ⟨1988872321269618370949455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2651829761692824494599273 1988872321269618370949455)
                      ·
                        rfl

theorem cell23_3873315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 4, 1, 2, 2].length) (baseStart_3873315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3873315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3873315 prefixEnd_3873315 := by exact prefixLift 3873315
  have htrace : WordTrace (prefixWord ++ tailWord_3873315) baseStart_3873315 baseEnd_3873315 := by
    simpa [prefixWord, tailWord_3873315, baseEnd_3873315] using wordTrace_append hprefix tailTrace_3873315
  have hstable : (prefixWord ++ tailWord_3873315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3873315).length < 2 ^ (prefixWord ++ tailWord_3873315).sum := by decide
  have hdescent : baseEnd_3873315 < baseStart_3873315 := by decide
  rcases family_descends (prefixWord ++ tailWord_3873315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3873317 : List Nat := [1, 3, 1, 2, 2, 1, 2, 1, 1, 9]
def baseStart_3873317 : Nat := 118140960795 + 3873317 * 2 ^ 59
def prefixEnd_3873317 : Nat := 4983230072969 + 3 ^ 40 * 3873317 * 2
def baseEnd_3873317 : Nat := 662957782743642454374815

theorem tailTrace_3873317 : CollatzResearch.WordTrace tailWord_3873317 prefixEnd_3873317 662957782743642454374815 := by
  unfold tailWord_3873317
  simp only [CollatzResearch.WordTrace]
  refine ⟨141271476908641493723218205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94180984605760995815478803 141271476908641493723218205)
  ·
    refine ⟨52976803840740560146206827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141271476908641493723218205 52976803840740560146206827)
    ·
      refine ⟨79465205761110840219310241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52976803840740560146206827 79465205761110840219310241)
      ·
        refine ⟨59598904320833130164482681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79465205761110840219310241 59598904320833130164482681)
        ·
          refine ⟨44699178240624847623362011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59598904320833130164482681 44699178240624847623362011)
          ·
            refine ⟨67048767360937271435043017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44699178240624847623362011 67048767360937271435043017)
            ·
              refine ⟨50286575520702953576282263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67048767360937271435043017 50286575520702953576282263)
              ·
                refine ⟨75429863281054430364423395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50286575520702953576282263 75429863281054430364423395)
                ·
                  refine ⟨113144794921581645546635093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75429863281054430364423395 113144794921581645546635093)
                  ·
                    refine ⟨662957782743642454374815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 113144794921581645546635093 662957782743642454374815)
                    ·
                      rfl

theorem cell23_3873317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 9].length) (baseStart_3873317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3873317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3873317 prefixEnd_3873317 := by exact prefixLift 3873317
  have htrace : WordTrace (prefixWord ++ tailWord_3873317) baseStart_3873317 baseEnd_3873317 := by
    simpa [prefixWord, tailWord_3873317, baseEnd_3873317] using wordTrace_append hprefix tailTrace_3873317
  have hstable : (prefixWord ++ tailWord_3873317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3873317).length < 2 ^ (prefixWord ++ tailWord_3873317).sum := by decide
  have hdescent : baseEnd_3873317 < baseStart_3873317 := by decide
  rcases family_descends (prefixWord ++ tailWord_3873317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3873327 : List Nat := [1, 1, 2, 1, 2, 1, 1, 1, 6, 2, 5]
def baseStart_3873327 : Nat := 118140960795 + 3873327 * 2 ^ 59
def prefixEnd_3873327 : Nat := 4983230072969 + 3 ^ 40 * 3873327 * 2
def baseEnd_3873327 : Nat := 1988878483037472323999399

theorem tailTrace_3873327 : CollatzResearch.WordTrace tailWord_3873327 prefixEnd_3873327 1988878483037472323999399 := by
  unfold tailWord_3873327
  simp only [CollatzResearch.WordTrace]
  refine ⟨141271841638605265431082235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94181227759070176954054823 141271841638605265431082235)
  ·
    refine ⟨211907762457907898146623353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141271841638605265431082235 211907762457907898146623353)
    ·
      refine ⟨158930821843430923609967515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211907762457907898146623353 158930821843430923609967515)
      ·
        refine ⟨238396232765146385414951273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158930821843430923609967515 238396232765146385414951273)
        ·
          refine ⟨178797174573859789061213455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238396232765146385414951273 178797174573859789061213455)
          ·
            refine ⟨268195761860789683591820183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178797174573859789061213455 268195761860789683591820183)
            ·
              refine ⟨402293642791184525387730275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 268195761860789683591820183 402293642791184525387730275)
              ·
                refine ⟨603440464186776788081595413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 402293642791184525387730275 603440464186776788081595413)
                ·
                  refine ⟨28286271758755161941324785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 603440464186776788081595413 28286271758755161941324785)
                  ·
                    refine ⟨21214703819066371455993589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28286271758755161941324785 21214703819066371455993589)
                    ·
                      refine ⟨1988878483037472323999399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21214703819066371455993589 1988878483037472323999399)
                      ·
                        rfl

theorem cell23_3873327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 6, 2, 5].length) (baseStart_3873327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3873327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3873327 prefixEnd_3873327 := by exact prefixLift 3873327
  have htrace : WordTrace (prefixWord ++ tailWord_3873327) baseStart_3873327 baseEnd_3873327 := by
    simpa [prefixWord, tailWord_3873327, baseEnd_3873327] using wordTrace_append hprefix tailTrace_3873327
  have hstable : (prefixWord ++ tailWord_3873327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3873327).length < 2 ^ (prefixWord ++ tailWord_3873327).sum := by decide
  have hdescent : baseEnd_3873327 < baseStart_3873327 := by decide
  rcases family_descends (prefixWord ++ tailWord_3873327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3873347 : List Nat := [1, 1, 1, 3, 1, 2, 1, 4, 1, 8]
def baseStart_3873347 : Nat := 118140960795 + 3873347 * 2 ^ 59
def prefixEnd_3873347 : Nat := 4983230072969 + 3 ^ 40 * 3873347 * 2
def baseEnd_3873347 : Nat := 662962917550187415249769

theorem tailTrace_3873347 : CollatzResearch.WordTrace tailWord_3873347 prefixEnd_3873347 662962917550187415249769 := by
  unfold tailWord_3873347
  simp only [CollatzResearch.WordTrace]
  refine ⟨141272571098532808846810295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94181714065688539231206863 141272571098532808846810295)
  ·
    refine ⟨211908856647799213270215443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141272571098532808846810295 211908856647799213270215443)
    ·
      refine ⟨317863284971698819905323165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211908856647799213270215443 317863284971698819905323165)
      ·
        refine ⟨119198731864387057464496187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 317863284971698819905323165 119198731864387057464496187)
        ·
          refine ⟨178798097796580586196744281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119198731864387057464496187 178798097796580586196744281)
          ·
            refine ⟨134098573347435439647558211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178798097796580586196744281 134098573347435439647558211)
            ·
              refine ⟨201147860021153159471337317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134098573347435439647558211 201147860021153159471337317)
              ·
                refine ⟨37715223753966217400875747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 201147860021153159471337317 37715223753966217400875747)
                ·
                  refine ⟨56572835630949326101313621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37715223753966217400875747 56572835630949326101313621)
                  ·
                    refine ⟨662962917550187415249769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 56572835630949326101313621 662962917550187415249769)
                    ·
                      rfl

theorem cell23_3873347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 4, 1, 8].length) (baseStart_3873347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3873347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3873347 prefixEnd_3873347 := by exact prefixLift 3873347
  have htrace : WordTrace (prefixWord ++ tailWord_3873347) baseStart_3873347 baseEnd_3873347 := by
    simpa [prefixWord, tailWord_3873347, baseEnd_3873347] using wordTrace_append hprefix tailTrace_3873347
  have hstable : (prefixWord ++ tailWord_3873347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3873347).length < 2 ^ (prefixWord ++ tailWord_3873347).sum := by decide
  have hdescent : baseEnd_3873347 < baseStart_3873347 := by decide
  rcases family_descends (prefixWord ++ tailWord_3873347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3873358 : List Nat := [4, 1, 1, 1, 1, 2, 4, 3, 1, 3, 2]
def baseStart_3873358 : Nat := 118140960795 + 3873358 * 2 ^ 59
def prefixEnd_3873358 : Nat := 4983230072969 + 3 ^ 40 * 3873358 * 2
def baseEnd_3873358 : Nat := 1988894400937761702711757

theorem tailTrace_3873358 : CollatzResearch.WordTrace tailWord_3873358 prefixEnd_3873358 1988894400937761702711757 := by
  unfold tailWord_3873358
  simp only [CollatzResearch.WordTrace]
  refine ⟨17659121537686619715682591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94181981534328638483640485 17659121537686619715682591)
  ·
    refine ⟨26488682306529929573523887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17659121537686619715682591 26488682306529929573523887)
    ·
      refine ⟨39733023459794894360285831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26488682306529929573523887 39733023459794894360285831)
      ·
        refine ⟨59599535189692341540428747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39733023459794894360285831 59599535189692341540428747)
        ·
          refine ⟨89399302784538512310643121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59599535189692341540428747 89399302784538512310643121)
          ·
            refine ⟨67049477088403884232982341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89399302784538512310643121 67049477088403884232982341)
            ·
              refine ⟨12571776954075728293684189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67049477088403884232982341 12571776954075728293684189)
              ·
                refine ⟨4714416357778398110131571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12571776954075728293684189 4714416357778398110131571)
                ·
                  refine ⟨7071624536667597165197357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4714416357778398110131571 7071624536667597165197357)
                  ·
                    refine ⟨2651859201250348936949009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7071624536667597165197357 2651859201250348936949009)
                    ·
                      refine ⟨1988894400937761702711757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2651859201250348936949009 1988894400937761702711757)
                      ·
                        rfl

theorem cell23_3873358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 3, 1, 3, 2].length) (baseStart_3873358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3873358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3873358 prefixEnd_3873358 := by exact prefixLift 3873358
  have htrace : WordTrace (prefixWord ++ tailWord_3873358) baseStart_3873358 baseEnd_3873358 := by
    simpa [prefixWord, tailWord_3873358, baseEnd_3873358] using wordTrace_append hprefix tailTrace_3873358
  have hstable : (prefixWord ++ tailWord_3873358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3873358).length < 2 ^ (prefixWord ++ tailWord_3873358).sum := by decide
  have hdescent : baseEnd_3873358 < baseStart_3873358 := by decide
  rcases family_descends (prefixWord ++ tailWord_3873358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3873392 : List Nat := [2, 1, 1, 1, 8, 1, 1, 2, 1, 3, 2]
def baseStart_3873392 : Nat := 118140960795 + 3873392 * 2 ^ 59
def prefixEnd_3873392 : Nat := 4983230072969 + 3 ^ 40 * 3873392 * 2
def baseEnd_3873392 : Nat := 1988911859280014569686601

theorem tailTrace_3873392 : CollatzResearch.WordTrace tailWord_3873392 prefixEnd_3873392 1988911859280014569686601 := by
  unfold tailWord_3873392
  simp only [CollatzResearch.WordTrace]
  refine ⟨70637106191684890766099215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94182808255579854354798953 70637106191684890766099215)
  ·
    refine ⟨105955659287527336149148823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70637106191684890766099215 105955659287527336149148823)
    ·
      refine ⟨158933488931291004223723235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105955659287527336149148823 158933488931291004223723235)
      ·
        refine ⟨238400233396936506335584853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158933488931291004223723235 238400233396936506335584853)
        ·
          refine ⟨2793752735120349683620135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 238400233396936506335584853 2793752735120349683620135)
          ·
            refine ⟨4190629102680524525430203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2793752735120349683620135 4190629102680524525430203)
            ·
              refine ⟨6285943654020786788145305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4190629102680524525430203 6285943654020786788145305)
              ·
                refine ⟨4714457740515590091108979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6285943654020786788145305 4714457740515590091108979)
                ·
                  refine ⟨7071686610773385136663469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4714457740515590091108979 7071686610773385136663469)
                  ·
                    refine ⟨2651882479040019426248801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7071686610773385136663469 2651882479040019426248801)
                    ·
                      refine ⟨1988911859280014569686601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2651882479040019426248801 1988911859280014569686601)
                      ·
                        rfl

theorem cell23_3873392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 1, 2, 1, 3, 2].length) (baseStart_3873392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3873392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3873392 prefixEnd_3873392 := by exact prefixLift 3873392
  have htrace : WordTrace (prefixWord ++ tailWord_3873392) baseStart_3873392 baseEnd_3873392 := by
    simpa [prefixWord, tailWord_3873392, baseEnd_3873392] using wordTrace_append hprefix tailTrace_3873392
  have hstable : (prefixWord ++ tailWord_3873392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3873392).length < 2 ^ (prefixWord ++ tailWord_3873392).sum := by decide
  have hdescent : baseEnd_3873392 < baseStart_3873392 := by decide
  rcases family_descends (prefixWord ++ tailWord_3873392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3873431 : List Nat := [1, 1, 3, 3, 2, 1, 1, 1, 1, 7, 2]
def baseStart_3873431 : Nat := 118140960795 + 3873431 * 2 ^ 59
def prefixEnd_3873431 : Nat := 4983230072969 + 3 ^ 40 * 3873431 * 2
def baseEnd_3873431 : Nat := 1988931885025539917098921

theorem tailTrace_3873431 : CollatzResearch.WordTrace tailWord_3873431 prefixEnd_3873431 1988931885025539917098921 := by
  unfold tailWord_3873431
  simp only [CollatzResearch.WordTrace]
  refine ⟨141275634830228491192868147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94183756553485660795245431 141275634830228491192868147)
  ·
    refine ⟨211913452245342736789302221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141275634830228491192868147 211913452245342736789302221)
    ·
      refine ⟨79467544592003526295988333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211913452245342736789302221 79467544592003526295988333)
      ·
        refine ⟨29800329222001322360995625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79467544592003526295988333 29800329222001322360995625)
        ·
          refine ⟨22350246916500991770746719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29800329222001322360995625 22350246916500991770746719)
          ·
            refine ⟨33525370374751487656120079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22350246916500991770746719 33525370374751487656120079)
            ·
              refine ⟨50288055562127231484180119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33525370374751487656120079 50288055562127231484180119)
              ·
                refine ⟨75432083343190847226270179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50288055562127231484180119 75432083343190847226270179)
                ·
                  refine ⟨113148125014786270839405269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75432083343190847226270179 113148125014786270839405269)
                  ·
                    refine ⟨2651909180034053222798561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 113148125014786270839405269 2651909180034053222798561)
                    ·
                      refine ⟨1988931885025539917098921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2651909180034053222798561 1988931885025539917098921)
                      ·
                        rfl

theorem cell23_3873431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 1, 7, 2].length) (baseStart_3873431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3873431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3873431 prefixEnd_3873431 := by exact prefixLift 3873431
  have htrace : WordTrace (prefixWord ++ tailWord_3873431) baseStart_3873431 baseEnd_3873431 := by
    simpa [prefixWord, tailWord_3873431, baseEnd_3873431] using wordTrace_append hprefix tailTrace_3873431
  have hstable : (prefixWord ++ tailWord_3873431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3873431).length < 2 ^ (prefixWord ++ tailWord_3873431).sum := by decide
  have hdescent : baseEnd_3873431 < baseStart_3873431 := by decide
  rcases family_descends (prefixWord ++ tailWord_3873431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3873438 : List Nat := [4, 3, 1, 1, 1, 1, 3, 1, 2, 3, 3]
def baseStart_3873438 : Nat := 118140960795 + 3873438 * 2 ^ 59
def prefixEnd_3873438 : Nat := 4983230072969 + 3 ^ 40 * 3873438 * 2
def baseEnd_3873438 : Nat := 1988935479390121389711389

theorem tailTrace_3873438 : CollatzResearch.WordTrace tailWord_3873438 prefixEnd_3873438 1988935479390121389711389 := by
  unfold tailWord_3873438
  simp only [CollatzResearch.WordTrace]
  refine ⟨17659486267650391423546621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94183926760802087592248645 17659486267650391423546621)
  ·
    refine ⟨6622307350368896783829983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17659486267650391423546621 6622307350368896783829983)
    ·
      refine ⟨9933461025553345175744975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6622307350368896783829983 9933461025553345175744975)
      ·
        refine ⟨14900191538330017763617463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9933461025553345175744975 14900191538330017763617463)
        ·
          refine ⟨22350287307495026645426195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14900191538330017763617463 22350287307495026645426195)
          ·
            refine ⟨33525430961242539968139293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22350287307495026645426195 33525430961242539968139293)
            ·
              refine ⟨12572036610465952488052235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33525430961242539968139293 12572036610465952488052235)
              ·
                refine ⟨18858054915698928732078353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12572036610465952488052235 18858054915698928732078353)
                ·
                  refine ⟨14143541186774196549058765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18858054915698928732078353 14143541186774196549058765)
                  ·
                    refine ⟨5303827945040323705897037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14143541186774196549058765 5303827945040323705897037)
                    ·
                      refine ⟨1988935479390121389711389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5303827945040323705897037 1988935479390121389711389)
                      ·
                        rfl

theorem cell23_3873438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 1, 2, 3, 3].length) (baseStart_3873438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3873438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3873438 prefixEnd_3873438 := by exact prefixLift 3873438
  have htrace : WordTrace (prefixWord ++ tailWord_3873438) baseStart_3873438 baseEnd_3873438 := by
    simpa [prefixWord, tailWord_3873438, baseEnd_3873438] using wordTrace_append hprefix tailTrace_3873438
  have hstable : (prefixWord ++ tailWord_3873438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3873438).length < 2 ^ (prefixWord ++ tailWord_3873438).sum := by decide
  have hdescent : baseEnd_3873438 < baseStart_3873438 := by decide
  rcases family_descends (prefixWord ++ tailWord_3873438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3873462 : List Nat := [5, 1, 3, 1, 2, 1, 2, 3, 5]
def baseStart_3873462 : Nat := 118140960795 + 3873462 * 2 ^ 59
def prefixEnd_3873462 : Nat := 4983230072969 + 3 ^ 40 * 3873462 * 2
def baseEnd_3873462 : Nat := 220994200325092143979031

theorem tailTrace_3873462 : CollatzResearch.WordTrace tailWord_3873462 prefixEnd_3873462 220994200325092143979031 := by
  unfold tailWord_3873462
  simp only [CollatzResearch.WordTrace]
  refine ⟨8829797843319761467952915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 94184510328744122324831093 8829797843319761467952915)
  ·
    refine ⟨13244696764979642201929373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8829797843319761467952915 13244696764979642201929373)
    ·
      refine ⟨4966761286867365825723515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13244696764979642201929373 4966761286867365825723515)
      ·
        refine ⟨7450141930301048738585273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4966761286867365825723515 7450141930301048738585273)
        ·
          refine ⟨5587606447725786553938955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7450141930301048738585273 5587606447725786553938955)
          ·
            refine ⟨8381409671588679830908433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5587606447725786553938955 8381409671588679830908433)
            ·
              refine ⟨6286057253691509873181325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8381409671588679830908433 6286057253691509873181325)
              ·
                refine ⟨2357271470134316202442997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6286057253691509873181325 2357271470134316202442997)
                ·
                  refine ⟨220994200325092143979031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2357271470134316202442997 220994200325092143979031)
                  ·
                    rfl

theorem cell23_3873462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 2, 3, 5].length) (baseStart_3873462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3873462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3873462 prefixEnd_3873462 := by exact prefixLift 3873462
  have htrace : WordTrace (prefixWord ++ tailWord_3873462) baseStart_3873462 baseEnd_3873462 := by
    simpa [prefixWord, tailWord_3873462, baseEnd_3873462] using wordTrace_append hprefix tailTrace_3873462
  have hstable : (prefixWord ++ tailWord_3873462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3873462).length < 2 ^ (prefixWord ++ tailWord_3873462).sum := by decide
  have hdescent : baseEnd_3873462 < baseStart_3873462 := by decide
  rcases family_descends (prefixWord ++ tailWord_3873462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3873504 : List Nat := [2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 6]
def baseStart_3873504 : Nat := 118140960795 + 3873504 * 2 ^ 59
def prefixEnd_3873504 : Nat := 4983230072969 + 3 ^ 40 * 3873504 * 2
def baseEnd_3873504 : Nat := 1988969369113318131486085

theorem tailTrace_3873504 : CollatzResearch.WordTrace tailWord_3873504 prefixEnd_3873504 1988969369113318131486085 := by
  unfold tailWord_3873504
  simp only [CollatzResearch.WordTrace]
  refine ⟨70639148679482012330137783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94185531572642683106850377 70639148679482012330137783)
  ·
    refine ⟨105958723019223018495206675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70639148679482012330137783 105958723019223018495206675)
    ·
      refine ⟨158938084528834527742810013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105958723019223018495206675 158938084528834527742810013)
      ·
        refine ⟨59601781698312947903553755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158938084528834527742810013 59601781698312947903553755)
        ·
          refine ⟨89402672547469421855330633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59601781698312947903553755 89402672547469421855330633)
          ·
            refine ⟨67052004410602066391497975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89402672547469421855330633 67052004410602066391497975)
            ·
              refine ⟨100578006615903099587246963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67052004410602066391497975 100578006615903099587246963)
              ·
                refine ⟨150867009923854649380870445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100578006615903099587246963 150867009923854649380870445)
                ·
                  refine ⟨56575128721445493517826417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 150867009923854649380870445 56575128721445493517826417)
                  ·
                    refine ⟨42431346541084120138369813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56575128721445493517826417 42431346541084120138369813)
                    ·
                      refine ⟨1988969369113318131486085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42431346541084120138369813 1988969369113318131486085)
                      ·
                        rfl

theorem cell23_3873504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 6].length) (baseStart_3873504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3873504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3873504 prefixEnd_3873504 := by exact prefixLift 3873504
  have htrace : WordTrace (prefixWord ++ tailWord_3873504) baseStart_3873504 baseEnd_3873504 := by
    simpa [prefixWord, tailWord_3873504, baseEnd_3873504] using wordTrace_append hprefix tailTrace_3873504
  have hstable : (prefixWord ++ tailWord_3873504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3873504).length < 2 ^ (prefixWord ++ tailWord_3873504).sum := by decide
  have hdescent : baseEnd_3873504 < baseStart_3873504 := by decide
  rcases family_descends (prefixWord ++ tailWord_3873504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3873522 : List Nat := [3, 2, 1, 3, 1, 4, 1, 3, 1, 4]
def baseStart_3873522 : Nat := 118140960795 + 3873522 * 2 ^ 59
def prefixEnd_3873522 : Nat := 4983230072969 + 3 ^ 40 * 3873522 * 2
def baseEnd_3873522 : Nat := 662992870588366353687001

theorem tailTrace_3873522 : CollatzResearch.WordTrace tailWord_3873522 prefixEnd_3873522 662992870588366353687001 := by
  unfold tailWord_3873522
  simp only [CollatzResearch.WordTrace]
  refine ⟨35319738468224703433607705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94185969248599209156287213 35319738468224703433607705)
  ·
    refine ⟨26489803851168527575205779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35319738468224703433607705 26489803851168527575205779)
    ·
      refine ⟨39734705776752791362808669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26489803851168527575205779 39734705776752791362808669)
      ·
        refine ⟨14900514666282296761053251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39734705776752791362808669 14900514666282296761053251)
        ·
          refine ⟨22350771999423445141579877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14900514666282296761053251 22350771999423445141579877)
          ·
            refine ⟨4190769749891895964046227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22350771999423445141579877 4190769749891895964046227)
            ·
              refine ⟨6286154624837843946069341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4190769749891895964046227 6286154624837843946069341)
              ·
                refine ⟨2357307984314191479776003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6286154624837843946069341 2357307984314191479776003)
                ·
                  refine ⟨3535961976471287219664005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2357307984314191479776003 3535961976471287219664005)
                  ·
                    refine ⟨662992870588366353687001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3535961976471287219664005 662992870588366353687001)
                    ·
                      rfl

theorem cell23_3873522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 1, 3, 1, 4].length) (baseStart_3873522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3873522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3873522 prefixEnd_3873522 := by exact prefixLift 3873522
  have htrace : WordTrace (prefixWord ++ tailWord_3873522) baseStart_3873522 baseEnd_3873522 := by
    simpa [prefixWord, tailWord_3873522, baseEnd_3873522] using wordTrace_append hprefix tailTrace_3873522
  have hstable : (prefixWord ++ tailWord_3873522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3873522).length < 2 ^ (prefixWord ++ tailWord_3873522).sum := by decide
  have hdescent : baseEnd_3873522 < baseStart_3873522 := by decide
  rcases family_descends (prefixWord ++ tailWord_3873522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3873545 : List Nat := [1, 2, 1, 1, 3, 2, 2, 6, 1, 1, 3]
def baseStart_3873545 : Nat := 118140960795 + 3873545 * 2 ^ 59
def prefixEnd_3873545 : Nat := 4983230072969 + 3 ^ 40 * 3873545 * 2
def baseEnd_3873545 : Nat := 1988990421820152471073397

theorem tailTrace_3873545 : CollatzResearch.WordTrace tailWord_3873545 prefixEnd_3873545 1988990421820152471073397 := by
  unfold tailWord_3873545
  simp only [CollatzResearch.WordTrace]
  refine ⟨141279792751815488662518089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94186528501210325775012059 141279792751815488662518089)
  ·
    refine ⟨105959844563861616496888567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141279792751815488662518089 105959844563861616496888567)
    ·
      refine ⟨158939766845792424745332851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105959844563861616496888567 158939766845792424745332851)
      ·
        refine ⟨238409650268688637117999277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158939766845792424745332851 238409650268688637117999277)
        ·
          refine ⟨89403618850758238919249729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 238409650268688637117999277 89403618850758238919249729)
          ·
            refine ⟨67052714138068679189437297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89403618850758238919249729 67052714138068679189437297)
            ·
              refine ⟨50289535603551509392077973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67052714138068679189437297 50289535603551509392077973)
              ·
                refine ⟨2357321981416477002753655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 50289535603551509392077973 2357321981416477002753655)
                ·
                  refine ⟨3535982972124715504130483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2357321981416477002753655 3535982972124715504130483)
                  ·
                    refine ⟨5303974458187073256195725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3535982972124715504130483 5303974458187073256195725)
                    ·
                      refine ⟨1988990421820152471073397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5303974458187073256195725 1988990421820152471073397)
                      ·
                        rfl

theorem cell23_3873545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 6, 1, 1, 3].length) (baseStart_3873545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3873545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3873545 prefixEnd_3873545 := by exact prefixLift 3873545
  have htrace : WordTrace (prefixWord ++ tailWord_3873545) baseStart_3873545 baseEnd_3873545 := by
    simpa [prefixWord, tailWord_3873545, baseEnd_3873545] using wordTrace_append hprefix tailTrace_3873545
  have hstable : (prefixWord ++ tailWord_3873545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3873545).length < 2 ^ (prefixWord ++ tailWord_3873545).sum := by decide
  have hdescent : baseEnd_3873545 < baseStart_3873545 := by decide
  rcases family_descends (prefixWord ++ tailWord_3873545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3873551 : List Nat := [1, 1, 2, 1, 1, 1, 6, 2, 3, 1, 4]
def baseStart_3873551 : Nat := 118140960795 + 3873551 * 2 ^ 59
def prefixEnd_3873551 : Nat := 4983230072969 + 3 ^ 40 * 3873551 * 2
def baseEnd_3873551 : Nat := 1988993502704079447598369

theorem tailTrace_3873551 : CollatzResearch.WordTrace tailWord_3873551 prefixEnd_3873551 1988993502704079447598369 := by
  unfold tailWord_3873551
  simp only [CollatzResearch.WordTrace]
  refine ⟨141280011589793751687236507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94186674393195834458157671 141280011589793751687236507)
  ·
    refine ⟨211920017384690627530854761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141280011589793751687236507 211920017384690627530854761)
    ·
      refine ⟨158940013038517970648141071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211920017384690627530854761 158940013038517970648141071)
      ·
        refine ⟨238410019557776955972211607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158940013038517970648141071 238410019557776955972211607)
        ·
          refine ⟨357615029336665433958317411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238410019557776955972211607 357615029336665433958317411)
          ·
            refine ⟨536422544004998150937476117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 357615029336665433958317411 536422544004998150937476117)
            ·
              refine ⟨25144806750234288325194193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 536422544004998150937476117 25144806750234288325194193)
              ·
                refine ⟨18858605062675716243895645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25144806750234288325194193 18858605062675716243895645)
                ·
                  refine ⟨7071976898503393591460867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18858605062675716243895645 7071976898503393591460867)
                  ·
                    refine ⟨10607965347755090387191301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7071976898503393591460867 10607965347755090387191301)
                    ·
                      refine ⟨1988993502704079447598369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10607965347755090387191301 1988993502704079447598369)
                      ·
                        rfl

theorem cell23_3873551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 6, 2, 3, 1, 4].length) (baseStart_3873551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3873551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3873551 prefixEnd_3873551 := by exact prefixLift 3873551
  have htrace : WordTrace (prefixWord ++ tailWord_3873551) baseStart_3873551 baseEnd_3873551 := by
    simpa [prefixWord, tailWord_3873551, baseEnd_3873551] using wordTrace_append hprefix tailTrace_3873551
  have hstable : (prefixWord ++ tailWord_3873551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3873551).length < 2 ^ (prefixWord ++ tailWord_3873551).sum := by decide
  have hdescent : baseEnd_3873551 < baseStart_3873551 := by decide
  rcases family_descends (prefixWord ++ tailWord_3873551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3873561 : List Nat := [1, 2, 1, 2, 1, 1, 1, 4, 6, 4]
def baseStart_3873561 : Nat := 118140960795 + 3873561 * 2 ^ 59
def prefixEnd_3873561 : Nat := 4983230072969 + 3 ^ 40 * 3873561 * 2
def baseEnd_3873561 : Nat := 662999545836874802824441

theorem tailTrace_3873561 : CollatzResearch.WordTrace tailWord_3873561 prefixEnd_3873561 662999545836874802824441 := by
  unfold tailWord_3873561
  simp only [CollatzResearch.WordTrace]
  refine ⟨141280376319757523395100537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94186917546505015596733691 141280376319757523395100537)
  ·
    refine ⟨105960282239818142546325403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141280376319757523395100537 105960282239818142546325403)
    ·
      refine ⟨158940423359727213819488105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105960282239818142546325403 158940423359727213819488105)
      ·
        refine ⟨119205317519795410364616079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158940423359727213819488105 119205317519795410364616079)
        ·
          refine ⟨178807976279693115546924119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119205317519795410364616079 178807976279693115546924119)
          ·
            refine ⟨268211964419539673320386179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178807976279693115546924119 268211964419539673320386179)
            ·
              refine ⟨402317946629309509980579269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 268211964419539673320386179 402317946629309509980579269)
              ·
                refine ⟨75434614992995533121358613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 402317946629309509980579269 75434614992995533121358613)
                ·
                  refine ⟨3535997577796665615063685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 75434614992995533121358613 3535997577796665615063685)
                  ·
                    refine ⟨662999545836874802824441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3535997577796665615063685 662999545836874802824441)
                    ·
                      rfl

theorem cell23_3873561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 6, 4].length) (baseStart_3873561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3873561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3873561 prefixEnd_3873561 := by exact prefixLift 3873561
  have htrace : WordTrace (prefixWord ++ tailWord_3873561) baseStart_3873561 baseEnd_3873561 := by
    simpa [prefixWord, tailWord_3873561, baseEnd_3873561] using wordTrace_append hprefix tailTrace_3873561
  have hstable : (prefixWord ++ tailWord_3873561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3873561).length < 2 ^ (prefixWord ++ tailWord_3873561).sum := by decide
  have hdescent : baseEnd_3873561 < baseStart_3873561 := by decide
  rcases family_descends (prefixWord ++ tailWord_3873561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3873565 : List Nat := [1, 4, 2, 4, 1, 1, 1, 1, 3, 5]
def baseStart_3873565 : Nat := 118140960795 + 3873565 * 2 ^ 59
def prefixEnd_3873565 : Nat := 4983230072969 + 3 ^ 40 * 3873565 * 2
def baseEnd_3873565 : Nat := 663000230477747464274435

theorem tailTrace_3873565 : CollatzResearch.WordTrace tailWord_3873565 prefixEnd_3873565 663000230477747464274435 := by
  unfold tailWord_3873565
  simp only [CollatzResearch.WordTrace]
  refine ⟨141280522211743032078246149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94187014807828688052164099 141280522211743032078246149)
  ·
    refine ⟨26490097914701818514671153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141280522211743032078246149 26490097914701818514671153)
    ·
      refine ⟨19867573436026363886003365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26490097914701818514671153 19867573436026363886003365)
      ·
        refine ⟨3725170019254943228625631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19867573436026363886003365 3725170019254943228625631)
        ·
          refine ⟨5587755028882414842938447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3725170019254943228625631 5587755028882414842938447)
          ·
            refine ⟨8381632543323622264407671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5587755028882414842938447 8381632543323622264407671)
            ·
              refine ⟨12572448814985433396611507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8381632543323622264407671 12572448814985433396611507)
              ·
                refine ⟨18858673222478150094917261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12572448814985433396611507 18858673222478150094917261)
                ·
                  refine ⟨7072002458429306285593973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18858673222478150094917261 7072002458429306285593973)
                  ·
                    refine ⟨663000230477747464274435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7072002458429306285593973 663000230477747464274435)
                    ·
                      rfl

theorem cell23_3873565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 1, 3, 5].length) (baseStart_3873565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3873565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3873565 prefixEnd_3873565 := by exact prefixLift 3873565
  have htrace : WordTrace (prefixWord ++ tailWord_3873565) baseStart_3873565 baseEnd_3873565 := by
    simpa [prefixWord, tailWord_3873565, baseEnd_3873565] using wordTrace_append hprefix tailTrace_3873565
  have hstable : (prefixWord ++ tailWord_3873565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3873565).length < 2 ^ (prefixWord ++ tailWord_3873565).sum := by decide
  have hdescent : baseEnd_3873565 < baseStart_3873565 := by decide
  rcases family_descends (prefixWord ++ tailWord_3873565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3873568 : List Nat := [2, 1, 1, 5, 1, 3, 1, 1, 3, 1, 4]
def baseStart_3873568 : Nat := 118140960795 + 3873568 * 2 ^ 59
def prefixEnd_3873568 : Nat := 4983230072969 + 3 ^ 40 * 3873568 * 2
def baseEnd_3873568 : Nat := 1989002231875205881085791

theorem tailTrace_3873568 : CollatzResearch.WordTrace tailWord_3873568 prefixEnd_3873568 1989002231875205881085791 := by
  unfold tailWord_3873568
  simp only [CollatzResearch.WordTrace]
  refine ⟨70640315815366081795302679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94187087753821442393736905 70640315815366081795302679)
  ·
    refine ⟨105960473723049122692954019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70640315815366081795302679 105960473723049122692954019)
    ·
      refine ⟨158940710584573684039431029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105960473723049122692954019 158940710584573684039431029)
      ·
        refine ⟨14900691617303782878696659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 158940710584573684039431029 14900691617303782878696659)
        ·
          refine ⟨22351037425955674318044989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14900691617303782878696659 22351037425955674318044989)
          ·
            refine ⟨8381639034733377869266871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22351037425955674318044989 8381639034733377869266871)
            ·
              refine ⟨12572458552100066803900307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8381639034733377869266871 12572458552100066803900307)
              ·
                refine ⟨18858687828150100205850461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12572458552100066803900307 18858687828150100205850461)
                ·
                  refine ⟨7072007935556287577193923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18858687828150100205850461 7072007935556287577193923)
                  ·
                    refine ⟨10608011903334431365790885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7072007935556287577193923 10608011903334431365790885)
                    ·
                      refine ⟨1989002231875205881085791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10608011903334431365790885 1989002231875205881085791)
                      ·
                        rfl

theorem cell23_3873568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_3873568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3873568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3873568 prefixEnd_3873568 := by exact prefixLift 3873568
  have htrace : WordTrace (prefixWord ++ tailWord_3873568) baseStart_3873568 baseEnd_3873568 := by
    simpa [prefixWord, tailWord_3873568, baseEnd_3873568] using wordTrace_append hprefix tailTrace_3873568
  have hstable : (prefixWord ++ tailWord_3873568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3873568).length < 2 ^ (prefixWord ++ tailWord_3873568).sum := by decide
  have hdescent : baseEnd_3873568 < baseStart_3873568 := by decide
  rcases family_descends (prefixWord ++ tailWord_3873568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3873572 : List Nat := [2, 3, 1, 3, 3, 1, 2, 1, 2, 3, 2]
def baseStart_3873572 : Nat := 118140960795 + 3873572 * 2 ^ 59
def prefixEnd_3873572 : Nat := 4983230072969 + 3 ^ 40 * 3873572 * 2
def baseEnd_3873572 : Nat := 1989004285797823865435773

theorem tailTrace_3873572 : CollatzResearch.WordTrace tailWord_3873572 prefixEnd_3873572 1989004285797823865435773 := by
  unfold tailWord_3873572
  simp only [CollatzResearch.WordTrace]
  refine ⟨70640388761358836136875485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94187185015145114849167313 70640388761358836136875485)
  ·
    refine ⟨26490145785509563551328307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70640388761358836136875485 26490145785509563551328307)
    ·
      refine ⟨39735218678264345326992461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26490145785509563551328307 39735218678264345326992461)
      ·
        refine ⟨14900707004349129497622173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39735218678264345326992461 14900707004349129497622173)
        ·
          refine ⟨5587765126630923561608315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14900707004349129497622173 5587765126630923561608315)
          ·
            refine ⟨8381647689946385342412473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5587765126630923561608315 8381647689946385342412473)
            ·
              refine ⟨6286235767459789006809355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8381647689946385342412473 6286235767459789006809355)
              ·
                refine ⟨9429353651189683510214033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6286235767459789006809355 9429353651189683510214033)
                ·
                  refine ⟨7072015238392262632660525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9429353651189683510214033 7072015238392262632660525)
                  ·
                    refine ⟨2652005714397098487247697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7072015238392262632660525 2652005714397098487247697)
                    ·
                      refine ⟨1989004285797823865435773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2652005714397098487247697 1989004285797823865435773)
                      ·
                        rfl

theorem cell23_3873572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 2, 1, 2, 3, 2].length) (baseStart_3873572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3873572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3873572 prefixEnd_3873572 := by exact prefixLift 3873572
  have htrace : WordTrace (prefixWord ++ tailWord_3873572) baseStart_3873572 baseEnd_3873572 := by
    simpa [prefixWord, tailWord_3873572, baseEnd_3873572] using wordTrace_append hprefix tailTrace_3873572
  have hstable : (prefixWord ++ tailWord_3873572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3873572).length < 2 ^ (prefixWord ++ tailWord_3873572).sum := by decide
  have hdescent : baseEnd_3873572 < baseStart_3873572 := by decide
  rcases family_descends (prefixWord ++ tailWord_3873572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3873582 : List Nat := [4, 1, 3, 2, 1, 2, 3, 1, 1, 5]
def baseStart_3873582 : Nat := 118140960795 + 3873582 * 2 ^ 59
def prefixEnd_3873582 : Nat := 4983230072969 + 3 ^ 40 * 3873582 * 2
def baseEnd_3873582 : Nat := 663003140201456275436909

theorem tailTrace_3873582 : CollatzResearch.WordTrace tailWord_3873582 prefixEnd_3873582 663003140201456275436909 := by
  unfold tailWord_3873582
  simp only [CollatzResearch.WordTrace]
  refine ⟨17660142781585180497701875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94187428168454295987743333 17660142781585180497701875)
  ·
    refine ⟨26490214172377770746552813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17660142781585180497701875 26490214172377770746552813)
    ·
      refine ⟨9933830314641664029957305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26490214172377770746552813 9933830314641664029957305)
      ·
        refine ⟨7450372735981248022467979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9933830314641664029957305 7450372735981248022467979)
        ·
          refine ⟨11175559103971872033701969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7450372735981248022467979 11175559103971872033701969)
          ·
            refine ⟨8381669327978904025276477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11175559103971872033701969 8381669327978904025276477)
            ·
              refine ⟨3143125997992089009478679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8381669327978904025276477 3143125997992089009478679)
              ·
                refine ⟨4714688996988133514218019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3143125997992089009478679 4714688996988133514218019)
                ·
                  refine ⟨7072033495482200271327029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4714688996988133514218019 7072033495482200271327029)
                  ·
                    refine ⟨663003140201456275436909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7072033495482200271327029 663003140201456275436909)
                    ·
                      rfl

theorem cell23_3873582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 3, 1, 1, 5].length) (baseStart_3873582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3873582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3873582 prefixEnd_3873582 := by exact prefixLift 3873582
  have htrace : WordTrace (prefixWord ++ tailWord_3873582) baseStart_3873582 baseEnd_3873582 := by
    simpa [prefixWord, tailWord_3873582, baseEnd_3873582] using wordTrace_append hprefix tailTrace_3873582
  have hstable : (prefixWord ++ tailWord_3873582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3873582).length < 2 ^ (prefixWord ++ tailWord_3873582).sum := by decide
  have hdescent : baseEnd_3873582 < baseStart_3873582 := by decide
  rcases family_descends (prefixWord ++ tailWord_3873582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3873585 : List Nat := [1, 2, 2, 3, 2, 1, 5, 1, 1, 1, 4]
def baseStart_3873585 : Nat := 118140960795 + 3873585 * 2 ^ 59
def prefixEnd_3873585 : Nat := 4983230072969 + 3 ^ 40 * 3873585 * 2
def baseEnd_3873585 : Nat := 1989010961046332314573213

theorem tailTrace_3873585 : CollatzResearch.WordTrace tailWord_3873585 prefixEnd_3873585 1989010961046332314573213 := by
  unfold tailWord_3873585
  simp only [CollatzResearch.WordTrace]
  refine ⟨141281251671670575493974209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94187501114447050329316139 141281251671670575493974209)
  ·
    refine ⟨105960938753752931620480657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141281251671670575493974209 105960938753752931620480657)
    ·
      refine ⟨79470704065314698715360493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105960938753752931620480657 79470704065314698715360493)
      ·
        refine ⟨29801514024493012018260185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79470704065314698715360493 29801514024493012018260185)
        ·
          refine ⟨22351135518369759013695139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29801514024493012018260185 22351135518369759013695139)
          ·
            refine ⟨33526703277554638520542709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22351135518369759013695139 33526703277554638520542709)
            ·
              refine ⟨3143128432270747361300879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33526703277554638520542709 3143128432270747361300879)
              ·
                refine ⟨4714692648406121041951319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3143128432270747361300879 4714692648406121041951319)
                ·
                  refine ⟨7072038972609181562926979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4714692648406121041951319 7072038972609181562926979)
                  ·
                    refine ⟨10608058458913772344390469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7072038972609181562926979 10608058458913772344390469)
                    ·
                      refine ⟨1989010961046332314573213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10608058458913772344390469 1989010961046332314573213)
                      ·
                        rfl

theorem cell23_3873585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 5, 1, 1, 1, 4].length) (baseStart_3873585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3873585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3873585 prefixEnd_3873585 := by exact prefixLift 3873585
  have htrace : WordTrace (prefixWord ++ tailWord_3873585) baseStart_3873585 baseEnd_3873585 := by
    simpa [prefixWord, tailWord_3873585, baseEnd_3873585] using wordTrace_append hprefix tailTrace_3873585
  have hstable : (prefixWord ++ tailWord_3873585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3873585).length < 2 ^ (prefixWord ++ tailWord_3873585).sum := by decide
  have hdescent : baseEnd_3873585 < baseStart_3873585 := by decide
  rcases family_descends (prefixWord ++ tailWord_3873585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3873621 : List Nat := [1, 3, 2, 2, 2, 1, 1, 2, 2, 7]
def baseStart_3873621 : Nat := 118140960795 + 3873621 * 2 ^ 59
def prefixEnd_3873621 : Nat := 4983230072969 + 3 ^ 40 * 3873621 * 2
def baseEnd_3873621 : Nat := 663009815449964724574349

theorem tailTrace_3873621 : CollatzResearch.WordTrace tailWord_3873621 prefixEnd_3873621 663009815449964724574349 := by
  unfold tailWord_3873621
  simp only [CollatzResearch.WordTrace]
  refine ⟨141282564699540153642284717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94188376466360102428189811 141282564699540153642284717)
  ·
    refine ⟨52980961762327557615856769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141282564699540153642284717 52980961762327557615856769)
    ·
      refine ⟨39735721321745668211892577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52980961762327557615856769 39735721321745668211892577)
      ·
        refine ⟨29801790991309251158919433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39735721321745668211892577 29801790991309251158919433)
        ·
          refine ⟨22351343243481938369189575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29801790991309251158919433 22351343243481938369189575)
          ·
            refine ⟨33527014865222907553784363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22351343243481938369189575 33527014865222907553784363)
            ·
              refine ⟨50290522297834361330676545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33527014865222907553784363 50290522297834361330676545)
              ·
                refine ⟨37717891723375770998007409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50290522297834361330676545 37717891723375770998007409)
                ·
                  refine ⟨28288418792531828248505557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37717891723375770998007409 28288418792531828248505557)
                  ·
                    refine ⟨663009815449964724574349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28288418792531828248505557 663009815449964724574349)
                    ·
                      rfl

theorem cell23_3873621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 2, 2, 7].length) (baseStart_3873621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3873621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3873621 prefixEnd_3873621 := by exact prefixLift 3873621
  have htrace : WordTrace (prefixWord ++ tailWord_3873621) baseStart_3873621 baseEnd_3873621 := by
    simpa [prefixWord, tailWord_3873621, baseEnd_3873621] using wordTrace_append hprefix tailTrace_3873621
  have hstable : (prefixWord ++ tailWord_3873621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3873621).length < 2 ^ (prefixWord ++ tailWord_3873621).sum := by decide
  have hdescent : baseEnd_3873621 < baseStart_3873621 := by decide
  rcases family_descends (prefixWord ++ tailWord_3873621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3873631 : List Nat := [1, 1, 2, 3, 1, 3, 2, 1, 2, 2, 5]
def baseStart_3873631 : Nat := 118140960795 + 3873631 * 2 ^ 59
def prefixEnd_3873631 : Nat := 4983230072969 + 3 ^ 40 * 3873631 * 2
def baseEnd_3873631 : Nat := 1989034581156439134598001

theorem tailTrace_3873631 : CollatzResearch.WordTrace tailWord_3873631 prefixEnd_3873631 1989034581156439134598001 := by
  unfold tailWord_3873631
  simp only [CollatzResearch.WordTrace]
  refine ⟨141282929429503925350148747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94188619619669283566765831 141282929429503925350148747)
  ·
    refine ⟨211924394144255888025223121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141282929429503925350148747 211924394144255888025223121)
    ·
      refine ⟨158943295608191916018917341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211924394144255888025223121 158943295608191916018917341)
      ·
        refine ⟨59603735853071968507094003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158943295608191916018917341 59603735853071968507094003)
        ·
          refine ⟨89405603779607952760641005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59603735853071968507094003 89405603779607952760641005)
          ·
            refine ⟨33527101417352982285240377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89405603779607952760641005 33527101417352982285240377)
            ·
              refine ⟨25145326063014736713930283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33527101417352982285240377 25145326063014736713930283)
              ·
                refine ⟨37717989094522105070895425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25145326063014736713930283 37717989094522105070895425)
                ·
                  refine ⟨28288491820891578803171569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37717989094522105070895425 28288491820891578803171569)
                  ·
                    refine ⟨21216368865668684102378677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28288491820891578803171569 21216368865668684102378677)
                    ·
                      refine ⟨1989034581156439134598001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21216368865668684102378677 1989034581156439134598001)
                      ·
                        rfl

theorem cell23_3873631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 1, 2, 2, 5].length) (baseStart_3873631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3873631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3873631 prefixEnd_3873631 := by exact prefixLift 3873631
  have htrace : WordTrace (prefixWord ++ tailWord_3873631) baseStart_3873631 baseEnd_3873631 := by
    simpa [prefixWord, tailWord_3873631, baseEnd_3873631] using wordTrace_append hprefix tailTrace_3873631
  have hstable : (prefixWord ++ tailWord_3873631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3873631).length < 2 ^ (prefixWord ++ tailWord_3873631).sum := by decide
  have hdescent : baseEnd_3873631 < baseStart_3873631 := by decide
  rcases family_descends (prefixWord ++ tailWord_3873631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3873651 : List Nat := [1, 1, 1, 2, 2, 1, 5, 2, 2, 6]
def baseStart_3873651 : Nat := 118140960795 + 3873651 * 2 ^ 59
def prefixEnd_3873651 : Nat := 4983230072969 + 3 ^ 40 * 3873651 * 2
def baseEnd_3873651 : Nat := 663014950256509685449303

theorem tailTrace_3873651 : CollatzResearch.WordTrace tailWord_3873651 prefixEnd_3873651 663014950256509685449303 := by
  unfold tailWord_3873651
  simp only [CollatzResearch.WordTrace]
  refine ⟨141283658889431468765876807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94189105926287645843917871 141283658889431468765876807)
  ·
    refine ⟨211925488334147203148815211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141283658889431468765876807 211925488334147203148815211)
    ·
      refine ⟨317888232501220804723222817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211925488334147203148815211 317888232501220804723222817)
      ·
        refine ⟨238416174375915603542417113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 317888232501220804723222817 238416174375915603542417113)
        ·
          refine ⟨178812130781936702656812835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238416174375915603542417113 178812130781936702656812835)
          ·
            refine ⟨268218196172905053985219253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178812130781936702656812835 268218196172905053985219253)
            ·
              refine ⟨25145455891209848811114305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 268218196172905053985219253 25145455891209848811114305)
              ·
                refine ⟨18859091918407386608335729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25145455891209848811114305 18859091918407386608335729)
                ·
                  refine ⟨14144318938805539956251797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18859091918407386608335729 14144318938805539956251797)
                  ·
                    refine ⟨663014950256509685449303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14144318938805539956251797 663014950256509685449303)
                    ·
                      rfl

theorem cell23_3873651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 2, 2, 6].length) (baseStart_3873651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3873651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3873651 prefixEnd_3873651 := by exact prefixLift 3873651
  have htrace : WordTrace (prefixWord ++ tailWord_3873651) baseStart_3873651 baseEnd_3873651 := by
    simpa [prefixWord, tailWord_3873651, baseEnd_3873651] using wordTrace_append hprefix tailTrace_3873651
  have hstable : (prefixWord ++ tailWord_3873651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3873651).length < 2 ^ (prefixWord ++ tailWord_3873651).sum := by decide
  have hdescent : baseEnd_3873651 < baseStart_3873651 := by decide
  rcases family_descends (prefixWord ++ tailWord_3873651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3873666 : List Nat := [3, 4, 2, 2, 2, 1, 1, 1, 1, 2, 4]
def baseStart_3873666 : Nat := 118140960795 + 3873666 * 2 ^ 59
def prefixEnd_3873666 : Nat := 4983230072969 + 3 ^ 40 * 3873666 * 2
def baseEnd_3873666 : Nat := 1989052552979346497660341

theorem tailTrace_3873666 : CollatzResearch.WordTrace tailWord_3873666 prefixEnd_3873666 1989052552979346497660341 := by
  unfold tailWord_3873666
  simp only [CollatzResearch.WordTrace]
  refine ⟨35321051496094281581918213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94189470656251417551781901 35321051496094281581918213)
  ·
    refine ⟨6622697155517677796609665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35321051496094281581918213 6622697155517677796609665)
    ·
      refine ⟨4967022866638258347457249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6622697155517677796609665 4967022866638258347457249)
      ·
        refine ⟨3725267149978693760592937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4967022866638258347457249 3725267149978693760592937)
        ·
          refine ⟨2793950362484020320444703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3725267149978693760592937 2793950362484020320444703)
          ·
            refine ⟨4190925543726030480667055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2793950362484020320444703 4190925543726030480667055)
            ·
              refine ⟨6286388315589045721000583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4190925543726030480667055 6286388315589045721000583)
              ·
                refine ⟨9429582473383568581500875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6286388315589045721000583 9429582473383568581500875)
                ·
                  refine ⟨14144373710075352872251313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9429582473383568581500875 14144373710075352872251313)
                  ·
                    refine ⟨10608280282556514654188485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14144373710075352872251313 10608280282556514654188485)
                    ·
                      refine ⟨1989052552979346497660341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10608280282556514654188485 1989052552979346497660341)
                      ·
                        rfl

theorem cell23_3873666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_3873666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3873666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3873666 prefixEnd_3873666 := by exact prefixLift 3873666
  have htrace : WordTrace (prefixWord ++ tailWord_3873666) baseStart_3873666 baseEnd_3873666 := by
    simpa [prefixWord, tailWord_3873666, baseEnd_3873666] using wordTrace_append hprefix tailTrace_3873666
  have hstable : (prefixWord ++ tailWord_3873666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3873666).length < 2 ^ (prefixWord ++ tailWord_3873666).sum := by decide
  have hdescent : baseEnd_3873666 < baseStart_3873666 := by decide
  rcases family_descends (prefixWord ++ tailWord_3873666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3873675 : List Nat := [1, 1, 1, 1, 4, 2, 5, 1, 1, 4, 2]
def baseStart_3873675 : Nat := 118140960795 + 3873675 * 2 ^ 59
def prefixEnd_3873675 : Nat := 4983230072969 + 3 ^ 40 * 3873675 * 2
def baseEnd_3873675 : Nat := 1989057174305236962447799

theorem tailTrace_3873675 : CollatzResearch.WordTrace tailWord_3873675 prefixEnd_3873675 1989057174305236962447799 := by
  unfold tailWord_3873675
  simp only [CollatzResearch.WordTrace]
  refine ⟨141284534241344520864750479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94189689494229680576500319 141284534241344520864750479)
  ·
    refine ⟨211926801362016781297125719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141284534241344520864750479 211926801362016781297125719)
    ·
      refine ⟨317890202043025171945688579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211926801362016781297125719 317890202043025171945688579)
      ·
        refine ⟨476835303064537757918532869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317890202043025171945688579 476835303064537757918532869)
        ·
          refine ⟨89406619324600829609724913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 476835303064537757918532869 89406619324600829609724913)
          ·
            refine ⟨67054964493450622207293685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89406619324600829609724913 67054964493450622207293685)
            ·
              refine ⟨6286402921260995831933783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67054964493450622207293685 6286402921260995831933783)
              ·
                refine ⟨9429604381891493747900675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6286402921260995831933783 9429604381891493747900675)
                ·
                  refine ⟨14144406572837240621851013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9429604381891493747900675 14144406572837240621851013)
                  ·
                    refine ⟨2652076232406982616597065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14144406572837240621851013 2652076232406982616597065)
                    ·
                      refine ⟨1989057174305236962447799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2652076232406982616597065 1989057174305236962447799)
                      ·
                        rfl

theorem cell23_3873675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 5, 1, 1, 4, 2].length) (baseStart_3873675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3873675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3873675 prefixEnd_3873675 := by exact prefixLift 3873675
  have htrace : WordTrace (prefixWord ++ tailWord_3873675) baseStart_3873675 baseEnd_3873675 := by
    simpa [prefixWord, tailWord_3873675, baseEnd_3873675] using wordTrace_append hprefix tailTrace_3873675
  have hstable : (prefixWord ++ tailWord_3873675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3873675).length < 2 ^ (prefixWord ++ tailWord_3873675).sum := by decide
  have hdescent : baseEnd_3873675 < baseStart_3873675 := by decide
  rcases family_descends (prefixWord ++ tailWord_3873675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3873701 : List Nat := [1, 3, 1, 2, 1, 1, 1, 1, 2, 4, 6]
def baseStart_3873701 : Nat := 118140960795 + 3873701 * 2 ^ 59
def prefixEnd_3873701 : Nat := 4983230072969 + 3 ^ 40 * 3873701 * 2
def baseEnd_3873701 : Nat := 1989070524802253860722679

theorem tailTrace_3873701 : CollatzResearch.WordTrace tailWord_3873701 prefixEnd_3873701 1989070524802253860722679 := by
  unfold tailWord_3873701
  simp only [CollatzResearch.WordTrace]
  refine ⟨141285482539250327305196957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94190321692833551536797971 141285482539250327305196957)
  ·
    refine ⟨52982055952218872739448859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141285482539250327305196957 52982055952218872739448859)
    ·
      refine ⟨79473083928328309109173289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52982055952218872739448859 79473083928328309109173289)
      ·
        refine ⟨59604812946246231831879967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79473083928328309109173289 59604812946246231831879967)
        ·
          refine ⟨89407219419369347747819951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59604812946246231831879967 89407219419369347747819951)
          ·
            refine ⟨134110829129054021621729927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89407219419369347747819951 134110829129054021621729927)
            ·
              refine ⟨201166243693581032432594891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134110829129054021621729927 201166243693581032432594891)
              ·
                refine ⟨301749365540371548648892337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 201166243693581032432594891 301749365540371548648892337)
                ·
                  refine ⟨226312024155278661486669253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 301749365540371548648892337 226312024155278661486669253)
                  ·
                    refine ⟨42433504529114749028750485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 226312024155278661486669253 42433504529114749028750485)
                    ·
                      refine ⟨1989070524802253860722679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42433504529114749028750485 1989070524802253860722679)
                      ·
                        rfl

theorem cell23_3873701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 4, 6].length) (baseStart_3873701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3873701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3873701 prefixEnd_3873701 := by exact prefixLift 3873701
  have htrace : WordTrace (prefixWord ++ tailWord_3873701) baseStart_3873701 baseEnd_3873701 := by
    simpa [prefixWord, tailWord_3873701, baseEnd_3873701] using wordTrace_append hprefix tailTrace_3873701
  have hstable : (prefixWord ++ tailWord_3873701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3873701).length < 2 ^ (prefixWord ++ tailWord_3873701).sum := by decide
  have hdescent : baseEnd_3873701 < baseStart_3873701 := by decide
  rcases family_descends (prefixWord ++ tailWord_3873701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3873711 : List Nat := [1, 1, 2, 1, 2, 2, 2, 2, 3, 7]
def baseStart_3873711 : Nat := 118140960795 + 3873711 * 2 ^ 59
def prefixEnd_3873711 : Nat := 4983230072969 + 3 ^ 40 * 3873711 * 2
def baseEnd_3873711 : Nat := 663025219869599607199211

theorem tailTrace_3873711 : CollatzResearch.WordTrace tailWord_3873711 prefixEnd_3873711 663025219869599607199211 := by
  unfold tailWord_3873711
  simp only [CollatzResearch.WordTrace]
  refine ⟨141285847269214099013060987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94190564846142732675373991 141285847269214099013060987)
  ·
    refine ⟨211928770903821148519591481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141285847269214099013060987 211928770903821148519591481)
    ·
      refine ⟨158946578177865861389693611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211928770903821148519591481 158946578177865861389693611)
      ·
        refine ⟨238419867266798792084540417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158946578177865861389693611 238419867266798792084540417)
        ·
          refine ⟨178814900450099094063405313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238419867266798792084540417 178814900450099094063405313)
          ·
            refine ⟨134111175337574320547553985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178814900450099094063405313 134111175337574320547553985)
            ·
              refine ⟨100583381503180740410665489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134111175337574320547553985 100583381503180740410665489)
              ·
                refine ⟨75437536127385555307999117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100583381503180740410665489 75437536127385555307999117)
                ·
                  refine ⟨28289076047769583240499669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75437536127385555307999117 28289076047769583240499669)
                  ·
                    refine ⟨663025219869599607199211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28289076047769583240499669 663025219869599607199211)
                    ·
                      rfl

theorem cell23_3873711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 3, 7].length) (baseStart_3873711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3873711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3873711 prefixEnd_3873711 := by exact prefixLift 3873711
  have htrace : WordTrace (prefixWord ++ tailWord_3873711) baseStart_3873711 baseEnd_3873711 := by
    simpa [prefixWord, tailWord_3873711, baseEnd_3873711] using wordTrace_append hprefix tailTrace_3873711
  have hstable : (prefixWord ++ tailWord_3873711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3873711).length < 2 ^ (prefixWord ++ tailWord_3873711).sum := by decide
  have hdescent : baseEnd_3873711 < baseStart_3873711 := by decide
  rcases family_descends (prefixWord ++ tailWord_3873711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3873762 : List Nat := [3, 3, 3, 1, 1, 1, 2, 2, 2, 5]
def baseStart_3873762 : Nat := 118140960795 + 3873762 * 2 ^ 59
def prefixEnd_3873762 : Nat := 4983230072969 + 3 ^ 40 * 3873762 * 2
def baseEnd_3873762 : Nat := 663033949040726040686633

theorem tailTrace_3873762 : CollatzResearch.WordTrace tailWord_3873762 prefixEnd_3873762 663033949040726040686633 := by
  unfold tailWord_3873762
  simp only [CollatzResearch.WordTrace]
  refine ⟨35321926848007333680791885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94191804928019556482111693 35321926848007333680791885)
  ·
    refine ⟨13245722568002750130296957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35321926848007333680791885 13245722568002750130296957)
    ·
      refine ⟨4967145963001031298861359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13245722568002750130296957 4967145963001031298861359)
      ·
        refine ⟨7450718944501546948292039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4967145963001031298861359 7450718944501546948292039)
        ·
          refine ⟨11176078416752320422438059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7450718944501546948292039 11176078416752320422438059)
          ·
            refine ⟨16764117625128480633657089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11176078416752320422438059 16764117625128480633657089)
            ·
              refine ⟨12573088218846360475242817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16764117625128480633657089 12573088218846360475242817)
              ·
                refine ⟨9429816164134770356432113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12573088218846360475242817 9429816164134770356432113)
                ·
                  refine ⟨7072362123101077767324085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9429816164134770356432113 7072362123101077767324085)
                  ·
                    refine ⟨663033949040726040686633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7072362123101077767324085 663033949040726040686633)
                    ·
                      rfl

theorem cell23_3873762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_3873762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3873762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3873762 prefixEnd_3873762 := by exact prefixLift 3873762
  have htrace : WordTrace (prefixWord ++ tailWord_3873762) baseStart_3873762 baseEnd_3873762 := by
    simpa [prefixWord, tailWord_3873762, baseEnd_3873762] using wordTrace_append hprefix tailTrace_3873762
  have hstable : (prefixWord ++ tailWord_3873762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3873762).length < 2 ^ (prefixWord ++ tailWord_3873762).sum := by decide
  have hdescent : baseEnd_3873762 < baseStart_3873762 := by decide
  rcases family_descends (prefixWord ++ tailWord_3873762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3873782 : List Nat := [5, 1, 1, 1, 3, 1, 1, 1, 1, 6, 2]
def baseStart_3873782 : Nat := 118140960795 + 3873782 * 2 ^ 59
def prefixEnd_3873782 : Nat := 4983230072969 + 3 ^ 40 * 3873782 * 2
def baseEnd_3873782 : Nat := 1989112116735268043809807

theorem tailTrace_3873782 : CollatzResearch.WordTrace tailWord_3873782 prefixEnd_3873782 1989112116735268043809807 := by
  unfold tailWord_3873782
  simp only [CollatzResearch.WordTrace]
  refine ⟨8830527303247304883680975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 94192291234637918759263733 8830527303247304883680975)
  ·
    refine ⟨13245790954870957325521463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8830527303247304883680975 13245790954870957325521463)
    ·
      refine ⟨19868686432306435988282195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13245790954870957325521463 19868686432306435988282195)
      ·
        refine ⟨29803029648459653982423293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19868686432306435988282195 29803029648459653982423293)
        ·
          refine ⟨11176136118172370243408735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29803029648459653982423293 11176136118172370243408735)
          ·
            refine ⟨16764204177258555365113103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11176136118172370243408735 16764204177258555365113103)
            ·
              refine ⟨25146306265887833047669655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16764204177258555365113103 25146306265887833047669655)
              ·
                refine ⟨37719459398831749571504483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25146306265887833047669655 37719459398831749571504483)
                ·
                  refine ⟨56579189098247624357256725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37719459398831749571504483 56579189098247624357256725)
                  ·
                    refine ⟨2652149488980357391746409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 56579189098247624357256725 2652149488980357391746409)
                    ·
                      refine ⟨1989112116735268043809807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2652149488980357391746409 1989112116735268043809807)
                      ·
                        rfl

theorem cell23_3873782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 1, 1, 6, 2].length) (baseStart_3873782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3873782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3873782 prefixEnd_3873782 := by exact prefixLift 3873782
  have htrace : WordTrace (prefixWord ++ tailWord_3873782) baseStart_3873782 baseEnd_3873782 := by
    simpa [prefixWord, tailWord_3873782, baseEnd_3873782] using wordTrace_append hprefix tailTrace_3873782
  have hstable : (prefixWord ++ tailWord_3873782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3873782).length < 2 ^ (prefixWord ++ tailWord_3873782).sum := by decide
  have hdescent : baseEnd_3873782 < baseStart_3873782 := by decide
  rcases family_descends (prefixWord ++ tailWord_3873782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3873802 : List Nat := [3, 1, 2, 2, 3, 1, 3, 1, 2, 2, 3]
def baseStart_3873802 : Nat := 118140960795 + 3873802 * 2 ^ 59
def prefixEnd_3873802 : Nat := 4983230072969 + 3 ^ 40 * 3873802 * 2
def baseEnd_3873802 : Nat := 1989122386348357965559715

theorem tailTrace_3873802 : CollatzResearch.WordTrace tailWord_3873802 prefixEnd_3873802 1989122386348357965559715 := by
  unfold tailWord_3873802
  simp only [CollatzResearch.WordTrace]
  refine ⟨35322291577971105388655915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94192777541256281036415773 35322291577971105388655915)
  ·
    refine ⟨52983437366956658082983873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35322291577971105388655915 52983437366956658082983873)
    ·
      refine ⟨39737578025217493562237905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52983437366956658082983873 39737578025217493562237905)
      ·
        refine ⟨29803183518913120171678429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39737578025217493562237905 29803183518913120171678429)
        ·
          refine ⟨11176193819592420064379411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29803183518913120171678429 11176193819592420064379411)
          ·
            refine ⟨16764290729388630096569117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11176193819592420064379411 16764290729388630096569117)
            ·
              refine ⟨6286609023520736286213419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16764290729388630096569117 6286609023520736286213419)
              ·
                refine ⟨9429913535281104429320129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6286609023520736286213419 9429913535281104429320129)
                ·
                  refine ⟨7072435151460828321990097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9429913535281104429320129 7072435151460828321990097)
                  ·
                    refine ⟨5304326363595621241492573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7072435151460828321990097 5304326363595621241492573)
                    ·
                      refine ⟨1989122386348357965559715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5304326363595621241492573 1989122386348357965559715)
                      ·
                        rfl

theorem cell23_3873802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 3, 1, 2, 2, 3].length) (baseStart_3873802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3873802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3873802 prefixEnd_3873802 := by exact prefixLift 3873802
  have htrace : WordTrace (prefixWord ++ tailWord_3873802) baseStart_3873802 baseEnd_3873802 := by
    simpa [prefixWord, tailWord_3873802, baseEnd_3873802] using wordTrace_append hprefix tailTrace_3873802
  have hstable : (prefixWord ++ tailWord_3873802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3873802).length < 2 ^ (prefixWord ++ tailWord_3873802).sum := by decide
  have hdescent : baseEnd_3873802 < baseStart_3873802 := by decide
  rcases family_descends (prefixWord ++ tailWord_3873802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3873852 : List Nat := [2, 2, 2, 2, 2, 3, 2, 2, 1, 5]
def baseStart_3873852 : Nat := 118140960795 + 3873852 * 2 ^ 59
def prefixEnd_3873852 : Nat := 4983230072969 + 3 ^ 40 * 3873852 * 2
def baseEnd_3873852 : Nat := 663049353460360923311495

theorem tailTrace_3873852 : CollatzResearch.WordTrace tailWord_3873852 prefixEnd_3873852 663049353460360923311495 := by
  unfold tailWord_3873852
  simp only [CollatzResearch.WordTrace]
  refine ⟨70645494980851640046971905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94193993307802186729295873 70645494980851640046971905)
  ·
    refine ⟨52984121235638730035228929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70645494980851640046971905 52984121235638730035228929)
    ·
      refine ⟨39738090926729047526421697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52984121235638730035228929 39738090926729047526421697)
      ·
        refine ⟨29803568195046785644816273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39738090926729047526421697 29803568195046785644816273)
        ·
          refine ⟨22352676146285089233612205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29803568195046785644816273 22352676146285089233612205)
          ·
            refine ⟨8382253554856908462604577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22352676146285089233612205 8382253554856908462604577)
            ·
              refine ⟨6286690166142681346953433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8382253554856908462604577 6286690166142681346953433)
              ·
                refine ⟨4715017624607011010215075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6286690166142681346953433 4715017624607011010215075)
                ·
                  refine ⟨7072526436910516515322613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4715017624607011010215075 7072526436910516515322613)
                  ·
                    refine ⟨663049353460360923311495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7072526436910516515322613 663049353460360923311495)
                    ·
                      rfl

theorem cell23_3873852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 2, 2, 1, 5].length) (baseStart_3873852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3873852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3873852 prefixEnd_3873852 := by exact prefixLift 3873852
  have htrace : WordTrace (prefixWord ++ tailWord_3873852) baseStart_3873852 baseEnd_3873852 := by
    simpa [prefixWord, tailWord_3873852, baseEnd_3873852] using wordTrace_append hprefix tailTrace_3873852
  have hstable : (prefixWord ++ tailWord_3873852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3873852).length < 2 ^ (prefixWord ++ tailWord_3873852).sum := by decide
  have hdescent : baseEnd_3873852 < baseStart_3873852 := by decide
  rcases family_descends (prefixWord ++ tailWord_3873852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3873855 : List Nat := [1, 1, 2, 2, 3, 1, 1, 1, 1, 8, 2]
def baseStart_3873855 : Nat := 118140960795 + 3873855 * 2 ^ 59
def prefixEnd_3873855 : Nat := 4983230072969 + 3 ^ 40 * 3873855 * 2
def baseEnd_3873855 : Nat := 1989149600823046258196971

theorem tailTrace_3873855 : CollatzResearch.WordTrace tailWord_3873855 prefixEnd_3873855 1989149600823046258196971 := by
  unfold tailWord_3873855
  simp only [CollatzResearch.WordTrace]
  refine ⟨141291099380692411606303019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94194066253794941070868679 141291099380692411606303019)
  ·
    refine ⟨211936649071038617409454529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141291099380692411606303019 211936649071038617409454529)
    ·
      refine ⟨158952486803278963057090897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211936649071038617409454529 158952486803278963057090897)
      ·
        refine ⟨119214365102459222292818173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158952486803278963057090897 119214365102459222292818173)
        ·
          refine ⟨44705386913422208359806815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119214365102459222292818173 44705386913422208359806815)
          ·
            refine ⟨67058080370133312539710223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44705386913422208359806815 67058080370133312539710223)
            ·
              refine ⟨100587120555199968809565335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67058080370133312539710223 100587120555199968809565335)
              ·
                refine ⟨150880680832799953214348003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100587120555199968809565335 150880680832799953214348003)
                ·
                  refine ⟨226321021249199929821522005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 150880680832799953214348003 226321021249199929821522005)
                  ·
                    refine ⟨2652199467764061677595961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 226321021249199929821522005 2652199467764061677595961)
                    ·
                      refine ⟨1989149600823046258196971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2652199467764061677595961 1989149600823046258196971)
                      ·
                        rfl

theorem cell23_3873855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 8, 2].length) (baseStart_3873855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3873855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3873855 prefixEnd_3873855 := by exact prefixLift 3873855
  have htrace : WordTrace (prefixWord ++ tailWord_3873855) baseStart_3873855 baseEnd_3873855 := by
    simpa [prefixWord, tailWord_3873855, baseEnd_3873855] using wordTrace_append hprefix tailTrace_3873855
  have hstable : (prefixWord ++ tailWord_3873855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3873855).length < 2 ^ (prefixWord ++ tailWord_3873855).sum := by decide
  have hdescent : baseEnd_3873855 < baseStart_3873855 := by decide
  rcases family_descends (prefixWord ++ tailWord_3873855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3873872 : List Nat := [2, 1, 1, 1, 1, 3, 1, 4, 5, 2, 2]
def baseStart_3873872 : Nat := 118140960795 + 3873872 * 2 ^ 59
def prefixEnd_3873872 : Nat := 4983230072969 + 3 ^ 40 * 3873872 * 2
def baseEnd_3873872 : Nat := 1989158329994172691684393

theorem tailTrace_3873872 : CollatzResearch.WordTrace tailWord_3873872 prefixEnd_3873872 1989158329994172691684393 := by
  unfold tailWord_3873872
  simp only [CollatzResearch.WordTrace]
  refine ⟨70645859710815411754835935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94194479614420549006447913 70645859710815411754835935)
  ·
    refine ⟨105968789566223117632253903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70645859710815411754835935 105968789566223117632253903)
    ·
      refine ⟨158953184349334676448380855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105968789566223117632253903 158953184349334676448380855)
      ·
        refine ⟨238429776524002014672571283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158953184349334676448380855 238429776524002014672571283)
        ·
          refine ⟨357644664786003022008856925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238429776524002014672571283 357644664786003022008856925)
          ·
            refine ⟨134116749294751133253321347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 357644664786003022008856925 134116749294751133253321347)
            ·
              refine ⟨201175123942126699879982021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134116749294751133253321347 201175123942126699879982021)
              ·
                refine ⟨37720335739148756227496629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 201175123942126699879982021 37720335739148756227496629)
                ·
                  refine ⟨3536281475545195896327809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37720335739148756227496629 3536281475545195896327809)
                  ·
                    refine ⟨2652211106658896922245857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3536281475545195896327809 2652211106658896922245857)
                    ·
                      refine ⟨1989158329994172691684393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2652211106658896922245857 1989158329994172691684393)
                      ·
                        rfl

theorem cell23_3873872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 4, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 4, 5, 2, 2].length) (baseStart_3873872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3873872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3873872 prefixEnd_3873872 := by exact prefixLift 3873872
  have htrace : WordTrace (prefixWord ++ tailWord_3873872) baseStart_3873872 baseEnd_3873872 := by
    simpa [prefixWord, tailWord_3873872, baseEnd_3873872] using wordTrace_append hprefix tailTrace_3873872
  have hstable : (prefixWord ++ tailWord_3873872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3873872).length < 2 ^ (prefixWord ++ tailWord_3873872).sum := by decide
  have hdescent : baseEnd_3873872 < baseStart_3873872 := by decide
  rcases family_descends (prefixWord ++ tailWord_3873872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3873889 : List Nat := [1, 2, 3, 1, 1, 2, 5, 1, 3, 2, 2]
def baseStart_3873889 : Nat := 118140960795 + 3873889 * 2 ^ 59
def prefixEnd_3873889 : Nat := 4983230072969 + 3 ^ 40 * 3873889 * 2
def baseEnd_3873889 : Nat := 1989167059165299125171815

theorem tailTrace_3873889 : CollatzResearch.WordTrace tailWord_3873889 prefixEnd_3873889 1989167059165299125171815 := by
  unfold tailWord_3873889
  simp only [CollatzResearch.WordTrace]
  refine ⟨141292339462569235413040721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94194892975046156942027147 141292339462569235413040721)
  ·
    refine ⟨105969254596926926559780541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141292339462569235413040721 105969254596926926559780541)
    ·
      refine ⟨39738470473847597459917703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105969254596926926559780541 39738470473847597459917703)
      ·
        refine ⟨59607705710771396189876555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39738470473847597459917703 59607705710771396189876555)
        ·
          refine ⟨89411558566157094284814833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59607705710771396189876555 89411558566157094284814833)
          ·
            refine ⟨67058668924617820713611125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89411558566157094284814833 67058668924617820713611125)
            ·
              refine ⟨6286750211682920691901043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67058668924617820713611125 6286750211682920691901043)
              ·
                refine ⟨9430125317524381037851565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6286750211682920691901043 9430125317524381037851565)
                ·
                  refine ⟨3536296994071642889194337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9430125317524381037851565 3536296994071642889194337)
                  ·
                    refine ⟨2652222745553732166895753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3536296994071642889194337 2652222745553732166895753)
                    ·
                      refine ⟨1989167059165299125171815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2652222745553732166895753 1989167059165299125171815)
                      ·
                        rfl

theorem cell23_3873889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 5, 1, 3, 2, 2].length) (baseStart_3873889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3873889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3873889 prefixEnd_3873889 := by exact prefixLift 3873889
  have htrace : WordTrace (prefixWord ++ tailWord_3873889) baseStart_3873889 baseEnd_3873889 := by
    simpa [prefixWord, tailWord_3873889, baseEnd_3873889] using wordTrace_append hprefix tailTrace_3873889
  have hstable : (prefixWord ++ tailWord_3873889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3873889).length < 2 ^ (prefixWord ++ tailWord_3873889).sum := by decide
  have hdescent : baseEnd_3873889 < baseStart_3873889 := by decide
  rcases family_descends (prefixWord ++ tailWord_3873889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3873895 : List Nat := [1, 1, 5, 1, 1, 4, 2, 8]
def baseStart_3873895 : Nat := 118140960795 + 3873895 * 2 ^ 59
def prefixEnd_3873895 : Nat := 4983230072969 + 3 ^ 40 * 3873895 * 2
def baseEnd_3873895 : Nat := 73672968149971337099881

theorem tailTrace_3873895 : CollatzResearch.WordTrace tailWord_3873895 prefixEnd_3873895 73672968149971337099881 := by
  unfold tailWord_3873895
  simp only [CollatzResearch.WordTrace]
  refine ⟨141292558300547498437759139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94195038867031665625172759 141292558300547498437759139)
  ·
    refine ⟨211938837450821247656638709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141292558300547498437759139 211938837450821247656638709)
    ·
      refine ⟨19869266011014491967809879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 211938837450821247656638709 19869266011014491967809879)
      ·
        refine ⟨29803899016521737951714819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19869266011014491967809879 29803899016521737951714819)
        ·
          refine ⟨44705848524782606927572229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29803899016521737951714819 44705848524782606927572229)
          ·
            refine ⟨8382346598396738798919793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44705848524782606927572229 8382346598396738798919793)
            ·
              refine ⟨6286759948797554099189845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8382346598396738798919793 6286759948797554099189845)
              ·
                refine ⟨73672968149971337099881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6286759948797554099189845 73672968149971337099881)
                ·
                  rfl

theorem cell23_3873895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 2, 8].length) (baseStart_3873895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3873895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3873895 prefixEnd_3873895 := by exact prefixLift 3873895
  have htrace : WordTrace (prefixWord ++ tailWord_3873895) baseStart_3873895 baseEnd_3873895 := by
    simpa [prefixWord, tailWord_3873895, baseEnd_3873895] using wordTrace_append hprefix tailTrace_3873895
  have hstable : (prefixWord ++ tailWord_3873895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3873895).length < 2 ^ (prefixWord ++ tailWord_3873895).sum := by decide
  have hdescent : baseEnd_3873895 < baseStart_3873895 := by decide
  rcases family_descends (prefixWord ++ tailWord_3873895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3873975 : List Nat := [1, 1, 3, 1, 4, 1, 1, 2, 1, 4, 4]
def baseStart_3873975 : Nat := 118140960795 + 3873975 * 2 ^ 59
def prefixEnd_3873975 : Nat := 4983230072969 + 3 ^ 40 * 3873975 * 2
def baseEnd_3873975 : Nat := 1989211218501585788696419

theorem tailTrace_3873975 : CollatzResearch.WordTrace tailWord_3873975 prefixEnd_3873975 1989211218501585788696419 := by
  unfold tailWord_3873975
  simp only [CollatzResearch.WordTrace]
  refine ⟨141295476140257672100671379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94196984093505114733780919 141295476140257672100671379)
  ·
    refine ⟨211943214210386508151007069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141295476140257672100671379 211943214210386508151007069)
    ·
      refine ⟨79478705328894940556627651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 211943214210386508151007069 79478705328894940556627651)
      ·
        refine ⟨119218057993342410834941477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79478705328894940556627651 119218057993342410834941477)
        ·
          refine ⟨22353385873751702031551527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 119218057993342410834941477 22353385873751702031551527)
          ·
            refine ⟨33530078810627553047327291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22353385873751702031551527 33530078810627553047327291)
            ·
              refine ⟨50295118215941329570990937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33530078810627553047327291 50295118215941329570990937)
              ·
                refine ⟨37721338661955997178243203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50295118215941329570990937 37721338661955997178243203)
                ·
                  refine ⟨56582007992933995767364805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37721338661955997178243203 56582007992933995767364805)
                  ·
                    refine ⟨10609126498675124206380901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56582007992933995767364805 10609126498675124206380901)
                    ·
                      refine ⟨1989211218501585788696419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10609126498675124206380901 1989211218501585788696419)
                      ·
                        rfl

theorem cell23_3873975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 2, 1, 4, 4].length) (baseStart_3873975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3873975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3873975 prefixEnd_3873975 := by exact prefixLift 3873975
  have htrace : WordTrace (prefixWord ++ tailWord_3873975) baseStart_3873975 baseEnd_3873975 := by
    simpa [prefixWord, tailWord_3873975, baseEnd_3873975] using wordTrace_append hprefix tailTrace_3873975
  have hstable : (prefixWord ++ tailWord_3873975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3873975).length < 2 ^ (prefixWord ++ tailWord_3873975).sum := by decide
  have hdescent : baseEnd_3873975 < baseStart_3873975 := by decide
  rcases family_descends (prefixWord ++ tailWord_3873975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3873990 : List Nat := [6, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3]
def baseStart_3873990 : Nat := 118140960795 + 3873990 * 2 ^ 59
def prefixEnd_3873990 : Nat := 4983230072969 + 3 ^ 40 * 3873990 * 2
def baseEnd_3873990 : Nat := 1989218920711403230008851

theorem tailTrace_3873990 : CollatzResearch.WordTrace tailWord_3873990 prefixEnd_3873990 1989218920711403230008851 := by
  unfold tailWord_3873990
  simp only [CollatzResearch.WordTrace]
  refine ⟨4415500726100104051952107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 94197348823468886441644949 4415500726100104051952107)
  ·
    refine ⟨6623251089150156077928161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4415500726100104051952107 6623251089150156077928161)
    ·
      refine ⟨4967438316862617058446121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6623251089150156077928161 4967438316862617058446121)
      ·
        refine ⟨3725578737646962793834591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4967438316862617058446121 3725578737646962793834591)
        ·
          refine ⟨5588368106470444190751887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3725578737646962793834591 5588368106470444190751887)
          ·
            refine ⟨8382552159705666286127831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5588368106470444190751887 8382552159705666286127831)
            ·
              refine ⟨12573828239558499429191747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8382552159705666286127831 12573828239558499429191747)
              ·
                refine ⟨18860742359337749143787621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12573828239558499429191747 18860742359337749143787621)
                ·
                  refine ⟨3536389192375827964460179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18860742359337749143787621 3536389192375827964460179)
                  ·
                    refine ⟨5304583788563741946690269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3536389192375827964460179 5304583788563741946690269)
                    ·
                      refine ⟨1989218920711403230008851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5304583788563741946690269 1989218920711403230008851)
                      ·
                        rfl

theorem cell23_3873990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_3873990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3873990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3873990 prefixEnd_3873990 := by exact prefixLift 3873990
  have htrace : WordTrace (prefixWord ++ tailWord_3873990) baseStart_3873990 baseEnd_3873990 := by
    simpa [prefixWord, tailWord_3873990, baseEnd_3873990] using wordTrace_append hprefix tailTrace_3873990
  have hstable : (prefixWord ++ tailWord_3873990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3873990).length < 2 ^ (prefixWord ++ tailWord_3873990).sum := by decide
  have hdescent : baseEnd_3873990 < baseStart_3873990 := by decide
  rcases family_descends (prefixWord ++ tailWord_3873990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3874002 : List Nat := [3, 2, 2, 2, 1, 1, 4, 1, 7]
def baseStart_3874002 : Nat := 118140960795 + 3874002 * 2 ^ 59
def prefixEnd_3874002 : Nat := 4983230072969 + 3 ^ 40 * 3874002 * 2
def baseEnd_3874002 : Nat := 221025009164361909228755

theorem tailTrace_3874002 : CollatzResearch.WordTrace tailWord_3874002 prefixEnd_3874002 221025009164361909228755 := by
  unfold tailWord_3874002
  simp only [CollatzResearch.WordTrace]
  refine ⟨35324115227789963927976065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94197640607439903807936173 35324115227789963927976065)
  ·
    refine ⟨26493086420842472945982049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35324115227789963927976065 26493086420842472945982049)
    ·
      refine ⟨19869814815631854709486537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26493086420842472945982049 19869814815631854709486537)
      ·
        refine ⟨14902361111723891032114903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19869814815631854709486537 14902361111723891032114903)
        ·
          refine ⟨22353541667585836548172355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14902361111723891032114903 22353541667585836548172355)
          ·
            refine ⟨33530312501378754822258533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22353541667585836548172355 33530312501378754822258533)
            ·
              refine ⟨6286933594008516529173475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33530312501378754822258533 6286933594008516529173475)
              ·
                refine ⟨9430400391012774793760213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6286933594008516529173475 9430400391012774793760213)
                ·
                  refine ⟨221025009164361909228755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9430400391012774793760213 221025009164361909228755)
                  ·
                    rfl

theorem cell23_3874002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 4, 1, 7].length) (baseStart_3874002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3874002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3874002 prefixEnd_3874002 := by exact prefixLift 3874002
  have htrace : WordTrace (prefixWord ++ tailWord_3874002) baseStart_3874002 baseEnd_3874002 := by
    simpa [prefixWord, tailWord_3874002, baseEnd_3874002] using wordTrace_append hprefix tailTrace_3874002
  have hstable : (prefixWord ++ tailWord_3874002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3874002).length < 2 ^ (prefixWord ++ tailWord_3874002).sum := by decide
  have hdescent : baseEnd_3874002 < baseStart_3874002 := by decide
  rcases family_descends (prefixWord ++ tailWord_3874002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3874013 : List Nat := [1, 4, 3, 2, 2, 2, 1, 1, 1, 4, 2]
def baseStart_3874013 : Nat := 118140960795 + 3874013 * 2 ^ 59
def prefixEnd_3874013 : Nat := 4983230072969 + 3 ^ 40 * 3874013 * 2
def baseEnd_3874013 : Nat := 1989230730766456640021245

theorem tailTrace_3874013 : CollatzResearch.WordTrace tailWord_3874013 prefixEnd_3874013 1989230730766456640021245 := by
  unfold tailWord_3874013
  simp only [CollatzResearch.WordTrace]
  refine ⟨141296862114120004590554693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94197908076080003060369795 141296862114120004590554693)
  ·
    refine ⟨26493161646397500860729005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141296862114120004590554693 26493161646397500860729005)
    ·
      refine ⟨9934935617399062822773377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26493161646397500860729005 9934935617399062822773377)
      ·
        refine ⟨7451201713049297117080033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9934935617399062822773377 7451201713049297117080033)
        ·
          refine ⟨5588401284786972837810025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7451201713049297117080033 5588401284786972837810025)
          ·
            refine ⟨4191300963590229628357519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5588401284786972837810025 4191300963590229628357519)
            ·
              refine ⟨6286951445385344442536279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4191300963590229628357519 6286951445385344442536279)
              ·
                refine ⟨9430427168078016663804419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6286951445385344442536279 9430427168078016663804419)
                ·
                  refine ⟨14145640752117024995706629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9430427168078016663804419 14145640752117024995706629)
                  ·
                    refine ⟨2652307641021942186694993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14145640752117024995706629 2652307641021942186694993)
                    ·
                      refine ⟨1989230730766456640021245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2652307641021942186694993 1989230730766456640021245)
                      ·
                        rfl

theorem cell23_3874013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 1, 1, 1, 4, 2].length) (baseStart_3874013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3874013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3874013 prefixEnd_3874013 := by exact prefixLift 3874013
  have htrace : WordTrace (prefixWord ++ tailWord_3874013) baseStart_3874013 baseEnd_3874013 := by
    simpa [prefixWord, tailWord_3874013, baseEnd_3874013] using wordTrace_append hprefix tailTrace_3874013
  have hstable : (prefixWord ++ tailWord_3874013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3874013).length < 2 ^ (prefixWord ++ tailWord_3874013).sum := by decide
  have hdescent : baseEnd_3874013 < baseStart_3874013 := by decide
  rcases family_descends (prefixWord ++ tailWord_3874013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3874015 : List Nat := [1, 1, 2, 3, 2, 1, 3, 2, 1, 7]
def baseStart_3874015 : Nat := 118140960795 + 3874015 * 2 ^ 59
def prefixEnd_3874015 : Nat := 4983230072969 + 3 ^ 40 * 3874015 * 2
def baseEnd_3874015 : Nat := 663077252575921877398745

theorem tailTrace_3874015 : CollatzResearch.WordTrace tailWord_3874015 prefixEnd_3874015 663077252575921877398745 := by
  unfold tailWord_3874015
  simp only [CollatzResearch.WordTrace]
  refine ⟨141296935060112758932127499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94197956706741839288084999 141296935060112758932127499)
  ·
    refine ⟨211945402590169138398191249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141296935060112758932127499 211945402590169138398191249)
    ·
      refine ⟨158959051942626853798643437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211945402590169138398191249 158959051942626853798643437)
      ·
        refine ⟨59609644478485070174491289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158959051942626853798643437 59609644478485070174491289)
        ·
          refine ⟨44707233358863802630868467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59609644478485070174491289 44707233358863802630868467)
          ·
            refine ⟨67060850038295703946302701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44707233358863802630868467 67060850038295703946302701)
            ·
              refine ⟨25147818764360888979863513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67060850038295703946302701 25147818764360888979863513)
              ·
                refine ⟨18860864073270666734897635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25147818764360888979863513 18860864073270666734897635)
                ·
                  refine ⟨28291296109906000102346453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18860864073270666734897635 28291296109906000102346453)
                  ·
                    refine ⟨663077252575921877398745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28291296109906000102346453 663077252575921877398745)
                    ·
                      rfl

theorem cell23_3874015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 2, 1, 7].length) (baseStart_3874015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3874015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3874015 prefixEnd_3874015 := by exact prefixLift 3874015
  have htrace : WordTrace (prefixWord ++ tailWord_3874015) baseStart_3874015 baseEnd_3874015 := by
    simpa [prefixWord, tailWord_3874015, baseEnd_3874015] using wordTrace_append hprefix tailTrace_3874015
  have hstable : (prefixWord ++ tailWord_3874015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3874015).length < 2 ^ (prefixWord ++ tailWord_3874015).sum := by decide
  have hdescent : baseEnd_3874015 < baseStart_3874015 := by decide
  rcases family_descends (prefixWord ++ tailWord_3874015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3874095 : List Nat := [1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 8]
def baseStart_3874095 : Nat := 118140960795 + 3874095 * 2 ^ 59
def prefixEnd_3874095 : Nat := 4983230072969 + 3 ^ 40 * 3874095 * 2
def baseEnd_3874095 : Nat := 1989272836180125319195867

theorem tailTrace_3874095 : CollatzResearch.WordTrace tailWord_3874095 prefixEnd_3874095 1989272836180125319195867 := by
  unfold tailWord_3874095
  simp only [CollatzResearch.WordTrace]
  refine ⟨141299852899822932595039739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94199901933215288396693159 141299852899822932595039739)
  ·
    refine ⟨211949779349734398892559609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141299852899822932595039739 211949779349734398892559609)
    ·
      refine ⟨158962334512300799169419707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211949779349734398892559609 158962334512300799169419707)
      ·
        refine ⟨238443501768451198754129561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158962334512300799169419707 238443501768451198754129561)
        ·
          refine ⟨178832626326338399065597171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238443501768451198754129561 178832626326338399065597171)
          ·
            refine ⟨268248939489507598598395757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178832626326338399065597171 268248939489507598598395757)
            ·
              refine ⟨100593352308565349474398409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 268248939489507598598395757 100593352308565349474398409)
              ·
                refine ⟨75445014231424012105798807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100593352308565349474398409 75445014231424012105798807)
                ·
                  refine ⟨113167521347136018158698211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75445014231424012105798807 113167521347136018158698211)
                  ·
                    refine ⟨169751282020704027238047317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 113167521347136018158698211 169751282020704027238047317)
                    ·
                      refine ⟨1989272836180125319195867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 169751282020704027238047317 1989272836180125319195867)
                      ·
                        rfl

theorem cell23_3874095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 8].length) (baseStart_3874095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3874095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3874095 prefixEnd_3874095 := by exact prefixLift 3874095
  have htrace : WordTrace (prefixWord ++ tailWord_3874095) baseStart_3874095 baseEnd_3874095 := by
    simpa [prefixWord, tailWord_3874095, baseEnd_3874095] using wordTrace_append hprefix tailTrace_3874095
  have hstable : (prefixWord ++ tailWord_3874095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3874095).length < 2 ^ (prefixWord ++ tailWord_3874095).sum := by decide
  have hdescent : baseEnd_3874095 < baseStart_3874095 := by decide
  rcases family_descends (prefixWord ++ tailWord_3874095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3874113 : List Nat := [1, 2, 5, 2, 1, 2, 1, 4, 1, 4]
def baseStart_3874113 : Nat := 118140960795 + 3874113 * 2 ^ 59
def prefixEnd_3874113 : Nat := 4983230072969 + 3 ^ 40 * 3874113 * 2
def baseEnd_3874113 : Nat := 663094026277302082923595

theorem tailTrace_3874113 : CollatzResearch.WordTrace tailWord_3874113 prefixEnd_3874113 663094026277302082923595 := by
  unfold tailWord_3874113
  simp only [CollatzResearch.WordTrace]
  refine ⟨141300509413757721669194993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94200339609171814446129995 141300509413757721669194993)
  ·
    refine ⟨105975382060318291251896245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141300509413757721669194993 105975382060318291251896245)
    ·
      refine ⟨9935192068154839804865273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 105975382060318291251896245 9935192068154839804865273)
      ·
        refine ⟨7451394051116129853648955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9935192068154839804865273 7451394051116129853648955)
        ·
          refine ⟨11177091076674194780473433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7451394051116129853648955 11177091076674194780473433)
          ·
            refine ⟨8382818307505646085355075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11177091076674194780473433 8382818307505646085355075)
            ·
              refine ⟨12574227461258469128032613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8382818307505646085355075 12574227461258469128032613)
              ·
                refine ⟨2357667648985962961506115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12574227461258469128032613 2357667648985962961506115)
                ·
                  refine ⟨3536501473478944442259173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2357667648985962961506115 3536501473478944442259173)
                  ·
                    refine ⟨663094026277302082923595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3536501473478944442259173 663094026277302082923595)
                    ·
                      rfl

theorem cell23_3874113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 1, 4, 1, 4].length) (baseStart_3874113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3874113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3874113 prefixEnd_3874113 := by exact prefixLift 3874113
  have htrace : WordTrace (prefixWord ++ tailWord_3874113) baseStart_3874113 baseEnd_3874113 := by
    simpa [prefixWord, tailWord_3874113, baseEnd_3874113] using wordTrace_append hprefix tailTrace_3874113
  have hstable : (prefixWord ++ tailWord_3874113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3874113).length < 2 ^ (prefixWord ++ tailWord_3874113).sum := by decide
  have hdescent : baseEnd_3874113 < baseStart_3874113 := by decide
  rcases family_descends (prefixWord ++ tailWord_3874113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3874129 : List Nat := [1, 2, 2, 1, 4, 1, 2, 2, 1, 5, 2]
def baseStart_3874129 : Nat := 118140960795 + 3874129 * 2 ^ 59
def prefixEnd_3874129 : Nat := 4983230072969 + 3 ^ 40 * 3874129 * 2
def baseEnd_3874129 : Nat := 1989290294522378186170711

theorem tailTrace_3874129 : CollatzResearch.WordTrace tailWord_3874129 prefixEnd_3874129 1989290294522378186170711 := by
  unfold tailWord_3874129
  simp only [CollatzResearch.WordTrace]
  refine ⟨141301092981699756401777441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94200728654466504267851627 141301092981699756401777441)
  ·
    refine ⟨105975819736274817301333081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141301092981699756401777441 105975819736274817301333081)
    ·
      refine ⟨79481864802206112975999811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105975819736274817301333081 79481864802206112975999811)
      ·
        refine ⟨119222797203309169463999717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79481864802206112975999811 119222797203309169463999717)
        ·
          refine ⟨22354274475620469274499947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 119222797203309169463999717 22354274475620469274499947)
          ·
            refine ⟨33531411713430703911749921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22354274475620469274499947 33531411713430703911749921)
            ·
              refine ⟨25148558785073027933812441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33531411713430703911749921 25148558785073027933812441)
              ·
                refine ⟨18861419088804770950359331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25148558785073027933812441 18861419088804770950359331)
                ·
                  refine ⟨28292128633207156425538997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18861419088804770950359331 28292128633207156425538997)
                  ·
                    refine ⟨2652387059363170914894281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28292128633207156425538997 2652387059363170914894281)
                    ·
                      refine ⟨1989290294522378186170711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2652387059363170914894281 1989290294522378186170711)
                      ·
                        rfl

theorem cell23_3874129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 2, 1, 5, 2].length) (baseStart_3874129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3874129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3874129 prefixEnd_3874129 := by exact prefixLift 3874129
  have htrace : WordTrace (prefixWord ++ tailWord_3874129) baseStart_3874129 baseEnd_3874129 := by
    simpa [prefixWord, tailWord_3874129, baseEnd_3874129] using wordTrace_append hprefix tailTrace_3874129
  have hstable : (prefixWord ++ tailWord_3874129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3874129).length < 2 ^ (prefixWord ++ tailWord_3874129).sum := by decide
  have hdescent : baseEnd_3874129 < baseStart_3874129 := by decide
  rcases family_descends (prefixWord ++ tailWord_3874129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3874132 : List Nat := [2, 4, 1, 1, 2, 1, 1, 1, 2, 1, 7]
def baseStart_3874132 : Nat := 118140960795 + 3874132 * 2 ^ 59
def prefixEnd_3874132 : Nat := 4983230072969 + 3 ^ 40 * 3874132 * 2
def baseEnd_3874132 : Nat := 1989291834964341674433197

theorem tailTrace_3874132 : CollatzResearch.WordTrace tailWord_3874132 prefixEnd_3874132 1989291834964341674433197 := by
  unfold tailWord_3874132
  simp only [CollatzResearch.WordTrace]
  refine ⟨70650601200344443957068325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94200801600459258609424433 70650601200344443957068325)
  ·
    refine ⟨13246987725064583241950311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70650601200344443957068325 13246987725064583241950311)
    ·
      refine ⟨19870481587596874862925467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13246987725064583241950311 19870481587596874862925467)
      ·
        refine ⟨29805722381395312294388201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19870481587596874862925467 29805722381395312294388201)
        ·
          refine ⟨22354291786046484220791151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29805722381395312294388201 22354291786046484220791151)
          ·
            refine ⟨33531437679069726331186727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22354291786046484220791151 33531437679069726331186727)
            ·
              refine ⟨50297156518604589496780091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33531437679069726331186727 50297156518604589496780091)
              ·
                refine ⟨75445734777906884245170137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50297156518604589496780091 75445734777906884245170137)
                ·
                  refine ⟨56584301083430163183877603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75445734777906884245170137 56584301083430163183877603)
                  ·
                    refine ⟨84876451625145244775816405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56584301083430163183877603 84876451625145244775816405)
                    ·
                      refine ⟨1989291834964341674433197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 84876451625145244775816405 1989291834964341674433197)
                      ·
                        rfl

theorem cell23_3874132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 2, 1, 7].length) (baseStart_3874132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3874132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3874132 prefixEnd_3874132 := by exact prefixLift 3874132
  have htrace : WordTrace (prefixWord ++ tailWord_3874132) baseStart_3874132 baseEnd_3874132 := by
    simpa [prefixWord, tailWord_3874132, baseEnd_3874132] using wordTrace_append hprefix tailTrace_3874132
  have hstable : (prefixWord ++ tailWord_3874132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3874132).length < 2 ^ (prefixWord ++ tailWord_3874132).sum := by decide
  have hdescent : baseEnd_3874132 < baseStart_3874132 := by decide
  rcases family_descends (prefixWord ++ tailWord_3874132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3874146 : List Nat := [3, 3, 2, 1, 1, 1, 3, 1, 1, 5, 2]
def baseStart_3874146 : Nat := 118140960795 + 3874146 * 2 ^ 59
def prefixEnd_3874146 : Nat := 4983230072969 + 3 ^ 40 * 3874146 * 2
def baseEnd_3874146 : Nat := 1989299023693504619658133

theorem tailTrace_3874146 : CollatzResearch.WordTrace tailWord_3874146 prefixEnd_3874146 1989299023693504619658133 := by
  unfold tailWord_3874146
  simp only [CollatzResearch.WordTrace]
  refine ⟨35325428255659542076286573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94201142015092112203430861 35325428255659542076286573)
  ·
    refine ⟨13247035595872328278607465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35325428255659542076286573 13247035595872328278607465)
    ·
      refine ⟨9935276696904246208955599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13247035595872328278607465 9935276696904246208955599)
      ·
        refine ⟨14902915045356369313433399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9935276696904246208955599 14902915045356369313433399)
        ·
          refine ⟨22354372568034553970150099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14902915045356369313433399 22354372568034553970150099)
          ·
            refine ⟨33531558852051830955225149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22354372568034553970150099 33531558852051830955225149)
            ·
              refine ⟨12574334569519436608209431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33531558852051830955225149 12574334569519436608209431)
              ·
                refine ⟨18861501854279154912314147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12574334569519436608209431 18861501854279154912314147)
                ·
                  refine ⟨28292252781418732368471221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18861501854279154912314147 28292252781418732368471221)
                  ·
                    refine ⟨2652398698258006159544177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28292252781418732368471221 2652398698258006159544177)
                    ·
                      refine ⟨1989299023693504619658133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2652398698258006159544177 1989299023693504619658133)
                      ·
                        rfl

theorem cell23_3874146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 1, 1, 5, 2].length) (baseStart_3874146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3874146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3874146 prefixEnd_3874146 := by exact prefixLift 3874146
  have htrace : WordTrace (prefixWord ++ tailWord_3874146) baseStart_3874146 baseEnd_3874146 := by
    simpa [prefixWord, tailWord_3874146, baseEnd_3874146] using wordTrace_append hprefix tailTrace_3874146
  have hstable : (prefixWord ++ tailWord_3874146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3874146).length < 2 ^ (prefixWord ++ tailWord_3874146).sum := by decide
  have hdescent : baseEnd_3874146 < baseStart_3874146 := by decide
  rcases family_descends (prefixWord ++ tailWord_3874146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3874156 : List Nat := [2, 2, 1, 1, 5, 1, 4, 1, 1, 5]
def baseStart_3874156 : Nat := 118140960795 + 3874156 * 2 ^ 59
def prefixEnd_3874156 : Nat := 4983230072969 + 3 ^ 40 * 3874156 * 2
def baseEnd_3874156 : Nat := 663101386166683193511029

theorem tailTrace_3874156 : CollatzResearch.WordTrace tailWord_3874156 prefixEnd_3874156 663101386166683193511029 := by
  unfold tailWord_3874156
  simp only [CollatzResearch.WordTrace]
  refine ⟨70651038876300970006505161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94201385168401293342006881 70651038876300970006505161)
  ·
    refine ⟨52988279157225727504878871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70651038876300970006505161 52988279157225727504878871)
    ·
      refine ⟨79482418735838591257318307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52988279157225727504878871 79482418735838591257318307)
      ·
        refine ⟨119223628103757886885977461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79482418735838591257318307 119223628103757886885977461)
        ·
          refine ⟨11177215134727301895560387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 119223628103757886885977461 11177215134727301895560387)
          ·
            refine ⟨16765822702090952843340581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11177215134727301895560387 16765822702090952843340581)
            ·
              refine ⟨3143591756642053658126359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16765822702090952843340581 3143591756642053658126359)
              ·
                refine ⟨4715387634963080487189539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3143591756642053658126359 4715387634963080487189539)
                ·
                  refine ⟨7073081452444620730784309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4715387634963080487189539 7073081452444620730784309)
                  ·
                    refine ⟨663101386166683193511029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7073081452444620730784309 663101386166683193511029)
                    ·
                      rfl

theorem cell23_3874156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 5].length) (baseStart_3874156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3874156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3874156 prefixEnd_3874156 := by exact prefixLift 3874156
  have htrace : WordTrace (prefixWord ++ tailWord_3874156) baseStart_3874156 baseEnd_3874156 := by
    simpa [prefixWord, tailWord_3874156, baseEnd_3874156] using wordTrace_append hprefix tailTrace_3874156
  have hstable : (prefixWord ++ tailWord_3874156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3874156).length < 2 ^ (prefixWord ++ tailWord_3874156).sum := by decide
  have hdescent : baseEnd_3874156 < baseStart_3874156 := by decide
  rcases family_descends (prefixWord ++ tailWord_3874156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3874159 : List Nat := [1, 1, 2, 1, 3, 1, 5, 3, 1, 1, 4]
def baseStart_3874159 : Nat := 118140960795 + 3874159 * 2 ^ 59
def prefixEnd_3874159 : Nat := 4983230072969 + 3 ^ 40 * 3874159 * 2
def baseEnd_3874159 : Nat := 1989305698942013068795573

theorem tailTrace_3874159 : CollatzResearch.WordTrace tailWord_3874159 prefixEnd_3874159 1989305698942013068795573 := by
  unfold tailWord_3874159
  simp only [CollatzResearch.WordTrace]
  refine ⟨141302187171591071525369531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94201458114394047683579687 141302187171591071525369531)
  ·
    refine ⟨211953280757386607288054297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141302187171591071525369531 211953280757386607288054297)
    ·
      refine ⟨158964960568039955466040723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211953280757386607288054297 158964960568039955466040723)
      ·
        refine ⟨238447440852059933199061085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158964960568039955466040723 238447440852059933199061085)
        ·
          refine ⟨89417790319522474949647907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 238447440852059933199061085 89417790319522474949647907)
          ·
            refine ⟨134126685479283712424471861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89417790319522474949647907 134126685479283712424471861)
            ·
              refine ⟨12574376763682848039794237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 134126685479283712424471861 12574376763682848039794237)
              ·
                refine ⟨4715391286381068014922839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12574376763682848039794237 4715391286381068014922839)
                ·
                  refine ⟨7073086929571602022384259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4715391286381068014922839 7073086929571602022384259)
                  ·
                    refine ⟨10609630394357403033576389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7073086929571602022384259 10609630394357403033576389)
                    ·
                      refine ⟨1989305698942013068795573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10609630394357403033576389 1989305698942013068795573)
                      ·
                        rfl

theorem cell23_3874159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 3, 1, 1, 4].length) (baseStart_3874159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3874159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3874159 prefixEnd_3874159 := by exact prefixLift 3874159
  have htrace : WordTrace (prefixWord ++ tailWord_3874159) baseStart_3874159 baseEnd_3874159 := by
    simpa [prefixWord, tailWord_3874159, baseEnd_3874159] using wordTrace_append hprefix tailTrace_3874159
  have hstable : (prefixWord ++ tailWord_3874159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3874159).length < 2 ^ (prefixWord ++ tailWord_3874159).sum := by decide
  have hdescent : baseEnd_3874159 < baseStart_3874159 := by decide
  rcases family_descends (prefixWord ++ tailWord_3874159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3874172 : List Nat := [2, 2, 2, 1, 1, 1, 4, 2, 1, 1, 6]
def baseStart_3874172 : Nat := 118140960795 + 3874172 * 2 ^ 59
def prefixEnd_3874172 : Nat := 4983230072969 + 3 ^ 40 * 3874172 * 2
def baseEnd_3874172 : Nat := 1989312374190521517933013

theorem tailTrace_3874172 : CollatzResearch.WordTrace tailWord_3874172 prefixEnd_3874172 1989312374190521517933013 := by
  unfold tailWord_3874172
  simp only [CollatzResearch.WordTrace]
  refine ⟨70651330660271987372796385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94201774213695983163728513 70651330660271987372796385)
  ·
    refine ⟨52988497995203990529597289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70651330660271987372796385 52988497995203990529597289)
    ·
      refine ⟨39741373496402992897197967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52988497995203990529597289 39741373496402992897197967)
      ·
        refine ⟨59612060244604489345796951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39741373496402992897197967 59612060244604489345796951)
        ·
          refine ⟨89418090366906734018695427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59612060244604489345796951 89418090366906734018695427)
          ·
            refine ⟨134127135550360101028043141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89418090366906734018695427 134127135550360101028043141)
            ·
              refine ⟨25148837915692518942758089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 134127135550360101028043141 25148837915692518942758089)
              ·
                refine ⟨18861628436769389207068567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25148837915692518942758089 18861628436769389207068567)
                ·
                  refine ⟨28292442655154083810602851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18861628436769389207068567 28292442655154083810602851)
                  ·
                    refine ⟨42438663982731125715904277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28292442655154083810602851 42438663982731125715904277)
                    ·
                      refine ⟨1989312374190521517933013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42438663982731125715904277 1989312374190521517933013)
                      ·
                        rfl

theorem cell23_3874172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 2, 1, 1, 6].length) (baseStart_3874172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3874172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3874172 prefixEnd_3874172 := by exact prefixLift 3874172
  have htrace : WordTrace (prefixWord ++ tailWord_3874172) baseStart_3874172 baseEnd_3874172 := by
    simpa [prefixWord, tailWord_3874172, baseEnd_3874172] using wordTrace_append hprefix tailTrace_3874172
  have hstable : (prefixWord ++ tailWord_3874172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3874172).length < 2 ^ (prefixWord ++ tailWord_3874172).sum := by decide
  have hdescent : baseEnd_3874172 < baseStart_3874172 := by decide
  rcases family_descends (prefixWord ++ tailWord_3874172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3874179 : List Nat := [1, 1, 1, 3, 5, 2, 1, 2, 1, 1, 5]
def baseStart_3874179 : Nat := 118140960795 + 3874179 * 2 ^ 59
def prefixEnd_3874179 : Nat := 4983230072969 + 3 ^ 40 * 3874179 * 2
def baseEnd_3874179 : Nat := 1989315968555102990545481

theorem tailTrace_3874179 : CollatzResearch.WordTrace tailWord_3874179 prefixEnd_3874179 1989315968555102990545481 := by
  unfold tailWord_3874179
  simp only [CollatzResearch.WordTrace]
  refine ⟨141302916631518614941097591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94201944421012409960731727 141302916631518614941097591)
  ·
    refine ⟨211954374947277922411646387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141302916631518614941097591 211954374947277922411646387)
    ·
      refine ⟨317931562420916883617469581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211954374947277922411646387 317931562420916883617469581)
      ·
        refine ⟨119224335907843831356551093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 317931562420916883617469581 119224335907843831356551093)
        ·
          refine ⟨11177281491360359189676665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 119224335907843831356551093 11177281491360359189676665)
          ·
            refine ⟨8382961118520269392257499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11177281491360359189676665 8382961118520269392257499)
            ·
              refine ⟨12574441677780404088386249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8382961118520269392257499 12574441677780404088386249)
              ·
                refine ⟨9430831258335303066289687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12574441677780404088386249 9430831258335303066289687)
                ·
                  refine ⟨14146246887502954599434531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9430831258335303066289687 14146246887502954599434531)
                  ·
                    refine ⟨21219370331254431899151797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14146246887502954599434531 21219370331254431899151797)
                    ·
                      refine ⟨1989315968555102990545481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21219370331254431899151797 1989315968555102990545481)
                      ·
                        rfl

theorem cell23_3874179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 2, 1, 1, 5].length) (baseStart_3874179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3874179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3874179 prefixEnd_3874179 := by exact prefixLift 3874179
  have htrace : WordTrace (prefixWord ++ tailWord_3874179) baseStart_3874179 baseEnd_3874179 := by
    simpa [prefixWord, tailWord_3874179, baseEnd_3874179] using wordTrace_append hprefix tailTrace_3874179
  have hstable : (prefixWord ++ tailWord_3874179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3874179).length < 2 ^ (prefixWord ++ tailWord_3874179).sum := by decide
  have hdescent : baseEnd_3874179 < baseStart_3874179 := by decide
  rcases family_descends (prefixWord ++ tailWord_3874179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3874204 : List Nat := [2, 2, 3, 4, 2, 1, 1, 3, 1, 1, 3]
def baseStart_3874204 : Nat := 118140960795 + 3874204 * 2 ^ 59
def prefixEnd_3874204 : Nat := 4983230072969 + 3 ^ 40 * 3874204 * 2
def baseEnd_3874204 : Nat := 1989328805571465392732867

theorem tailTrace_3874204 : CollatzResearch.WordTrace tailWord_3874204 prefixEnd_3874204 1989328805571465392732867 := by
  unfold tailWord_3874204
  simp only [CollatzResearch.WordTrace]
  refine ⟨70651914228214022105378833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94202552304285362807171777 70651914228214022105378833)
  ·
    refine ⟨52988935671160516579034125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70651914228214022105378833 52988935671160516579034125)
    ·
      refine ⟨19870850876685193717137797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52988935671160516579034125 19870850876685193717137797)
      ·
        refine ⟨3725784539378473821963337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19870850876685193717137797 3725784539378473821963337)
        ·
          refine ⟨2794338404533855366472503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3725784539378473821963337 2794338404533855366472503)
          ·
            refine ⟨4191507606800783049708755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2794338404533855366472503 4191507606800783049708755)
            ·
              refine ⟨6287261410201174574563133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4191507606800783049708755 6287261410201174574563133)
              ·
                refine ⟨2357723028825440465461175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6287261410201174574563133 2357723028825440465461175)
                ·
                  refine ⟨3536584543238160698191763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2357723028825440465461175 3536584543238160698191763)
                  ·
                    refine ⟨5304876814857241047287645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3536584543238160698191763 5304876814857241047287645)
                    ·
                      refine ⟨1989328805571465392732867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5304876814857241047287645 1989328805571465392732867)
                      ·
                        rfl

theorem cell23_3874204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_3874204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3874204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3874204 prefixEnd_3874204 := by exact prefixLift 3874204
  have htrace : WordTrace (prefixWord ++ tailWord_3874204) baseStart_3874204 baseEnd_3874204 := by
    simpa [prefixWord, tailWord_3874204, baseEnd_3874204] using wordTrace_append hprefix tailTrace_3874204
  have hstable : (prefixWord ++ tailWord_3874204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3874204).length < 2 ^ (prefixWord ++ tailWord_3874204).sum := by decide
  have hdescent : baseEnd_3874204 < baseStart_3874204 := by decide
  rcases family_descends (prefixWord ++ tailWord_3874204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3874212 : List Nat := [2, 3, 1, 2, 1, 1, 1, 2, 1, 9]
def baseStart_3874212 : Nat := 118140960795 + 3874212 * 2 ^ 59
def prefixEnd_3874212 : Nat := 4983230072969 + 3 ^ 40 * 3874212 * 2
def baseEnd_3874212 : Nat := 663110971138900453810943

theorem tailTrace_3874212 : CollatzResearch.WordTrace tailWord_3874212 prefixEnd_3874212 663110971138900453810943 := by
  unfold tailWord_3874212
  simp only [CollatzResearch.WordTrace]
  refine ⟨70652060120199530788524445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94202746826932707718032593 70652060120199530788524445)
  ·
    refine ⟨26494522545074824045696667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70652060120199530788524445 26494522545074824045696667)
    ·
      refine ⟨39741783817612236068545001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26494522545074824045696667 39741783817612236068545001)
      ·
        refine ⟨29806337863209177051408751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39741783817612236068545001 29806337863209177051408751)
        ·
          refine ⟨44709506794813765577113127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29806337863209177051408751 44709506794813765577113127)
          ·
            refine ⟨67064260192220648365669691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44709506794813765577113127 67064260192220648365669691)
            ·
              refine ⟨100596390288330972548504537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67064260192220648365669691 100596390288330972548504537)
              ·
                refine ⟨75447292716248229411378403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100596390288330972548504537 75447292716248229411378403)
                ·
                  refine ⟨113170939074372344117067605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75447292716248229411378403 113170939074372344117067605)
                  ·
                    refine ⟨663110971138900453810943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 113170939074372344117067605 663110971138900453810943)
                    ·
                      rfl

theorem cell23_3874212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 1, 9].length) (baseStart_3874212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3874212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3874212 prefixEnd_3874212 := by exact prefixLift 3874212
  have htrace : WordTrace (prefixWord ++ tailWord_3874212) baseStart_3874212 baseEnd_3874212 := by
    simpa [prefixWord, tailWord_3874212, baseEnd_3874212] using wordTrace_append hprefix tailTrace_3874212
  have hstable : (prefixWord ++ tailWord_3874212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3874212).length < 2 ^ (prefixWord ++ tailWord_3874212).sum := by decide
  have hdescent : baseEnd_3874212 < baseStart_3874212 := by decide
  rcases family_descends (prefixWord ++ tailWord_3874212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3874216 : List Nat := [2, 1, 6, 1, 2, 2, 9]
def baseStart_3874216 : Nat := 118140960795 + 3874216 * 2 ^ 59
def prefixEnd_3874216 : Nat := 4983230072969 + 3 ^ 40 * 3874216 * 2
def baseEnd_3874216 : Nat := 24559690954806411676331

theorem tailTrace_3874216 : CollatzResearch.WordTrace tailWord_3874216 prefixEnd_3874216 24559690954806411676331 := by
  unfold tailWord_3874216
  simp only [CollatzResearch.WordTrace]
  refine ⟨70652133066192285130097251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94202844088256380173463001 70652133066192285130097251)
  ·
    refine ⟨105978199599288427695145877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70652133066192285130097251 105978199599288427695145877)
    ·
      refine ⟨4967728106216645048209963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 105978199599288427695145877 4967728106216645048209963)
      ·
        refine ⟨7451592159324967572314945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4967728106216645048209963 7451592159324967572314945)
        ·
          refine ⟨5588694119493725679236209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7451592159324967572314945 5588694119493725679236209)
          ·
            refine ⟨4191520589620294259427157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5588694119493725679236209 4191520589620294259427157)
            ·
              refine ⟨24559690954806411676331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4191520589620294259427157 24559690954806411676331)
              ·
                rfl

theorem cell23_3874216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 9].length) (baseStart_3874216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3874216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3874216 prefixEnd_3874216 := by exact prefixLift 3874216
  have htrace : WordTrace (prefixWord ++ tailWord_3874216) baseStart_3874216 baseEnd_3874216 := by
    simpa [prefixWord, tailWord_3874216, baseEnd_3874216] using wordTrace_append hprefix tailTrace_3874216
  have hstable : (prefixWord ++ tailWord_3874216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3874216).length < 2 ^ (prefixWord ++ tailWord_3874216).sum := by decide
  have hdescent : baseEnd_3874216 < baseStart_3874216 := by decide
  rcases family_descends (prefixWord ++ tailWord_3874216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3874243 : List Nat := [1, 1, 1, 3, 1, 1, 8, 1, 2, 1, 3]
def baseStart_3874243 : Nat := 118140960795 + 3874243 * 2 ^ 59
def prefixEnd_3874243 : Nat := 4983230072969 + 3 ^ 40 * 3874243 * 2
def baseEnd_3874243 : Nat := 1989348831316990740145187

theorem tailTrace_3874243 : CollatzResearch.WordTrace tailWord_3874243 prefixEnd_3874243 1989348831316990740145187 := by
  unfold tailWord_3874243
  simp only [CollatzResearch.WordTrace]
  refine ⟨141305250903286753871427383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94203500602191169247618255 141305250903286753871427383)
  ·
    refine ⟨211957876354930130807141075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141305250903286753871427383 211957876354930130807141075)
    ·
      refine ⟨317936814532395196210711613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211957876354930130807141075 317936814532395196210711613)
      ·
        refine ⟨119226305449648198579016855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 317936814532395196210711613 119226305449648198579016855)
        ·
          refine ⟨178839458174472297868525283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119226305449648198579016855 178839458174472297868525283)
          ·
            refine ⟨268259187261708446802787925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178839458174472297868525283 268259187261708446802787925)
            ·
              refine ⟨3143662350723145860970171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 268259187261708446802787925 3143662350723145860970171)
              ·
                refine ⟨4715493526084718791455257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3143662350723145860970171 4715493526084718791455257)
                ·
                  refine ⟨3536620144563539093591443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4715493526084718791455257 3536620144563539093591443)
                  ·
                    refine ⟨5304930216845308640387165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3536620144563539093591443 5304930216845308640387165)
                    ·
                      refine ⟨1989348831316990740145187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5304930216845308640387165 1989348831316990740145187)
                      ·
                        rfl

theorem cell23_3874243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 8, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 8, 1, 2, 1, 3].length) (baseStart_3874243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3874243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3874243 prefixEnd_3874243 := by exact prefixLift 3874243
  have htrace : WordTrace (prefixWord ++ tailWord_3874243) baseStart_3874243 baseEnd_3874243 := by
    simpa [prefixWord, tailWord_3874243, baseEnd_3874243] using wordTrace_append hprefix tailTrace_3874243
  have hstable : (prefixWord ++ tailWord_3874243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3874243).length < 2 ^ (prefixWord ++ tailWord_3874243).sum := by decide
  have hdescent : baseEnd_3874243 < baseStart_3874243 := by decide
  rcases family_descends (prefixWord ++ tailWord_3874243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3874266 : List Nat := [3, 1, 1, 2, 3, 2, 1, 1, 3, 4, 2]
def baseStart_3874266 : Nat := 118140960795 + 3874266 * 2 ^ 59
def prefixEnd_3874266 : Nat := 4983230072969 + 3 ^ 40 * 3874266 * 2
def baseEnd_3874266 : Nat := 1989360641372044150157581

theorem tailTrace_3874266 : CollatzResearch.WordTrace tailWord_3874266 prefixEnd_3874266 1989360641372044150157581 := by
  unfold tailWord_3874266
  simp only [CollatzResearch.WordTrace]
  refine ⟨35326522445550857199878663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94204059854802285866343101 35326522445550857199878663)
  ·
    refine ⟨52989783668326285799817995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35326522445550857199878663 52989783668326285799817995)
    ·
      refine ⟨79484675502489428699726993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52989783668326285799817995 79484675502489428699726993)
      ·
        refine ⟨59613506626867071524795245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79484675502489428699726993 59613506626867071524795245)
        ·
          refine ⟨22355064985075151821798217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59613506626867071524795245 22355064985075151821798217)
          ·
            refine ⟨16766298738806363866348663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22355064985075151821798217 16766298738806363866348663)
            ·
              refine ⟨25149448108209545799522995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16766298738806363866348663 25149448108209545799522995)
              ·
                refine ⟨37724172162314318699284493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25149448108209545799522995 37724172162314318699284493)
                ·
                  refine ⟨14146564560867869512231685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37724172162314318699284493 14146564560867869512231685)
                  ·
                    refine ⟨2652480855162725533543441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14146564560867869512231685 2652480855162725533543441)
                    ·
                      refine ⟨1989360641372044150157581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2652480855162725533543441 1989360641372044150157581)
                      ·
                        rfl

theorem cell23_3874266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 1, 3, 4, 2].length) (baseStart_3874266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3874266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3874266 prefixEnd_3874266 := by exact prefixLift 3874266
  have htrace : WordTrace (prefixWord ++ tailWord_3874266) baseStart_3874266 baseEnd_3874266 := by
    simpa [prefixWord, tailWord_3874266, baseEnd_3874266] using wordTrace_append hprefix tailTrace_3874266
  have hstable : (prefixWord ++ tailWord_3874266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3874266).length < 2 ^ (prefixWord ++ tailWord_3874266).sum := by decide
  have hdescent : baseEnd_3874266 < baseStart_3874266 := by decide
  rcases family_descends (prefixWord ++ tailWord_3874266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3874272 : List Nat := [2, 1, 1, 3, 1, 1, 2, 1, 11]
def baseStart_3874272 : Nat := 118140960795 + 3874272 * 2 ^ 59
def prefixEnd_3874272 : Nat := 4983230072969 + 3 ^ 40 * 3874272 * 2
def baseEnd_3874272 : Nat := 221040413583996791853617

theorem tailTrace_3874272 : CollatzResearch.WordTrace tailWord_3874272 prefixEnd_3874272 221040413583996791853617 := by
  unfold tailWord_3874272
  simp only [CollatzResearch.WordTrace]
  refine ⟨70653154310090845912116535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94204205746787794549488713 70653154310090845912116535)
  ·
    refine ⟨105979731465136268868174803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70653154310090845912116535 105979731465136268868174803)
    ·
      refine ⟨158969597197704403302262205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105979731465136268868174803 158969597197704403302262205)
      ·
        refine ⟨59613598949139151238348327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 158969597197704403302262205 59613598949139151238348327)
        ·
          refine ⟨89420398423708726857522491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59613598949139151238348327 89420398423708726857522491)
          ·
            refine ⟨134130597635563090286283737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89420398423708726857522491 134130597635563090286283737)
            ·
              refine ⟨100597948226672317714712803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134130597635563090286283737 100597948226672317714712803)
              ·
                refine ⟨150896922340008476572069205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100597948226672317714712803 150896922340008476572069205)
                ·
                  refine ⟨221040413583996791853617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 150896922340008476572069205 221040413583996791853617)
                  ·
                    rfl

theorem cell23_3874272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 11].length) (baseStart_3874272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3874272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3874272 prefixEnd_3874272 := by exact prefixLift 3874272
  have htrace : WordTrace (prefixWord ++ tailWord_3874272) baseStart_3874272 baseEnd_3874272 := by
    simpa [prefixWord, tailWord_3874272, baseEnd_3874272] using wordTrace_append hprefix tailTrace_3874272
  have hstable : (prefixWord ++ tailWord_3874272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3874272).length < 2 ^ (prefixWord ++ tailWord_3874272).sum := by decide
  have hdescent : baseEnd_3874272 < baseStart_3874272 := by decide
  rcases family_descends (prefixWord ++ tailWord_3874272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3874299 : List Nat := [1, 1, 1, 1, 1, 3, 2, 5, 2, 3, 3]
def baseStart_3874299 : Nat := 118140960795 + 3874299 * 2 ^ 59
def prefixEnd_3874299 : Nat := 4983230072969 + 3 ^ 40 * 3874299 * 2
def baseEnd_3874299 : Nat := 1989377586233642521044929

theorem tailTrace_3874299 : CollatzResearch.WordTrace tailWord_3874299 prefixEnd_3874299 1989377586233642521044929 := by
  unfold tailWord_3874299
  simp only [CollatzResearch.WordTrace]
  refine ⟨141307293391083875435465951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94204862260722583623643967 141307293391083875435465951)
  ·
    refine ⟨211960940086625813153198927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141307293391083875435465951 211960940086625813153198927)
    ·
      refine ⟨317941410129938719729798391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211960940086625813153198927 317941410129938719729798391)
      ·
        refine ⟨476912115194908079594697587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317941410129938719729798391 476912115194908079594697587)
        ·
          refine ⟨715368172792362119392046381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 476912115194908079594697587 715368172792362119392046381)
          ·
            refine ⟨268263064797135794772017393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 715368172792362119392046381 268263064797135794772017393)
            ·
              refine ⟨201197298597851846079013045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 268263064797135794772017393 201197298597851846079013045)
              ·
                refine ⟨18862246743548610569907473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 201197298597851846079013045 18862246743548610569907473)
                ·
                  refine ⟨14146685057661457927430605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18862246743548610569907473 14146685057661457927430605)
                  ·
                    refine ⟨5305006896623046722786477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14146685057661457927430605 5305006896623046722786477)
                    ·
                      refine ⟨1989377586233642521044929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5305006896623046722786477 1989377586233642521044929)
                      ·
                        rfl

theorem cell23_3874299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 5, 2, 3, 3].length) (baseStart_3874299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3874299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3874299 prefixEnd_3874299 := by exact prefixLift 3874299
  have htrace : WordTrace (prefixWord ++ tailWord_3874299) baseStart_3874299 baseEnd_3874299 := by
    simpa [prefixWord, tailWord_3874299, baseEnd_3874299] using wordTrace_append hprefix tailTrace_3874299
  have hstable : (prefixWord ++ tailWord_3874299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3874299).length < 2 ^ (prefixWord ++ tailWord_3874299).sum := by decide
  have hdescent : baseEnd_3874299 < baseStart_3874299 := by decide
  rcases family_descends (prefixWord ++ tailWord_3874299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3874306 : List Nat := [3, 4, 1, 2, 1, 1, 1, 1, 9]
def baseStart_3874306 : Nat := 118140960795 + 3874306 * 2 ^ 59
def prefixEnd_3874306 : Nat := 4983230072969 + 3 ^ 40 * 3874306 * 2
def baseEnd_3874306 : Nat := 221042353399802665961933

theorem tailTrace_3874306 : CollatzResearch.WordTrace tailWord_3874306 prefixEnd_3874306 221042353399802665961933 := by
  unfold tailWord_3874306
  simp only [CollatzResearch.WordTrace]
  refine ⟨35326887175514628907742693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94205032468039010420647181 35326887175514628907742693)
  ·
    refine ⟨6623791345408992920201755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35326887175514628907742693 6623791345408992920201755)
    ·
      refine ⟨9935687018113489380302633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6623791345408992920201755 9935687018113489380302633)
      ·
        refine ⟨7451765263585117035226975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9935687018113489380302633 7451765263585117035226975)
        ·
          refine ⟨11177647895377675552840463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7451765263585117035226975 11177647895377675552840463)
          ·
            refine ⟨16766471843066513329260695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11177647895377675552840463 16766471843066513329260695)
            ·
              refine ⟨25149707764599769993891043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16766471843066513329260695 25149707764599769993891043)
              ·
                refine ⟨37724561646899654990836565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25149707764599769993891043 37724561646899654990836565)
                ·
                  refine ⟨221042353399802665961933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 37724561646899654990836565 221042353399802665961933)
                  ·
                    rfl

theorem cell23_3874306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 1, 9].length) (baseStart_3874306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3874306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3874306 prefixEnd_3874306 := by exact prefixLift 3874306
  have htrace : WordTrace (prefixWord ++ tailWord_3874306) baseStart_3874306 baseEnd_3874306 := by
    simpa [prefixWord, tailWord_3874306, baseEnd_3874306] using wordTrace_append hprefix tailTrace_3874306
  have hstable : (prefixWord ++ tailWord_3874306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3874306).length < 2 ^ (prefixWord ++ tailWord_3874306).sum := by decide
  have hdescent : baseEnd_3874306 < baseStart_3874306 := by decide
  rcases family_descends (prefixWord ++ tailWord_3874306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3874374 : List Nat := [6, 1, 1, 1, 4, 1, 1, 3, 5]
def baseStart_3874374 : Nat := 118140960795 + 3874374 * 2 ^ 59
def prefixEnd_3874374 : Nat := 4983230072969 + 3 ^ 40 * 3874374 * 2
def baseEnd_3874374 : Nat := 221046233031414414178565

theorem tailTrace_3874374 : CollatzResearch.WordTrace tailWord_3874374 prefixEnd_3874374 221046233031414414178565 := by
  unfold tailWord_3874374
  simp only [CollatzResearch.WordTrace]
  refine ⟨4415938402056630101388943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 94206685910541442162964117 4415938402056630101388943)
  ·
    refine ⟨6623907603084945152083415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4415938402056630101388943 6623907603084945152083415)
    ·
      refine ⟨9935861404627417728125123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6623907603084945152083415 9935861404627417728125123)
      ·
        refine ⟨14903792106941126592187685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9935861404627417728125123 14903792106941126592187685)
        ·
          refine ⟨2794461020051461236035191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14903792106941126592187685 2794461020051461236035191)
          ·
            refine ⟨4191691530077191854052787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2794461020051461236035191 4191691530077191854052787)
            ·
              refine ⟨6287537295115787781079181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4191691530077191854052787 6287537295115787781079181)
              ·
                refine ⟨2357826485668420417904693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6287537295115787781079181 2357826485668420417904693)
                ·
                  refine ⟨221046233031414414178565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2357826485668420417904693 221046233031414414178565)
                  ·
                    rfl

theorem cell23_3874374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 1, 3, 5].length) (baseStart_3874374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3874374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3874374 prefixEnd_3874374 := by exact prefixLift 3874374
  have htrace : WordTrace (prefixWord ++ tailWord_3874374) baseStart_3874374 baseEnd_3874374 := by
    simpa [prefixWord, tailWord_3874374, baseEnd_3874374] using wordTrace_append hprefix tailTrace_3874374
  have hstable : (prefixWord ++ tailWord_3874374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3874374).length < 2 ^ (prefixWord ++ tailWord_3874374).sum := by decide
  have hdescent : baseEnd_3874374 < baseStart_3874374 := by decide
  rcases family_descends (prefixWord ++ tailWord_3874374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3874396 : List Nat := [2, 2, 4, 1, 2, 1, 2, 1, 8]
def baseStart_3874396 : Nat := 118140960795 + 3874396 * 2 ^ 59
def prefixEnd_3874396 : Nat := 4983230072969 + 3 ^ 40 * 3874396 * 2
def baseEnd_3874396 : Nat := 221047488206347626836887

theorem tailTrace_3874396 : CollatzResearch.WordTrace tailWord_3874396 prefixEnd_3874396 221047488206347626836887 := by
  unfold tailWord_3874396
  simp only [CollatzResearch.WordTrace]
  refine ⟨70655415635866230500873521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94207220847821640667831361 70655415635866230500873521)
  ·
    refine ⟨52991561726899672875655141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70655415635866230500873521 52991561726899672875655141)
    ·
      refine ⟨9935917823793688664185339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52991561726899672875655141 9935917823793688664185339)
      ·
        refine ⟨14903876735690532996278009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9935917823793688664185339 14903876735690532996278009)
        ·
          refine ⟨11177907551767899747208507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14903876735690532996278009 11177907551767899747208507)
          ·
            refine ⟨16766861327651849620812761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11177907551767899747208507 16766861327651849620812761)
            ·
              refine ⟨12575145995738887215609571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16766861327651849620812761 12575145995738887215609571)
              ·
                refine ⟨18862718993608330823414357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12575145995738887215609571 18862718993608330823414357)
                ·
                  refine ⟨221047488206347626836887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 18862718993608330823414357 221047488206347626836887)
                  ·
                    rfl

theorem cell23_3874396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 2, 1, 8].length) (baseStart_3874396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3874396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3874396 prefixEnd_3874396 := by exact prefixLift 3874396
  have htrace : WordTrace (prefixWord ++ tailWord_3874396) baseStart_3874396 baseEnd_3874396 := by
    simpa [prefixWord, tailWord_3874396, baseEnd_3874396] using wordTrace_append hprefix tailTrace_3874396
  have hstable : (prefixWord ++ tailWord_3874396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3874396).length < 2 ^ (prefixWord ++ tailWord_3874396).sum := by decide
  have hdescent : baseEnd_3874396 < baseStart_3874396 := by decide
  rcases family_descends (prefixWord ++ tailWord_3874396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3874413 : List Nat := [1, 5, 1, 1, 4, 1, 1, 3, 6]
def baseStart_3874413 : Nat := 118140960795 + 3874413 * 2 ^ 59
def prefixEnd_3874413 : Nat := 4983230072969 + 3 ^ 40 * 3874413 * 2
def baseEnd_3874413 : Nat := 221048458114250563891045

theorem tailTrace_3874413 : CollatzResearch.WordTrace tailWord_3874413 prefixEnd_3874413 221048458114250563891045 := by
  unfold tailWord_3874413
  simp only [CollatzResearch.WordTrace]
  refine ⟨141311451312670872905115893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94207634208447248603410595 141311451312670872905115893)
  ·
    refine ⟨13247948560562894334854615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 141311451312670872905115893 13247948560562894334854615)
    ·
      refine ⟨19871922840844341502281923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13247948560562894334854615 19871922840844341502281923)
      ·
        refine ⟨29807884261266512253422885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19871922840844341502281923 29807884261266512253422885)
        ·
          refine ⟨5588978298987471047516791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29807884261266512253422885 5588978298987471047516791)
          ·
            refine ⟨8383467448481206571275187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5588978298987471047516791 8383467448481206571275187)
            ·
              refine ⟨12575201172721809856912781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8383467448481206571275187 12575201172721809856912781)
              ·
                refine ⟨4715700439770678696342293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12575201172721809856912781 4715700439770678696342293)
                ·
                  refine ⟨221048458114250563891045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4715700439770678696342293 221048458114250563891045)
                  ·
                    rfl

theorem cell23_3874413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 3, 6].length) (baseStart_3874413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3874413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3874413 prefixEnd_3874413 := by exact prefixLift 3874413
  have htrace : WordTrace (prefixWord ++ tailWord_3874413) baseStart_3874413 baseEnd_3874413 := by
    simpa [prefixWord, tailWord_3874413, baseEnd_3874413] using wordTrace_append hprefix tailTrace_3874413
  have hstable : (prefixWord ++ tailWord_3874413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3874413).length < 2 ^ (prefixWord ++ tailWord_3874413).sum := by decide
  have hdescent : baseEnd_3874413 < baseStart_3874413 := by decide
  rcases family_descends (prefixWord ++ tailWord_3874413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3874426 : List Nat := [3, 1, 1, 1, 1, 1, 1, 8, 1, 5]
def baseStart_3874426 : Nat := 118140960795 + 3874426 * 2 ^ 59
def prefixEnd_3874426 : Nat := 4983230072969 + 3 ^ 40 * 3874426 * 2
def baseEnd_3874426 : Nat := 663147599425587841385615

theorem tailTrace_3874426 : CollatzResearch.WordTrace tailWord_3874426 prefixEnd_3874426 663147599425587841385615 := by
  unfold tailWord_3874426
  simp only [CollatzResearch.WordTrace]
  refine ⟨35327981365405944031334783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94207950307749184083559421 35327981365405944031334783)
  ·
    refine ⟨52991972048108916047002175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35327981365405944031334783 52991972048108916047002175)
    ·
      refine ⟨79487958072163374070503263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52991972048108916047002175 79487958072163374070503263)
      ·
        refine ⟨119231937108245061105754895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79487958072163374070503263 119231937108245061105754895)
        ·
          refine ⟨178847905662367591658632343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119231937108245061105754895 178847905662367591658632343)
          ·
            refine ⟨268271858493551387487948515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178847905662367591658632343 268271858493551387487948515)
            ·
              refine ⟨402407787740327081231922773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 268271858493551387487948515 402407787740327081231922773)
              ·
                refine ⟨4715716262581957983186595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 402407787740327081231922773 4715716262581957983186595)
                ·
                  refine ⟨7073574393872936974779893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4715716262581957983186595 7073574393872936974779893)
                  ·
                    refine ⟨663147599425587841385615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7073574393872936974779893 663147599425587841385615)
                    ·
                      rfl

theorem cell23_3874426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 8, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 8, 1, 5].length) (baseStart_3874426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3874426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3874426 prefixEnd_3874426 := by exact prefixLift 3874426
  have htrace : WordTrace (prefixWord ++ tailWord_3874426) baseStart_3874426 baseEnd_3874426 := by
    simpa [prefixWord, tailWord_3874426, baseEnd_3874426] using wordTrace_append hprefix tailTrace_3874426
  have hstable : (prefixWord ++ tailWord_3874426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3874426).length < 2 ^ (prefixWord ++ tailWord_3874426).sum := by decide
  have hdescent : baseEnd_3874426 < baseStart_3874426 := by decide
  rcases family_descends (prefixWord ++ tailWord_3874426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3874443 : List Nat := [1, 1, 1, 1, 4, 1, 7, 1, 1, 5]
def baseStart_3874443 : Nat := 118140960795 + 3874443 * 2 ^ 59
def prefixEnd_3874443 : Nat := 4983230072969 + 3 ^ 40 * 3874443 * 2
def baseEnd_3874443 : Nat := 663150509149296652548089

theorem tailTrace_3874443 : CollatzResearch.WordTrace tailWord_3874443 prefixEnd_3874443 663150509149296652548089 := by
  unfold tailWord_3874443
  simp only [CollatzResearch.WordTrace]
  refine ⟨141312545502562188028707983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94208363668374792019138655 141312545502562188028707983)
  ·
    refine ⟨211968818253843282043061975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141312545502562188028707983 211968818253843282043061975)
    ·
      refine ⟨317953227380764923064592963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211968818253843282043061975 317953227380764923064592963)
      ·
        refine ⟨476929841071147384596889445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317953227380764923064592963 476929841071147384596889445)
        ·
          refine ⟨89424345200840134611916771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 476929841071147384596889445 89424345200840134611916771)
          ·
            refine ⟨134136517801260201917875157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89424345200840134611916771 134136517801260201917875157)
            ·
              refine ⟨3143824635967035982450199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 134136517801260201917875157 3143824635967035982450199)
              ·
                refine ⟨4715736953950553973675299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3143824635967035982450199 4715736953950553973675299)
                ·
                  refine ⟨7073605430925830960512949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4715736953950553973675299 7073605430925830960512949)
                  ·
                    refine ⟨663150509149296652548089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7073605430925830960512949 663150509149296652548089)
                    ·
                      rfl

theorem cell23_3874443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 7, 1, 1, 5].length) (baseStart_3874443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3874443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3874443 prefixEnd_3874443 := by exact prefixLift 3874443
  have htrace : WordTrace (prefixWord ++ tailWord_3874443) baseStart_3874443 baseEnd_3874443 := by
    simpa [prefixWord, tailWord_3874443, baseEnd_3874443] using wordTrace_append hprefix tailTrace_3874443
  have hstable : (prefixWord ++ tailWord_3874443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3874443).length < 2 ^ (prefixWord ++ tailWord_3874443).sum := by decide
  have hdescent : baseEnd_3874443 < baseStart_3874443 := by decide
  rcases family_descends (prefixWord ++ tailWord_3874443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3874483 : List Nat := [1, 1, 1, 2, 3, 3, 2, 4, 1, 2, 3]
def baseStart_3874483 : Nat := 118140960795 + 3874483 * 2 ^ 59
def prefixEnd_3874483 : Nat := 4983230072969 + 3 ^ 40 * 3874483 * 2
def baseEnd_3874483 : Nat := 1989472066674069801144083

theorem tailTrace_3874483 : CollatzResearch.WordTrace tailWord_3874483 prefixEnd_3874483 1989472066674069801144083 := by
  unfold tailWord_3874483
  simp only [CollatzResearch.WordTrace]
  refine ⟨141314004422417274860164103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94209336281611516573442735 141314004422417274860164103)
  ·
    refine ⟨211971006633625912290246155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141314004422417274860164103 211971006633625912290246155)
    ·
      refine ⟨317956509950438868435369233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211971006633625912290246155 317956509950438868435369233)
      ·
        refine ⟨238467382462829151326526925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 317956509950438868435369233 238467382462829151326526925)
        ·
          refine ⟨89425268423560931747447597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 238467382462829151326526925 89425268423560931747447597)
          ·
            refine ⟨33534475658835349405292849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89425268423560931747447597 33534475658835349405292849)
            ·
              refine ⟨25150856744126512053969637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33534475658835349405292849 25150856744126512053969637)
              ·
                refine ⟨4715785639523721010119307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25150856744126512053969637 4715785639523721010119307)
                ·
                  refine ⟨7073678459285581515178961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4715785639523721010119307 7073678459285581515178961)
                  ·
                    refine ⟨5305258844464186136384221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7073678459285581515178961 5305258844464186136384221)
                    ·
                      refine ⟨1989472066674069801144083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5305258844464186136384221 1989472066674069801144083)
                      ·
                        rfl

theorem cell23_3874483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 4, 1, 2, 3].length) (baseStart_3874483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3874483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3874483 prefixEnd_3874483 := by exact prefixLift 3874483
  have htrace : WordTrace (prefixWord ++ tailWord_3874483) baseStart_3874483 baseEnd_3874483 := by
    simpa [prefixWord, tailWord_3874483, baseEnd_3874483] using wordTrace_append hprefix tailTrace_3874483
  have hstable : (prefixWord ++ tailWord_3874483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3874483).length < 2 ^ (prefixWord ++ tailWord_3874483).sum := by decide
  have hdescent : baseEnd_3874483 < baseStart_3874483 := by decide
  rcases family_descends (prefixWord ++ tailWord_3874483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3874500 : List Nat := [2, 3, 3, 1, 1, 1, 3, 3, 1, 2, 3]
def baseStart_3874500 : Nat := 118140960795 + 3874500 * 2 ^ 59
def prefixEnd_3874500 : Nat := 4983230072969 + 3 ^ 40 * 3874500 * 2
def baseEnd_3874500 : Nat := 1989480795845196234631505

theorem tailTrace_3874500 : CollatzResearch.WordTrace tailWord_3874500 prefixEnd_3874500 1989480795845196234631505 := by
  unfold tailWord_3874500
  simp only [CollatzResearch.WordTrace]
  refine ⟨70657312231677843381766477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94209749642237124509021969 70657312231677843381766477)
  ·
    refine ⟨26496492086879191268162429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70657312231677843381766477 26496492086879191268162429)
    ·
      refine ⟨9936184532579696725560911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26496492086879191268162429 9936184532579696725560911)
      ·
        refine ⟨14904276798869545088341367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9936184532579696725560911 14904276798869545088341367)
        ·
          refine ⟨22356415198304317632512051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14904276798869545088341367 22356415198304317632512051)
          ·
            refine ⟨33534622797456476448768077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22356415198304317632512051 33534622797456476448768077)
            ·
              refine ⟨12575483549046178668288029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33534622797456476448768077 12575483549046178668288029)
              ·
                refine ⟨4715806330892317000608011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12575483549046178668288029 4715806330892317000608011)
                ·
                  refine ⟨7073709496338475500912017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4715806330892317000608011 7073709496338475500912017)
                  ·
                    refine ⟨5305282122253856625684013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7073709496338475500912017 5305282122253856625684013)
                    ·
                      refine ⟨1989480795845196234631505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5305282122253856625684013 1989480795845196234631505)
                      ·
                        rfl

theorem cell23_3874500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 3, 1, 2, 3].length) (baseStart_3874500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3874500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3874500 prefixEnd_3874500 := by exact prefixLift 3874500
  have htrace : WordTrace (prefixWord ++ tailWord_3874500) baseStart_3874500 baseEnd_3874500 := by
    simpa [prefixWord, tailWord_3874500, baseEnd_3874500] using wordTrace_append hprefix tailTrace_3874500
  have hstable : (prefixWord ++ tailWord_3874500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3874500).length < 2 ^ (prefixWord ++ tailWord_3874500).sum := by decide
  have hdescent : baseEnd_3874500 < baseStart_3874500 := by decide
  rcases family_descends (prefixWord ++ tailWord_3874500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3874514 : List Nat := [3, 2, 2, 2, 2, 1, 2, 4, 1, 2, 2]
def baseStart_3874514 : Nat := 118140960795 + 3874514 * 2 ^ 59
def prefixEnd_3874514 : Nat := 4983230072969 + 3 ^ 40 * 3874514 * 2
def baseEnd_3874514 : Nat := 1989487984574359179856441

theorem tailTrace_3874514 : CollatzResearch.WordTrace tailWord_3874514 prefixEnd_3874514 1989487984574359179856441 := by
  unfold tailWord_3874514
  simp only [CollatzResearch.WordTrace]
  refine ⟨35328783771326241788635649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94210090056869978103028397 35328783771326241788635649)
  ·
    refine ⟨26496587828494681341476737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35328783771326241788635649 26496587828494681341476737)
    ·
      refine ⟨19872440871371011006107553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26496587828494681341476737 19872440871371011006107553)
      ·
        refine ⟨14904330653528258254580665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19872440871371011006107553 14904330653528258254580665)
        ·
          refine ⟨11178247990146193690935499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14904330653528258254580665 11178247990146193690935499)
          ·
            refine ⟨16767371985219290536403249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11178247990146193690935499 16767371985219290536403249)
            ·
              refine ⟨12575528988914467902302437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16767371985219290536403249 12575528988914467902302437)
              ·
                refine ⟨2357911685421462731681707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12575528988914467902302437 2357911685421462731681707)
                ·
                  refine ⟨3536867528132194097522561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2357911685421462731681707 3536867528132194097522561)
                  ·
                    refine ⟨2652650646099145573141921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3536867528132194097522561 2652650646099145573141921)
                    ·
                      refine ⟨1989487984574359179856441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2652650646099145573141921 1989487984574359179856441)
                      ·
                        rfl

theorem cell23_3874514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 4, 1, 2, 2].length) (baseStart_3874514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3874514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3874514 prefixEnd_3874514 := by exact prefixLift 3874514
  have htrace : WordTrace (prefixWord ++ tailWord_3874514) baseStart_3874514 baseEnd_3874514 := by
    simpa [prefixWord, tailWord_3874514, baseEnd_3874514] using wordTrace_append hprefix tailTrace_3874514
  have hstable : (prefixWord ++ tailWord_3874514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3874514).length < 2 ^ (prefixWord ++ tailWord_3874514).sum := by decide
  have hdescent : baseEnd_3874514 < baseStart_3874514 := by decide
  rcases family_descends (prefixWord ++ tailWord_3874514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3874524 : List Nat := [2, 2, 5, 1, 2, 1, 3, 1, 2, 4]
def baseStart_3874524 : Nat := 118140960795 + 3874524 * 2 ^ 59
def prefixEnd_3874524 : Nat := 4983230072969 + 3 ^ 40 * 3874524 * 2
def baseEnd_3874524 : Nat := 663164373126968046910465

theorem tailTrace_3874524 : CollatzResearch.WordTrace tailWord_3874524 prefixEnd_3874524 663164373126968046910465 := by
  unfold tailWord_3874524
  simp only [CollatzResearch.WordTrace]
  refine ⟨70657749907634369431203313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94210333210179159241604417 70657749907634369431203313)
  ·
    refine ⟨52993312430725777073402485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70657749907634369431203313 52993312430725777073402485)
    ·
      refine ⟨4968123040380541600631483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 52993312430725777073402485 4968123040380541600631483)
      ·
        refine ⟨7452184560570812400947225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4968123040380541600631483 7452184560570812400947225)
        ·
          refine ⟨5589138420428109300710419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7452184560570812400947225 5589138420428109300710419)
          ·
            refine ⟨8383707630642163951065629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5589138420428109300710419 8383707630642163951065629)
            ·
              refine ⟨3143890361490811481649611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8383707630642163951065629 3143890361490811481649611)
              ·
                refine ⟨4715835542236217222474417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3143890361490811481649611 4715835542236217222474417)
                ·
                  refine ⟨3536876656677162916855813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4715835542236217222474417 3536876656677162916855813)
                  ·
                    refine ⟨663164373126968046910465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3536876656677162916855813 663164373126968046910465)
                    ·
                      rfl

theorem cell23_3874524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_3874524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3874524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3874524 prefixEnd_3874524 := by exact prefixLift 3874524
  have htrace : WordTrace (prefixWord ++ tailWord_3874524) baseStart_3874524 baseEnd_3874524 := by
    simpa [prefixWord, tailWord_3874524, baseEnd_3874524] using wordTrace_append hprefix tailTrace_3874524
  have hstable : (prefixWord ++ tailWord_3874524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3874524).length < 2 ^ (prefixWord ++ tailWord_3874524).sum := by decide
  have hdescent : baseEnd_3874524 < baseStart_3874524 := by decide
  rcases family_descends (prefixWord ++ tailWord_3874524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3874540 : List Nat := [2, 2, 1, 1, 2, 2, 3, 4, 1, 3, 2]
def baseStart_3874540 : Nat := 118140960795 + 3874540 * 2 ^ 59
def prefixEnd_3874540 : Nat := 4983230072969 + 3 ^ 40 * 3874540 * 2
def baseEnd_3874540 : Nat := 1989501335071376078131321

theorem tailTrace_3874540 : CollatzResearch.WordTrace tailWord_3874540 prefixEnd_3874540 1989501335071376078131321 := by
  unfold tailWord_3874540
  simp only [CollatzResearch.WordTrace]
  refine ⟨70658041691605386797494537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94210722255473849063326049 70658041691605386797494537)
  ·
    refine ⟨52993531268704040098120903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70658041691605386797494537 52993531268704040098120903)
    ·
      refine ⟨79490296903056060147181355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52993531268704040098120903 79490296903056060147181355)
      ·
        refine ⟨119235445354584090220772033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79490296903056060147181355 119235445354584090220772033)
        ·
          refine ⟨89426584015938067665579025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119235445354584090220772033 89426584015938067665579025)
          ·
            refine ⟨67069938011953550749184269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89426584015938067665579025 67069938011953550749184269)
            ·
              refine ⟨25151226754482581530944101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67069938011953550749184269 25151226754482581530944101)
              ·
                refine ⟨4715855016465484037052019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25151226754482581530944101 4715855016465484037052019)
                ·
                  refine ⟨7073782524698226055578029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4715855016465484037052019 7073782524698226055578029)
                  ·
                    refine ⟨2652668446761834770841761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7073782524698226055578029 2652668446761834770841761)
                    ·
                      refine ⟨1989501335071376078131321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2652668446761834770841761 1989501335071376078131321)
                      ·
                        rfl

theorem cell23_3874540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 3, 2].length) (baseStart_3874540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3874540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3874540 prefixEnd_3874540 := by exact prefixLift 3874540
  have htrace : WordTrace (prefixWord ++ tailWord_3874540) baseStart_3874540 baseEnd_3874540 := by
    simpa [prefixWord, tailWord_3874540, baseEnd_3874540] using wordTrace_append hprefix tailTrace_3874540
  have hstable : (prefixWord ++ tailWord_3874540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3874540).length < 2 ^ (prefixWord ++ tailWord_3874540).sum := by decide
  have hdescent : baseEnd_3874540 < baseStart_3874540 := by decide
  rcases family_descends (prefixWord ++ tailWord_3874540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3874548 : List Nat := [2, 6, 1, 1, 1, 1, 3, 3, 1, 2, 2]
def baseStart_3874548 : Nat := 118140960795 + 3874548 * 2 ^ 59
def prefixEnd_3874548 : Nat := 4983230072969 + 3 ^ 40 * 3874548 * 2
def baseEnd_3874548 : Nat := 1989505442916612046831285

theorem tailTrace_3874548 : CollatzResearch.WordTrace tailWord_3874548 prefixEnd_3874548 1989505442916612046831285 := by
  unfold tailWord_3874548
  simp only [CollatzResearch.WordTrace]
  refine ⟨70658187583590895480640149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94210916778121193974186865 70658187583590895480640149)
  ·
    refine ⟨3312102542980823225655007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 70658187583590895480640149 3312102542980823225655007)
    ·
      refine ⟨4968153814471234838482511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3312102542980823225655007 4968153814471234838482511)
      ·
        refine ⟨7452230721706852257723767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4968153814471234838482511 7452230721706852257723767)
        ·
          refine ⟨11178346082560278386585651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7452230721706852257723767 11178346082560278386585651)
          ·
            refine ⟨16767519123840417579878477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11178346082560278386585651 16767519123840417579878477)
            ·
              refine ⟨6287819671440156592454429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16767519123840417579878477 6287819671440156592454429)
              ·
                refine ⟨2357932376790058722170411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6287819671440156592454429 2357932376790058722170411)
                ·
                  refine ⟨3536898565185088083255617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2357932376790058722170411 3536898565185088083255617)
                  ·
                    refine ⟨2652673923888816062441713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3536898565185088083255617 2652673923888816062441713)
                    ·
                      refine ⟨1989505442916612046831285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2652673923888816062441713 1989505442916612046831285)
                      ·
                        rfl

theorem cell23_3874548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 3, 3, 1, 2, 2].length) (baseStart_3874548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3874548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3874548 prefixEnd_3874548 := by exact prefixLift 3874548
  have htrace : WordTrace (prefixWord ++ tailWord_3874548) baseStart_3874548 baseEnd_3874548 := by
    simpa [prefixWord, tailWord_3874548, baseEnd_3874548] using wordTrace_append hprefix tailTrace_3874548
  have hstable : (prefixWord ++ tailWord_3874548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3874548).length < 2 ^ (prefixWord ++ tailWord_3874548).sum := by decide
  have hdescent : baseEnd_3874548 < baseStart_3874548 := by decide
  rcases family_descends (prefixWord ++ tailWord_3874548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3874627 : List Nat := [1, 1, 1, 3, 1, 7, 2, 2, 5]
def baseStart_3874627 : Nat := 118140960795 + 3874627 * 2 ^ 59
def prefixEnd_3874627 : Nat := 4983230072969 + 3 ^ 40 * 3874627 * 2
def baseEnd_3874627 : Nat := 221060667543146359749269

theorem tailTrace_3874627 : CollatzResearch.WordTrace tailWord_3874627 prefixEnd_3874627 221060667543146359749269 := by
  unfold tailWord_3874627
  simp only [CollatzResearch.WordTrace]
  refine ⟨141319256533895587453406135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94212837689263724968937423 141319256533895587453406135)
  ·
    refine ⟨211978884800843381180109203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141319256533895587453406135 211978884800843381180109203)
    ·
      refine ⟨317968327201265071770163805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211978884800843381180109203 317968327201265071770163805)
      ·
        refine ⟨119238122700474401913811427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 317968327201265071770163805 119238122700474401913811427)
        ·
          refine ⟨178857184050711602870717141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119238122700474401913811427 178857184050711602870717141)
          ·
            refine ⟨4191965251188553192282433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 178857184050711602870717141 4191965251188553192282433)
            ·
              refine ⟨3143973938391414894211825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4191965251188553192282433 3143973938391414894211825)
              ·
                refine ⟨2357980453793561170658869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3143973938391414894211825 2357980453793561170658869)
                ·
                  refine ⟨221060667543146359749269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2357980453793561170658869 221060667543146359749269)
                  ·
                    rfl

theorem cell23_3874627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 2, 2, 5].length) (baseStart_3874627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3874627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3874627 prefixEnd_3874627 := by exact prefixLift 3874627
  have htrace : WordTrace (prefixWord ++ tailWord_3874627) baseStart_3874627 baseEnd_3874627 := by
    simpa [prefixWord, tailWord_3874627, baseEnd_3874627] using wordTrace_append hprefix tailTrace_3874627
  have hstable : (prefixWord ++ tailWord_3874627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3874627).length < 2 ^ (prefixWord ++ tailWord_3874627).sum := by decide
  have hdescent : baseEnd_3874627 < baseStart_3874627 := by decide
  rcases family_descends (prefixWord ++ tailWord_3874627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3874637 : List Nat := [1, 6, 1, 2, 1, 2, 1, 1, 2, 3, 3]
def baseStart_3874637 : Nat := 118140960795 + 3874637 * 2 ^ 59
def prefixEnd_3874637 : Nat := 4983230072969 + 3 ^ 40 * 3874637 * 2
def baseEnd_3874637 : Nat := 1989551142694862198618375

theorem tailTrace_3874637 : CollatzResearch.WordTrace tailWord_3874637 prefixEnd_3874637 1989551142694862198618375 := by
  unfold tailWord_3874637
  simp only [CollatzResearch.WordTrace]
  refine ⟨141319621263859359161270165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94213080842572906107513443 141319621263859359161270165)
  ·
    refine ⟨6624357246743407460684539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 141319621263859359161270165 6624357246743407460684539)
    ·
      refine ⟨9936535870115111191026809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6624357246743407460684539 9936535870115111191026809)
      ·
        refine ⟨7452401902586333393270107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9936535870115111191026809 7452401902586333393270107)
        ·
          refine ⟨11178602853879500089905161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7452401902586333393270107 11178602853879500089905161)
          ·
            refine ⟨8383952140409625067428871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11178602853879500089905161 8383952140409625067428871)
            ·
              refine ⟨12575928210614437601143307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8383952140409625067428871 12575928210614437601143307)
              ·
                refine ⟨18863892315921656401714961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12575928210614437601143307 18863892315921656401714961)
                ·
                  refine ⟨14147919236941242301286221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18863892315921656401714961 14147919236941242301286221)
                  ·
                    refine ⟨5305469713852965862982333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14147919236941242301286221 5305469713852965862982333)
                    ·
                      refine ⟨1989551142694862198618375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5305469713852965862982333 1989551142694862198618375)
                      ·
                        rfl

theorem cell23_3874637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_3874637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3874637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3874637 prefixEnd_3874637 := by exact prefixLift 3874637
  have htrace : WordTrace (prefixWord ++ tailWord_3874637) baseStart_3874637 baseEnd_3874637 := by
    simpa [prefixWord, tailWord_3874637, baseEnd_3874637] using wordTrace_append hprefix tailTrace_3874637
  have hstable : (prefixWord ++ tailWord_3874637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3874637).length < 2 ^ (prefixWord ++ tailWord_3874637).sum := by decide
  have hdescent : baseEnd_3874637 < baseStart_3874637 := by decide
  rcases family_descends (prefixWord ++ tailWord_3874637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3874660 : List Nat := [2, 3, 1, 1, 5, 1, 1, 1, 1, 3, 4]
def baseStart_3874660 : Nat := 118140960795 + 3874660 * 2 ^ 59
def prefixEnd_3874660 : Nat := 4983230072969 + 3 ^ 40 * 3874660 * 2
def baseEnd_3874660 : Nat := 1989562952749915608630769

theorem tailTrace_3874660 : CollatzResearch.WordTrace tailWord_3874660 prefixEnd_3874660 1989562952749915608630769 := by
  unfold tailWord_3874660
  simp only [CollatzResearch.WordTrace]
  refine ⟨70660230071388017044678717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94213640095184022726238289 70660230071388017044678717)
  ·
    refine ⟨26497586276770506391754519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70660230071388017044678717 26497586276770506391754519)
    ·
      refine ⟨39746379415155759587631779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26497586276770506391754519 39746379415155759587631779)
      ·
        refine ⟨59619569122733639381447669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39746379415155759587631779 59619569122733639381447669)
        ·
          refine ⟨5589334605256278692010719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 59619569122733639381447669 5589334605256278692010719)
          ·
            refine ⟨8384001907884418038016079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5589334605256278692010719 8384001907884418038016079)
            ·
              refine ⟨12576002861826627057024119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8384001907884418038016079 12576002861826627057024119)
              ·
                refine ⟨18864004292739940585536179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12576002861826627057024119 18864004292739940585536179)
                ·
                  refine ⟨28296006439109910878304269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18864004292739940585536179 28296006439109910878304269)
                  ·
                    refine ⟨10611002414666216579364101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28296006439109910878304269 10611002414666216579364101)
                    ·
                      refine ⟨1989562952749915608630769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10611002414666216579364101 1989562952749915608630769)
                      ·
                        rfl

theorem cell23_3874660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 1, 1, 3, 4].length) (baseStart_3874660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3874660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3874660 prefixEnd_3874660 := by exact prefixLift 3874660
  have htrace : WordTrace (prefixWord ++ tailWord_3874660) baseStart_3874660 baseEnd_3874660 := by
    simpa [prefixWord, tailWord_3874660, baseEnd_3874660] using wordTrace_append hprefix tailTrace_3874660
  have hstable : (prefixWord ++ tailWord_3874660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3874660).length < 2 ^ (prefixWord ++ tailWord_3874660).sum := by decide
  have hdescent : baseEnd_3874660 < baseStart_3874660 := by decide
  rcases family_descends (prefixWord ++ tailWord_3874660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3874713 : List Nat := [1, 2, 1, 2, 1, 3, 2, 3, 3, 5]
def baseStart_3874713 : Nat := 118140960795 + 3874713 * 2 ^ 59
def prefixEnd_3874713 : Nat := 4983230072969 + 3 ^ 40 * 3874713 * 2
def baseEnd_3874713 : Nat := 663196722408201300422675

theorem tailTrace_3874713 : CollatzResearch.WordTrace tailWord_3874713 prefixEnd_3874713 663196722408201300422675 := by
  unfold tailWord_3874713
  simp only [CollatzResearch.WordTrace]
  refine ⟨141322393211584024141036793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94214928807722682760691195 141322393211584024141036793)
  ·
    refine ⟨105991794908688018105777595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141322393211584024141036793 105991794908688018105777595)
    ·
      refine ⟨158987692363032027158666393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105991794908688018105777595 158987692363032027158666393)
      ·
        refine ⟨119240769272274020368999795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158987692363032027158666393 119240769272274020368999795)
        ·
          refine ⟨178861153908411030553499693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119240769272274020368999795 178861153908411030553499693)
          ·
            refine ⟨67072932715654136457562385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 178861153908411030553499693 67072932715654136457562385)
            ·
              refine ⟨50304699536740602343171789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67072932715654136457562385 50304699536740602343171789)
              ·
                refine ⟨18864262326277725878689421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50304699536740602343171789 18864262326277725878689421)
                ·
                  refine ⟨7074098372354147204508533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18864262326277725878689421 7074098372354147204508533)
                  ·
                    refine ⟨663196722408201300422675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7074098372354147204508533 663196722408201300422675)
                    ·
                      rfl

theorem cell23_3874713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 3, 3, 5].length) (baseStart_3874713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3874713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3874713 prefixEnd_3874713 := by exact prefixLift 3874713
  have htrace : WordTrace (prefixWord ++ tailWord_3874713) baseStart_3874713 baseEnd_3874713 := by
    simpa [prefixWord, tailWord_3874713, baseEnd_3874713] using wordTrace_append hprefix tailTrace_3874713
  have hstable : (prefixWord ++ tailWord_3874713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3874713).length < 2 ^ (prefixWord ++ tailWord_3874713).sum := by decide
  have hdescent : baseEnd_3874713 < baseStart_3874713 := by decide
  rcases family_descends (prefixWord ++ tailWord_3874713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3874721 : List Nat := [1, 2, 3, 4, 2, 2, 1, 3, 1, 4]
def baseStart_3874721 : Nat := 118140960795 + 3874721 * 2 ^ 59
def prefixEnd_3874721 : Nat := 4983230072969 + 3 ^ 40 * 3874721 * 2
def baseEnd_3874721 : Nat := 663198091689946623322663

theorem tailTrace_3874721 : CollatzResearch.WordTrace tailWord_3874721 prefixEnd_3874721 663198091689946623322663 := by
  unfold tailWord_3874721
  simp only [CollatzResearch.WordTrace]
  refine ⟨141322684995555041507328017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94215123330370027671552011 141322684995555041507328017)
  ·
    refine ⟨105992013746666281130496013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141322684995555041507328017 105992013746666281130496013)
    ·
      refine ⟨39747005154999855423936005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105992013746666281130496013 39747005154999855423936005)
      ·
        refine ⟨7452563466562472891988001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39747005154999855423936005 7452563466562472891988001)
        ·
          refine ⟨5589422599921854668991001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7452563466562472891988001 5589422599921854668991001)
          ·
            refine ⟨4192066949941391001743251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5589422599921854668991001 4192066949941391001743251)
            ·
              refine ⟨6288100424912086502614877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4192066949941391001743251 6288100424912086502614877)
              ·
                refine ⟨2358037659342032438480579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6288100424912086502614877 2358037659342032438480579)
                ·
                  refine ⟨3537056489013048657720869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2358037659342032438480579 3537056489013048657720869)
                  ·
                    refine ⟨663198091689946623322663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3537056489013048657720869 663198091689946623322663)
                    ·
                      rfl

theorem cell23_3874721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 1, 3, 1, 4].length) (baseStart_3874721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3874721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3874721 prefixEnd_3874721 := by exact prefixLift 3874721
  have htrace : WordTrace (prefixWord ++ tailWord_3874721) baseStart_3874721 baseEnd_3874721 := by
    simpa [prefixWord, tailWord_3874721, baseEnd_3874721] using wordTrace_append hprefix tailTrace_3874721
  have hstable : (prefixWord ++ tailWord_3874721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3874721).length < 2 ^ (prefixWord ++ tailWord_3874721).sum := by decide
  have hdescent : baseEnd_3874721 < baseStart_3874721 := by decide
  rcases family_descends (prefixWord ++ tailWord_3874721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3874737 : List Nat := [1, 2, 2, 4, 2, 1, 1, 1, 4, 3, 2]
def baseStart_3874737 : Nat := 118140960795 + 3874737 * 2 ^ 59
def prefixEnd_3874737 : Nat := 4983230072969 + 3 ^ 40 * 3874737 * 2
def baseEnd_3874737 : Nat := 1989602490760311807367915

theorem tailTrace_3874737 : CollatzResearch.WordTrace tailWord_3874737 prefixEnd_3874737 1989602490760311807367915 := by
  unfold tailWord_3874737
  simp only [CollatzResearch.WordTrace]
  refine ⟨141323268563497076239910465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94215512375664717493273643 141323268563497076239910465)
  ·
    refine ⟨105992451422622807179932849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141323268563497076239910465 105992451422622807179932849)
    ·
      refine ⟨79494338566967105384949637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105992451422622807179932849 79494338566967105384949637)
      ·
        refine ⟨14905188481306332259678057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79494338566967105384949637 14905188481306332259678057)
        ·
          refine ⟨11178891360979749194758543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14905188481306332259678057 11178891360979749194758543)
          ·
            refine ⟨16768337041469623792137815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11178891360979749194758543 16768337041469623792137815)
            ·
              refine ⟨25152505562204435688206723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16768337041469623792137815 25152505562204435688206723)
              ·
                refine ⟨37728758343306653532310085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25152505562204435688206723 37728758343306653532310085)
                ·
                  refine ⟨7074142189369997537308141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37728758343306653532310085 7074142189369997537308141)
                  ·
                    refine ⟨2652803321013749076490553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7074142189369997537308141 2652803321013749076490553)
                    ·
                      refine ⟨1989602490760311807367915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2652803321013749076490553 1989602490760311807367915)
                      ·
                        rfl

theorem cell23_3874737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 1, 4, 3, 2].length) (baseStart_3874737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3874737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3874737 prefixEnd_3874737 := by exact prefixLift 3874737
  have htrace : WordTrace (prefixWord ++ tailWord_3874737) baseStart_3874737 baseEnd_3874737 := by
    simpa [prefixWord, tailWord_3874737, baseEnd_3874737] using wordTrace_append hprefix tailTrace_3874737
  have hstable : (prefixWord ++ tailWord_3874737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3874737).length < 2 ^ (prefixWord ++ tailWord_3874737).sum := by decide
  have hdescent : baseEnd_3874737 < baseStart_3874737 := by decide
  rcases family_descends (prefixWord ++ tailWord_3874737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3874763 : List Nat := [1, 1, 1, 1, 3, 4, 1, 3, 1, 1, 6]
def baseStart_3874763 : Nat := 118140960795 + 3874763 * 2 ^ 59
def prefixEnd_3874763 : Nat := 4983230072969 + 3 ^ 40 * 3874763 * 2
def baseEnd_3874763 : Nat := 1989615841257328705642795

theorem tailTrace_3874763 : CollatzResearch.WordTrace tailWord_3874763 prefixEnd_3874763 1989615841257328705642795 := by
  unfold tailWord_3874763
  simp only [CollatzResearch.WordTrace]
  refine ⟨141324216861402882680356943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94216144574268588453571295 141324216861402882680356943)
  ·
    refine ⟨211986325292104324020535415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141324216861402882680356943 211986325292104324020535415)
    ·
      refine ⟨317979487938156486030803123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211986325292104324020535415 317979487938156486030803123)
      ·
        refine ⟨476969231907234729046204685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317979487938156486030803123 476969231907234729046204685)
        ·
          refine ⟨178863461965213023392326757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 476969231907234729046204685 178863461965213023392326757)
          ·
            refine ⟨33536899118477441886061267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 178863461965213023392326757 33536899118477441886061267)
            ·
              refine ⟨50305348677716162829091901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33536899118477441886061267 50305348677716162829091901)
              ·
                refine ⟨18864505754143561060909463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50305348677716162829091901 18864505754143561060909463)
                ·
                  refine ⟨28296758631215341591364195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18864505754143561060909463 28296758631215341591364195)
                  ·
                    refine ⟨42445137946823012387046293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28296758631215341591364195 42445137946823012387046293)
                    ·
                      refine ⟨1989615841257328705642795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42445137946823012387046293 1989615841257328705642795)
                      ·
                        rfl

theorem cell23_3874763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 3, 1, 1, 6].length) (baseStart_3874763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3874763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3874763 prefixEnd_3874763 := by exact prefixLift 3874763
  have htrace : WordTrace (prefixWord ++ tailWord_3874763) baseStart_3874763 baseEnd_3874763 := by
    simpa [prefixWord, tailWord_3874763, baseEnd_3874763] using wordTrace_append hprefix tailTrace_3874763
  have hstable : (prefixWord ++ tailWord_3874763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3874763).length < 2 ^ (prefixWord ++ tailWord_3874763).sum := by decide
  have hdescent : baseEnd_3874763 < baseStart_3874763 := by decide
  rcases family_descends (prefixWord ++ tailWord_3874763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3874767 : List Nat := [1, 1, 2, 1, 1, 5, 2, 1, 5, 2, 2]
def baseStart_3874767 : Nat := 118140960795 + 3874767 * 2 ^ 59
def prefixEnd_3874767 : Nat := 4983230072969 + 3 ^ 40 * 3874767 * 2
def baseEnd_3874767 : Nat := 1989617895179946689992777

theorem tailTrace_3874767 : CollatzResearch.WordTrace tailWord_3874767 prefixEnd_3874767 1989617895179946689992777 := by
  unfold tailWord_3874767
  simp only [CollatzResearch.WordTrace]
  refine ⟨141324362753388391363502555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94216241835592260909001703 141324362753388391363502555)
  ·
    refine ⟨211986544130082587045253833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141324362753388391363502555 211986544130082587045253833)
    ·
      refine ⟨158989908097561940283940375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 211986544130082587045253833 158989908097561940283940375)
      ·
        refine ⟨238484862146342910425910563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158989908097561940283940375 238484862146342910425910563)
        ·
          refine ⟨357727293219514365638865845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238484862146342910425910563 357727293219514365638865845)
          ·
            refine ⟨33536933739329471778643673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 357727293219514365638865845 33536933739329471778643673)
            ·
              refine ⟨25152700304497103833982755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33536933739329471778643673 25152700304497103833982755)
              ·
                refine ⟨37729050456745655750974133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25152700304497103833982755 37729050456745655750974133)
                ·
                  refine ⟨3537098480319905226653825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37729050456745655750974133 3537098480319905226653825)
                  ·
                    refine ⟨2652823860239928919990369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3537098480319905226653825 2652823860239928919990369)
                    ·
                      refine ⟨1989617895179946689992777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2652823860239928919990369 1989617895179946689992777)
                      ·
                        rfl

theorem cell23_3874767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2, 1, 5, 2, 2].length) (baseStart_3874767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3874767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3874767 prefixEnd_3874767 := by exact prefixLift 3874767
  have htrace : WordTrace (prefixWord ++ tailWord_3874767) baseStart_3874767 baseEnd_3874767 := by
    simpa [prefixWord, tailWord_3874767, baseEnd_3874767] using wordTrace_append hprefix tailTrace_3874767
  have hstable : (prefixWord ++ tailWord_3874767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3874767).length < 2 ^ (prefixWord ++ tailWord_3874767).sum := by decide
  have hdescent : baseEnd_3874767 < baseStart_3874767 := by decide
  rcases family_descends (prefixWord ++ tailWord_3874767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3874787 : List Nat := [1, 1, 1, 6, 1, 4, 1, 1, 1, 1, 5]
def baseStart_3874787 : Nat := 118140960795 + 3874787 * 2 ^ 59
def prefixEnd_3874787 : Nat := 4983230072969 + 3 ^ 40 * 3874787 * 2
def baseEnd_3874787 : Nat := 1989628164793036611742685

theorem tailTrace_3874787 : CollatzResearch.WordTrace tailWord_3874787 prefixEnd_3874787 1989628164793036611742685 := by
  unfold tailWord_3874787
  simp only [CollatzResearch.WordTrace]
  refine ⟨141325092213315934779230615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94216728142210623186153743 141325092213315934779230615)
  ·
    refine ⟨211987638319973902168845923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141325092213315934779230615 211987638319973902168845923)
    ·
      refine ⟨317981457479960853253268885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211987638319973902168845923 317981457479960853253268885)
      ·
        refine ⟨14905380819373164996246979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 317981457479960853253268885 14905380819373164996246979)
        ·
          refine ⟨22358071229059747494370469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14905380819373164996246979 22358071229059747494370469)
          ·
            refine ⟨4192138355448702655194463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22358071229059747494370469 4192138355448702655194463)
            ·
              refine ⟨6288207533173053982791695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4192138355448702655194463 6288207533173053982791695)
              ·
                refine ⟨9432311299759580974187543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6288207533173053982791695 9432311299759580974187543)
                ·
                  refine ⟨14148466949639371461281315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9432311299759580974187543 14148466949639371461281315)
                  ·
                    refine ⟨21222700424459057191921973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14148466949639371461281315 21222700424459057191921973)
                    ·
                      refine ⟨1989628164793036611742685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21222700424459057191921973 1989628164793036611742685)
                      ·
                        rfl

theorem cell23_3874787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 1, 1, 1, 1, 5].length) (baseStart_3874787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3874787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3874787 prefixEnd_3874787 := by exact prefixLift 3874787
  have htrace : WordTrace (prefixWord ++ tailWord_3874787) baseStart_3874787 baseEnd_3874787 := by
    simpa [prefixWord, tailWord_3874787, baseEnd_3874787] using wordTrace_append hprefix tailTrace_3874787
  have hstable : (prefixWord ++ tailWord_3874787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3874787).length < 2 ^ (prefixWord ++ tailWord_3874787).sum := by decide
  have hdescent : baseEnd_3874787 < baseStart_3874787 := by decide
  rcases family_descends (prefixWord ++ tailWord_3874787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3874814 : List Nat := [4, 2, 2, 2, 1, 2, 2, 1, 1, 2, 4]
def baseStart_3874814 : Nat := 118140960795 + 3874814 * 2 ^ 59
def prefixEnd_3874814 : Nat := 4983230072969 + 3 ^ 40 * 3874814 * 2
def baseEnd_3874814 : Nat := 1989642028770708006105061

theorem tailTrace_3874814 : CollatzResearch.WordTrace tailWord_3874814 prefixEnd_3874814 1989642028770708006105061 := by
  unfold tailWord_3874814
  simp only [CollatzResearch.WordTrace]
  refine ⟨17665759623027264798807937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94217384656145412260308997 17665759623027264798807937)
  ·
    refine ⟨13249319717270448599105953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17665759623027264798807937 13249319717270448599105953)
    ·
      refine ⟨9936989787952836449329465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13249319717270448599105953 9936989787952836449329465)
      ·
        refine ⟨7452742340964627336997099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9936989787952836449329465 7452742340964627336997099)
        ·
          refine ⟨11179113511446941005495649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7452742340964627336997099 11179113511446941005495649)
          ·
            refine ⟨8384335133585205754121737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11179113511446941005495649 8384335133585205754121737)
            ·
              refine ⟨6288251350188904315591303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8384335133585205754121737 6288251350188904315591303)
              ·
                refine ⟨9432377025283356473386955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6288251350188904315591303 9432377025283356473386955)
                ·
                  refine ⟨14148565537925034710080433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9432377025283356473386955 14148565537925034710080433)
                  ·
                    refine ⟨10611424153443776032560325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14148565537925034710080433 10611424153443776032560325)
                    ·
                      refine ⟨1989642028770708006105061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10611424153443776032560325 1989642028770708006105061)
                      ·
                        rfl

theorem cell23_3874814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_3874814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3874814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3874814 prefixEnd_3874814 := by exact prefixLift 3874814
  have htrace : WordTrace (prefixWord ++ tailWord_3874814) baseStart_3874814 baseEnd_3874814 := by
    simpa [prefixWord, tailWord_3874814, baseEnd_3874814] using wordTrace_append hprefix tailTrace_3874814
  have hstable : (prefixWord ++ tailWord_3874814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3874814).length < 2 ^ (prefixWord ++ tailWord_3874814).sum := by decide
  have hdescent : baseEnd_3874814 < baseStart_3874814 := by decide
  rcases family_descends (prefixWord ++ tailWord_3874814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3874817 : List Nat := [1, 2, 4, 1, 2, 1, 4, 1, 1, 3, 3]
def baseStart_3874817 : Nat := 118140960795 + 3874817 * 2 ^ 59
def prefixEnd_3874817 : Nat := 4983230072969 + 3 ^ 40 * 3874817 * 2
def baseEnd_3874817 : Nat := 1989643569212671494367547

theorem tailTrace_3874817 : CollatzResearch.WordTrace tailWord_3874817 prefixEnd_3874817 1989643569212671494367547 := by
  unfold tailWord_3874817
  simp only [CollatzResearch.WordTrace]
  refine ⟨141326186403207249902822705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94217457602138166601881803 141326186403207249902822705)
  ·
    refine ⟨105994639802405437427117029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141326186403207249902822705 105994639802405437427117029)
    ·
      refine ⟨19873994962951019517584443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105994639802405437427117029 19873994962951019517584443)
      ·
        refine ⟨29810992444426529276376665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19873994962951019517584443 29810992444426529276376665)
        ·
          refine ⟨22358244333319896957282499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29810992444426529276376665 22358244333319896957282499)
          ·
            refine ⟨33537366499979845435923749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22358244333319896957282499 33537366499979845435923749)
            ·
              refine ⟨6288256218746221019235703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33537366499979845435923749 6288256218746221019235703)
              ·
                refine ⟨9432384328119331528853555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6288256218746221019235703 9432384328119331528853555)
                ·
                  refine ⟨14148576492178997293280333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9432384328119331528853555 14148576492178997293280333)
                  ·
                    refine ⟨5305716184567123984980125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14148576492178997293280333 5305716184567123984980125)
                    ·
                      refine ⟨1989643569212671494367547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5305716184567123984980125 1989643569212671494367547)
                      ·
                        rfl

theorem cell23_3874817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 4, 1, 1, 3, 3].length) (baseStart_3874817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3874817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3874817 prefixEnd_3874817 := by exact prefixLift 3874817
  have htrace : WordTrace (prefixWord ++ tailWord_3874817) baseStart_3874817 baseEnd_3874817 := by
    simpa [prefixWord, tailWord_3874817, baseEnd_3874817] using wordTrace_append hprefix tailTrace_3874817
  have hstable : (prefixWord ++ tailWord_3874817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3874817).length < 2 ^ (prefixWord ++ tailWord_3874817).sum := by decide
  have hdescent : baseEnd_3874817 < baseStart_3874817 := by decide
  rcases family_descends (prefixWord ++ tailWord_3874817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3874822 : List Nat := [6, 2, 1, 2, 1, 2, 1, 1, 2, 3, 2]
def baseStart_3874822 : Nat := 118140960795 + 3874822 * 2 ^ 59
def prefixEnd_3874822 : Nat := 4983230072969 + 3 ^ 40 * 3874822 * 2
def baseEnd_3874822 : Nat := 1989646136615943974805025

theorem tailTrace_3874822 : CollatzResearch.WordTrace tailWord_3874822 prefixEnd_3874822 1989646136615943974805025 := by
  unfold tailWord_3874822
  simp only [CollatzResearch.WordTrace]
  refine ⟨4416449024005910492398585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 94217579178792757171169813 4416449024005910492398585)
  ·
    refine ⟨3312336768004432869298939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4416449024005910492398585 3312336768004432869298939)
    ·
      refine ⟨4968505152006649303948409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3312336768004432869298939 4968505152006649303948409)
      ·
        refine ⟨3726378864004986977961307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4968505152006649303948409 3726378864004986977961307)
        ·
          refine ⟨5589568296007480466941961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3726378864004986977961307 5589568296007480466941961)
          ·
            refine ⟨4192176222005610350206471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5589568296007480466941961 4192176222005610350206471)
            ·
              refine ⟨6288264333008415525309707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4192176222005610350206471 6288264333008415525309707)
              ·
                refine ⟨9432396499512623287964561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6288264333008415525309707 9432396499512623287964561)
                ·
                  refine ⟨7074297374634467465973421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9432396499512623287964561 7074297374634467465973421)
                  ·
                    refine ⟨2652861515487925299740033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7074297374634467465973421 2652861515487925299740033)
                    ·
                      refine ⟨1989646136615943974805025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2652861515487925299740033 1989646136615943974805025)
                      ·
                        rfl

theorem cell23_3874822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_3874822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3874822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3874822 prefixEnd_3874822 := by exact prefixLift 3874822
  have htrace : WordTrace (prefixWord ++ tailWord_3874822) baseStart_3874822 baseEnd_3874822 := by
    simpa [prefixWord, tailWord_3874822, baseEnd_3874822] using wordTrace_append hprefix tailTrace_3874822
  have hstable : (prefixWord ++ tailWord_3874822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3874822).length < 2 ^ (prefixWord ++ tailWord_3874822).sum := by decide
  have hdescent : baseEnd_3874822 < baseStart_3874822 := by decide
  rcases family_descends (prefixWord ++ tailWord_3874822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3874827 : List Nat := [1, 1, 1, 1, 6, 1, 1, 3, 3, 3, 2]
def baseStart_3874827 : Nat := 118140960795 + 3874827 * 2 ^ 59
def prefixEnd_3874827 : Nat := 4983230072969 + 3 ^ 40 * 3874827 * 2
def baseEnd_3874827 : Nat := 1989648704019216455242501

theorem tailTrace_3874827 : CollatzResearch.WordTrace tailWord_3874827 prefixEnd_3874827 1989648704019216455242501 := by
  unfold tailWord_3874827
  simp only [CollatzResearch.WordTrace]
  refine ⟨141326551133171021610686735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94217700755447347740457823 141326551133171021610686735)
  ·
    refine ⟨211989826699756532416030103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141326551133171021610686735 211989826699756532416030103)
    ·
      refine ⟨317984740049634798624045155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211989826699756532416030103 317984740049634798624045155)
      ·
        refine ⟨476977110074452197936067733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317984740049634798624045155 476977110074452197936067733)
        ·
          refine ⟨22358302034739946778253175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 476977110074452197936067733 22358302034739946778253175)
          ·
            refine ⟨33537453052109920167379763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22358302034739946778253175 33537453052109920167379763)
            ·
              refine ⟨50306179578164880251069645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33537453052109920167379763 50306179578164880251069645)
              ·
                refine ⟨18864817341811830094151117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50306179578164880251069645 18864817341811830094151117)
                ·
                  refine ⟨7074306503179436285306669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18864817341811830094151117 7074306503179436285306669)
                  ·
                    refine ⟨2652864938692288606990001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7074306503179436285306669 2652864938692288606990001)
                    ·
                      refine ⟨1989648704019216455242501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2652864938692288606990001 1989648704019216455242501)
                      ·
                        rfl

theorem cell23_3874827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 3, 3, 3, 2].length) (baseStart_3874827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3874827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3874827 prefixEnd_3874827 := by exact prefixLift 3874827
  have htrace : WordTrace (prefixWord ++ tailWord_3874827) baseStart_3874827 baseEnd_3874827 := by
    simpa [prefixWord, tailWord_3874827, baseEnd_3874827] using wordTrace_append hprefix tailTrace_3874827
  have hstable : (prefixWord ++ tailWord_3874827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3874827).length < 2 ^ (prefixWord ++ tailWord_3874827).sum := by decide
  have hdescent : baseEnd_3874827 < baseStart_3874827 := by decide
  rcases family_descends (prefixWord ++ tailWord_3874827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3874830 : List Nat := [4, 1, 1, 2, 2, 1, 2, 1, 2, 2, 5]
def baseStart_3874830 : Nat := 118140960795 + 3874830 * 2 ^ 59
def prefixEnd_3874830 : Nat := 4983230072969 + 3 ^ 40 * 3874830 * 2
def baseEnd_3874830 : Nat := 1989650244461179943504987

theorem tailTrace_3874830 : CollatzResearch.WordTrace tailWord_3874830 prefixEnd_3874830 1989650244461179943504987 := by
  unfold tailWord_3874830
  simp only [CollatzResearch.WordTrace]
  refine ⟨17665832569020019140380743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94217773701440102082030629 17665832569020019140380743)
  ·
    refine ⟨26498748853530028710571115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17665832569020019140380743 26498748853530028710571115)
    ·
      refine ⟨39748123280295043065856673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26498748853530028710571115 39748123280295043065856673)
      ·
        refine ⟨29811092460221282299392505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39748123280295043065856673 29811092460221282299392505)
        ·
          refine ⟨22358319345165961724544379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29811092460221282299392505 22358319345165961724544379)
          ·
            refine ⟨33537479017748942586816569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22358319345165961724544379 33537479017748942586816569)
            ·
              refine ⟨25153109263311706940112427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33537479017748942586816569 25153109263311706940112427)
              ·
                refine ⟨37729663894967560410168641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25153109263311706940112427 37729663894967560410168641)
                ·
                  refine ⟨28297247921225670307626481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37729663894967560410168641 28297247921225670307626481)
                  ·
                    refine ⟨21222935940919252730719861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28297247921225670307626481 21222935940919252730719861)
                    ·
                      refine ⟨1989650244461179943504987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21222935940919252730719861 1989650244461179943504987)
                      ·
                        rfl

theorem cell23_3874830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 1, 2, 2, 5].length) (baseStart_3874830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3874830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3874830 prefixEnd_3874830 := by exact prefixLift 3874830
  have htrace : WordTrace (prefixWord ++ tailWord_3874830) baseStart_3874830 baseEnd_3874830 := by
    simpa [prefixWord, tailWord_3874830, baseEnd_3874830] using wordTrace_append hprefix tailTrace_3874830
  have hstable : (prefixWord ++ tailWord_3874830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3874830).length < 2 ^ (prefixWord ++ tailWord_3874830).sum := by decide
  have hdescent : baseEnd_3874830 < baseStart_3874830 := by decide
  rcases family_descends (prefixWord ++ tailWord_3874830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3874850 : List Nat := [3, 3, 1, 1, 1, 2, 1, 1, 4, 6]
def baseStart_3874850 : Nat := 118140960795 + 3874850 * 2 ^ 59
def prefixEnd_3874850 : Nat := 4983230072969 + 3 ^ 40 * 3874850 * 2
def baseEnd_3874850 : Nat := 663220171358089955084965

theorem tailTrace_3874850 : CollatzResearch.WordTrace tailWord_3874850 prefixEnd_3874850 663220171358089955084965 := by
  unfold tailWord_3874850
  simp only [CollatzResearch.WordTrace]
  refine ⟨35331847503021924134693501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94218260008058464359182669 35331847503021924134693501)
  ·
    refine ⟨13249442813633221550510063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35331847503021924134693501 13249442813633221550510063)
    ·
      refine ⟨19874164220449832325765095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13249442813633221550510063 19874164220449832325765095)
      ·
        refine ⟨29811246330674748488647643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19874164220449832325765095 29811246330674748488647643)
        ·
          refine ⟨44716869496012122732971465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29811246330674748488647643 44716869496012122732971465)
          ·
            refine ⟨33537652122009092049728599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44716869496012122732971465 33537652122009092049728599)
            ·
              refine ⟨50306478183013638074592899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33537652122009092049728599 50306478183013638074592899)
              ·
                refine ⟨75459717274520457111889349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50306478183013638074592899 75459717274520457111889349)
                ·
                  refine ⟨14148696988972585708479253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75459717274520457111889349 14148696988972585708479253)
                  ·
                    refine ⟨663220171358089955084965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14148696988972585708479253 663220171358089955084965)
                    ·
                      rfl

theorem cell23_3874850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 4, 6].length) (baseStart_3874850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3874850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3874850 prefixEnd_3874850 := by exact prefixLift 3874850
  have htrace : WordTrace (prefixWord ++ tailWord_3874850) baseStart_3874850 baseEnd_3874850 := by
    simpa [prefixWord, tailWord_3874850, baseEnd_3874850] using wordTrace_append hprefix tailTrace_3874850
  have hstable : (prefixWord ++ tailWord_3874850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3874850).length < 2 ^ (prefixWord ++ tailWord_3874850).sum := by decide
  have hdescent : baseEnd_3874850 < baseStart_3874850 := by decide
  rcases family_descends (prefixWord ++ tailWord_3874850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3874860 : List Nat := [2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 3]
def baseStart_3874860 : Nat := 118140960795 + 3874860 * 2 ^ 59
def prefixEnd_3874860 : Nat := 4983230072969 + 3 ^ 40 * 3874860 * 2
def baseEnd_3874860 : Nat := 1989665648880814826129849

theorem tailTrace_3874860 : CollatzResearch.WordTrace tailWord_3874860 prefixEnd_3874860 1989665648880814826129849 := by
  unfold tailWord_3874860
  simp only [CollatzResearch.WordTrace]
  refine ⟨70663877371025734123319017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94218503161367645497758689 70663877371025734123319017)
  ·
    refine ⟨52997908028269300592489263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70663877371025734123319017 52997908028269300592489263)
    ·
      refine ⟨79496862042403950888733895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52997908028269300592489263 79496862042403950888733895)
      ·
        refine ⟨119245293063605926333100843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79496862042403950888733895 119245293063605926333100843)
        ·
          refine ⟨178867939595408889499651265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119245293063605926333100843 178867939595408889499651265)
          ·
            refine ⟨134150954696556667124738449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178867939595408889499651265 134150954696556667124738449)
            ·
              refine ⟨100613216022417500343553837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134150954696556667124738449 100613216022417500343553837)
              ·
                refine ⟨37729956008406562628832689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100613216022417500343553837 37729956008406562628832689)
                ·
                  refine ⟨28297467006304921971624517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37729956008406562628832689 28297467006304921971624517)
                  ·
                    refine ⟨5305775063682172869679597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28297467006304921971624517 5305775063682172869679597)
                    ·
                      refine ⟨1989665648880814826129849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5305775063682172869679597 1989665648880814826129849)
                      ·
                        rfl

theorem cell23_3874860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 3].length) (baseStart_3874860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3874860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3874860 prefixEnd_3874860 := by exact prefixLift 3874860
  have htrace : WordTrace (prefixWord ++ tailWord_3874860) baseStart_3874860 baseEnd_3874860 := by
    simpa [prefixWord, tailWord_3874860, baseEnd_3874860] using wordTrace_append hprefix tailTrace_3874860
  have hstable : (prefixWord ++ tailWord_3874860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3874860).length < 2 ^ (prefixWord ++ tailWord_3874860).sum := by decide
  have hdescent : baseEnd_3874860 < baseStart_3874860 := by decide
  rcases family_descends (prefixWord ++ tailWord_3874860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3874868 : List Nat := [2, 5, 1, 2, 3, 1, 1, 1, 1, 3, 3]
def baseStart_3874868 : Nat := 118140960795 + 3874868 * 2 ^ 59
def prefixEnd_3874868 : Nat := 4983230072969 + 3 ^ 40 * 3874868 * 2
def baseEnd_3874868 : Nat := 1989669756726050794829813

theorem tailTrace_3874868 : CollatzResearch.WordTrace tailWord_3874868 prefixEnd_3874868 1989669756726050794829813 := by
  unfold tailWord_3874868
  simp only [CollatzResearch.WordTrace]
  refine ⟨70664023263011242806464629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94218697684014990408619505 70664023263011242806464629)
  ·
    refine ⟨6624752180907304013106059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 70664023263011242806464629 6624752180907304013106059)
    ·
      refine ⟨9937128271360956019659089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6624752180907304013106059 9937128271360956019659089)
      ·
        refine ⟨7452846203520717014744317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9937128271360956019659089 7452846203520717014744317)
        ·
          refine ⟨2794817326320268880529119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7452846203520717014744317 2794817326320268880529119)
          ·
            refine ⟨4192225989480403320793679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2794817326320268880529119 4192225989480403320793679)
            ·
              refine ⟨6288338984220604981190519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4192225989480403320793679 6288338984220604981190519)
              ·
                refine ⟨9432508476330907471785779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6288338984220604981190519 9432508476330907471785779)
                ·
                  refine ⟨14148762714496361207678669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9432508476330907471785779 14148762714496361207678669)
                  ·
                    refine ⟨5305786017936135452879501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14148762714496361207678669 5305786017936135452879501)
                    ·
                      refine ⟨1989669756726050794829813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5305786017936135452879501 1989669756726050794829813)
                      ·
                        rfl

theorem cell23_3874868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 1, 1, 1, 3, 3].length) (baseStart_3874868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3874868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3874868 prefixEnd_3874868 := by exact prefixLift 3874868
  have htrace : WordTrace (prefixWord ++ tailWord_3874868) baseStart_3874868 baseEnd_3874868 := by
    simpa [prefixWord, tailWord_3874868, baseEnd_3874868] using wordTrace_append hprefix tailTrace_3874868
  have hstable : (prefixWord ++ tailWord_3874868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3874868).length < 2 ^ (prefixWord ++ tailWord_3874868).sum := by decide
  have hdescent : baseEnd_3874868 < baseStart_3874868 := by decide
  rcases family_descends (prefixWord ++ tailWord_3874868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3874878 : List Nat := [4, 2, 1, 3, 2, 1, 2, 2, 1, 3, 2]
def baseStart_3874878 : Nat := 118140960795 + 3874878 * 2 ^ 59
def prefixEnd_3874878 : Nat := 4983230072969 + 3 ^ 40 * 3874878 * 2
def baseEnd_3874878 : Nat := 1989674891532595755704767

theorem tailTrace_3874878 : CollatzResearch.WordTrace tailWord_3874878 prefixEnd_3874878 1989674891532595755704767 := by
  unfold tailWord_3874878
  simp only [CollatzResearch.WordTrace]
  refine ⟨17666051406998282165099161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94218940837324171547195525 17666051406998282165099161)
  ·
    refine ⟨13249538555248711623824371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17666051406998282165099161 13249538555248711623824371)
    ·
      refine ⟨19874307832873067435736557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13249538555248711623824371 19874307832873067435736557)
      ·
        refine ⟨7452865437327400288401209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19874307832873067435736557 7452865437327400288401209)
        ·
          refine ⟨5589649077995550216300907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7452865437327400288401209 5589649077995550216300907)
          ·
            refine ⟨8384473616993325324451361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5589649077995550216300907 8384473616993325324451361)
            ·
              refine ⟨6288355212744993993338521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8384473616993325324451361 6288355212744993993338521)
              ·
                refine ⟨4716266409558745495003891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6288355212744993993338521 4716266409558745495003891)
                ·
                  refine ⟨7074399614338118242505837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4716266409558745495003891 7074399614338118242505837)
                  ·
                    refine ⟨2652899855376794340939689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7074399614338118242505837 2652899855376794340939689)
                    ·
                      refine ⟨1989674891532595755704767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2652899855376794340939689 1989674891532595755704767)
                      ·
                        rfl

theorem cell23_3874878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 2, 2, 1, 3, 2].length) (baseStart_3874878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3874878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3874878 prefixEnd_3874878 := by exact prefixLift 3874878
  have htrace : WordTrace (prefixWord ++ tailWord_3874878) baseStart_3874878 baseEnd_3874878 := by
    simpa [prefixWord, tailWord_3874878, baseEnd_3874878] using wordTrace_append hprefix tailTrace_3874878
  have hstable : (prefixWord ++ tailWord_3874878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3874878).length < 2 ^ (prefixWord ++ tailWord_3874878).sum := by decide
  have hdescent : baseEnd_3874878 < baseStart_3874878 := by decide
  rcases family_descends (prefixWord ++ tailWord_3874878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3874880 : List Nat := [2, 1, 1, 2, 2, 4, 2, 2, 7]
def baseStart_3874880 : Nat := 118140960795 + 3874880 * 2 ^ 59
def prefixEnd_3874880 : Nat := 4983230072969 + 3 ^ 40 * 3874880 * 2
def baseEnd_3874880 : Nat := 221075102054878305319973

theorem tailTrace_3874880 : CollatzResearch.WordTrace tailWord_3874880 prefixEnd_3874880 221075102054878305319973 := by
  unfold tailWord_3874880
  simp only [CollatzResearch.WordTrace]
  refine ⟨70664242100989505831183047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94218989467986007774910729 70664242100989505831183047)
  ·
    refine ⟨105996363151484258746774571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70664242100989505831183047 105996363151484258746774571)
    ·
      refine ⟨158994544727226388120161857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105996363151484258746774571 158994544727226388120161857)
      ·
        refine ⟨119245908545419791090121393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 158994544727226388120161857 119245908545419791090121393)
        ·
          refine ⟨89434431409064843317591045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119245908545419791090121393 89434431409064843317591045)
          ·
            refine ⟨16768955889199658122048321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89434431409064843317591045 16768955889199658122048321)
            ·
              refine ⟨12576716916899743591536241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16768955889199658122048321 12576716916899743591536241)
              ·
                refine ⟨9432537687674807693652181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12576716916899743591536241 9432537687674807693652181)
                ·
                  refine ⟨221075102054878305319973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9432537687674807693652181 221075102054878305319973)
                  ·
                    rfl

theorem cell23_3874880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 2, 7].length) (baseStart_3874880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3874880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3874880 prefixEnd_3874880 := by exact prefixLift 3874880
  have htrace : WordTrace (prefixWord ++ tailWord_3874880) baseStart_3874880 baseEnd_3874880 := by
    simpa [prefixWord, tailWord_3874880, baseEnd_3874880] using wordTrace_append hprefix tailTrace_3874880
  have hstable : (prefixWord ++ tailWord_3874880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3874880).length < 2 ^ (prefixWord ++ tailWord_3874880).sum := by decide
  have hdescent : baseEnd_3874880 < baseStart_3874880 := by decide
  rcases family_descends (prefixWord ++ tailWord_3874880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3874947 : List Nat := [1, 1, 1, 3, 3, 3, 1, 3, 2, 1, 4]
def baseStart_3874947 : Nat := 118140960795 + 3874947 * 2 ^ 59
def prefixEnd_3874947 : Nat := 4983230072969 + 3 ^ 40 * 3874947 * 2
def baseEnd_3874947 : Nat := 1989710321697755985741949

theorem tailTrace_3874947 : CollatzResearch.WordTrace tailWord_3874947 prefixEnd_3874947 1989710321697755985741949 := by
  unfold tailWord_3874947
  simp only [CollatzResearch.WordTrace]
  refine ⟨141330927892736282105055095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94220618595157521403370063 141330927892736282105055095)
  ·
    refine ⟨211996391839104423157582643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141330927892736282105055095 211996391839104423157582643)
    ·
      refine ⟨317994587758656634736373965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 211996391839104423157582643 317994587758656634736373965)
      ·
        refine ⟨119247970409496238026140237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 317994587758656634736373965 119247970409496238026140237)
        ·
          refine ⟨44717988903561089259802589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119247970409496238026140237 44717988903561089259802589)
          ·
            refine ⟨16769245838835408472425971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44717988903561089259802589 16769245838835408472425971)
            ·
              refine ⟨25153868758253112708638957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16769245838835408472425971 25153868758253112708638957)
              ·
                refine ⟨9432700784344917265739609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25153868758253112708638957 9432700784344917265739609)
                ·
                  refine ⟨7074525588258687949304707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9432700784344917265739609 7074525588258687949304707)
                  ·
                    refine ⟨10611788382388031923957061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7074525588258687949304707 10611788382388031923957061)
                    ·
                      refine ⟨1989710321697755985741949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10611788382388031923957061 1989710321697755985741949)
                      ·
                        rfl

theorem cell23_3874947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 3, 2, 1, 4].length) (baseStart_3874947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3874947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3874947 prefixEnd_3874947 := by exact prefixLift 3874947
  have htrace : WordTrace (prefixWord ++ tailWord_3874947) baseStart_3874947 baseEnd_3874947 := by
    simpa [prefixWord, tailWord_3874947, baseEnd_3874947] using wordTrace_append hprefix tailTrace_3874947
  have hstable : (prefixWord ++ tailWord_3874947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3874947).length < 2 ^ (prefixWord ++ tailWord_3874947).sum := by decide
  have hdescent : baseEnd_3874947 < baseStart_3874947 := by decide
  rcases family_descends (prefixWord ++ tailWord_3874947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3874960 : List Nat := [2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 6]
def baseStart_3874960 : Nat := 118140960795 + 3874960 * 2 ^ 59
def prefixEnd_3874960 : Nat := 4983230072969 + 3 ^ 40 * 3874960 * 2
def baseEnd_3874960 : Nat := 1989716996946264434879389

theorem tailTrace_3874960 : CollatzResearch.WordTrace tailWord_3874960 prefixEnd_3874960 1989716996946264434879389 := by
  unfold tailWord_3874960
  simp only [CollatzResearch.WordTrace]
  refine ⟨70665701020844592662639167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94220934694459456883518889 70665701020844592662639167)
  ·
    refine ⟨105998551531266888993958751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70665701020844592662639167 105998551531266888993958751)
    ·
      refine ⟨158997827296900333490938127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105998551531266888993958751 158997827296900333490938127)
      ·
        refine ⟨238496740945350500236407191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 158997827296900333490938127 238496740945350500236407191)
        ·
          refine ⟨357745111418025750354610787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238496740945350500236407191 357745111418025750354610787)
          ·
            refine ⟨536617667127038625531916181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 357745111418025750354610787 536617667127038625531916181)
            ·
              refine ⟨25153953146579935571808571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 536617667127038625531916181 25153953146579935571808571)
              ·
                refine ⟨37730929719869903357712857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25153953146579935571808571 37730929719869903357712857)
                ·
                  refine ⟨28298197289902427518284643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37730929719869903357712857 28298197289902427518284643)
                  ·
                    refine ⟨42447295934853641277426965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28298197289902427518284643 42447295934853641277426965)
                    ·
                      refine ⟨1989716996946264434879389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42447295934853641277426965 1989716996946264434879389)
                      ·
                        rfl

theorem cell23_3874960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 6].length) (baseStart_3874960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3874960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3874960 prefixEnd_3874960 := by exact prefixLift 3874960
  have htrace : WordTrace (prefixWord ++ tailWord_3874960) baseStart_3874960 baseEnd_3874960 := by
    simpa [prefixWord, tailWord_3874960, baseEnd_3874960] using wordTrace_append hprefix tailTrace_3874960
  have hstable : (prefixWord ++ tailWord_3874960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3874960).length < 2 ^ (prefixWord ++ tailWord_3874960).sum := by decide
  have hdescent : baseEnd_3874960 < baseStart_3874960 := by decide
  rcases family_descends (prefixWord ++ tailWord_3874960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3875054 : List Nat := [4, 1, 2, 1, 1, 1, 1, 1, 1, 8, 2]
def baseStart_3875054 : Nat := 118140960795 + 3875054 * 2 ^ 59
def prefixEnd_3875054 : Nat := 4983230072969 + 3 ^ 40 * 3875054 * 2
def baseEnd_3875054 : Nat := 1989765264127787067103957

theorem tailTrace_3875054 : CollatzResearch.WordTrace tailWord_3875054 prefixEnd_3875054 1989765264127787067103957 := by
  unfold tailWord_3875054
  simp only [CollatzResearch.WordTrace]
  refine ⟨17666853812918579922400027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94223220335565759586133477 17666853812918579922400027)
  ·
    refine ⟨26500280719377869883600041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17666853812918579922400027 26500280719377869883600041)
    ·
      refine ⟨19875210539533402412700031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26500280719377869883600041 19875210539533402412700031)
      ·
        refine ⟨29812815809300103619050047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19875210539533402412700031 29812815809300103619050047)
        ·
          refine ⟨44719223713950155428575071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29812815809300103619050047 44719223713950155428575071)
          ·
            refine ⟨67078835570925233142862607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44719223713950155428575071 67078835570925233142862607)
            ·
              refine ⟨100618253356387849714293911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67078835570925233142862607 100618253356387849714293911)
              ·
                refine ⟨150927380034581774571440867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100618253356387849714293911 150927380034581774571440867)
                ·
                  refine ⟨226391070051872661857161301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 150927380034581774571440867 226391070051872661857161301)
                  ·
                    refine ⟨2653020352170382756138609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 226391070051872661857161301 2653020352170382756138609)
                    ·
                      refine ⟨1989765264127787067103957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2653020352170382756138609 1989765264127787067103957)
                      ·
                        rfl

theorem cell23_3875054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 1, 8, 2].length) (baseStart_3875054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3875054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3875054 prefixEnd_3875054 := by exact prefixLift 3875054
  have htrace : WordTrace (prefixWord ++ tailWord_3875054) baseStart_3875054 baseEnd_3875054 := by
    simpa [prefixWord, tailWord_3875054, baseEnd_3875054] using wordTrace_append hprefix tailTrace_3875054
  have hstable : (prefixWord ++ tailWord_3875054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3875054).length < 2 ^ (prefixWord ++ tailWord_3875054).sum := by decide
  have hdescent : baseEnd_3875054 < baseStart_3875054 := by decide
  rcases family_descends (prefixWord ++ tailWord_3875054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3875108 : List Nat := [2, 3, 1, 3, 1, 4, 1, 2, 1, 2, 3]
def baseStart_3875108 : Nat := 118140960795 + 3875108 * 2 ^ 59
def prefixEnd_3875108 : Nat := 4983230072969 + 3 ^ 40 * 3875108 * 2
def baseEnd_3875108 : Nat := 1989792992083129855828709

theorem tailTrace_3875108 : CollatzResearch.WordTrace tailWord_3875108 prefixEnd_3875108 1989792992083129855828709 := by
  unfold tailWord_3875108
  simp only [CollatzResearch.WordTrace]
  refine ⟨70668400022576503300832989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94224533363435337734443985 70668400022576503300832989)
  ·
    refine ⟨26500650008466188737812371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70668400022576503300832989 26500650008466188737812371)
    ·
      refine ⟨39750975012699283106718557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26500650008466188737812371 39750975012699283106718557)
      ·
        refine ⟨14906615629762231165019459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39750975012699283106718557 14906615629762231165019459)
        ·
          refine ⟨22359923444643346747529189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14906615629762231165019459 22359923444643346747529189)
          ·
            refine ⟨4192485645870627515161723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22359923444643346747529189 4192485645870627515161723)
            ·
              refine ⟨6288728468805941272742585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4192485645870627515161723 6288728468805941272742585)
              ·
                refine ⟨4716546351604455954556939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6288728468805941272742585 4716546351604455954556939)
                ·
                  refine ⟨7074819527406683931835409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4716546351604455954556939 7074819527406683931835409)
                  ·
                    refine ⟨5306114645555012948876557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7074819527406683931835409 5306114645555012948876557)
                    ·
                      refine ⟨1989792992083129855828709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5306114645555012948876557 1989792992083129855828709)
                      ·
                        rfl

theorem cell23_3875108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 1, 2, 1, 2, 3].length) (baseStart_3875108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3875108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3875108 prefixEnd_3875108 := by exact prefixLift 3875108
  have htrace : WordTrace (prefixWord ++ tailWord_3875108) baseStart_3875108 baseEnd_3875108 := by
    simpa [prefixWord, tailWord_3875108, baseEnd_3875108] using wordTrace_append hprefix tailTrace_3875108
  have hstable : (prefixWord ++ tailWord_3875108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3875108).length < 2 ^ (prefixWord ++ tailWord_3875108).sum := by decide
  have hdescent : baseEnd_3875108 < baseStart_3875108 := by decide
  rcases family_descends (prefixWord ++ tailWord_3875108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3875118 : List Nat := [4, 1, 3, 3, 1, 1, 1, 2, 1, 2, 4]
def baseStart_3875118 : Nat := 118140960795 + 3875118 * 2 ^ 59
def prefixEnd_3875118 : Nat := 4983230072969 + 3 ^ 40 * 3875118 * 2
def baseEnd_3875118 : Nat := 1989798126889674816703663

theorem tailTrace_3875118 : CollatzResearch.WordTrace tailWord_3875118 prefixEnd_3875118 1989798126889674816703663 := by
  unfold tailWord_3875118
  simp only [CollatzResearch.WordTrace]
  refine ⟨17667145596889597288691251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94224776516744518873020005 17667145596889597288691251)
  ·
    refine ⟨26500718395334395933036877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17667145596889597288691251 26500718395334395933036877)
    ·
      refine ⟨9937769398250398474888829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26500718395334395933036877 9937769398250398474888829)
      ·
        refine ⟨3726663524343899428083311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9937769398250398474888829 3726663524343899428083311)
        ·
          refine ⟨5589995286515849142124967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3726663524343899428083311 5589995286515849142124967)
          ·
            refine ⟨8384992929773773713187451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5589995286515849142124967 8384992929773773713187451)
            ·
              refine ⟨12577489394660660569781177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8384992929773773713187451 12577489394660660569781177)
              ·
                refine ⟨9433117045995495427335883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12577489394660660569781177 9433117045995495427335883)
                ·
                  refine ⟨14149675568993243141003825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9433117045995495427335883 14149675568993243141003825)
                  ·
                    refine ⟨10612256676744932355752869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14149675568993243141003825 10612256676744932355752869)
                    ·
                      refine ⟨1989798126889674816703663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10612256676744932355752869 1989798126889674816703663)
                      ·
                        rfl

theorem cell23_3875118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_3875118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3875118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3875118 prefixEnd_3875118 := by exact prefixLift 3875118
  have htrace : WordTrace (prefixWord ++ tailWord_3875118) baseStart_3875118 baseEnd_3875118 := by
    simpa [prefixWord, tailWord_3875118, baseEnd_3875118] using wordTrace_append hprefix tailTrace_3875118
  have hstable : (prefixWord ++ tailWord_3875118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3875118).length < 2 ^ (prefixWord ++ tailWord_3875118).sum := by decide
  have hdescent : baseEnd_3875118 < baseStart_3875118 := by decide
  rcases family_descends (prefixWord ++ tailWord_3875118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3875121 : List Nat := [1, 2, 2, 3, 4, 1, 1, 2, 1, 3, 3]
def baseStart_3875121 : Nat := 118140960795 + 3875121 * 2 ^ 59
def prefixEnd_3875121 : Nat := 4983230072969 + 3 ^ 40 * 3875121 * 2
def baseEnd_3875121 : Nat := 1989799667331638304966149

theorem tailTrace_3875121 : CollatzResearch.WordTrace tailWord_3875121 prefixEnd_3875121 1989799667331638304966149 := by
  unfold tailWord_3875121
  simp only [CollatzResearch.WordTrace]
  refine ⟨141337274194105909821889217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94224849462737273214592811 141337274194105909821889217)
  ·
    refine ⟨106002955645579432366416913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141337274194105909821889217 106002955645579432366416913)
    ·
      refine ⟨79502216734184574274812685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106002955645579432366416913 79502216734184574274812685)
      ·
        refine ⟨29813331275319215353054757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79502216734184574274812685 29813331275319215353054757)
        ·
          refine ⟨5589999614122352878697767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29813331275319215353054757 5589999614122352878697767)
          ·
            refine ⟨8384999421183529318046651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5589999614122352878697767 8384999421183529318046651)
            ·
              refine ⟨12577499131775293977069977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8384999421183529318046651 12577499131775293977069977)
              ·
                refine ⟨9433124348831470482802483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12577499131775293977069977 9433124348831470482802483)
                ·
                  refine ⟨14149686523247205724203725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9433124348831470482802483 14149686523247205724203725)
                  ·
                    refine ⟨5306132446217702146576397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14149686523247205724203725 5306132446217702146576397)
                    ·
                      refine ⟨1989799667331638304966149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5306132446217702146576397 1989799667331638304966149)
                      ·
                        rfl

theorem cell23_3875121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 2, 1, 3, 3].length) (baseStart_3875121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3875121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3875121 prefixEnd_3875121 := by exact prefixLift 3875121
  have htrace : WordTrace (prefixWord ++ tailWord_3875121) baseStart_3875121 baseEnd_3875121 := by
    simpa [prefixWord, tailWord_3875121, baseEnd_3875121] using wordTrace_append hprefix tailTrace_3875121
  have hstable : (prefixWord ++ tailWord_3875121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3875121).length < 2 ^ (prefixWord ++ tailWord_3875121).sum := by decide
  have hdescent : baseEnd_3875121 < baseStart_3875121 := by decide
  rcases family_descends (prefixWord ++ tailWord_3875121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3875127 : List Nat := [1, 1, 3, 1, 2, 1, 1, 2, 4, 3, 4]
def baseStart_3875127 : Nat := 118140960795 + 3875127 * 2 ^ 59
def prefixEnd_3875127 : Nat := 4983230072969 + 3 ^ 40 * 3875127 * 2
def baseEnd_3875127 : Nat := 1989802748215565281491121

theorem tailTrace_3875127 : CollatzResearch.WordTrace tailWord_3875127 prefixEnd_3875127 1989802748215565281491121 := by
  unfold tailWord_3875127
  simp only [CollatzResearch.WordTrace]
  refine ⟨141337493032084172846607635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94224995354722781897738423 141337493032084172846607635)
  ·
    refine ⟨212006239548126259269911453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141337493032084172846607635 212006239548126259269911453)
    ·
      refine ⟨79502339830547347226216795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212006239548126259269911453 79502339830547347226216795)
      ·
        refine ⟨119253509745821020839325193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79502339830547347226216795 119253509745821020839325193)
        ·
          refine ⟨89440132309365765629493895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119253509745821020839325193 89440132309365765629493895)
          ·
            refine ⟨134160198464048648444240843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89440132309365765629493895 134160198464048648444240843)
            ·
              refine ⟨201240297696072972666361265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134160198464048648444240843 201240297696072972666361265)
              ·
                refine ⟨150930223272054729499770949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 201240297696072972666361265 150930223272054729499770949)
                ·
                  refine ⟨28299416863510261781207053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 150930223272054729499770949 28299416863510261781207053)
                  ·
                    refine ⟨10612281323816348167952645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28299416863510261781207053 10612281323816348167952645)
                    ·
                      refine ⟨1989802748215565281491121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10612281323816348167952645 1989802748215565281491121)
                      ·
                        rfl

theorem cell23_3875127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 4, 3, 4].length) (baseStart_3875127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3875127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3875127 prefixEnd_3875127 := by exact prefixLift 3875127
  have htrace : WordTrace (prefixWord ++ tailWord_3875127) baseStart_3875127 baseEnd_3875127 := by
    simpa [prefixWord, tailWord_3875127, baseEnd_3875127] using wordTrace_append hprefix tailTrace_3875127
  have hstable : (prefixWord ++ tailWord_3875127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3875127).length < 2 ^ (prefixWord ++ tailWord_3875127).sum := by decide
  have hdescent : baseEnd_3875127 < baseStart_3875127 := by decide
  rcases family_descends (prefixWord ++ tailWord_3875127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3875147 : List Nat := [1, 1, 1, 1, 3, 1, 1, 4, 4, 1, 5]
def baseStart_3875147 : Nat := 118140960795 + 3875147 * 2 ^ 59
def prefixEnd_3875147 : Nat := 4983230072969 + 3 ^ 40 * 3875147 * 2
def baseEnd_3875147 : Nat := 1989813017828655203241029

theorem tailTrace_3875147 : CollatzResearch.WordTrace tailWord_3875147 prefixEnd_3875147 1989813017828655203241029 := by
  unfold tailWord_3875147
  simp only [CollatzResearch.WordTrace]
  refine ⟨141338222492011716262335695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94225481661341144174890463 141338222492011716262335695)
  ·
    refine ⟨212007333738017574393503543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141338222492011716262335695 212007333738017574393503543)
    ·
      refine ⟨318011000607026361590255315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212007333738017574393503543 318011000607026361590255315)
      ·
        refine ⟨477016500910539542385382973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318011000607026361590255315 477016500910539542385382973)
        ·
          refine ⟨178881187841452328394518615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 477016500910539542385382973 178881187841452328394518615)
          ·
            refine ⟨268321781762178492591777923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178881187841452328394518615 268321781762178492591777923)
            ·
              refine ⟨402482672643267738887666885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 268321781762178492591777923 402482672643267738887666885)
              ·
                refine ⟨75465501120612701041437541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 402482672643267738887666885 75465501120612701041437541)
                ·
                  refine ⟨14149781460114881445269539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 75465501120612701041437541 14149781460114881445269539)
                  ·
                    refine ⟨21224672190172322167904309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14149781460114881445269539 21224672190172322167904309)
                    ·
                      refine ⟨1989813017828655203241029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21224672190172322167904309 1989813017828655203241029)
                      ·
                        rfl

theorem cell23_3875147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 4, 1, 5].length) (baseStart_3875147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3875147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3875147 prefixEnd_3875147 := by exact prefixLift 3875147
  have htrace : WordTrace (prefixWord ++ tailWord_3875147) baseStart_3875147 baseEnd_3875147 := by
    simpa [prefixWord, tailWord_3875147, baseEnd_3875147] using wordTrace_append hprefix tailTrace_3875147
  have hstable : (prefixWord ++ tailWord_3875147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3875147).length < 2 ^ (prefixWord ++ tailWord_3875147).sum := by decide
  have hdescent : baseEnd_3875147 < baseStart_3875147 := by decide
  rcases family_descends (prefixWord ++ tailWord_3875147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3875161 : List Nat := [1, 2, 1, 2, 2, 2, 1, 2, 6, 2, 2]
def baseStart_3875161 : Nat := 118140960795 + 3875161 * 2 ^ 59
def prefixEnd_3875161 : Nat := 4983230072969 + 3 ^ 40 * 3875161 * 2
def baseEnd_3875161 : Nat := 1989820206557818148465965

theorem tailTrace_3875161 : CollatzResearch.WordTrace tailWord_3875161 prefixEnd_3875161 1989820206557818148465965 := by
  unfold tailWord_3875161
  simp only [CollatzResearch.WordTrace]
  refine ⟨141338733113960996653345337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94225822075973997768896891 141338733113960996653345337)
  ·
    refine ⟨106004049835470747490009003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141338733113960996653345337 106004049835470747490009003)
    ·
      refine ⟨159006074753206121235013505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106004049835470747490009003 159006074753206121235013505)
      ·
        refine ⟨119254556064904590926260129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159006074753206121235013505 119254556064904590926260129)
        ·
          refine ⟨89440917048678443194695097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119254556064904590926260129 89440917048678443194695097)
          ·
            refine ⟨67080687786508832396021323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89440917048678443194695097 67080687786508832396021323)
            ·
              refine ⟨100621031679763248594031985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67080687786508832396021323 100621031679763248594031985)
              ·
                refine ⟨75465773759822436445523989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100621031679763248594031985 75465773759822436445523989)
                ·
                  refine ⟨3537458144991676708383937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 75465773759822436445523989 3537458144991676708383937)
                  ·
                    refine ⟨2653093608743757531287953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3537458144991676708383937 2653093608743757531287953)
                    ·
                      refine ⟨1989820206557818148465965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2653093608743757531287953 1989820206557818148465965)
                      ·
                        rfl

theorem cell23_3875161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 2, 6, 2, 2].length) (baseStart_3875161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3875161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3875161 prefixEnd_3875161 := by exact prefixLift 3875161
  have htrace : WordTrace (prefixWord ++ tailWord_3875161) baseStart_3875161 baseEnd_3875161 := by
    simpa [prefixWord, tailWord_3875161, baseEnd_3875161] using wordTrace_append hprefix tailTrace_3875161
  have hstable : (prefixWord ++ tailWord_3875161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3875161).length < 2 ^ (prefixWord ++ tailWord_3875161).sum := by decide
  have hdescent : baseEnd_3875161 < baseStart_3875161 := by decide
  rcases family_descends (prefixWord ++ tailWord_3875161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3875167 : List Nat := [1, 1, 2, 3, 1, 2, 3, 1, 9]
def baseStart_3875167 : Nat := 118140960795 + 3875167 * 2 ^ 59
def prefixEnd_3875167 : Nat := 4983230072969 + 3 ^ 40 * 3875167 * 2
def baseEnd_3875167 : Nat := 221091476382416124998993

theorem tailTrace_3875167 : CollatzResearch.WordTrace tailWord_3875167 prefixEnd_3875167 221091476382416124998993 := by
  unfold tailWord_3875167
  simp only [CollatzResearch.WordTrace]
  refine ⟨141338951951939259678063755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94225967967959506452042503 141338951951939259678063755)
  ·
    refine ⟨212008427927908889517095633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141338951951939259678063755 212008427927908889517095633)
    ·
      refine ⟨159006320945931667137821725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212008427927908889517095633 159006320945931667137821725)
      ·
        refine ⟨59627370354724375176683147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159006320945931667137821725 59627370354724375176683147)
        ·
          refine ⟨89441055532086562765024721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59627370354724375176683147 89441055532086562765024721)
          ·
            refine ⟨67080791649064922073768541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89441055532086562765024721 67080791649064922073768541)
            ·
              refine ⟨25155296868399345777663203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67080791649064922073768541 25155296868399345777663203)
              ·
                refine ⟨37732945302599018666494805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25155296868399345777663203 37732945302599018666494805)
                ·
                  refine ⟨221091476382416124998993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 37732945302599018666494805 221091476382416124998993)
                  ·
                    rfl

theorem cell23_3875167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 1, 9].length) (baseStart_3875167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3875167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3875167 prefixEnd_3875167 := by exact prefixLift 3875167
  have htrace : WordTrace (prefixWord ++ tailWord_3875167) baseStart_3875167 baseEnd_3875167 := by
    simpa [prefixWord, tailWord_3875167, baseEnd_3875167] using wordTrace_append hprefix tailTrace_3875167
  have hstable : (prefixWord ++ tailWord_3875167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3875167).length < 2 ^ (prefixWord ++ tailWord_3875167).sum := by decide
  have hdescent : baseEnd_3875167 < baseStart_3875167 := by decide
  rcases family_descends (prefixWord ++ tailWord_3875167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3875178 : List Nat := [3, 1, 3, 3, 1, 1, 2, 2, 1, 4, 2]
def baseStart_3875178 : Nat := 118140960795 + 3875178 * 2 ^ 59
def prefixEnd_3875178 : Nat := 4983230072969 + 3 ^ 40 * 3875178 * 2
def baseEnd_3875178 : Nat := 1989828935728944581953387

theorem tailTrace_3875178 : CollatzResearch.WordTrace tailWord_3875178 prefixEnd_3875178 1989828935728944581953387 := by
  unfold tailWord_3875178
  simp only [CollatzResearch.WordTrace]
  refine ⟨35334838288724852139178547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94226235436599605704476125 35334838288724852139178547)
  ·
    refine ⟨53002257433087278208767821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35334838288724852139178547 53002257433087278208767821)
    ·
      refine ⟨19875846537407729328287933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53002257433087278208767821 19875846537407729328287933)
      ·
        refine ⟨7453442451527898498107975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19875846537407729328287933 7453442451527898498107975)
        ·
          refine ⟨11180163677291847747161963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7453442451527898498107975 11180163677291847747161963)
          ·
            refine ⟨16770245515937771620742945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11180163677291847747161963 16770245515937771620742945)
            ·
              refine ⟨12577684136953328715557209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16770245515937771620742945 12577684136953328715557209)
              ·
                refine ⟨9433263102714996536667907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12577684136953328715557209 9433263102714996536667907)
                ·
                  refine ⟨14149894654072494805001861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9433263102714996536667907 14149894654072494805001861)
                  ·
                    refine ⟨2653105247638592775937849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14149894654072494805001861 2653105247638592775937849)
                    ·
                      refine ⟨1989828935728944581953387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2653105247638592775937849 1989828935728944581953387)
                      ·
                        rfl

theorem cell23_3875178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 2, 1, 4, 2].length) (baseStart_3875178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3875178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3875178 prefixEnd_3875178 := by exact prefixLift 3875178
  have htrace : WordTrace (prefixWord ++ tailWord_3875178) baseStart_3875178 baseEnd_3875178 := by
    simpa [prefixWord, tailWord_3875178, baseEnd_3875178] using wordTrace_append hprefix tailTrace_3875178
  have hstable : (prefixWord ++ tailWord_3875178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3875178).length < 2 ^ (prefixWord ++ tailWord_3875178).sum := by decide
  have hdescent : baseEnd_3875178 < baseStart_3875178 := by decide
  rcases family_descends (prefixWord ++ tailWord_3875178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3875195 : List Nat := [1, 1, 1, 1, 1, 9, 1, 2, 2, 2, 2]
def baseStart_3875195 : Nat := 118140960795 + 3875195 * 2 ^ 59
def prefixEnd_3875195 : Nat := 4983230072969 + 3 ^ 40 * 3875195 * 2
def baseEnd_3875195 : Nat := 1989837664900071015440809

theorem tailTrace_3875195 : CollatzResearch.WordTrace tailWord_3875195 prefixEnd_3875195 1989837664900071015440809 := by
  unfold tailWord_3875195
  simp only [CollatzResearch.WordTrace]
  refine ⟨141339973195837820460083039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94226648797225213640055359 141339973195837820460083039)
  ·
    refine ⟨212009959793756730690124559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141339973195837820460083039 212009959793756730690124559)
    ·
      refine ⟨318014939690635096035186839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212009959793756730690124559 318014939690635096035186839)
      ·
        refine ⟨477022409535952644052780259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318014939690635096035186839 477022409535952644052780259)
        ·
          refine ⟨715533614303928966079170389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 477022409535952644052780259 715533614303928966079170389)
          ·
            refine ⟨4192579771312083785620139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 715533614303928966079170389 4192579771312083785620139)
            ·
              refine ⟨6288869656968125678430209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4192579771312083785620139 6288869656968125678430209)
              ·
                refine ⟨4716652242726094258822657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6288869656968125678430209 4716652242726094258822657)
                ·
                  refine ⟨3537489182044570694116993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4716652242726094258822657 3537489182044570694116993)
                  ·
                    refine ⟨2653116886533428020587745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3537489182044570694116993 2653116886533428020587745)
                    ·
                      refine ⟨1989837664900071015440809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2653116886533428020587745 1989837664900071015440809)
                      ·
                        rfl

theorem cell23_3875195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 1, 2, 2, 2, 2].length) (baseStart_3875195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3875195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3875195 prefixEnd_3875195 := by exact prefixLift 3875195
  have htrace : WordTrace (prefixWord ++ tailWord_3875195) baseStart_3875195 baseEnd_3875195 := by
    simpa [prefixWord, tailWord_3875195, baseEnd_3875195] using wordTrace_append hprefix tailTrace_3875195
  have hstable : (prefixWord ++ tailWord_3875195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3875195).length < 2 ^ (prefixWord ++ tailWord_3875195).sum := by decide
  have hdescent : baseEnd_3875195 < baseStart_3875195 := by decide
  rcases family_descends (prefixWord ++ tailWord_3875195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3875201 : List Nat := [1, 2, 4, 3, 1, 2, 2, 1, 7]
def baseStart_3875201 : Nat := 118140960795 + 3875201 * 2 ^ 59
def prefixEnd_3875201 : Nat := 4983230072969 + 3 ^ 40 * 3875201 * 2
def baseEnd_3875201 : Nat := 221093416198221999107309

theorem tailTrace_3875201 : CollatzResearch.WordTrace tailWord_3875201 prefixEnd_3875201 221093416198221999107309 := by
  unfold tailWord_3875201
  simp only [CollatzResearch.WordTrace]
  refine ⟨141340192033816083484801457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94226794689210722323200971 141340192033816083484801457)
  ·
    refine ⟨106005144025362062613601093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141340192033816083484801457 106005144025362062613601093)
    ·
      refine ⟨19875964504755386740050205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106005144025362062613601093 19875964504755386740050205)
      ·
        refine ⟨7453486689283270027518827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19875964504755386740050205 7453486689283270027518827)
        ·
          refine ⟨11180230033924905041278241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7453486689283270027518827 11180230033924905041278241)
          ·
            refine ⟨8385172525443678780958681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11180230033924905041278241 8385172525443678780958681)
            ·
              refine ⟨6288879394082759085719011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8385172525443678780958681 6288879394082759085719011)
              ·
                refine ⟨9433319091124138628578517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6288879394082759085719011 9433319091124138628578517)
                ·
                  refine ⟨221093416198221999107309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9433319091124138628578517 221093416198221999107309)
                  ·
                    rfl

theorem cell23_3875201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 2, 1, 7].length) (baseStart_3875201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3875201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3875201 prefixEnd_3875201 := by exact prefixLift 3875201
  have htrace : WordTrace (prefixWord ++ tailWord_3875201) baseStart_3875201 baseEnd_3875201 := by
    simpa [prefixWord, tailWord_3875201, baseEnd_3875201] using wordTrace_append hprefix tailTrace_3875201
  have hstable : (prefixWord ++ tailWord_3875201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3875201).length < 2 ^ (prefixWord ++ tailWord_3875201).sum := by decide
  have hdescent : baseEnd_3875201 < baseStart_3875201 := by decide
  rcases family_descends (prefixWord ++ tailWord_3875201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3875252 : List Nat := [2, 5, 2, 2, 2, 1, 1, 1, 7]
def baseStart_3875252 : Nat := 118140960795 + 3875252 * 2 ^ 59
def prefixEnd_3875252 : Nat := 4983230072969 + 3 ^ 40 * 3875252 * 2
def baseEnd_3875252 : Nat := 221096325921930810269783

theorem tailTrace_3875252 : CollatzResearch.WordTrace tailWord_3875252 prefixEnd_3875252 221096325921930810269783 := by
  unfold tailWord_3875252
  simp only [CollatzResearch.WordTrace]
  refine ⟨70671026078315659597454005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94228034771087546129938673 70671026078315659597454005)
  ·
    refine ⟨6625408694842093087261313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 70671026078315659597454005 6625408694842093087261313)
    ·
      refine ⟨4969056521131569815445985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6625408694842093087261313 4969056521131569815445985)
      ·
        refine ⟨3726792390848677361584489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4969056521131569815445985 3726792390848677361584489)
        ·
          refine ⟨2795094293136508021188367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3726792390848677361584489 2795094293136508021188367)
          ·
            refine ⟨4192641439704762031782551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2795094293136508021188367 4192641439704762031782551)
            ·
              refine ⟨6288962159557143047673827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4192641439704762031782551 6288962159557143047673827)
              ·
                refine ⟨9433443239335714571510741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6288962159557143047673827 9433443239335714571510741)
                ·
                  refine ⟨221096325921930810269783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9433443239335714571510741 221096325921930810269783)
                  ·
                    rfl

theorem cell23_3875252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 1, 1, 7].length) (baseStart_3875252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3875252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3875252 prefixEnd_3875252 := by exact prefixLift 3875252
  have htrace : WordTrace (prefixWord ++ tailWord_3875252) baseStart_3875252 baseEnd_3875252 := by
    simpa [prefixWord, tailWord_3875252, baseEnd_3875252] using wordTrace_append hprefix tailTrace_3875252
  have hstable : (prefixWord ++ tailWord_3875252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3875252).length < 2 ^ (prefixWord ++ tailWord_3875252).sum := by decide
  have hdescent : baseEnd_3875252 < baseStart_3875252 := by decide
  rcases family_descends (prefixWord ++ tailWord_3875252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3875311 : List Nat := [1, 1, 2, 1, 4, 1, 1, 2, 3, 5, 2]
def baseStart_3875311 : Nat := 118140960795 + 3875311 * 2 ^ 59
def prefixEnd_3875311 : Nat := 4983230072969 + 3 ^ 40 * 3875311 * 2
def baseEnd_3875311 : Nat := 1989897228655992561590275

theorem tailTrace_3875311 : CollatzResearch.WordTrace tailWord_3875311 prefixEnd_3875311 1989897228655992561590275 := by
  unfold tailWord_3875311
  simp only [CollatzResearch.WordTrace]
  refine ⟨141344204063417572271305787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94229469375611714847537191 141344204063417572271305787)
  ·
    refine ⟨212016306095126358406958681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141344204063417572271305787 212016306095126358406958681)
    ·
      refine ⟨159012229571344768805219011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212016306095126358406958681 159012229571344768805219011)
      ·
        refine ⟨238518344357017153207828517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159012229571344768805219011 238518344357017153207828517)
        ·
          refine ⟨44722189566940716226467847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 238518344357017153207828517 44722189566940716226467847)
          ·
            refine ⟨67083284350411074339701771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44722189566940716226467847 67083284350411074339701771)
            ·
              refine ⟨100624926525616611509552657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67083284350411074339701771 100624926525616611509552657)
              ·
                refine ⟨75468694894212458632164493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100624926525616611509552657 75468694894212458632164493)
                ·
                  refine ⟨28300760585329671987061685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75468694894212458632164493 28300760585329671987061685)
                  ·
                    refine ⟨2653196304874656748787033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28300760585329671987061685 2653196304874656748787033)
                    ·
                      refine ⟨1989897228655992561590275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2653196304874656748787033 1989897228655992561590275)
                      ·
                        rfl

theorem cell23_3875311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 3, 5, 2].length) (baseStart_3875311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3875311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3875311 prefixEnd_3875311 := by exact prefixLift 3875311
  have htrace : WordTrace (prefixWord ++ tailWord_3875311) baseStart_3875311 baseEnd_3875311 := by
    simpa [prefixWord, tailWord_3875311, baseEnd_3875311] using wordTrace_append hprefix tailTrace_3875311
  have hstable : (prefixWord ++ tailWord_3875311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3875311).length < 2 ^ (prefixWord ++ tailWord_3875311).sum := by decide
  have hdescent : baseEnd_3875311 < baseStart_3875311 := by decide
  rcases family_descends (prefixWord ++ tailWord_3875311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3875335 : List Nat := [1, 1, 4, 3, 3, 1, 1, 2, 3, 1, 3]
def baseStart_3875335 : Nat := 118140960795 + 3875335 * 2 ^ 59
def prefixEnd_3875335 : Nat := 4983230072969 + 3 ^ 40 * 3875335 * 2
def baseEnd_3875335 : Nat := 1989909552191700467690165

theorem tailTrace_3875335 : CollatzResearch.WordTrace tailWord_3875335 prefixEnd_3875335 1989909552191700467690165 := by
  unfold tailWord_3875335
  simp only [CollatzResearch.WordTrace]
  refine ⟨141345079415330624370179459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94230052943553749580119639 141345079415330624370179459)
  ·
    refine ⟨212017619122995936555269189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141345079415330624370179459 212017619122995936555269189)
    ·
      refine ⟨39753303585561738104112973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 212017619122995936555269189 39753303585561738104112973)
      ·
        refine ⟨14907488844585651789042365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39753303585561738104112973 14907488844585651789042365)
        ·
          refine ⟨5590308316719619420890887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14907488844585651789042365 5590308316719619420890887)
          ·
            refine ⟨8385462475079429131336331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5590308316719619420890887 8385462475079429131336331)
            ·
              refine ⟨12578193712619143697004497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8385462475079429131336331 12578193712619143697004497)
              ·
                refine ⟨9433645284464357772753373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12578193712619143697004497 9433645284464357772753373)
                ·
                  refine ⟨3537616981674134164782515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9433645284464357772753373 3537616981674134164782515)
                  ·
                    refine ⟨5306425472511201247173773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3537616981674134164782515 5306425472511201247173773)
                    ·
                      refine ⟨1989909552191700467690165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5306425472511201247173773 1989909552191700467690165)
                      ·
                        rfl

theorem cell23_3875335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 2, 3, 1, 3].length) (baseStart_3875335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3875335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3875335 prefixEnd_3875335 := by exact prefixLift 3875335
  have htrace : WordTrace (prefixWord ++ tailWord_3875335) baseStart_3875335 baseEnd_3875335 := by
    simpa [prefixWord, tailWord_3875335, baseEnd_3875335] using wordTrace_append hprefix tailTrace_3875335
  have hstable : (prefixWord ++ tailWord_3875335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3875335).length < 2 ^ (prefixWord ++ tailWord_3875335).sum := by decide
  have hdescent : baseEnd_3875335 < baseStart_3875335 := by decide
  rcases family_descends (prefixWord ++ tailWord_3875335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3875352 : List Nat := [2, 1, 2, 3, 3, 2, 2, 3, 1, 1, 3]
def baseStart_3875352 : Nat := 118140960795 + 3875352 * 2 ^ 59
def prefixEnd_3875352 : Nat := 4983230072969 + 3 ^ 40 * 3875352 * 2
def baseEnd_3875352 : Nat := 1989918281362826901177587

theorem tailTrace_3875352 : CollatzResearch.WordTrace tailWord_3875352 prefixEnd_3875352 1989918281362826901177587 := by
  unfold tailWord_3875352
  simp only [CollatzResearch.WordTrace]
  refine ⟨70672849728134518136774155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94230466304179357515698873 70672849728134518136774155)
  ·
    refine ⟨106009274592201777205161233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70672849728134518136774155 106009274592201777205161233)
    ·
      refine ⟨79506955944151332903870925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106009274592201777205161233 79506955944151332903870925)
      ·
        refine ⟨29815108479056749838951597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79506955944151332903870925 29815108479056749838951597)
        ·
          refine ⟨11180665679646281189606849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29815108479056749838951597 11180665679646281189606849)
          ·
            refine ⟨8385499259734710892205137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11180665679646281189606849 8385499259734710892205137)
            ·
              refine ⟨6289124444801033169153853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8385499259734710892205137 6289124444801033169153853)
              ·
                refine ⟨2358421666800387438432695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6289124444801033169153853 2358421666800387438432695)
                ·
                  refine ⟨3537632500200581157649043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2358421666800387438432695 3537632500200581157649043)
                  ·
                    refine ⟨5306448750300871736473565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3537632500200581157649043 5306448750300871736473565)
                    ·
                      refine ⟨1989918281362826901177587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5306448750300871736473565 1989918281362826901177587)
                      ·
                        rfl

theorem cell23_3875352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 2, 3, 1, 1, 3].length) (baseStart_3875352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3875352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3875352 prefixEnd_3875352 := by exact prefixLift 3875352
  have htrace : WordTrace (prefixWord ++ tailWord_3875352) baseStart_3875352 baseEnd_3875352 := by
    simpa [prefixWord, tailWord_3875352, baseEnd_3875352] using wordTrace_append hprefix tailTrace_3875352
  have hstable : (prefixWord ++ tailWord_3875352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3875352).length < 2 ^ (prefixWord ++ tailWord_3875352).sum := by decide
  have hdescent : baseEnd_3875352 < baseStart_3875352 := by decide
  rcases family_descends (prefixWord ++ tailWord_3875352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3875361 : List Nat := [1, 2, 3, 2, 2, 1, 2, 3, 1, 1, 5]
def baseStart_3875361 : Nat := 118140960795 + 3875361 * 2 ^ 59
def prefixEnd_3875361 : Nat := 4983230072969 + 3 ^ 40 * 3875361 * 2
def baseEnd_3875361 : Nat := 1989922902688717365965045

theorem tailTrace_3875361 : CollatzResearch.WordTrace tailWord_3875361 prefixEnd_3875361 1989922902688717365965045 := by
  unfold tailWord_3875361
  simp only [CollatzResearch.WordTrace]
  refine ⟨141346027713236430810625937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94230685142157620540417291 141346027713236430810625937)
  ·
    refine ⟨106009520784927323107969453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141346027713236430810625937 106009520784927323107969453)
    ·
      refine ⟨39753570294347746165488545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106009520784927323107969453 39753570294347746165488545)
      ·
        refine ⟨29815177720760809624116409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39753570294347746165488545 29815177720760809624116409)
        ·
          refine ⟨22361383290570607218087307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29815177720760809624116409 22361383290570607218087307)
          ·
            refine ⟨33542074935855910827130961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22361383290570607218087307 33542074935855910827130961)
            ·
              refine ⟨25156556201891933120348221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33542074935855910827130961 25156556201891933120348221)
              ·
                refine ⟨9433708575709474920130583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25156556201891933120348221 9433708575709474920130583)
                ·
                  refine ⟨14150562863564212380195875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9433708575709474920130583 14150562863564212380195875)
                  ·
                    refine ⟨21225844295346318570293813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14150562863564212380195875 21225844295346318570293813)
                    ·
                      refine ⟨1989922902688717365965045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21225844295346318570293813 1989922902688717365965045)
                      ·
                        rfl

theorem cell23_3875361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 3, 1, 1, 5].length) (baseStart_3875361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3875361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3875361 prefixEnd_3875361 := by exact prefixLift 3875361
  have htrace : WordTrace (prefixWord ++ tailWord_3875361) baseStart_3875361 baseEnd_3875361 := by
    simpa [prefixWord, tailWord_3875361, baseEnd_3875361] using wordTrace_append hprefix tailTrace_3875361
  have hstable : (prefixWord ++ tailWord_3875361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3875361).length < 2 ^ (prefixWord ++ tailWord_3875361).sum := by decide
  have hdescent : baseEnd_3875361 < baseStart_3875361 := by decide
  rcases family_descends (prefixWord ++ tailWord_3875361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3875385 : List Nat := [1, 2, 1, 5, 1, 1, 5, 1, 2, 4]
def baseStart_3875385 : Nat := 118140960795 + 3875385 * 2 ^ 59
def prefixEnd_3875385 : Nat := 4983230072969 + 3 ^ 40 * 3875385 * 2
def baseEnd_3875385 : Nat := 663311742074808424021645

theorem tailTrace_3875385 : CollatzResearch.WordTrace tailWord_3875385 prefixEnd_3875385 663311742074808424021645 := by
  unfold tailWord_3875385
  simp only [CollatzResearch.WordTrace]
  refine ⟨141346903065149482909499609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94231268710099655272999739 141346903065149482909499609)
  ·
    refine ⟨106010177298862112182124707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141346903065149482909499609 106010177298862112182124707)
    ·
      refine ⟨159015265948293168273187061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106010177298862112182124707 159015265948293168273187061)
      ·
        refine ⟨14907681182652484525611287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 159015265948293168273187061 14907681182652484525611287)
        ·
          refine ⟨22361521773978726788416931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14907681182652484525611287 22361521773978726788416931)
          ·
            refine ⟨33542282660968090182625397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22361521773978726788416931 33542282660968090182625397)
            ·
              refine ⟨3144588999465758454621131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33542282660968090182625397 3144588999465758454621131)
              ·
                refine ⟨4716883499198637681931697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3144588999465758454621131 4716883499198637681931697)
                ·
                  refine ⟨3537662624398978261448773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4716883499198637681931697 3537662624398978261448773)
                  ·
                    refine ⟨663311742074808424021645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3537662624398978261448773 663311742074808424021645)
                    ·
                      rfl

theorem cell23_3875385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 5, 1, 2, 4].length) (baseStart_3875385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3875385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3875385 prefixEnd_3875385 := by exact prefixLift 3875385
  have htrace : WordTrace (prefixWord ++ tailWord_3875385) baseStart_3875385 baseEnd_3875385 := by
    simpa [prefixWord, tailWord_3875385, baseEnd_3875385] using wordTrace_append hprefix tailTrace_3875385
  have hstable : (prefixWord ++ tailWord_3875385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3875385).length < 2 ^ (prefixWord ++ tailWord_3875385).sum := by decide
  have hdescent : baseEnd_3875385 < baseStart_3875385 := by decide
  rcases family_descends (prefixWord ++ tailWord_3875385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3875388 : List Nat := [2, 2, 2, 2, 3, 1, 3, 1, 1, 2, 4]
def baseStart_3875388 : Nat := 118140960795 + 3875388 * 2 ^ 59
def prefixEnd_3875388 : Nat := 4983230072969 + 3 ^ 40 * 3875388 * 2
def baseEnd_3875388 : Nat := 1989936766666388760327421

theorem tailTrace_3875388 : CollatzResearch.WordTrace tailWord_3875388 prefixEnd_3875388 1989936766666388760327421 := by
  unfold tailWord_3875388
  simp only [CollatzResearch.WordTrace]
  refine ⟨70673506242069307210929409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94231341656092409614572545 70673506242069307210929409)
  ·
    refine ⟨53005129681551980408197057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70673506242069307210929409 53005129681551980408197057)
    ·
      refine ⟨39753847261163985306147793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53005129681551980408197057 39753847261163985306147793)
      ·
        refine ⟨29815385445872988979610845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39753847261163985306147793 29815385445872988979610845)
        ·
          refine ⟨11180769542202370867354067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29815385445872988979610845 11180769542202370867354067)
          ·
            refine ⟨16771154313303556301031101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11180769542202370867354067 16771154313303556301031101)
            ·
              refine ⟨6289182867488833612886663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16771154313303556301031101 6289182867488833612886663)
              ·
                refine ⟨9433774301233250419329995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6289182867488833612886663 9433774301233250419329995)
                ·
                  refine ⟨14150661451849875628994993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9433774301233250419329995 14150661451849875628994993)
                  ·
                    refine ⟨10612996088887406721746245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14150661451849875628994993 10612996088887406721746245)
                    ·
                      refine ⟨1989936766666388760327421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10612996088887406721746245 1989936766666388760327421)
                      ·
                        rfl

theorem cell23_3875388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 3, 1, 1, 2, 4].length) (baseStart_3875388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3875388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3875388 prefixEnd_3875388 := by exact prefixLift 3875388
  have htrace : WordTrace (prefixWord ++ tailWord_3875388) baseStart_3875388 baseEnd_3875388 := by
    simpa [prefixWord, tailWord_3875388, baseEnd_3875388] using wordTrace_append hprefix tailTrace_3875388
  have hstable : (prefixWord ++ tailWord_3875388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3875388).length < 2 ^ (prefixWord ++ tailWord_3875388).sum := by decide
  have hdescent : baseEnd_3875388 < baseStart_3875388 := by decide
  rcases family_descends (prefixWord ++ tailWord_3875388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3875409 : List Nat := [1, 2, 2, 1, 3, 5, 1, 3, 1, 2, 2]
def baseStart_3875409 : Nat := 118140960795 + 3875409 * 2 ^ 59
def prefixEnd_3875409 : Nat := 4983230072969 + 3 ^ 40 * 3875409 * 2
def baseEnd_3875409 : Nat := 1989947549760133178164825

theorem tailTrace_3875409 : CollatzResearch.WordTrace tailWord_3875409 prefixEnd_3875409 1989947549760133178164825 := by
  unfold tailWord_3875409
  simp only [CollatzResearch.WordTrace]
  refine ⟨141347778417062535008373281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94231852278041690005582187 141347778417062535008373281)
  ·
    refine ⟨106010833812796901256279961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141347778417062535008373281 106010833812796901256279961)
    ·
      refine ⟨79508125359597675942209971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106010833812796901256279961 79508125359597675942209971)
      ·
        refine ⟨119262188039396513913314957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79508125359597675942209971 119262188039396513913314957)
        ·
          refine ⟨44723320514773692717493109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119262188039396513913314957 44723320514773692717493109)
          ·
            refine ⟨4192811298260033692264979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44723320514773692717493109 4192811298260033692264979)
            ·
              refine ⟨6289216947390050538397469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4192811298260033692264979 6289216947390050538397469)
              ·
                refine ⟨2358456355271268951899051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6289216947390050538397469 2358456355271268951899051)
                ·
                  refine ⟨3537684532906903427848577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2358456355271268951899051 3537684532906903427848577)
                  ·
                    refine ⟨2653263399680177570886433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3537684532906903427848577 2653263399680177570886433)
                    ·
                      refine ⟨1989947549760133178164825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2653263399680177570886433 1989947549760133178164825)
                      ·
                        rfl

theorem cell23_3875409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 1, 3, 1, 2, 2].length) (baseStart_3875409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3875409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3875409 prefixEnd_3875409 := by exact prefixLift 3875409
  have htrace : WordTrace (prefixWord ++ tailWord_3875409) baseStart_3875409 baseEnd_3875409 := by
    simpa [prefixWord, tailWord_3875409, baseEnd_3875409] using wordTrace_append hprefix tailTrace_3875409
  have hstable : (prefixWord ++ tailWord_3875409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3875409).length < 2 ^ (prefixWord ++ tailWord_3875409).sum := by decide
  have hdescent : baseEnd_3875409 < baseStart_3875409 := by decide
  rcases family_descends (prefixWord ++ tailWord_3875409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3875418 : List Nat := [3, 1, 1, 2, 1, 1, 1, 1, 7, 3, 2]
def baseStart_3875418 : Nat := 118140960795 + 3875418 * 2 ^ 59
def prefixEnd_3875418 : Nat := 4983230072969 + 3 ^ 40 * 3875418 * 2
def baseEnd_3875418 : Nat := 1989952171086023642952283

theorem tailTrace_3875418 : CollatzResearch.WordTrace tailWord_3875418 prefixEnd_3875418 1989952171086023642952283 := by
  unfold tailWord_3875418
  simp only [CollatzResearch.WordTrace]
  refine ⟨35337026668507482386362727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94232071116019953030300605 35337026668507482386362727)
  ·
    refine ⟨53005540002761223579544091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35337026668507482386362727 53005540002761223579544091)
    ·
      refine ⟨79508310004141835369316137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53005540002761223579544091 79508310004141835369316137)
      ·
        refine ⟨59631232503106376526987103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79508310004141835369316137 59631232503106376526987103)
        ·
          refine ⟨89446848754659564790480655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59631232503106376526987103 89446848754659564790480655)
          ·
            refine ⟨134170273131989347185720983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89446848754659564790480655 134170273131989347185720983)
            ·
              refine ⟨201255409697984020778581475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134170273131989347185720983 201255409697984020778581475)
              ·
                refine ⟨301883114546976031167872213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 201255409697984020778581475 301883114546976031167872213)
                ·
                  refine ⟨7075385497194750730497005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 301883114546976031167872213 7075385497194750730497005)
                  ·
                    refine ⟨2653269561448031523936377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7075385497194750730497005 2653269561448031523936377)
                    ·
                      refine ⟨1989952171086023642952283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2653269561448031523936377 1989952171086023642952283)
                      ·
                        rfl

theorem cell23_3875418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 7, 3, 2].length) (baseStart_3875418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3875418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3875418 prefixEnd_3875418 := by exact prefixLift 3875418
  have htrace : WordTrace (prefixWord ++ tailWord_3875418) baseStart_3875418 baseEnd_3875418 := by
    simpa [prefixWord, tailWord_3875418, baseEnd_3875418] using wordTrace_append hprefix tailTrace_3875418
  have hstable : (prefixWord ++ tailWord_3875418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3875418).length < 2 ^ (prefixWord ++ tailWord_3875418).sum := by decide
  have hdescent : baseEnd_3875418 < baseStart_3875418 := by decide
  rcases family_descends (prefixWord ++ tailWord_3875418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3875426 : List Nat := [3, 3, 2, 3, 1, 2, 1, 1, 3, 2, 2]
def baseStart_3875426 : Nat := 118140960795 + 3875426 * 2 ^ 59
def prefixEnd_3875426 : Nat := 4983230072969 + 3 ^ 40 * 3875426 * 2
def baseEnd_3875426 : Nat := 1989956278931259611652247

theorem tailTrace_3875426 : CollatzResearch.WordTrace tailWord_3875426 prefixEnd_3875426 1989956278931259611652247 := by
  unfold tailWord_3875426
  simp only [CollatzResearch.WordTrace]
  refine ⟨35337099614500236727935533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94232265638667297941161421 35337099614500236727935533)
  ·
    refine ⟨13251412355437588772975825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35337099614500236727935533 13251412355437588772975825)
    ·
      refine ⟨9938559266578191579731869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13251412355437588772975825 9938559266578191579731869)
      ·
        refine ⟨3726959724966821842399451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9938559266578191579731869 3726959724966821842399451)
        ·
          refine ⟨5590439587450232763599177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3726959724966821842399451 5590439587450232763599177)
          ·
            refine ⟨4192829690587674572699383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5590439587450232763599177 4192829690587674572699383)
            ·
              refine ⟨6289244535881511859049075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4192829690587674572699383 6289244535881511859049075)
              ·
                refine ⟨9433866803822267788573613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6289244535881511859049075 9433866803822267788573613)
                ·
                  refine ⟨3537700051433350420715105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9433866803822267788573613 3537700051433350420715105)
                  ·
                    refine ⟨2653275038575012815536329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3537700051433350420715105 2653275038575012815536329)
                    ·
                      refine ⟨1989956278931259611652247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2653275038575012815536329 1989956278931259611652247)
                      ·
                        rfl

theorem cell23_3875426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_3875426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3875426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3875426 prefixEnd_3875426 := by exact prefixLift 3875426
  have htrace : WordTrace (prefixWord ++ tailWord_3875426) baseStart_3875426 baseEnd_3875426 := by
    simpa [prefixWord, tailWord_3875426, baseEnd_3875426] using wordTrace_append hprefix tailTrace_3875426
  have hstable : (prefixWord ++ tailWord_3875426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3875426).length < 2 ^ (prefixWord ++ tailWord_3875426).sum := by decide
  have hdescent : baseEnd_3875426 < baseStart_3875426 := by decide
  rcases family_descends (prefixWord ++ tailWord_3875426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3875431 : List Nat := [1, 1, 5, 1, 1, 1, 1, 3, 2, 3, 4]
def baseStart_3875431 : Nat := 118140960795 + 3875431 * 2 ^ 59
def prefixEnd_3875431 : Nat := 4983230072969 + 3 ^ 40 * 3875431 * 2
def baseEnd_3875431 : Nat := 1989958846334532092089723

theorem tailTrace_3875431 : CollatzResearch.WordTrace tailWord_3875431 prefixEnd_3875431 1989958846334532092089723 := by
  unfold tailWord_3875431
  simp only [CollatzResearch.WordTrace]
  refine ⟨141348580822982832765674147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94232387215321888510449431 141348580822982832765674147)
  ·
    refine ⟨212022871234474249148511221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141348580822982832765674147 212022871234474249148511221)
    ·
      refine ⟨19877144178231960857672927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 212022871234474249148511221 19877144178231960857672927)
      ·
        refine ⟨29815716267347941286509391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19877144178231960857672927 29815716267347941286509391)
        ·
          refine ⟨44723574401021911929764087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29815716267347941286509391 44723574401021911929764087)
          ·
            refine ⟨67085361601532867894646131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44723574401021911929764087 67085361601532867894646131)
            ·
              refine ⟨100628042402299301841969197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67085361601532867894646131 100628042402299301841969197)
              ·
                refine ⟨37735515900862238190738449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100628042402299301841969197 37735515900862238190738449)
                ·
                  refine ⟨28301636925646678643053837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37735515900862238190738449 28301636925646678643053837)
                  ·
                    refine ⟨10613113847117504491145189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28301636925646678643053837 10613113847117504491145189)
                    ·
                      refine ⟨1989958846334532092089723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10613113847117504491145189 1989958846334532092089723)
                      ·
                        rfl

theorem cell23_3875431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 3, 2, 3, 4].length) (baseStart_3875431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3875431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3875431 prefixEnd_3875431 := by exact prefixLift 3875431
  have htrace : WordTrace (prefixWord ++ tailWord_3875431) baseStart_3875431 baseEnd_3875431 := by
    simpa [prefixWord, tailWord_3875431, baseEnd_3875431] using wordTrace_append hprefix tailTrace_3875431
  have hstable : (prefixWord ++ tailWord_3875431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3875431).length < 2 ^ (prefixWord ++ tailWord_3875431).sum := by decide
  have hdescent : baseEnd_3875431 < baseStart_3875431 := by decide
  rcases family_descends (prefixWord ++ tailWord_3875431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3875442 : List Nat := [3, 2, 1, 2, 4, 1, 1, 3, 2, 1, 3]
def baseStart_3875442 : Nat := 118140960795 + 3875442 * 2 ^ 59
def prefixEnd_3875442 : Nat := 4983230072969 + 3 ^ 40 * 3875442 * 2
def baseEnd_3875442 : Nat := 1989964494621731549052173

theorem tailTrace_3875442 : CollatzResearch.WordTrace tailWord_3875442 prefixEnd_3875442 1989964494621731549052173 := by
  unfold tailWord_3875442
  simp only [CollatzResearch.WordTrace]
  refine ⟨35337245506485745411081145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94232654683961987762883053 35337245506485745411081145)
  ·
    refine ⟨26502934129864309058310859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35337245506485745411081145 26502934129864309058310859)
    ·
      refine ⟨39754401194796463587466289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26502934129864309058310859 39754401194796463587466289)
      ·
        refine ⟨29815800896097347690599717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39754401194796463587466289 29815800896097347690599717)
        ·
          refine ⟨5590462668018252691987447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29815800896097347690599717 5590462668018252691987447)
          ·
            refine ⟨8385694002027379037981171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5590462668018252691987447 8385694002027379037981171)
            ·
              refine ⟨12578541003041068556971757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8385694002027379037981171 12578541003041068556971757)
              ·
                refine ⟨4716952876140400708864409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12578541003041068556971757 4716952876140400708864409)
                ·
                  refine ⟨3537714657105300531648307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4716952876140400708864409 3537714657105300531648307)
                  ·
                    refine ⟨5306571985657950797472461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3537714657105300531648307 5306571985657950797472461)
                    ·
                      refine ⟨1989964494621731549052173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5306571985657950797472461 1989964494621731549052173)
                      ·
                        rfl

theorem cell23_3875442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 3, 2, 1, 3].length) (baseStart_3875442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3875442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3875442 prefixEnd_3875442 := by exact prefixLift 3875442
  have htrace : WordTrace (prefixWord ++ tailWord_3875442) baseStart_3875442 baseEnd_3875442 := by
    simpa [prefixWord, tailWord_3875442, baseEnd_3875442] using wordTrace_append hprefix tailTrace_3875442
  have hstable : (prefixWord ++ tailWord_3875442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3875442).length < 2 ^ (prefixWord ++ tailWord_3875442).sum := by decide
  have hdescent : baseEnd_3875442 < baseStart_3875442 := by decide
  rcases family_descends (prefixWord ++ tailWord_3875442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3875451 : List Nat := [1, 1, 1, 1, 1, 4, 2, 1, 4, 4, 3]
def baseStart_3875451 : Nat := 118140960795 + 3875451 * 2 ^ 59
def prefixEnd_3875451 : Nat := 4983230072969 + 3 ^ 40 * 3875451 * 2
def baseEnd_3875451 : Nat := 1989969115947622013839631

theorem tailTrace_3875451 : CollatzResearch.WordTrace tailWord_3875451 prefixEnd_3875451 1989969115947622013839631 := by
  unfold tailWord_3875451
  simp only [CollatzResearch.WordTrace]
  refine ⟨141349310282910376181402207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94232873521940250787601471 141349310282910376181402207)
  ·
    refine ⟨212023965424365564272103311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141349310282910376181402207 212023965424365564272103311)
    ·
      refine ⟨318035948136548346408154967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212023965424365564272103311 318035948136548346408154967)
      ·
        refine ⟨477053922204822519612232451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318035948136548346408154967 477053922204822519612232451)
        ·
          refine ⟨715580883307233779418348677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 477053922204822519612232451 715580883307233779418348677)
          ·
            refine ⟨134171415620106333640940377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 715580883307233779418348677 134171415620106333640940377)
            ·
              refine ⟨100628561715079750230705283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134171415620106333640940377 100628561715079750230705283)
              ·
                refine ⟨150942842572619625346057925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100628561715079750230705283 150942842572619625346057925)
                ·
                  refine ⟨28301782982366179752385861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 150942842572619625346057925 28301782982366179752385861)
                  ·
                    refine ⟨5306584309193658703572349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28301782982366179752385861 5306584309193658703572349)
                    ·
                      refine ⟨1989969115947622013839631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5306584309193658703572349 1989969115947622013839631)
                      ·
                        rfl

theorem cell23_3875451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 4, 4, 3].length) (baseStart_3875451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3875451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3875451 prefixEnd_3875451 := by exact prefixLift 3875451
  have htrace : WordTrace (prefixWord ++ tailWord_3875451) baseStart_3875451 baseEnd_3875451 := by
    simpa [prefixWord, tailWord_3875451, baseEnd_3875451] using wordTrace_append hprefix tailTrace_3875451
  have hstable : (prefixWord ++ tailWord_3875451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3875451).length < 2 ^ (prefixWord ++ tailWord_3875451).sum := by decide
  have hdescent : baseEnd_3875451 < baseStart_3875451 := by decide
  rcases family_descends (prefixWord ++ tailWord_3875451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3875505 : List Nat := [1, 2, 2, 6, 1, 1, 1, 2, 7]
def baseStart_3875505 : Nat := 118140960795 + 3875505 * 2 ^ 59
def prefixEnd_3875505 : Nat := 4983230072969 + 3 ^ 40 * 3875505 * 2
def baseEnd_3875505 : Nat := 221110760433662755840487

theorem tailTrace_3875505 : CollatzResearch.WordTrace tailWord_3875505 prefixEnd_3875505 221110760433662755840487 := by
  unfold tailWord_3875505
  simp only [CollatzResearch.WordTrace]
  refine ⟨141351279824714743403867969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94234186549809828935911979 141351279824714743403867969)
  ·
    refine ⟨106013459868536057552900977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141351279824714743403867969 106013459868536057552900977)
    ·
      refine ⟨79510094901402043164675733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106013459868536057552900977 79510094901402043164675733)
      ·
        refine ⟨3727035698503220773344175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 79510094901402043164675733 3727035698503220773344175)
        ·
          refine ⟨5590553547754831160016263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3727035698503220773344175 5590553547754831160016263)
          ·
            refine ⟨8385830321632246740024395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5590553547754831160016263 8385830321632246740024395)
            ·
              refine ⟨12578745482448370110036593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8385830321632246740024395 12578745482448370110036593)
              ·
                refine ⟨9434059111836277582527445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12578745482448370110036593 9434059111836277582527445)
                ·
                  refine ⟨221110760433662755840487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9434059111836277582527445 221110760433662755840487)
                  ·
                    rfl

theorem cell23_3875505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 2, 7].length) (baseStart_3875505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3875505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3875505 prefixEnd_3875505 := by exact prefixLift 3875505
  have htrace : WordTrace (prefixWord ++ tailWord_3875505) baseStart_3875505 baseEnd_3875505 := by
    simpa [prefixWord, tailWord_3875505, baseEnd_3875505] using wordTrace_append hprefix tailTrace_3875505
  have hstable : (prefixWord ++ tailWord_3875505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3875505).length < 2 ^ (prefixWord ++ tailWord_3875505).sum := by decide
  have hdescent : baseEnd_3875505 < baseStart_3875505 := by decide
  rcases family_descends (prefixWord ++ tailWord_3875505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3875518 : List Nat := [4, 2, 1, 1, 2, 1, 3, 1, 1, 7]
def baseStart_3875518 : Nat := 118140960795 + 3875518 * 2 ^ 59
def prefixEnd_3875518 : Nat := 4983230072969 + 3 ^ 40 * 3875518 * 2
def baseEnd_3875518 : Nat := 663334506383824417233941

theorem tailTrace_3875518 : CollatzResearch.WordTrace tailWord_3875518 prefixEnd_3875518 663334506383824417233941 := by
  unfold tailWord_3875518
  simp only [CollatzResearch.WordTrace]
  refine ⟨17668969246708455828011401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94234502649111764416060805 17668969246708455828011401)
  ·
    refine ⟨13251726935031341871008551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17668969246708455828011401 13251726935031341871008551)
    ·
      refine ⟨19877590402547012806512827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13251726935031341871008551 19877590402547012806512827)
      ·
        refine ⟨29816385603820519209769241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19877590402547012806512827 29816385603820519209769241)
        ·
          refine ⟨22362289202865389407326931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29816385603820519209769241 22362289202865389407326931)
          ·
            refine ⟨33543433804298084110990397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22362289202865389407326931 33543433804298084110990397)
            ·
              refine ⟨12578787676611781541621399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33543433804298084110990397 12578787676611781541621399)
              ·
                refine ⟨18868181514917672312432099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12578787676611781541621399 18868181514917672312432099)
                ·
                  refine ⟨28302272272376508468648149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18868181514917672312432099 28302272272376508468648149)
                  ·
                    refine ⟨663334506383824417233941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28302272272376508468648149 663334506383824417233941)
                    ·
                      rfl

theorem cell23_3875518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 1, 1, 7].length) (baseStart_3875518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3875518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3875518 prefixEnd_3875518 := by exact prefixLift 3875518
  have htrace : WordTrace (prefixWord ++ tailWord_3875518) baseStart_3875518 baseEnd_3875518 := by
    simpa [prefixWord, tailWord_3875518, baseEnd_3875518] using wordTrace_append hprefix tailTrace_3875518
  have hstable : (prefixWord ++ tailWord_3875518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3875518).length < 2 ^ (prefixWord ++ tailWord_3875518).sum := by decide
  have hdescent : baseEnd_3875518 < baseStart_3875518 := by decide
  rcases family_descends (prefixWord ++ tailWord_3875518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3875533 : List Nat := [1, 6, 2, 1, 2, 2, 1, 2, 2, 2, 2]
def baseStart_3875533 : Nat := 118140960795 + 3875533 * 2 ^ 59
def prefixEnd_3875533 : Nat := 4983230072969 + 3 ^ 40 * 3875533 * 2
def baseEnd_3875533 : Nat := 1990011221361290693014255

theorem tailTrace_3875533 : CollatzResearch.WordTrace tailWord_3875533 prefixEnd_3875533 1990011221361290693014255 := by
  unfold tailWord_3875533
  simp only [CollatzResearch.WordTrace]
  refine ⟨141352301068613304185887253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94234867379075536123924835 141352301068613304185887253)
  ·
    refine ⟨6625889112591248633713465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 141352301068613304185887253 6625889112591248633713465)
    ·
      refine ⟨4969416834443436475285099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6625889112591248633713465 4969416834443436475285099)
      ·
        refine ⟨7454125251665154712927649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4969416834443436475285099 7454125251665154712927649)
        ·
          refine ⟨5590593938748866034695737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7454125251665154712927649 5590593938748866034695737)
          ·
            refine ⟨4192945454061649526021803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5590593938748866034695737 4192945454061649526021803)
            ·
              refine ⟨6289418181092474289032705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4192945454061649526021803 6289418181092474289032705)
              ·
                refine ⟨4717063635819355716774529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6289418181092474289032705 4717063635819355716774529)
                ·
                  refine ⟨3537797726864516787580897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4717063635819355716774529 3537797726864516787580897)
                  ·
                    refine ⟨2653348295148387590685673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3537797726864516787580897 2653348295148387590685673)
                    ·
                      refine ⟨1990011221361290693014255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2653348295148387590685673 1990011221361290693014255)
                      ·
                        rfl

theorem cell23_3875533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 1, 2, 2, 2, 2].length) (baseStart_3875533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3875533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3875533 prefixEnd_3875533 := by exact prefixLift 3875533
  have htrace : WordTrace (prefixWord ++ tailWord_3875533) baseStart_3875533 baseEnd_3875533 := by
    simpa [prefixWord, tailWord_3875533, baseEnd_3875533] using wordTrace_append hprefix tailTrace_3875533
  have hstable : (prefixWord ++ tailWord_3875533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3875533).length < 2 ^ (prefixWord ++ tailWord_3875533).sum := by decide
  have hdescent : baseEnd_3875533 < baseStart_3875533 := by decide
  rcases family_descends (prefixWord ++ tailWord_3875533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3875565 : List Nat := [1, 5, 1, 2, 1, 1, 1, 4, 3, 4]
def baseStart_3875565 : Nat := 118140960795 + 3875565 * 2 ^ 59
def prefixEnd_3875565 : Nat := 4983230072969 + 3 ^ 40 * 3875565 * 2
def baseEnd_3875565 : Nat := 663342550914078189271369

theorem tailTrace_3875565 : CollatzResearch.WordTrace tailWord_3875565 prefixEnd_3875565 663342550914078189271369 := by
  unfold tailWord_3875565
  simp only [CollatzResearch.WordTrace]
  refine ⟨141353468204497373651052149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94235645469664915767368099 141353468204497373651052149)
  ·
    refine ⟨13251887644171628779786139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 141353468204497373651052149 13251887644171628779786139)
    ·
      refine ⟨19877831466257443169679209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13251887644171628779786139 19877831466257443169679209)
      ·
        refine ⟨14908373599693082377259407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19877831466257443169679209 14908373599693082377259407)
        ·
          refine ⟨22362560399539623565889111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14908373599693082377259407 22362560399539623565889111)
          ·
            refine ⟨33543840599309435348833667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22362560399539623565889111 33543840599309435348833667)
            ·
              refine ⟨50315760898964153023250501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33543840599309435348833667 50315760898964153023250501)
              ·
                refine ⟨9434205168555778691859469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50315760898964153023250501 9434205168555778691859469)
                ·
                  refine ⟨3537826938208417009447301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9434205168555778691859469 3537826938208417009447301)
                  ·
                    refine ⟨663342550914078189271369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3537826938208417009447301 663342550914078189271369)
                    ·
                      rfl

theorem cell23_3875565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 4, 3, 4].length) (baseStart_3875565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3875565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3875565 prefixEnd_3875565 := by exact prefixLift 3875565
  have htrace : WordTrace (prefixWord ++ tailWord_3875565) baseStart_3875565 baseEnd_3875565 := by
    simpa [prefixWord, tailWord_3875565, baseEnd_3875565] using wordTrace_append hprefix tailTrace_3875565
  have hstable : (prefixWord ++ tailWord_3875565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3875565).length < 2 ^ (prefixWord ++ tailWord_3875565).sum := by decide
  have hdescent : baseEnd_3875565 < baseStart_3875565 := by decide
  rcases family_descends (prefixWord ++ tailWord_3875565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3875573 : List Nat := [1, 3, 6, 1, 2, 1, 1, 3, 5]
def baseStart_3875573 : Nat := 118140960795 + 3875573 * 2 ^ 59
def prefixEnd_3875573 : Nat := 4983230072969 + 3 ^ 40 * 3875573 * 2
def baseEnd_3875573 : Nat := 221114640065274504057119

theorem tailTrace_3875573 : CollatzResearch.WordTrace tailWord_3875573 prefixEnd_3875573 221114640065274504057119 := by
  unfold tailWord_3875573
  simp only [CollatzResearch.WordTrace]
  refine ⟨141353759988468391017343373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94235839992312260678228915 141353759988468391017343373)
  ·
    refine ⟨53007659995675646631503765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141353759988468391017343373 53007659995675646631503765)
    ·
      refine ⟨2484734062297295935851739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 53007659995675646631503765 2484734062297295935851739)
      ·
        refine ⟨3727101093445943903777609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2484734062297295935851739 3727101093445943903777609)
        ·
          refine ⟨2795325820084457927833207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3727101093445943903777609 2795325820084457927833207)
          ·
            refine ⟨4192988730126686891749811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2795325820084457927833207 4192988730126686891749811)
            ·
              refine ⟨6289483095190030337624717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4192988730126686891749811 6289483095190030337624717)
              ·
                refine ⟨2358556160696261376609269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6289483095190030337624717 2358556160696261376609269)
                ·
                  refine ⟨221114640065274504057119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2358556160696261376609269 221114640065274504057119)
                  ·
                    rfl

theorem cell23_3875573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 1, 3, 5].length) (baseStart_3875573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3875573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3875573 prefixEnd_3875573 := by exact prefixLift 3875573
  have htrace : WordTrace (prefixWord ++ tailWord_3875573) baseStart_3875573 baseEnd_3875573 := by
    simpa [prefixWord, tailWord_3875573, baseEnd_3875573] using wordTrace_append hprefix tailTrace_3875573
  have hstable : (prefixWord ++ tailWord_3875573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3875573).length < 2 ^ (prefixWord ++ tailWord_3875573).sum := by decide
  have hdescent : baseEnd_3875573 < baseStart_3875573 := by decide
  rcases family_descends (prefixWord ++ tailWord_3875573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3875608 : List Nat := [2, 1, 2, 3, 1, 1, 1, 4, 3, 5]
def baseStart_3875608 : Nat := 118140960795 + 3875608 * 2 ^ 59
def prefixEnd_3875608 : Nat := 4983230072969 + 3 ^ 40 * 3875608 * 2
def baseEnd_3875608 : Nat := 663349910803459299858803

theorem tailTrace_3875608 : CollatzResearch.WordTrace tailWord_3875608 prefixEnd_3875608 663349910803459299858803 := by
  unfold tailWord_3875608
  simp only [CollatzResearch.WordTrace]
  refine ⟨70677518271670795997433739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94236691028894394663244985 70677518271670795997433739)
  ·
    refine ⟨106016277407506193996150609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70677518271670795997433739 106016277407506193996150609)
    ·
      refine ⟨79512208055629645497112957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106016277407506193996150609 79512208055629645497112957)
      ·
        refine ⟨29817078020861117061417359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79512208055629645497112957 29817078020861117061417359)
        ·
          refine ⟨44725617031291675592126039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29817078020861117061417359 44725617031291675592126039)
          ·
            refine ⟨67088425546937513388189059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44725617031291675592126039 67088425546937513388189059)
            ·
              refine ⟨100632638320406270082283589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67088425546937513388189059 100632638320406270082283589)
              ·
                refine ⟨18868619685076175640428173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100632638320406270082283589 18868619685076175640428173)
                ·
                  refine ⟨7075732381903565865160565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18868619685076175640428173 7075732381903565865160565)
                  ·
                    refine ⟨663349910803459299858803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7075732381903565865160565 663349910803459299858803)
                    ·
                      rfl

theorem cell23_3875608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 4, 3, 5].length) (baseStart_3875608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3875608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3875608 prefixEnd_3875608 := by exact prefixLift 3875608
  have htrace : WordTrace (prefixWord ++ tailWord_3875608) baseStart_3875608 baseEnd_3875608 := by
    simpa [prefixWord, tailWord_3875608, baseEnd_3875608] using wordTrace_append hprefix tailTrace_3875608
  have hstable : (prefixWord ++ tailWord_3875608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3875608).length < 2 ^ (prefixWord ++ tailWord_3875608).sum := by decide
  have hdescent : baseEnd_3875608 < baseStart_3875608 := by decide
  rcases family_descends (prefixWord ++ tailWord_3875608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3875612 : List Nat := [2, 2, 3, 1, 1, 5, 2, 1, 6]
def baseStart_3875612 : Nat := 118140960795 + 3875612 * 2 ^ 59
def prefixEnd_3875612 : Nat := 4983230072969 + 3 ^ 40 * 3875612 * 2
def baseEnd_3875612 : Nat := 221116865148110653769599

theorem tailTrace_3875612 : CollatzResearch.WordTrace tailWord_3875612 prefixEnd_3875612 221116865148110653769599 := by
  unfold tailWord_3875612
  simp only [CollatzResearch.WordTrace]
  refine ⟨70677591217663550339006545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94236788290218067118675393 70677591217663550339006545)
  ·
    refine ⟨53008193413247662754254909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70677591217663550339006545 53008193413247662754254909)
    ·
      refine ⟨19878072529967873532845591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53008193413247662754254909 19878072529967873532845591)
      ·
        refine ⟨29817108794951810299268387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19878072529967873532845591 29817108794951810299268387)
        ·
          refine ⟨44725663192427715448902581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29817108794951810299268387 44725663192427715448902581)
          ·
            refine ⟨4193030924290098323334617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44725663192427715448902581 4193030924290098323334617)
            ·
              refine ⟨3144773193217573742500963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4193030924290098323334617 3144773193217573742500963)
              ·
                refine ⟨4717159789826360613751445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3144773193217573742500963 4717159789826360613751445)
                ·
                  refine ⟨221116865148110653769599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4717159789826360613751445 221116865148110653769599)
                  ·
                    rfl

theorem cell23_3875612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 2, 1, 6].length) (baseStart_3875612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3875612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3875612 prefixEnd_3875612 := by exact prefixLift 3875612
  have htrace : WordTrace (prefixWord ++ tailWord_3875612) baseStart_3875612 baseEnd_3875612 := by
    simpa [prefixWord, tailWord_3875612, baseEnd_3875612] using wordTrace_append hprefix tailTrace_3875612
  have hstable : (prefixWord ++ tailWord_3875612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3875612).length < 2 ^ (prefixWord ++ tailWord_3875612).sum := by decide
  have hdescent : baseEnd_3875612 < baseStart_3875612 := by decide
  rcases family_descends (prefixWord ++ tailWord_3875612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3875658 : List Nat := [3, 1, 2, 1, 1, 1, 2, 4, 1, 1, 6]
def baseStart_3875658 : Nat := 118140960795 + 3875658 * 2 ^ 59
def prefixEnd_3875658 : Nat := 4983230072969 + 3 ^ 40 * 3875658 * 2
def baseEnd_3875658 : Nat := 1990075406443102703951179

theorem tailTrace_3875658 : CollatzResearch.WordTrace tailWord_3875658 prefixEnd_3875658 1990075406443102703951179 := by
  unfold tailWord_3875658
  simp only [CollatzResearch.WordTrace]
  refine ⟨35339215048290112633546907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94237906795440300356125085 35339215048290112633546907)
  ·
    refine ⟨53008822572435168950320361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35339215048290112633546907 53008822572435168950320361)
    ·
      refine ⟨39756616929326376712740271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53008822572435168950320361 39756616929326376712740271)
      ·
        refine ⟨59634925393989565069110407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39756616929326376712740271 59634925393989565069110407)
        ·
          refine ⟨89452388090984347603665611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59634925393989565069110407 89452388090984347603665611)
          ·
            refine ⟨134178582136476521405498417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89452388090984347603665611 134178582136476521405498417)
            ·
              refine ⟨100633936602357391054123813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134178582136476521405498417 100633936602357391054123813)
              ·
                refine ⟨18868863112942010822648215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100633936602357391054123813 18868863112942010822648215)
                ·
                  refine ⟨28303294669413016233972323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18868863112942010822648215 28303294669413016233972323)
                  ·
                    refine ⟨42454942004119524350958485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28303294669413016233972323 42454942004119524350958485)
                    ·
                      refine ⟨1990075406443102703951179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42454942004119524350958485 1990075406443102703951179)
                      ·
                        rfl

theorem cell23_3875658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 4, 1, 1, 6].length) (baseStart_3875658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3875658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3875658 prefixEnd_3875658 := by exact prefixLift 3875658
  have htrace : WordTrace (prefixWord ++ tailWord_3875658) baseStart_3875658 baseEnd_3875658 := by
    simpa [prefixWord, tailWord_3875658, baseEnd_3875658] using wordTrace_append hprefix tailTrace_3875658
  have hstable : (prefixWord ++ tailWord_3875658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3875658).length < 2 ^ (prefixWord ++ tailWord_3875658).sum := by decide
  have hdescent : baseEnd_3875658 < baseStart_3875658 := by decide
  rcases family_descends (prefixWord ++ tailWord_3875658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3875662 : List Nat := [4, 1, 1, 1, 1, 1, 1, 2, 7, 2, 2]
def baseStart_3875662 : Nat := 118140960795 + 3875662 * 2 ^ 59
def prefixEnd_3875662 : Nat := 4983230072969 + 3 ^ 40 * 3875662 * 2
def baseEnd_3875662 : Nat := 1990077460365720688301161

theorem tailTrace_3875662 : CollatzResearch.WordTrace tailWord_3875662 prefixEnd_3875662 1990077460365720688301161 := by
  unfold tailWord_3875662
  simp only [CollatzResearch.WordTrace]
  refine ⟨17669625760643244902166655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94238004056763972811555493 17669625760643244902166655)
  ·
    refine ⟨26504438640964867353249983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17669625760643244902166655 26504438640964867353249983)
    ·
      refine ⟨39756657961447301029874975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26504438640964867353249983 39756657961447301029874975)
      ·
        refine ⟨59634986942170951544812463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39756657961447301029874975 59634986942170951544812463)
        ·
          refine ⟨89452480413256427317218695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59634986942170951544812463 89452480413256427317218695)
          ·
            refine ⟨134178720619884640975828043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89452480413256427317218695 134178720619884640975828043)
            ·
              refine ⟨201268080929826961463742065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134178720619884640975828043 201268080929826961463742065)
              ·
                refine ⟨150951060697370221097806549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 201268080929826961463742065 150951060697370221097806549)
                ·
                  refine ⟨3537915485094614556979841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 150951060697370221097806549 3537915485094614556979841)
                  ·
                    refine ⟨2653436613820960917734881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3537915485094614556979841 2653436613820960917734881)
                    ·
                      refine ⟨1990077460365720688301161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2653436613820960917734881 1990077460365720688301161)
                      ·
                        rfl

theorem cell23_3875662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 7, 2, 2].length) (baseStart_3875662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3875662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3875662 prefixEnd_3875662 := by exact prefixLift 3875662
  have htrace : WordTrace (prefixWord ++ tailWord_3875662) baseStart_3875662 baseEnd_3875662 := by
    simpa [prefixWord, tailWord_3875662, baseEnd_3875662] using wordTrace_append hprefix tailTrace_3875662
  have hstable : (prefixWord ++ tailWord_3875662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3875662).length < 2 ^ (prefixWord ++ tailWord_3875662).sum := by decide
  have hdescent : baseEnd_3875662 < baseStart_3875662 := by decide
  rcases family_descends (prefixWord ++ tailWord_3875662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3875712 : List Nat := [2, 1, 1, 2, 1, 2, 2, 6, 2, 1, 3]
def baseStart_3875712 : Nat := 118140960795 + 3875712 * 2 ^ 59
def prefixEnd_3875712 : Nat := 4983230072969 + 3 ^ 40 * 3875712 * 2
def baseEnd_3875712 : Nat := 1990103134398445492675931

theorem tailTrace_3875712 : CollatzResearch.WordTrace tailWord_3875712 prefixEnd_3875712 1990103134398445492675931 := by
  unfold tailWord_3875712
  simp only [CollatzResearch.WordTrace]
  refine ⟨70679414867482408878326695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94239219823309878504435593 70679414867482408878326695)
  ·
    refine ⟨106019122301223613317490043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70679414867482408878326695 106019122301223613317490043)
    ·
      refine ⟨159028683451835419976235065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106019122301223613317490043 159028683451835419976235065)
      ·
        refine ⟨119271512588876564982176299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159028683451835419976235065 119271512588876564982176299)
        ·
          refine ⟨178907268883314847473264449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119271512588876564982176299 178907268883314847473264449)
          ·
            refine ⟨134180451662486135604948337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178907268883314847473264449 134180451662486135604948337)
            ·
              refine ⟨100635338746864601703711253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134180451662486135604948337 100635338746864601703711253)
              ·
                refine ⟨4717281503759278204861465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 100635338746864601703711253 4717281503759278204861465)
                ·
                  refine ⟨3537961127819458653646099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4717281503759278204861465 3537961127819458653646099)
                  ·
                    refine ⟨5306941691729187980469149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3537961127819458653646099 5306941691729187980469149)
                    ·
                      refine ⟨1990103134398445492675931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5306941691729187980469149 1990103134398445492675931)
                      ·
                        rfl

theorem cell23_3875712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 6, 2, 1, 3].length) (baseStart_3875712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3875712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3875712 prefixEnd_3875712 := by exact prefixLift 3875712
  have htrace : WordTrace (prefixWord ++ tailWord_3875712) baseStart_3875712 baseEnd_3875712 := by
    simpa [prefixWord, tailWord_3875712, baseEnd_3875712] using wordTrace_append hprefix tailTrace_3875712
  have hstable : (prefixWord ++ tailWord_3875712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3875712).length < 2 ^ (prefixWord ++ tailWord_3875712).sum := by decide
  have hdescent : baseEnd_3875712 < baseStart_3875712 := by decide
  rcases family_descends (prefixWord ++ tailWord_3875712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3875728 : List Nat := [2, 1, 1, 1, 1, 1, 2, 2, 6, 6]
def baseStart_3875728 : Nat := 118140960795 + 3875728 * 2 ^ 59
def prefixEnd_3875728 : Nat := 4983230072969 + 3 ^ 40 * 3875728 * 2
def baseEnd_3875728 : Nat := 663370450029639143358619

theorem tailTrace_3875728 : CollatzResearch.WordTrace tailWord_3875728 prefixEnd_3875728 663370450029639143358619 := by
  unfold tailWord_3875728
  simp only [CollatzResearch.WordTrace]
  refine ⟨70679706651453426244617919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94239608868604568326157225 70679706651453426244617919)
  ·
    refine ⟨106019559977180139366926879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70679706651453426244617919 106019559977180139366926879)
    ·
      refine ⟨159029339965770209050390319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106019559977180139366926879 159029339965770209050390319)
      ·
        refine ⟨238544009948655313575585479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159029339965770209050390319 238544009948655313575585479)
        ·
          refine ⟨357816014922982970363378219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238544009948655313575585479 357816014922982970363378219)
          ·
            refine ⟨536724022384474455545067329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 357816014922982970363378219 536724022384474455545067329)
            ·
              refine ⟨402543016788355841658800497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 536724022384474455545067329 402543016788355841658800497)
              ·
                refine ⟨301907262591266881244100373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 402543016788355841658800497 301907262591266881244100373)
                ·
                  refine ⟨14151902933965635058317205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 301907262591266881244100373 14151902933965635058317205)
                  ·
                    refine ⟨663370450029639143358619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14151902933965635058317205 663370450029639143358619)
                    ·
                      rfl

theorem cell23_3875728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 6, 6].length) (baseStart_3875728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3875728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3875728 prefixEnd_3875728 := by exact prefixLift 3875728
  have htrace : WordTrace (prefixWord ++ tailWord_3875728) baseStart_3875728 baseEnd_3875728 := by
    simpa [prefixWord, tailWord_3875728, baseEnd_3875728] using wordTrace_append hprefix tailTrace_3875728
  have hstable : (prefixWord ++ tailWord_3875728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3875728).length < 2 ^ (prefixWord ++ tailWord_3875728).sum := by decide
  have hdescent : baseEnd_3875728 < baseStart_3875728 := by decide
  rcases family_descends (prefixWord ++ tailWord_3875728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3875769 : List Nat := [1, 2, 1, 4, 2, 2, 2, 1, 4, 2, 2]
def baseStart_3875769 : Nat := 118140960795 + 3875769 * 2 ^ 59
def prefixEnd_3875769 : Nat := 4983230072969 + 3 ^ 40 * 3875769 * 2
def baseEnd_3875769 : Nat := 1990132402795751769663169

theorem tailTrace_3875769 : CollatzResearch.WordTrace tailWord_3875769 prefixEnd_3875769 1990132402795751769663169 := by
  unfold tailWord_3875769
  simp only [CollatzResearch.WordTrace]
  refine ⟨141360908695758316491478361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94240605797172210994318907 141360908695758316491478361)
  ·
    refine ⟨106020681521818737368608771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141360908695758316491478361 106020681521818737368608771)
    ·
      refine ⟨159031022282728106052913157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106020681521818737368608771 159031022282728106052913157)
      ·
        refine ⟨29818316678011519884921217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 159031022282728106052913157 29818316678011519884921217)
        ·
          refine ⟨22363737508508639913690913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29818316678011519884921217 22363737508508639913690913)
          ·
            refine ⟨16772803131381479935268185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22363737508508639913690913 16772803131381479935268185)
            ·
              refine ⟨12579602348536109951451139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16772803131381479935268185 12579602348536109951451139)
              ·
                refine ⟨18869403522804164927176709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12579602348536109951451139 18869403522804164927176709)
                ·
                  refine ⟨3538013160525780923845633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18869403522804164927176709 3538013160525780923845633)
                  ·
                    refine ⟨2653509870394335692884225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3538013160525780923845633 2653509870394335692884225)
                    ·
                      refine ⟨1990132402795751769663169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2653509870394335692884225 1990132402795751769663169)
                      ·
                        rfl

theorem cell23_3875769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 1, 4, 2, 2].length) (baseStart_3875769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3875769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3875769 prefixEnd_3875769 := by exact prefixLift 3875769
  have htrace : WordTrace (prefixWord ++ tailWord_3875769) baseStart_3875769 baseEnd_3875769 := by
    simpa [prefixWord, tailWord_3875769, baseEnd_3875769] using wordTrace_append hprefix tailTrace_3875769
  have hstable : (prefixWord ++ tailWord_3875769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3875769).length < 2 ^ (prefixWord ++ tailWord_3875769).sum := by decide
  have hdescent : baseEnd_3875769 < baseStart_3875769 := by decide
  rcases family_descends (prefixWord ++ tailWord_3875769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3875780 : List Nat := [2, 3, 3, 3, 1, 2, 2, 1, 2, 1, 3]
def baseStart_3875780 : Nat := 118140960795 + 3875780 * 2 ^ 59
def prefixEnd_3875780 : Nat := 4983230072969 + 3 ^ 40 * 3875780 * 2
def baseEnd_3875780 : Nat := 1990138051082951226625619

theorem tailTrace_3875780 : CollatzResearch.WordTrace tailWord_3875780 prefixEnd_3875780 1990138051082951226625619 := by
  unfold tailWord_3875780
  simp only [CollatzResearch.WordTrace]
  refine ⟨70680654949359232685064397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94240873265812310246752529 70680654949359232685064397)
  ·
    refine ⟨26505245606009712256899149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70680654949359232685064397 26505245606009712256899149)
    ·
      refine ⟨9939467102253642096337181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26505245606009712256899149 9939467102253642096337181)
      ·
        refine ⟨3727300163345115786126443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9939467102253642096337181 3727300163345115786126443)
        ·
          refine ⟨5590950245017673679189665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3727300163345115786126443 5590950245017673679189665)
          ·
            refine ⟨4193212683763255259392249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5590950245017673679189665 4193212683763255259392249)
            ·
              refine ⟨3144909512822441444544187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4193212683763255259392249 3144909512822441444544187)
              ·
                refine ⟨4717364269233662166816281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3144909512822441444544187 4717364269233662166816281)
                ·
                  refine ⟨3538023201925246625112211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4717364269233662166816281 3538023201925246625112211)
                  ·
                    refine ⟨5307034802887869937668317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3538023201925246625112211 5307034802887869937668317)
                    ·
                      refine ⟨1990138051082951226625619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5307034802887869937668317 1990138051082951226625619)
                      ·
                        rfl

theorem cell23_3875780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_3875780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3875780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3875780 prefixEnd_3875780 := by exact prefixLift 3875780
  have htrace : WordTrace (prefixWord ++ tailWord_3875780) baseStart_3875780 baseEnd_3875780 := by
    simpa [prefixWord, tailWord_3875780, baseEnd_3875780] using wordTrace_append hprefix tailTrace_3875780
  have hstable : (prefixWord ++ tailWord_3875780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3875780).length < 2 ^ (prefixWord ++ tailWord_3875780).sum := by decide
  have hdescent : baseEnd_3875780 < baseStart_3875780 := by decide
  rcases family_descends (prefixWord ++ tailWord_3875780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3875826 : List Nat := [3, 2, 1, 5, 1, 1, 1, 4, 5]
def baseStart_3875826 : Nat := 118140960795 + 3875826 * 2 ^ 59
def prefixEnd_3875826 : Nat := 4983230072969 + 3 ^ 40 * 3875826 * 2
def baseEnd_3875826 : Nat := 221129074577006449627823

theorem tailTrace_3875826 : CollatzResearch.WordTrace tailWord_3875826 prefixEnd_3875826 221129074577006449627823 := by
  unfold tailWord_3875826
  simp only [CollatzResearch.WordTrace]
  refine ⟨35340746914137953806575833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94241991771034543484202221 35340746914137953806575833)
  ·
    refine ⟨26505560185603465354931875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35340746914137953806575833 26505560185603465354931875)
    ·
      refine ⟨39758340278405198032397813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26505560185603465354931875 39758340278405198032397813)
      ·
        refine ⟨3727344401100487315537295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 39758340278405198032397813 3727344401100487315537295)
        ·
          refine ⟨5591016601650730973305943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3727344401100487315537295 5591016601650730973305943)
          ·
            refine ⟨8386524902476096459958915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5591016601650730973305943 8386524902476096459958915)
            ·
              refine ⟨12579787353714144689938373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8386524902476096459958915 12579787353714144689938373)
              ·
                refine ⟨2358710128821402129363445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12579787353714144689938373 2358710128821402129363445)
                ·
                  refine ⟨221129074577006449627823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2358710128821402129363445 221129074577006449627823)
                  ·
                    rfl

theorem cell23_3875826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 4, 5].length) (baseStart_3875826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3875826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3875826 prefixEnd_3875826 := by exact prefixLift 3875826
  have htrace : WordTrace (prefixWord ++ tailWord_3875826) baseStart_3875826 baseEnd_3875826 := by
    simpa [prefixWord, tailWord_3875826, baseEnd_3875826] using wordTrace_append hprefix tailTrace_3875826
  have hstable : (prefixWord ++ tailWord_3875826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3875826).length < 2 ^ (prefixWord ++ tailWord_3875826).sum := by decide
  have hdescent : baseEnd_3875826 < baseStart_3875826 := by decide
  rcases family_descends (prefixWord ++ tailWord_3875826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3875852 : List Nat := [2, 2, 1, 2, 3, 2, 1, 1, 5, 4]
def baseStart_3875852 : Nat := 118140960795 + 3875852 * 2 ^ 59
def prefixEnd_3875852 : Nat := 4983230072969 + 3 ^ 40 * 3875852 * 2
def baseEnd_3875852 : Nat := 663391673896691648308429

theorem tailTrace_3875852 : CollatzResearch.WordTrace tailWord_3875852 prefixEnd_3875852 663391673896691648308429 := by
  unfold tailWord_3875852
  simp only [CollatzResearch.WordTrace]
  refine ⟨70681967977228810833374905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94242623969638414444499873 70681967977228810833374905)
  ·
    refine ⟨53011475982921608125031179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70681967977228810833374905 53011475982921608125031179)
    ·
      refine ⟨79517213974382412187546769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53011475982921608125031179 79517213974382412187546769)
      ·
        refine ⟨59637910480786809140660077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79517213974382412187546769 59637910480786809140660077)
        ·
          refine ⟨22364216430295053427747529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59637910480786809140660077 22364216430295053427747529)
          ·
            refine ⟨16773162322721290070810647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22364216430295053427747529 16773162322721290070810647)
            ·
              refine ⟨25159743484081935106215971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16773162322721290070810647 25159743484081935106215971)
              ·
                refine ⟨37739615226122902659323957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25159743484081935106215971 37739615226122902659323957)
                ·
                  refine ⟨3538088927449022124311621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37739615226122902659323957 3538088927449022124311621)
                  ·
                    refine ⟨663391673896691648308429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3538088927449022124311621 663391673896691648308429)
                    ·
                      rfl

theorem cell23_3875852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 1, 5, 4].length) (baseStart_3875852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3875852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3875852 prefixEnd_3875852 := by exact prefixLift 3875852
  have htrace : WordTrace (prefixWord ++ tailWord_3875852) baseStart_3875852 baseEnd_3875852 := by
    simpa [prefixWord, tailWord_3875852, baseEnd_3875852] using wordTrace_append hprefix tailTrace_3875852
  have hstable : (prefixWord ++ tailWord_3875852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3875852).length < 2 ^ (prefixWord ++ tailWord_3875852).sum := by decide
  have hdescent : baseEnd_3875852 < baseStart_3875852 := by decide
  rcases family_descends (prefixWord ++ tailWord_3875852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3875886 : List Nat := [4, 1, 3, 1, 1, 1, 1, 6, 1, 4]
def baseStart_3875886 : Nat := 118140960795 + 3875886 * 2 ^ 59
def prefixEnd_3875886 : Nat := 4983230072969 + 3 ^ 40 * 3875886 * 2
def baseEnd_3875886 : Nat := 663397493344109270633377

theorem tailTrace_3875886 : CollatzResearch.WordTrace tailWord_3875886 prefixEnd_3875886 663397493344109270633377 := by
  unfold tailWord_3875886
  simp only [CollatzResearch.WordTrace]
  refine ⟨17670647004541805684185939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94243450690889630315658341 17670647004541805684185939)
  ·
    refine ⟨26505970506812708526278909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17670647004541805684185939 26505970506812708526278909)
    ·
      refine ⟨9939738940054765697354591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26505970506812708526278909 9939738940054765697354591)
      ·
        refine ⟨14909608410082148546031887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9939738940054765697354591 14909608410082148546031887)
        ·
          refine ⟨22364412615123222819047831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14909608410082148546031887 22364412615123222819047831)
          ·
            refine ⟨33546618922684834228571747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22364412615123222819047831 33546618922684834228571747)
            ·
              refine ⟨50319928384027251342857621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33546618922684834228571747 50319928384027251342857621)
              ·
                refine ⟨2358746643001277406696451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 50319928384027251342857621 2358746643001277406696451)
                ·
                  refine ⟨3538119964501916110044677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2358746643001277406696451 3538119964501916110044677)
                  ·
                    refine ⟨663397493344109270633377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3538119964501916110044677 663397493344109270633377)
                    ·
                      rfl

theorem cell23_3875886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 6, 1, 4].length) (baseStart_3875886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3875886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3875886 prefixEnd_3875886 := by exact prefixLift 3875886
  have htrace : WordTrace (prefixWord ++ tailWord_3875886) baseStart_3875886 baseEnd_3875886 := by
    simpa [prefixWord, tailWord_3875886, baseEnd_3875886] using wordTrace_append hprefix tailTrace_3875886
  have hstable : (prefixWord ++ tailWord_3875886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3875886).length < 2 ^ (prefixWord ++ tailWord_3875886).sum := by decide
  have hdescent : baseEnd_3875886 < baseStart_3875886 := by decide
  rcases family_descends (prefixWord ++ tailWord_3875886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3875909 : List Nat := [1, 3, 1, 1, 1, 3, 4, 2, 3, 1, 3]
def baseStart_3875909 : Nat := 118140960795 + 3875909 * 2 ^ 59
def prefixEnd_3875909 : Nat := 4983230072969 + 3 ^ 40 * 3875909 * 2
def baseEnd_3875909 : Nat := 1990204290087381221912525

theorem tailTrace_3875909 : CollatzResearch.WordTrace tailWord_3875909 prefixEnd_3875909 1990204290087381221912525 := by
  unfold tailWord_3875909
  simp only [CollatzResearch.WordTrace]
  refine ⟨141366014915251120401574781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94244009943500746934383187 141366014915251120401574781)
  ·
    refine ⟨53012255593219170150590543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141366014915251120401574781 53012255593219170150590543)
    ·
      refine ⟨79518383389828755225885815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53012255593219170150590543 79518383389828755225885815)
      ·
        refine ⟨119277575084743132838828723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79518383389828755225885815 119277575084743132838828723)
        ·
          refine ⟨178916362627114699258243085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119277575084743132838828723 178916362627114699258243085)
          ·
            refine ⟨67093635985168012221841157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 178916362627114699258243085 67093635985168012221841157)
            ·
              refine ⟨12580056747219002291595217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67093635985168012221841157 12580056747219002291595217)
              ·
                refine ⟨9435042560414251718696413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12580056747219002291595217 9435042560414251718696413)
                ·
                  refine ⟨3538140960155344394511155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9435042560414251718696413 3538140960155344394511155)
                  ·
                    refine ⟨5307211440233016591766733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3538140960155344394511155 5307211440233016591766733)
                    ·
                      refine ⟨1990204290087381221912525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5307211440233016591766733 1990204290087381221912525)
                      ·
                        rfl

theorem cell23_3875909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 2, 3, 1, 3].length) (baseStart_3875909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3875909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3875909 prefixEnd_3875909 := by exact prefixLift 3875909
  have htrace : WordTrace (prefixWord ++ tailWord_3875909) baseStart_3875909 baseEnd_3875909 := by
    simpa [prefixWord, tailWord_3875909, baseEnd_3875909] using wordTrace_append hprefix tailTrace_3875909
  have hstable : (prefixWord ++ tailWord_3875909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3875909).length < 2 ^ (prefixWord ++ tailWord_3875909).sum := by decide
  have hdescent : baseEnd_3875909 < baseStart_3875909 := by decide
  rcases family_descends (prefixWord ++ tailWord_3875909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3875952 : List Nat := [2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 5]
def baseStart_3875952 : Nat := 118140960795 + 3875952 * 2 ^ 59
def prefixEnd_3875952 : Nat := 4983230072969 + 3 ^ 40 * 3875952 * 2
def baseEnd_3875952 : Nat := 1990226369755524553674827

theorem tailTrace_3875952 : CollatzResearch.WordTrace tailWord_3875952 prefixEnd_3875952 1990226369755524553674827 := by
  unfold tailWord_3875952
  simp only [CollatzResearch.WordTrace]
  refine ⟨70683791627047669372695055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94245055502730225830260073 70683791627047669372695055)
  ·
    refine ⟨106025687440571504059042583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70683791627047669372695055 106025687440571504059042583)
    ·
      refine ⟨159038531160857256088563875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106025687440571504059042583 159038531160857256088563875)
      ·
        refine ⟨238557796741285884132845813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159038531160857256088563875 238557796741285884132845813)
        ·
          refine ⟨22364793444495551637454295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 238557796741285884132845813 22364793444495551637454295)
          ·
            refine ⟨33547190166743327456181443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22364793444495551637454295 33547190166743327456181443)
            ·
              refine ⟨50320785250114991184272165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33547190166743327456181443 50320785250114991184272165)
              ·
                refine ⟨9435147234396560847051031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50320785250114991184272165 9435147234396560847051031)
                ·
                  refine ⟨14152720851594841270576547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9435147234396560847051031 14152720851594841270576547)
                  ·
                    refine ⟨21229081277392261905864821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14152720851594841270576547 21229081277392261905864821)
                    ·
                      refine ⟨1990226369755524553674827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21229081277392261905864821 1990226369755524553674827)
                      ·
                        rfl

theorem cell23_3875952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 5].length) (baseStart_3875952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3875952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3875952 prefixEnd_3875952 := by exact prefixLift 3875952
  have htrace : WordTrace (prefixWord ++ tailWord_3875952) baseStart_3875952 baseEnd_3875952 := by
    simpa [prefixWord, tailWord_3875952, baseEnd_3875952] using wordTrace_append hprefix tailTrace_3875952
  have hstable : (prefixWord ++ tailWord_3875952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3875952).length < 2 ^ (prefixWord ++ tailWord_3875952).sum := by decide
  have hdescent : baseEnd_3875952 < baseStart_3875952 := by decide
  rcases family_descends (prefixWord ++ tailWord_3875952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3875959 : List Nat := [1, 1, 3, 1, 1, 4, 3, 3, 2, 4]
def baseStart_3875959 : Nat := 118140960795 + 3875959 * 2 ^ 59
def prefixEnd_3875959 : Nat := 4983230072969 + 3 ^ 40 * 3875959 * 2
def baseEnd_3875959 : Nat := 663409988040035342095765

theorem tailTrace_3875959 : CollatzResearch.WordTrace tailWord_3875959 prefixEnd_3875959 663409988040035342095765 := by
  unfold tailWord_3875959
  simp only [CollatzResearch.WordTrace]
  refine ⟨141367838565069978940894931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94245225710046652627263287 141367838565069978940894931)
  ·
    refine ⟨212051757847604968411342397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141367838565069978940894931 212051757847604968411342397)
    ·
      refine ⟨79519409192851863154253399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212051757847604968411342397 79519409192851863154253399)
      ·
        refine ⟨119279113789277794731380099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79519409192851863154253399 119279113789277794731380099)
        ·
          refine ⟨178918670683916692097070149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119279113789277794731380099 178918670683916692097070149)
          ·
            refine ⟨33547250753234379768200653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 178918670683916692097070149 33547250753234379768200653)
            ·
              refine ⟨12580219032462892413075245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33547250753234379768200653 12580219032462892413075245)
              ·
                refine ⟨4717582137173584654903217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12580219032462892413075245 4717582137173584654903217)
                ·
                  refine ⟨3538186602880188491177413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4717582137173584654903217 3538186602880188491177413)
                  ·
                    refine ⟨663409988040035342095765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3538186602880188491177413 663409988040035342095765)
                    ·
                      rfl

theorem cell23_3875959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 3, 2, 4].length) (baseStart_3875959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3875959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3875959 prefixEnd_3875959 := by exact prefixLift 3875959
  have htrace : WordTrace (prefixWord ++ tailWord_3875959) baseStart_3875959 baseEnd_3875959 := by
    simpa [prefixWord, tailWord_3875959, baseEnd_3875959] using wordTrace_append hprefix tailTrace_3875959
  have hstable : (prefixWord ++ tailWord_3875959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3875959).length < 2 ^ (prefixWord ++ tailWord_3875959).sum := by decide
  have hdescent : baseEnd_3875959 < baseStart_3875959 := by decide
  rcases family_descends (prefixWord ++ tailWord_3875959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3875972 : List Nat := [2, 3, 2, 1, 2, 2, 2, 9]
def baseStart_3875972 : Nat := 118140960795 + 3875972 * 2 ^ 59
def prefixEnd_3875972 : Nat := 4983230072969 + 3 ^ 40 * 3875972 * 2
def baseEnd_3875972 : Nat := 73712468124763499089805

theorem tailTrace_3875972 : CollatzResearch.WordTrace tailWord_3875972 prefixEnd_3875972 73712468124763499089805 := by
  unfold tailWord_3875972
  simp only [CollatzResearch.WordTrace]
  refine ⟨70684156357011441080559085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94245541809348588107412113 70684156357011441080559085)
  ·
    refine ⟨26506558633879290405209657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70684156357011441080559085 26506558633879290405209657)
    ·
      refine ⟨19879918975409467803907243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26506558633879290405209657 19879918975409467803907243)
      ·
        refine ⟨29819878463114201705860865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19879918975409467803907243 29819878463114201705860865)
        ·
          refine ⟨22364908847335651279395649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29819878463114201705860865 22364908847335651279395649)
          ·
            refine ⟨16773681635501738459546737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22364908847335651279395649 16773681635501738459546737)
            ·
              refine ⟨12580261226626303844660053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16773681635501738459546737 12580261226626303844660053)
              ·
                refine ⟨73712468124763499089805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12580261226626303844660053 73712468124763499089805)
                ·
                  rfl

theorem cell23_3875972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 9].length) (baseStart_3875972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3875972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3875972 prefixEnd_3875972 := by exact prefixLift 3875972
  have htrace : WordTrace (prefixWord ++ tailWord_3875972) baseStart_3875972 baseEnd_3875972 := by
    simpa [prefixWord, tailWord_3875972, baseEnd_3875972] using wordTrace_append hprefix tailTrace_3875972
  have hstable : (prefixWord ++ tailWord_3875972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3875972).length < 2 ^ (prefixWord ++ tailWord_3875972).sum := by decide
  have hdescent : baseEnd_3875972 < baseStart_3875972 := by decide
  rcases family_descends (prefixWord ++ tailWord_3875972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3875986 : List Nat := [3, 2, 3, 1, 1, 4, 1, 1, 1, 1, 5]
def baseStart_3875986 : Nat := 118140960795 + 3875986 * 2 ^ 59
def prefixEnd_3875986 : Nat := 4983230072969 + 3 ^ 40 * 3875986 * 2
def baseEnd_3875986 : Nat := 1990243828097777420649671

theorem tailTrace_3875986 : CollatzResearch.WordTrace tailWord_3875986 prefixEnd_3875986 1990243828097777420649671 := by
  unfold tailWord_3875986
  simp only [CollatzResearch.WordTrace]
  refine ⟨35342205833993040638031953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94245882223981441701418541 35342205833993040638031953)
  ·
    refine ⟨26506654375494780478523965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35342205833993040638031953 26506654375494780478523965)
    ·
      refine ⟨9939995390810542679446487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26506654375494780478523965 9939995390810542679446487)
      ·
        refine ⟨14909993086215814019169731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9939995390810542679446487 14909993086215814019169731)
        ·
          refine ⟨22364989629323721028754597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14909993086215814019169731 22364989629323721028754597)
          ·
            refine ⟨4193435555498197692891487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22364989629323721028754597 4193435555498197692891487)
            ·
              refine ⟨6290153333247296539337231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4193435555498197692891487 6290153333247296539337231)
              ·
                refine ⟨9435229999870944809005847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6290153333247296539337231 9435229999870944809005847)
                ·
                  refine ⟨14152844999806417213508771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9435229999870944809005847 14152844999806417213508771)
                  ·
                    refine ⟨21229267499709625820263157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14152844999806417213508771 21229267499709625820263157)
                    ·
                      refine ⟨1990243828097777420649671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21229267499709625820263157 1990243828097777420649671)
                      ·
                        rfl

theorem cell23_3875986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 1, 1, 1, 1, 5].length) (baseStart_3875986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3875986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3875986 prefixEnd_3875986 := by exact prefixLift 3875986
  have htrace : WordTrace (prefixWord ++ tailWord_3875986) baseStart_3875986 baseEnd_3875986 := by
    simpa [prefixWord, tailWord_3875986, baseEnd_3875986] using wordTrace_append hprefix tailTrace_3875986
  have hstable : (prefixWord ++ tailWord_3875986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3875986).length < 2 ^ (prefixWord ++ tailWord_3875986).sum := by decide
  have hdescent : baseEnd_3875986 < baseStart_3875986 := by decide
  rcases family_descends (prefixWord ++ tailWord_3875986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3876026 : List Nat := [3, 1, 1, 1, 2, 2, 1, 6, 1, 3, 2]
def baseStart_3876026 : Nat := 118140960795 + 3876026 * 2 ^ 59
def prefixEnd_3876026 : Nat := 4983230072969 + 3 ^ 40 * 3876026 * 2
def baseEnd_3876026 : Nat := 1990264367323957264149487

theorem tailTrace_3876026 : CollatzResearch.WordTrace tailWord_3876026 prefixEnd_3876026 1990264367323957264149487 := by
  unfold tailWord_3876026
  simp only [CollatzResearch.WordTrace]
  refine ⟨35342570563956812345895983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94246854837218166255722621 35342570563956812345895983)
  ·
    refine ⟨53013855845935218518843975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35342570563956812345895983 53013855845935218518843975)
    ·
      refine ⟨79520783768902827778265963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53013855845935218518843975 79520783768902827778265963)
      ·
        refine ⟨119281175653354241667398945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79520783768902827778265963 119281175653354241667398945)
        ·
          refine ⟨89460881740015681250549209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119281175653354241667398945 89460881740015681250549209)
          ·
            refine ⟨67095661305011760937911907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89460881740015681250549209 67095661305011760937911907)
            ·
              refine ⟨100643491957517641406867861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67095661305011760937911907 100643491957517641406867861)
              ·
                refine ⟨4717663685508639440946931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 100643491957517641406867861 4717663685508639440946931)
                ·
                  refine ⟨7076495528262959161420397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4717663685508639440946931 7076495528262959161420397)
                  ·
                    refine ⟨2653685823098609685532649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7076495528262959161420397 2653685823098609685532649)
                    ·
                      refine ⟨1990264367323957264149487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2653685823098609685532649 1990264367323957264149487)
                      ·
                        rfl

theorem cell23_3876026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 6, 1, 3, 2].length) (baseStart_3876026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3876026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3876026 prefixEnd_3876026 := by exact prefixLift 3876026
  have htrace : WordTrace (prefixWord ++ tailWord_3876026) baseStart_3876026 baseEnd_3876026 := by
    simpa [prefixWord, tailWord_3876026, baseEnd_3876026] using wordTrace_append hprefix tailTrace_3876026
  have hstable : (prefixWord ++ tailWord_3876026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3876026).length < 2 ^ (prefixWord ++ tailWord_3876026).sum := by decide
  have hdescent : baseEnd_3876026 < baseStart_3876026 := by decide
  rcases family_descends (prefixWord ++ tailWord_3876026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3876034 : List Nat := [3, 5, 1, 1, 3, 1, 2, 1, 1, 1, 4]
def baseStart_3876034 : Nat := 118140960795 + 3876034 * 2 ^ 59
def prefixEnd_3876034 : Nat := 4983230072969 + 3 ^ 40 * 3876034 * 2
def baseEnd_3876034 : Nat := 1990268475169193232849451

theorem tailTrace_3876034 : CollatzResearch.WordTrace tailWord_3876034 prefixEnd_3876034 1990268475169193232849451 := by
  unfold tailWord_3876034
  simp only [CollatzResearch.WordTrace]
  refine ⟨35342643509949566687468789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94247049359865511166583437 35342643509949566687468789)
  ·
    refine ⟨3313372829057771876950199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 35342643509949566687468789 3313372829057771876950199)
    ·
      refine ⟨4970059243586657815425299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3313372829057771876950199 4970059243586657815425299)
      ·
        refine ⟨7455088865379986723137949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4970059243586657815425299 7455088865379986723137949)
        ·
          refine ⟨2795658324517495021176731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7455088865379986723137949 2795658324517495021176731)
          ·
            refine ⟨4193487486776242531765097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2795658324517495021176731 4193487486776242531765097)
            ·
              refine ⟨3145115615082181898823823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4193487486776242531765097 3145115615082181898823823)
              ·
                refine ⟨4717673422623272848235735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3145115615082181898823823 4717673422623272848235735)
                ·
                  refine ⟨7076510133934909272353603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4717673422623272848235735 7076510133934909272353603)
                  ·
                    refine ⟨10614765200902363908530405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7076510133934909272353603 10614765200902363908530405)
                    ·
                      refine ⟨1990268475169193232849451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10614765200902363908530405 1990268475169193232849451)
                      ·
                        rfl

theorem cell23_3876034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 2, 1, 1, 1, 4].length) (baseStart_3876034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3876034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3876034 prefixEnd_3876034 := by exact prefixLift 3876034
  have htrace : WordTrace (prefixWord ++ tailWord_3876034) baseStart_3876034 baseEnd_3876034 := by
    simpa [prefixWord, tailWord_3876034, baseEnd_3876034] using wordTrace_append hprefix tailTrace_3876034
  have hstable : (prefixWord ++ tailWord_3876034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3876034).length < 2 ^ (prefixWord ++ tailWord_3876034).sum := by decide
  have hdescent : baseEnd_3876034 < baseStart_3876034 := by decide
  rcases family_descends (prefixWord ++ tailWord_3876034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3876119 : List Nat := [1, 1, 3, 4, 1, 1, 3, 1, 1, 2, 5]
def baseStart_3876119 : Nat := 118140960795 + 3876119 * 2 ^ 59
def prefixEnd_3876119 : Nat := 4983230072969 + 3 ^ 40 * 3876119 * 2
def baseEnd_3876119 : Nat := 1990312121024825400286559

theorem tailTrace_3876119 : CollatzResearch.WordTrace tailWord_3876119 prefixEnd_3876119 1990312121024825400286559 := by
  unfold tailWord_3876119
  simp only [CollatzResearch.WordTrace]
  refine ⟨141373674244490326266719411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94249116162993550844479607 141373674244490326266719411)
  ·
    refine ⟨212060511366735489400079117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141373674244490326266719411 212060511366735489400079117)
    ·
      refine ⟨79522691762525808525029669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212060511366735489400079117 79522691762525808525029669)
      ·
        refine ⟨14910504705473589098443063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79522691762525808525029669 14910504705473589098443063)
        ·
          refine ⟨22365757058210383647664595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14910504705473589098443063 22365757058210383647664595)
          ·
            refine ⟨33548635587315575471496893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22365757058210383647664595 33548635587315575471496893)
            ·
              refine ⟨12580738345243340801811335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33548635587315575471496893 12580738345243340801811335)
              ·
                refine ⟨18871107517865011202717003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12580738345243340801811335 18871107517865011202717003)
                ·
                  refine ⟨28306661276797516804075505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18871107517865011202717003 28306661276797516804075505)
                  ·
                    refine ⟨21229995957598137603056629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28306661276797516804075505 21229995957598137603056629)
                    ·
                      refine ⟨1990312121024825400286559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21229995957598137603056629 1990312121024825400286559)
                      ·
                        rfl

theorem cell23_3876119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_3876119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3876119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3876119 prefixEnd_3876119 := by exact prefixLift 3876119
  have htrace : WordTrace (prefixWord ++ tailWord_3876119) baseStart_3876119 baseEnd_3876119 := by
    simpa [prefixWord, tailWord_3876119, baseEnd_3876119] using wordTrace_append hprefix tailTrace_3876119
  have hstable : (prefixWord ++ tailWord_3876119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3876119).length < 2 ^ (prefixWord ++ tailWord_3876119).sum := by decide
  have hdescent : baseEnd_3876119 < baseStart_3876119 := by decide
  rcases family_descends (prefixWord ++ tailWord_3876119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3876129 : List Nat := [1, 2, 3, 2, 1, 1, 1, 1, 6, 1, 4]
def baseStart_3876129 : Nat := 118140960795 + 3876129 * 2 ^ 59
def prefixEnd_3876129 : Nat := 4983230072969 + 3 ^ 40 * 3876129 * 2
def baseEnd_3876129 : Nat := 1990317255831370361161513

theorem tailTrace_3876129 : CollatzResearch.WordTrace tailWord_3876129 prefixEnd_3876129 1990317255831370361161513 := by
  unfold tailWord_3876129
  simp only [CollatzResearch.WordTrace]
  refine ⟨141374038974454097974583441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94249359316302731983055627 141374038974454097974583441)
  ·
    refine ⟨106030529230840573480937581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141374038974454097974583441 106030529230840573480937581)
    ·
      refine ⟨39761448461565215055351593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106030529230840573480937581 39761448461565215055351593)
      ·
        refine ⟨29821086346173911291513695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39761448461565215055351593 29821086346173911291513695)
        ·
          refine ⟨44731629519260866937270543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29821086346173911291513695 44731629519260866937270543)
          ·
            refine ⟨67097444278891300405905815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44731629519260866937270543 67097444278891300405905815)
            ·
              refine ⟨100646166418336950608858723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67097444278891300405905815 100646166418336950608858723)
              ·
                refine ⟨150969249627505425913288085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100646166418336950608858723 150969249627505425913288085)
                ·
                  refine ⟨7076683576289316839685379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 150969249627505425913288085 7076683576289316839685379)
                  ·
                    refine ⟨10615025364433975259528069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7076683576289316839685379 10615025364433975259528069)
                    ·
                      refine ⟨1990317255831370361161513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10615025364433975259528069 1990317255831370361161513)
                      ·
                        rfl

theorem cell23_3876129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 6, 1, 4].length) (baseStart_3876129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3876129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3876129 prefixEnd_3876129 := by exact prefixLift 3876129
  have htrace : WordTrace (prefixWord ++ tailWord_3876129) baseStart_3876129 baseEnd_3876129 := by
    simpa [prefixWord, tailWord_3876129, baseEnd_3876129] using wordTrace_append hprefix tailTrace_3876129
  have hstable : (prefixWord ++ tailWord_3876129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3876129).length < 2 ^ (prefixWord ++ tailWord_3876129).sum := by decide
  have hdescent : baseEnd_3876129 < baseStart_3876129 := by decide
  rcases family_descends (prefixWord ++ tailWord_3876129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3876146 : List Nat := [3, 2, 1, 1, 4, 1, 1, 3, 2, 1, 4]
def baseStart_3876146 : Nat := 118140960795 + 3876146 * 2 ^ 59
def prefixEnd_3876146 : Nat := 4983230072969 + 3 ^ 40 * 3876146 * 2
def baseEnd_3876146 : Nat := 1990325985002496794648935

theorem tailTrace_3876146 : CollatzResearch.WordTrace tailWord_3876146 prefixEnd_3876146 1990325985002496794648935 := by
  unfold tailWord_3876146
  simp only [CollatzResearch.WordTrace]
  refine ⟨35343664753848127469488073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94249772676928339918634861 35343664753848127469488073)
  ·
    refine ⟨26507748565386095602116055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35343664753848127469488073 26507748565386095602116055)
    ·
      refine ⟨39761622848079143403174083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26507748565386095602116055 39761622848079143403174083)
      ·
        refine ⟨59642434272118715104761125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39761622848079143403174083 59642434272118715104761125)
        ·
          refine ⟨11182956426022259082142711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59642434272118715104761125 11182956426022259082142711)
          ·
            refine ⟨16774434639033388623214067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11182956426022259082142711 16774434639033388623214067)
            ·
              refine ⟨25161651958550082934821101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16774434639033388623214067 25161651958550082934821101)
              ·
                refine ⟨9435619484456281100557913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25161651958550082934821101 9435619484456281100557913)
                ·
                  refine ⟨7076714613342210825418435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9435619484456281100557913 7076714613342210825418435)
                  ·
                    refine ⟨10615071920013316238127653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7076714613342210825418435 10615071920013316238127653)
                    ·
                      refine ⟨1990325985002496794648935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10615071920013316238127653 1990325985002496794648935)
                      ·
                        rfl

theorem cell23_3876146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 3, 2, 1, 4].length) (baseStart_3876146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3876146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3876146 prefixEnd_3876146 := by exact prefixLift 3876146
  have htrace : WordTrace (prefixWord ++ tailWord_3876146) baseStart_3876146 baseEnd_3876146 := by
    simpa [prefixWord, tailWord_3876146, baseEnd_3876146] using wordTrace_append hprefix tailTrace_3876146
  have hstable : (prefixWord ++ tailWord_3876146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3876146).length < 2 ^ (prefixWord ++ tailWord_3876146).sum := by decide
  have hdescent : baseEnd_3876146 < baseStart_3876146 := by decide
  rcases family_descends (prefixWord ++ tailWord_3876146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3876169 : List Nat := [1, 2, 1, 1, 2, 3, 3, 4, 6]
def baseStart_3876169 : Nat := 118140960795 + 3876169 * 2 ^ 59
def prefixEnd_3876169 : Nat := 4983230072969 + 3 ^ 40 * 3876169 * 2
def baseEnd_3876169 : Nat := 221148643895283356073481

theorem tailTrace_3876169 : CollatzResearch.WordTrace tailWord_3876169 prefixEnd_3876169 221148643895283356073481 := by
  unfold tailWord_3876169
  simp only [CollatzResearch.WordTrace]
  refine ⟨141375497894309184806039561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94250331929539456537359707 141375497894309184806039561)
  ·
    refine ⟨106031623420731888604529671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141375497894309184806039561 106031623420731888604529671)
    ·
      refine ⟨159047435131097832906794507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106031623420731888604529671 159047435131097832906794507)
      ·
        refine ⟨238571152696646749360191761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159047435131097832906794507 238571152696646749360191761)
        ·
          refine ⟨178928364522485062020143821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238571152696646749360191761 178928364522485062020143821)
          ·
            refine ⟨67098136695931898257553933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 178928364522485062020143821 67098136695931898257553933)
            ·
              refine ⟨25161801260974461846582725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67098136695931898257553933 25161801260974461846582725)
              ·
                refine ⟨4717837736432711596234261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25161801260974461846582725 4717837736432711596234261)
                ·
                  refine ⟨221148643895283356073481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4717837736432711596234261 221148643895283356073481)
                  ·
                    rfl

theorem cell23_3876169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 4, 6].length) (baseStart_3876169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3876169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3876169 prefixEnd_3876169 := by exact prefixLift 3876169
  have htrace : WordTrace (prefixWord ++ tailWord_3876169) baseStart_3876169 baseEnd_3876169 := by
    simpa [prefixWord, tailWord_3876169, baseEnd_3876169] using wordTrace_append hprefix tailTrace_3876169
  have hstable : (prefixWord ++ tailWord_3876169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3876169).length < 2 ^ (prefixWord ++ tailWord_3876169).sum := by decide
  have hdescent : baseEnd_3876169 < baseStart_3876169 := by decide
  rcases family_descends (prefixWord ++ tailWord_3876169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3876200 : List Nat := [2, 1, 4, 2, 3, 2, 1, 1, 2, 2, 3]
def baseStart_3876200 : Nat := 118140960795 + 3876200 * 2 ^ 59
def prefixEnd_3876200 : Nat := 4983230072969 + 3 ^ 40 * 3876200 * 2
def baseEnd_3876200 : Nat := 1990353712957839583373687

theorem tailTrace_3876200 : CollatzResearch.WordTrace tailWord_3876200 prefixEnd_3876200 1990353712957839583373687 := by
  unfold tailWord_3876200
  simp only [CollatzResearch.WordTrace]
  refine ⟨70688314278598438550209027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94251085704797918066945369 70688314278598438550209027)
  ·
    refine ⟨106032471417897657825313541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70688314278598438550209027 106032471417897657825313541)
    ·
      refine ⟨19881088390855810842246289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106032471417897657825313541 19881088390855810842246289)
      ·
        refine ⟨14910816293141858131684717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19881088390855810842246289 14910816293141858131684717)
        ·
          refine ⟨5591556109928196799381769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14910816293141858131684717 5591556109928196799381769)
          ·
            refine ⟨4193667082446147599536327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5591556109928196799381769 4193667082446147599536327)
            ·
              refine ⟨6290500623669221399304491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4193667082446147599536327 6290500623669221399304491)
              ·
                refine ⟨9435750935503832098956737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6290500623669221399304491 9435750935503832098956737)
                ·
                  refine ⟨7076813201627874074217553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9435750935503832098956737 7076813201627874074217553)
                  ·
                    refine ⟨5307609901220905555663165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7076813201627874074217553 5307609901220905555663165)
                    ·
                      refine ⟨1990353712957839583373687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5307609901220905555663165 1990353712957839583373687)
                      ·
                        rfl

theorem cell23_3876200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 1, 1, 2, 2, 3].length) (baseStart_3876200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3876200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3876200 prefixEnd_3876200 := by exact prefixLift 3876200
  have htrace : WordTrace (prefixWord ++ tailWord_3876200) baseStart_3876200 baseEnd_3876200 := by
    simpa [prefixWord, tailWord_3876200, baseEnd_3876200] using wordTrace_append hprefix tailTrace_3876200
  have hstable : (prefixWord ++ tailWord_3876200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3876200).length < 2 ^ (prefixWord ++ tailWord_3876200).sum := by decide
  have hdescent : baseEnd_3876200 < baseStart_3876200 := by decide
  rcases family_descends (prefixWord ++ tailWord_3876200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3876229 : List Nat := [1, 3, 1, 1, 3, 1, 2, 2, 3, 6]
def baseStart_3876229 : Nat := 118140960795 + 3876229 * 2 ^ 59
def prefixEnd_3876229 : Nat := 4983230072969 + 3 ^ 40 * 3876229 * 2
def baseEnd_3876229 : Nat := 663456201298939989970351

theorem tailTrace_3876229 : CollatzResearch.WordTrace tailWord_3876229 prefixEnd_3876229 663456201298939989970351 := by
  unfold tailWord_3876229
  simp only [CollatzResearch.WordTrace]
  refine ⟨141377686274091815053223741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94251790849394543368815827 141377686274091815053223741)
  ·
    refine ⟨53016632352784430644958903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141377686274091815053223741 53016632352784430644958903)
    ·
      refine ⟨79524948529176645967438355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53016632352784430644958903 79524948529176645967438355)
      ·
        refine ⟨119287422793764968951157533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79524948529176645967438355 119287422793764968951157533)
        ·
          refine ⟨44732783547661863356684075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119287422793764968951157533 44732783547661863356684075)
          ·
            refine ⟨67099175321492795035026113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44732783547661863356684075 67099175321492795035026113)
            ·
              refine ⟨50324381491119596276269585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67099175321492795035026113 50324381491119596276269585)
              ·
                refine ⟨37743286118339697207202189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50324381491119596276269585 37743286118339697207202189)
                ·
                  refine ⟨14153732294377386452700821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37743286118339697207202189 14153732294377386452700821)
                  ·
                    refine ⟨663456201298939989970351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14153732294377386452700821 663456201298939989970351)
                    ·
                      rfl

theorem cell23_3876229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 2, 3, 6].length) (baseStart_3876229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3876229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3876229 prefixEnd_3876229 := by exact prefixLift 3876229
  have htrace : WordTrace (prefixWord ++ tailWord_3876229) baseStart_3876229 baseEnd_3876229 := by
    simpa [prefixWord, tailWord_3876229, baseEnd_3876229] using wordTrace_append hprefix tailTrace_3876229
  have hstable : (prefixWord ++ tailWord_3876229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3876229).length < 2 ^ (prefixWord ++ tailWord_3876229).sum := by decide
  have hdescent : baseEnd_3876229 < baseStart_3876229 := by decide
  rcases family_descends (prefixWord ++ tailWord_3876229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3876253 : List Nat := [1, 4, 2, 1, 3, 1, 1, 4, 1, 1, 4]
def baseStart_3876253 : Nat := 118140960795 + 3876253 * 2 ^ 59
def prefixEnd_3876253 : Nat := 4983230072969 + 3 ^ 40 * 3876253 * 2
def baseEnd_3876253 : Nat := 1990380927432527876010943

theorem tailTrace_3876253 : CollatzResearch.WordTrace tailWord_3876253 prefixEnd_3876253 1990380927432527876010943 := by
  unfold tailWord_3876253
  simp only [CollatzResearch.WordTrace]
  refine ⟨141378561626004867152097413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94252374417336578101398275 141378561626004867152097413)
  ·
    refine ⟨26508480304875912591018265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141378561626004867152097413 26508480304875912591018265)
    ·
      refine ⟨19881360228656934443263699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26508480304875912591018265 19881360228656934443263699)
      ·
        refine ⟨29822040342985401664895549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19881360228656934443263699 29822040342985401664895549)
        ·
          refine ⟨11183265128619525624335831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29822040342985401664895549 11183265128619525624335831)
          ·
            refine ⟨16774897692929288436503747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11183265128619525624335831 16774897692929288436503747)
            ·
              refine ⟨25162346539393932654755621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16774897692929288436503747 25162346539393932654755621)
              ·
                refine ⟨4717939976136362372766679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25162346539393932654755621 4717939976136362372766679)
                ·
                  refine ⟨7076909964204543559150019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4717939976136362372766679 7076909964204543559150019)
                  ·
                    refine ⟨10615364946306815338725029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7076909964204543559150019 10615364946306815338725029)
                    ·
                      refine ⟨1990380927432527876010943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10615364946306815338725029 1990380927432527876010943)
                      ·
                        rfl

theorem cell23_3876253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 4, 1, 1, 4].length) (baseStart_3876253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3876253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3876253 prefixEnd_3876253 := by exact prefixLift 3876253
  have htrace : WordTrace (prefixWord ++ tailWord_3876253) baseStart_3876253 baseEnd_3876253 := by
    simpa [prefixWord, tailWord_3876253, baseEnd_3876253] using wordTrace_append hprefix tailTrace_3876253
  have hstable : (prefixWord ++ tailWord_3876253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3876253).length < 2 ^ (prefixWord ++ tailWord_3876253).sum := by decide
  have hdescent : baseEnd_3876253 < baseStart_3876253 := by decide
  rcases family_descends (prefixWord ++ tailWord_3876253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3876259 : List Nat := [1, 1, 1, 4, 1, 3, 3, 9]
def baseStart_3876259 : Nat := 118140960795 + 3876259 * 2 ^ 59
def prefixEnd_3876259 : Nat := 4983230072969 + 3 ^ 40 * 3876259 * 2
def baseEnd_3876259 : Nat := 73717926233942772316145

theorem tailTrace_3876259 : CollatzResearch.WordTrace tailWord_3876259 prefixEnd_3876259 73717926233942772316145 := by
  unfold tailWord_3876259
  simp only [CollatzResearch.WordTrace]
  refine ⟨141378780463983130176815831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94252520309322086784543887 141378780463983130176815831)
  ·
    refine ⟨212068170695974695265223747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141378780463983130176815831 212068170695974695265223747)
    ·
      refine ⟨318102256043962042897835621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212068170695974695265223747 318102256043962042897835621)
      ·
        refine ⟨59644173008242883043344179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 318102256043962042897835621 59644173008242883043344179)
        ·
          refine ⟨89466259512364324565016269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59644173008242883043344179 89466259512364324565016269)
          ·
            refine ⟨33549847317136621711881101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89466259512364324565016269 33549847317136621711881101)
            ·
              refine ⟨12581192743926233141955413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33549847317136621711881101 12581192743926233141955413)
              ·
                refine ⟨73717926233942772316145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12581192743926233141955413 73717926233942772316145)
                ·
                  rfl

theorem cell23_3876259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 9].length) (baseStart_3876259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3876259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3876259 prefixEnd_3876259 := by exact prefixLift 3876259
  have htrace : WordTrace (prefixWord ++ tailWord_3876259) baseStart_3876259 baseEnd_3876259 := by
    simpa [prefixWord, tailWord_3876259, baseEnd_3876259] using wordTrace_append hprefix tailTrace_3876259
  have hstable : (prefixWord ++ tailWord_3876259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3876259).length < 2 ^ (prefixWord ++ tailWord_3876259).sum := by decide
  have hdescent : baseEnd_3876259 < baseStart_3876259 := by decide
  rcases family_descends (prefixWord ++ tailWord_3876259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3876273 : List Nat := [1, 2, 2, 4, 1, 1, 1, 5, 1, 2, 3]
def baseStart_3876273 : Nat := 118140960795 + 3876273 * 2 ^ 59
def prefixEnd_3876273 : Nat := 4983230072969 + 3 ^ 40 * 3876273 * 2
def baseEnd_3876273 : Nat := 1990391197045617797760851

theorem tailTrace_3876273 : CollatzResearch.WordTrace tailWord_3876273 prefixEnd_3876273 1990391197045617797760851 := by
  unfold tailWord_3876273
  simp only [CollatzResearch.WordTrace]
  refine ⟨141379291085932410567825473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94252860723954940378550315 141379291085932410567825473)
  ·
    refine ⟨106034468314449307925869105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141379291085932410567825473 106034468314449307925869105)
    ·
      refine ⟨79525851235836980944401829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106034468314449307925869105 79525851235836980944401829)
      ·
        refine ⟨14911097106719433927075343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79525851235836980944401829 14911097106719433927075343)
        ·
          refine ⟨22366645660079150890613015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14911097106719433927075343 22366645660079150890613015)
          ·
            refine ⟨33549968490118726335919523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22366645660079150890613015 33549968490118726335919523)
            ·
              refine ⟨50324952735178089503879285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33549968490118726335919523 50324952735178089503879285)
              ·
                refine ⟨4717964318922945890988683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50324952735178089503879285 4717964318922945890988683)
                ·
                  refine ⟨7076946478384418836483025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4717964318922945890988683 7076946478384418836483025)
                  ·
                    refine ⟨5307709858788314127362269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7076946478384418836483025 5307709858788314127362269)
                    ·
                      refine ⟨1990391197045617797760851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5307709858788314127362269 1990391197045617797760851)
                      ·
                        rfl

theorem cell23_3876273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 5, 1, 2, 3].length) (baseStart_3876273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3876273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3876273 prefixEnd_3876273 := by exact prefixLift 3876273
  have htrace : WordTrace (prefixWord ++ tailWord_3876273) baseStart_3876273 baseEnd_3876273 := by
    simpa [prefixWord, tailWord_3876273, baseEnd_3876273] using wordTrace_append hprefix tailTrace_3876273
  have hstable : (prefixWord ++ tailWord_3876273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3876273).length < 2 ^ (prefixWord ++ tailWord_3876273).sum := by decide
  have hdescent : baseEnd_3876273 < baseStart_3876273 := by decide
  rcases family_descends (prefixWord ++ tailWord_3876273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3876346 : List Nat := [3, 1, 1, 1, 1, 2, 3, 1, 1, 6, 3]
def baseStart_3876346 : Nat := 118140960795 + 3876346 * 2 ^ 59
def prefixEnd_3876346 : Nat := 4983230072969 + 3 ^ 40 * 3876346 * 2
def baseEnd_3876346 : Nat := 1990428681133396012148015

theorem tailTrace_3876346 : CollatzResearch.WordTrace tailWord_3876346 prefixEnd_3876346 1990428681133396012148015 := by
  unfold tailWord_3876346
  simp only [CollatzResearch.WordTrace]
  refine ⟨35345488403666986008808223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94254635743111962690155261 35345488403666986008808223)
  ·
    refine ⟨53018232605500479013212335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35345488403666986008808223 53018232605500479013212335)
    ·
      refine ⟨79527348908250718519818503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53018232605500479013212335 79527348908250718519818503)
      ·
        refine ⟨119291023362376077779727755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79527348908250718519818503 119291023362376077779727755)
        ·
          refine ⟨178936535043564116669591633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119291023362376077779727755 178936535043564116669591633)
          ·
            refine ⟨134202401282673087502193725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178936535043564116669591633 134202401282673087502193725)
            ·
              refine ⟨50325900481002407813322647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134202401282673087502193725 50325900481002407813322647)
              ·
                refine ⟨75488850721503611719983971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50325900481002407813322647 75488850721503611719983971)
                ·
                  refine ⟨113233276082255417579975957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75488850721503611719983971 113233276082255417579975957)
                  ·
                    refine ⟨5307809816355722699061373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 113233276082255417579975957 5307809816355722699061373)
                    ·
                      refine ⟨1990428681133396012148015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5307809816355722699061373 1990428681133396012148015)
                      ·
                        rfl

theorem cell23_3876346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 1, 6, 3].length) (baseStart_3876346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3876346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3876346 prefixEnd_3876346 := by exact prefixLift 3876346
  have htrace : WordTrace (prefixWord ++ tailWord_3876346) baseStart_3876346 baseEnd_3876346 := by
    simpa [prefixWord, tailWord_3876346, baseEnd_3876346] using wordTrace_append hprefix tailTrace_3876346
  have hstable : (prefixWord ++ tailWord_3876346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3876346).length < 2 ^ (prefixWord ++ tailWord_3876346).sum := by decide
  have hdescent : baseEnd_3876346 < baseStart_3876346 := by decide
  rcases family_descends (prefixWord ++ tailWord_3876346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3876353 : List Nat := [1, 2, 4, 1, 4, 1, 1, 1, 2, 6]
def baseStart_3876353 : Nat := 118140960795 + 3876353 * 2 ^ 59
def prefixEnd_3876353 : Nat := 4983230072969 + 3 ^ 40 * 3876353 * 2
def baseEnd_3876353 : Nat := 663477425165992494920161

theorem tailTrace_3876353 : CollatzResearch.WordTrace tailWord_3876353 prefixEnd_3876353 663477425165992494920161 := by
  unfold tailWord_3876353
  simp only [CollatzResearch.WordTrace]
  refine ⟨141382208925642584230737713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94254805950428389487158475 141382208925642584230737713)
  ·
    refine ⟨106036656694231938173053285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141382208925642584230737713 106036656694231938173053285)
    ·
      refine ⟨19881873130168488407447491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106036656694231938173053285 19881873130168488407447491)
      ·
        refine ⟨29822809695252732611171237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19881873130168488407447491 29822809695252732611171237)
        ·
          refine ⟨5591776817859887364594607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29822809695252732611171237 5591776817859887364594607)
          ·
            refine ⟨8387665226789831046891911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5591776817859887364594607 8387665226789831046891911)
            ·
              refine ⟨12581497840184746570337867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8387665226789831046891911 12581497840184746570337867)
              ·
                refine ⟨18872246760277119855506801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12581497840184746570337867 18872246760277119855506801)
                ·
                  refine ⟨14154185070207839891630101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18872246760277119855506801 14154185070207839891630101)
                  ·
                    refine ⟨663477425165992494920161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14154185070207839891630101 663477425165992494920161)
                    ·
                      rfl

theorem cell23_3876353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 1, 2, 6].length) (baseStart_3876353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3876353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3876353 prefixEnd_3876353 := by exact prefixLift 3876353
  have htrace : WordTrace (prefixWord ++ tailWord_3876353) baseStart_3876353 baseEnd_3876353 := by
    simpa [prefixWord, tailWord_3876353, baseEnd_3876353] using wordTrace_append hprefix tailTrace_3876353
  have hstable : (prefixWord ++ tailWord_3876353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3876353).length < 2 ^ (prefixWord ++ tailWord_3876353).sum := by decide
  have hdescent : baseEnd_3876353 < baseStart_3876353 := by decide
  rcases family_descends (prefixWord ++ tailWord_3876353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3876383 : List Nat := [1, 1, 2, 4, 1, 1, 3, 5, 5]
def baseStart_3876383 : Nat := 118140960795 + 3876383 * 2 ^ 59
def prefixEnd_3876383 : Nat := 4983230072969 + 3 ^ 40 * 3876383 * 2
def baseEnd_3876383 : Nat := 221160853324179151931705

theorem tailTrace_3876383 : CollatzResearch.WordTrace tailWord_3876383 prefixEnd_3876383 221160853324179151931705 := by
  unfold tailWord_3876383
  simp only [CollatzResearch.WordTrace]
  refine ⟨141383303115533899354329803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94255535410355932902886535 141383303115533899354329803)
  ·
    refine ⟨212074954673300849031494705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141383303115533899354329803 212074954673300849031494705)
    ·
      refine ⟨159056216004975636773621029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212074954673300849031494705 159056216004975636773621029)
      ·
        refine ⟨29823040500932931895053943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 159056216004975636773621029 29823040500932931895053943)
        ·
          refine ⟨44734560751399397842580915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29823040500932931895053943 44734560751399397842580915)
          ·
            refine ⟨67101841127099096763871373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44734560751399397842580915 67101841127099096763871373)
            ·
              refine ⟨25163190422662161286451765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67101841127099096763871373 25163190422662161286451765)
              ·
                refine ⟨2359049102124577620604853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25163190422662161286451765 2359049102124577620604853)
                ·
                  refine ⟨221160853324179151931705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2359049102124577620604853 221160853324179151931705)
                  ·
                    rfl

theorem cell23_3876383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 5, 5].length) (baseStart_3876383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3876383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3876383 prefixEnd_3876383 := by exact prefixLift 3876383
  have htrace : WordTrace (prefixWord ++ tailWord_3876383) baseStart_3876383 baseEnd_3876383 := by
    simpa [prefixWord, tailWord_3876383, baseEnd_3876383] using wordTrace_append hprefix tailTrace_3876383
  have hstable : (prefixWord ++ tailWord_3876383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3876383).length < 2 ^ (prefixWord ++ tailWord_3876383).sum := by decide
  have hdescent : baseEnd_3876383 < baseStart_3876383 := by decide
  rcases family_descends (prefixWord ++ tailWord_3876383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3876426 : List Nat := [3, 1, 2, 1, 1, 3, 1, 1, 2, 8]
def baseStart_3876426 : Nat := 118140960795 + 3876426 * 2 ^ 59
def prefixEnd_3876426 : Nat := 4983230072969 + 3 ^ 40 * 3876426 * 2
def baseEnd_3876426 : Nat := 663489919861918566382549

theorem tailTrace_3876426 : CollatzResearch.WordTrace tailWord_3876426 prefixEnd_3876426 663489919861918566382549 := by
  unfold tailWord_3876426
  simp only [CollatzResearch.WordTrace]
  refine ⟨35346217863594529424536283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94256580969585411798763421 35346217863594529424536283)
  ·
    refine ⟨53019326795391794136804425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35346217863594529424536283 53019326795391794136804425)
    ·
      refine ⟨39764495096543845602603319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53019326795391794136804425 39764495096543845602603319)
      ·
        refine ⟨59646742644815768403904979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39764495096543845602603319 59646742644815768403904979)
        ·
          refine ⟨89470113967223652605857469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59646742644815768403904979 89470113967223652605857469)
          ·
            refine ⟨33551292737708869727196551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 89470113967223652605857469 33551292737708869727196551)
            ·
              refine ⟨50326939106563304590794827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33551292737708869727196551 50326939106563304590794827)
              ·
                refine ⟨75490408659844956886192241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50326939106563304590794827 75490408659844956886192241)
                ·
                  refine ⟨56617806494883717664644181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75490408659844956886192241 56617806494883717664644181)
                  ·
                    refine ⟨663489919861918566382549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 56617806494883717664644181 663489919861918566382549)
                    ·
                      rfl

theorem cell23_3876426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 2, 8].length) (baseStart_3876426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3876426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3876426 prefixEnd_3876426 := by exact prefixLift 3876426
  have htrace : WordTrace (prefixWord ++ tailWord_3876426) baseStart_3876426 baseEnd_3876426 := by
    simpa [prefixWord, tailWord_3876426, baseEnd_3876426] using wordTrace_append hprefix tailTrace_3876426
  have hstable : (prefixWord ++ tailWord_3876426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3876426).length < 2 ^ (prefixWord ++ tailWord_3876426).sum := by decide
  have hdescent : baseEnd_3876426 < baseStart_3876426 := by decide
  rcases family_descends (prefixWord ++ tailWord_3876426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3876433 : List Nat := [1, 2, 2, 1, 3, 2, 2, 3, 2, 1, 4]
def baseStart_3876433 : Nat := 118140960795 + 3876433 * 2 ^ 59
def prefixEnd_3876433 : Nat := 4983230072969 + 3 ^ 40 * 3876433 * 2
def baseEnd_3876433 : Nat := 1990473353950337171760115

theorem tailTrace_3876433 : CollatzResearch.WordTrace tailWord_3876433 prefixEnd_3876433 1990473353950337171760115 := by
  unfold tailWord_3876433
  simp only [CollatzResearch.WordTrace]
  refine ⟨141385126765352757893649953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94256751176901838595766635 141385126765352757893649953)
  ·
    refine ⟨106038845074014568420237465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141385126765352757893649953 106038845074014568420237465)
    ·
      refine ⟨79529133805510926315178099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106038845074014568420237465 79529133805510926315178099)
      ·
        refine ⟨119293700708266389472767149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79529133805510926315178099 119293700708266389472767149)
        ·
          refine ⟨44735137765599896052287681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119293700708266389472767149 44735137765599896052287681)
          ·
            refine ⟨33551353324199922039215761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44735137765599896052287681 33551353324199922039215761)
            ·
              refine ⟨25163514993149941529411821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33551353324199922039215761 25163514993149941529411821)
              ·
                refine ⟨9436318122431228073529433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25163514993149941529411821 9436318122431228073529433)
                ·
                  refine ⟨7077238591823421055147075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9436318122431228073529433 7077238591823421055147075)
                  ·
                    refine ⟨10615857887735131582720613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7077238591823421055147075 10615857887735131582720613)
                    ·
                      refine ⟨1990473353950337171760115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10615857887735131582720613 1990473353950337171760115)
                      ·
                        rfl

theorem cell23_3876433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 3, 2, 1, 4].length) (baseStart_3876433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3876433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3876433 prefixEnd_3876433 := by exact prefixLift 3876433
  have htrace : WordTrace (prefixWord ++ tailWord_3876433) baseStart_3876433 baseEnd_3876433 := by
    simpa [prefixWord, tailWord_3876433, baseEnd_3876433] using wordTrace_append hprefix tailTrace_3876433
  have hstable : (prefixWord ++ tailWord_3876433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3876433).length < 2 ^ (prefixWord ++ tailWord_3876433).sum := by decide
  have hdescent : baseEnd_3876433 < baseStart_3876433 := by decide
  rcases family_descends (prefixWord ++ tailWord_3876433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3876473 : List Nat := [1, 2, 1, 3, 3, 1, 3, 3, 6]
def baseStart_3876473 : Nat := 118140960795 + 3876473 * 2 ^ 59
def prefixEnd_3876473 : Nat := 4983230072969 + 3 ^ 40 * 3876473 * 2
def baseEnd_3876473 : Nat := 221165988130724112806659

theorem tailTrace_3876473 : CollatzResearch.WordTrace tailWord_3876473 prefixEnd_3876473 221165988130724112806659 := by
  unfold tailWord_3876473
  simp only [CollatzResearch.WordTrace]
  refine ⟨141386585685207844725106073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94257723790138563150070715 141386585685207844725106073)
  ·
    refine ⟨106039939263905883543829555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141386585685207844725106073 106039939263905883543829555)
    ·
      refine ⟨159059908895858825315744333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106039939263905883543829555 159059908895858825315744333)
      ·
        refine ⟨59647465835947059493404125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159059908895858825315744333 59647465835947059493404125)
        ·
          refine ⟨22367799688480147310026547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59647465835947059493404125 22367799688480147310026547)
          ·
            refine ⟨33551699532720220965039821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22367799688480147310026547 33551699532720220965039821)
            ·
              refine ⟨12581887324770082861889933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33551699532720220965039821 12581887324770082861889933)
              ·
                refine ⟨4718207746788781073208725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12581887324770082861889933 4718207746788781073208725)
                ·
                  refine ⟨221165988130724112806659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4718207746788781073208725 221165988130724112806659)
                  ·
                    rfl

theorem cell23_3876473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 3, 6].length) (baseStart_3876473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3876473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3876473 prefixEnd_3876473 := by exact prefixLift 3876473
  have htrace : WordTrace (prefixWord ++ tailWord_3876473) baseStart_3876473 baseEnd_3876473 := by
    simpa [prefixWord, tailWord_3876473, baseEnd_3876473] using wordTrace_append hprefix tailTrace_3876473
  have hstable : (prefixWord ++ tailWord_3876473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3876473).length < 2 ^ (prefixWord ++ tailWord_3876473).sum := by decide
  have hdescent : baseEnd_3876473 < baseStart_3876473 := by decide
  rcases family_descends (prefixWord ++ tailWord_3876473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3876496 : List Nat := [2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 7]
def baseStart_3876496 : Nat := 118140960795 + 3876496 * 2 ^ 59
def prefixEnd_3876496 : Nat := 4983230072969 + 3 ^ 40 * 3876496 * 2
def baseEnd_3876496 : Nat := 1990505703231570425272325

theorem tailTrace_3876496 : CollatzResearch.WordTrace tailWord_3876496 prefixEnd_3876496 1990505703231570425272325 := by
  unfold tailWord_3876496
  simp only [CollatzResearch.WordTrace]
  refine ⟨70693712282062259826596671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94258283042749679768795561 70693712282062259826596671)
  ·
    refine ⟨106040568423093389739895007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70693712282062259826596671 106040568423093389739895007)
    ·
      refine ⟨159060852634640084609842511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106040568423093389739895007 159060852634640084609842511)
      ·
        refine ⟨238591278951960126914763767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159060852634640084609842511 238591278951960126914763767)
        ·
          refine ⟨357886918427940190372145651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238591278951960126914763767 357886918427940190372145651)
          ·
            refine ⟨536830377641910285558218477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 357886918427940190372145651 536830377641910285558218477)
            ·
              refine ⟨201311391615716357084331929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 536830377641910285558218477 201311391615716357084331929)
              ·
                refine ⟨150983543711787267813248947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 201311391615716357084331929 150983543711787267813248947)
                ·
                  refine ⟨226475315567680901719873421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 150983543711787267813248947 226475315567680901719873421)
                  ·
                    refine ⟨84928243337880338144952533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 226475315567680901719873421 84928243337880338144952533)
                    ·
                      refine ⟨1990505703231570425272325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 84928243337880338144952533 1990505703231570425272325)
                      ·
                        rfl

theorem cell23_3876496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 7].length) (baseStart_3876496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3876496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3876496 prefixEnd_3876496 := by exact prefixLift 3876496
  have htrace : WordTrace (prefixWord ++ tailWord_3876496) baseStart_3876496 baseEnd_3876496 := by
    simpa [prefixWord, tailWord_3876496, baseEnd_3876496] using wordTrace_append hprefix tailTrace_3876496
  have hstable : (prefixWord ++ tailWord_3876496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3876496).length < 2 ^ (prefixWord ++ tailWord_3876496).sum := by decide
  have hdescent : baseEnd_3876496 < baseStart_3876496 := by decide
  rcases family_descends (prefixWord ++ tailWord_3876496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3876534 : List Nat := [5, 1, 3, 1, 1, 1, 1, 1, 5, 1, 3]
def baseStart_3876534 : Nat := 118140960795 + 3876534 * 2 ^ 59
def prefixEnd_3876534 : Nat := 4983230072969 + 3 ^ 40 * 3876534 * 2
def baseEnd_3876534 : Nat := 1990525215496441276597151

theorem tailTrace_3876534 : CollatzResearch.WordTrace tailWord_3876534 prefixEnd_3876534 1990525215496441276597151 := by
  unfold tailWord_3876534
  simp only [CollatzResearch.WordTrace]
  refine ⟨8836800658624178258942291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 94259207025324568095384437 8836800658624178258942291)
  ·
    refine ⟨13255200987936267388413437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8836800658624178258942291 13255200987936267388413437)
    ·
      refine ⟨4970700370476100270655039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13255200987936267388413437 4970700370476100270655039)
      ·
        refine ⟨7456050555714150405982559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4970700370476100270655039 7456050555714150405982559)
        ·
          refine ⟨11184075833571225608973839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7456050555714150405982559 11184075833571225608973839)
          ·
            refine ⟨16776113750356838413460759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11184075833571225608973839 16776113750356838413460759)
            ·
              refine ⟨25164170625535257620191139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16776113750356838413460759 25164170625535257620191139)
              ·
                refine ⟨37746255938302886430286709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25164170625535257620191139 37746255938302886430286709)
                ·
                  refine ⟨3538711494215895602839379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37746255938302886430286709 3538711494215895602839379)
                  ·
                    refine ⟨5308067241323843404259069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3538711494215895602839379 5308067241323843404259069)
                    ·
                      refine ⟨1990525215496441276597151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5308067241323843404259069 1990525215496441276597151)
                      ·
                        rfl

theorem cell23_3876534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_3876534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3876534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3876534 prefixEnd_3876534 := by exact prefixLift 3876534
  have htrace : WordTrace (prefixWord ++ tailWord_3876534) baseStart_3876534 baseEnd_3876534 := by
    simpa [prefixWord, tailWord_3876534, baseEnd_3876534] using wordTrace_append hprefix tailTrace_3876534
  have hstable : (prefixWord ++ tailWord_3876534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3876534).length < 2 ^ (prefixWord ++ tailWord_3876534).sum := by decide
  have hdescent : baseEnd_3876534 < baseStart_3876534 := by decide
  rcases family_descends (prefixWord ++ tailWord_3876534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3876540 : List Nat := [2, 2, 2, 3, 1, 2, 2, 1, 3, 1, 4]
def baseStart_3876540 : Nat := 118140960795 + 3876540 * 2 ^ 59
def prefixEnd_3876540 : Nat := 4983230072969 + 3 ^ 40 * 3876540 * 2
def baseEnd_3876540 : Nat := 1990528296380368253122123

theorem tailTrace_3876540 : CollatzResearch.WordTrace tailWord_3876540 prefixEnd_3876540 1990528296380368253122123 := by
  unfold tailWord_3876540
  simp only [CollatzResearch.WordTrace]
  refine ⟨70694514687982557583897537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94259352917310076778530049 70694514687982557583897537)
  ·
    refine ⟨53020886015986918187923153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70694514687982557583897537 53020886015986918187923153)
    ·
      refine ⟨39765664511990188640942365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53020886015986918187923153 39765664511990188640942365)
      ·
        refine ⟨14912124191996320740353387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39765664511990188640942365 14912124191996320740353387)
        ·
          refine ⟨22368186287994481110530081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14912124191996320740353387 22368186287994481110530081)
          ·
            refine ⟨16776139715995860832897561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22368186287994481110530081 16776139715995860832897561)
            ·
              refine ⟨12582104786996895624673171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16776139715995860832897561 12582104786996895624673171)
              ·
                refine ⟨18873157180495343437009757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12582104786996895624673171 18873157180495343437009757)
                ·
                  refine ⟨7077433942685753788878659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18873157180495343437009757 7077433942685753788878659)
                  ·
                    refine ⟨10616150914028630683317989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7077433942685753788878659 10616150914028630683317989)
                    ·
                      refine ⟨1990528296380368253122123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10616150914028630683317989 1990528296380368253122123)
                      ·
                        rfl

theorem cell23_3876540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_3876540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3876540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3876540 prefixEnd_3876540 := by exact prefixLift 3876540
  have htrace : WordTrace (prefixWord ++ tailWord_3876540) baseStart_3876540 baseEnd_3876540 := by
    simpa [prefixWord, tailWord_3876540, baseEnd_3876540] using wordTrace_append hprefix tailTrace_3876540
  have hstable : (prefixWord ++ tailWord_3876540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3876540).length < 2 ^ (prefixWord ++ tailWord_3876540).sum := by decide
  have hdescent : baseEnd_3876540 < baseStart_3876540 := by decide
  rcases family_descends (prefixWord ++ tailWord_3876540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3876554 : List Nat := [3, 1, 2, 1, 5, 2, 2, 1, 1, 5]
def baseStart_3876554 : Nat := 118140960795 + 3876554 * 2 ^ 59
def prefixEnd_3876554 : Nat := 4983230072969 + 3 ^ 40 * 3876554 * 2
def baseEnd_3876554 : Nat := 663511828369843732782353

theorem tailTrace_3876554 : CollatzResearch.WordTrace tailWord_3876554 prefixEnd_3876554 663511828369843732782353 := by
  unfold tailWord_3876554
  simp only [CollatzResearch.WordTrace]
  refine ⟨35347384999478598889701179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94259693331942930372536477 35347384999478598889701179)
  ·
    refine ⟨53021077499217898334551769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35347384999478598889701179 53021077499217898334551769)
    ·
      refine ⟨39765808124413423750913827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53021077499217898334551769 39765808124413423750913827)
      ·
        refine ⟨59648712186620135626370741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39765808124413423750913827 59648712186620135626370741)
        ·
          refine ⟨5592066767495637714972257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 59648712186620135626370741 5592066767495637714972257)
          ·
            refine ⟨4194050075621728286229193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5592066767495637714972257 4194050075621728286229193)
            ·
              refine ⟨3145537556716296214671895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4194050075621728286229193 3145537556716296214671895)
              ·
                refine ⟨4718306335074444322007843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3145537556716296214671895 4718306335074444322007843)
                ·
                  refine ⟨7077459502611666483011765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4718306335074444322007843 7077459502611666483011765)
                  ·
                    refine ⟨663511828369843732782353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7077459502611666483011765 663511828369843732782353)
                    ·
                      rfl

theorem cell23_3876554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 2, 1, 1, 5].length) (baseStart_3876554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3876554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3876554 prefixEnd_3876554 := by exact prefixLift 3876554
  have htrace : WordTrace (prefixWord ++ tailWord_3876554) baseStart_3876554 baseEnd_3876554 := by
    simpa [prefixWord, tailWord_3876554, baseEnd_3876554] using wordTrace_append hprefix tailTrace_3876554
  have hstable : (prefixWord ++ tailWord_3876554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3876554).length < 2 ^ (prefixWord ++ tailWord_3876554).sum := by decide
  have hdescent : baseEnd_3876554 < baseStart_3876554 := by decide
  rcases family_descends (prefixWord ++ tailWord_3876554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3876584 : List Nat := [2, 1, 4, 1, 3, 2, 3, 1, 2, 4]
def baseStart_3876584 : Nat := 118140960795 + 3876584 * 2 ^ 59
def prefixEnd_3876584 : Nat := 4983230072969 + 3 ^ 40 * 3876584 * 2
def baseEnd_3876584 : Nat := 663516963176388693657307

theorem tailTrace_3876584 : CollatzResearch.WordTrace tailWord_3876584 prefixEnd_3876584 663516963176388693657307 := by
  unfold tailWord_3876584
  simp only [CollatzResearch.WordTrace]
  refine ⟨70695317093902855341198403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94260422791870473788264537 70695317093902855341198403)
  ·
    refine ⟨106042975640854283011797605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70695317093902855341198403 106042975640854283011797605)
    ·
      refine ⟨19883057932660178064712051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106042975640854283011797605 19883057932660178064712051)
      ·
        refine ⟨29824586898990267097068077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19883057932660178064712051 29824586898990267097068077)
        ·
          refine ⟨11184220087121350161400529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29824586898990267097068077 11184220087121350161400529)
          ·
            refine ⟨8388165065341012621050397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11184220087121350161400529 8388165065341012621050397)
            ·
              refine ⟨3145561899502879732893899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8388165065341012621050397 3145561899502879732893899)
              ·
                refine ⟨4718342849254319599340849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3145561899502879732893899 4718342849254319599340849)
                ·
                  refine ⟨3538757136940739699505637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4718342849254319599340849 3538757136940739699505637)
                  ·
                    refine ⟨663516963176388693657307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3538757136940739699505637 663516963176388693657307)
                    ·
                      rfl

theorem cell23_3876584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 3, 1, 2, 4].length) (baseStart_3876584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3876584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3876584 prefixEnd_3876584 := by exact prefixLift 3876584
  have htrace : WordTrace (prefixWord ++ tailWord_3876584) baseStart_3876584 baseEnd_3876584 := by
    simpa [prefixWord, tailWord_3876584, baseEnd_3876584] using wordTrace_append hprefix tailTrace_3876584
  have hstable : (prefixWord ++ tailWord_3876584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3876584).length < 2 ^ (prefixWord ++ tailWord_3876584).sum := by decide
  have hdescent : baseEnd_3876584 < baseStart_3876584 := by decide
  rcases family_descends (prefixWord ++ tailWord_3876584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3876613 : List Nat := [1, 3, 1, 1, 2, 1, 1, 1, 3, 5, 4]
def baseStart_3876613 : Nat := 118140960795 + 3876613 * 2 ^ 59
def prefixEnd_3876613 : Nat := 4983230072969 + 3 ^ 40 * 3876613 * 2
def baseEnd_3876613 : Nat := 1990565780468146467509287

theorem tailTrace_3876613 : CollatzResearch.WordTrace tailWord_3876613 prefixEnd_3876613 1990565780468146467509287 := by
  unfold tailWord_3876613
  simp only [CollatzResearch.WordTrace]
  refine ⟨141391691904700648635202493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94261127936467099090134995 141391691904700648635202493)
  ·
    refine ⟨53021884464262743238200935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141391691904700648635202493 53021884464262743238200935)
    ·
      refine ⟨79532826696394114857301403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53021884464262743238200935 79532826696394114857301403)
      ·
        refine ⟨119299240044591172285952105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79532826696394114857301403 119299240044591172285952105)
        ·
          refine ⟨89474430033443379214464079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119299240044591172285952105 89474430033443379214464079)
          ·
            refine ⟨134211645050165068821696119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89474430033443379214464079 134211645050165068821696119)
            ·
              refine ⟨201317467575247603232544179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134211645050165068821696119 201317467575247603232544179)
              ·
                refine ⟨301976201362871404848816269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 201317467575247603232544179 301976201362871404848816269)
                ·
                  refine ⟨113241075511076776818306101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 301976201362871404848816269 113241075511076776818306101)
                  ·
                    refine ⟨10616350829163447826716197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 113241075511076776818306101 10616350829163447826716197)
                    ·
                      refine ⟨1990565780468146467509287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10616350829163447826716197 1990565780468146467509287)
                      ·
                        rfl

theorem cell23_3876613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 5, 4].length) (baseStart_3876613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3876613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3876613 prefixEnd_3876613 := by exact prefixLift 3876613
  have htrace : WordTrace (prefixWord ++ tailWord_3876613) baseStart_3876613 baseEnd_3876613 := by
    simpa [prefixWord, tailWord_3876613, baseEnd_3876613] using wordTrace_append hprefix tailTrace_3876613
  have hstable : (prefixWord ++ tailWord_3876613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3876613).length < 2 ^ (prefixWord ++ tailWord_3876613).sum := by decide
  have hdescent : baseEnd_3876613 < baseStart_3876613 := by decide
  rcases family_descends (prefixWord ++ tailWord_3876613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3876623 : List Nat := [1, 1, 2, 1, 1, 1, 4, 4, 2, 6]
def baseStart_3876623 : Nat := 118140960795 + 3876623 * 2 ^ 59
def prefixEnd_3876623 : Nat := 4983230072969 + 3 ^ 40 * 3876623 * 2
def baseEnd_3876623 : Nat := 663523638424897142794747

theorem tailTrace_3876623 : CollatzResearch.WordTrace tailWord_3876623 prefixEnd_3876623 663523638424897142794747 := by
  unfold tailWord_3876623
  simp only [CollatzResearch.WordTrace]
  refine ⟨141392056634664420343066523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94261371089776280228711015 141392056634664420343066523)
  ·
    refine ⟨212088084951996630514599785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141392056634664420343066523 212088084951996630514599785)
    ·
      refine ⟨159066063713997472885949839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212088084951996630514599785 159066063713997472885949839)
      ·
        refine ⟨238599095570996209328924759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159066063713997472885949839 238599095570996209328924759)
        ·
          refine ⟨357898643356494313993387139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238599095570996209328924759 357898643356494313993387139)
          ·
            refine ⟨536847965034741470990080709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 357898643356494313993387139 536847965034741470990080709)
            ·
              refine ⟨100658993444014025810640133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 536847965034741470990080709 100658993444014025810640133)
              ·
                refine ⟨18873561270752629839495025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100658993444014025810640133 18873561270752629839495025)
                ·
                  refine ⟨14155170953064472379621269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18873561270752629839495025 14155170953064472379621269)
                  ·
                    refine ⟨663523638424897142794747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14155170953064472379621269 663523638424897142794747)
                    ·
                      rfl

theorem cell23_3876623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 4, 2, 6].length) (baseStart_3876623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3876623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3876623 prefixEnd_3876623 := by exact prefixLift 3876623
  have htrace : WordTrace (prefixWord ++ tailWord_3876623) baseStart_3876623 baseEnd_3876623 := by
    simpa [prefixWord, tailWord_3876623, baseEnd_3876623] using wordTrace_append hprefix tailTrace_3876623
  have hstable : (prefixWord ++ tailWord_3876623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3876623).length < 2 ^ (prefixWord ++ tailWord_3876623).sum := by decide
  have hdescent : baseEnd_3876623 < baseStart_3876623 := by decide
  rcases family_descends (prefixWord ++ tailWord_3876623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3876641 : List Nat := [1, 2, 3, 2, 1, 5, 2, 1, 2, 1, 3]
def baseStart_3876641 : Nat := 118140960795 + 3876641 * 2 ^ 59
def prefixEnd_3876641 : Nat := 4983230072969 + 3 ^ 40 * 3876641 * 2
def baseEnd_3876641 : Nat := 1990580157926472357959159

theorem tailTrace_3876641 : CollatzResearch.WordTrace tailWord_3876641 prefixEnd_3876641 1990580157926472357959159 := by
  unfold tailWord_3876641
  simp only [CollatzResearch.WordTrace]
  refine ⟨141392713148599209417221777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94261808765732806278147851 141392713148599209417221777)
  ·
    refine ⟨106044534861449407062916333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141392713148599209417221777 106044534861449407062916333)
    ·
      refine ⟨39766700573043527648593625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106044534861449407062916333 39766700573043527648593625)
      ·
        refine ⟨29825025429782645736445219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39766700573043527648593625 29825025429782645736445219)
        ·
          refine ⟨44737538144673968604667829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29825025429782645736445219 44737538144673968604667829)
          ·
            refine ⟨4194144201063184556687609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 44737538144673968604667829 4194144201063184556687609)
            ·
              refine ⟨3145608150797388417515707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4194144201063184556687609 3145608150797388417515707)
              ·
                refine ⟨4718412226196082626273561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3145608150797388417515707 4718412226196082626273561)
                ·
                  refine ⟨3538809169647061969705171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4718412226196082626273561 3538809169647061969705171)
                  ·
                    refine ⟨5308213754470592954557757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3538809169647061969705171 5308213754470592954557757)
                    ·
                      refine ⟨1990580157926472357959159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5308213754470592954557757 1990580157926472357959159)
                      ·
                        rfl

theorem cell23_3876641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 2, 1, 2, 1, 3].length) (baseStart_3876641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3876641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3876641 prefixEnd_3876641 := by exact prefixLift 3876641
  have htrace : WordTrace (prefixWord ++ tailWord_3876641) baseStart_3876641 baseEnd_3876641 := by
    simpa [prefixWord, tailWord_3876641, baseEnd_3876641] using wordTrace_append hprefix tailTrace_3876641
  have hstable : (prefixWord ++ tailWord_3876641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3876641).length < 2 ^ (prefixWord ++ tailWord_3876641).sum := by decide
  have hdescent : baseEnd_3876641 < baseStart_3876641 := by decide
  rcases family_descends (prefixWord ++ tailWord_3876641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3876663 : List Nat := [1, 1, 3, 1, 2, 1, 2, 2, 1, 2, 7]
def baseStart_3876663 : Nat := 118140960795 + 3876663 * 2 ^ 59
def prefixEnd_3876663 : Nat := 4983230072969 + 3 ^ 40 * 3876663 * 2
def baseEnd_3876663 : Nat := 1990591454500871271884057

theorem tailTrace_3876663 : CollatzResearch.WordTrace tailWord_3876663 prefixEnd_3876663 1990591454500871271884057 := by
  unfold tailWord_3876663
  simp only [CollatzResearch.WordTrace]
  refine ⟨141393515554519507174522643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94262343703013004783015095 141393515554519507174522643)
  ·
    refine ⟨212090273331779260761783965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141393515554519507174522643 212090273331779260761783965)
    ·
      refine ⟨79533852499417222785668987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212090273331779260761783965 79533852499417222785668987)
      ·
        refine ⟨119300778749125834178503481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79533852499417222785668987 119300778749125834178503481)
        ·
          refine ⟨89475584061844375633877611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119300778749125834178503481 89475584061844375633877611)
          ·
            refine ⟨134213376092766563450816417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89475584061844375633877611 134213376092766563450816417)
            ·
              refine ⟨100660032069574922588112313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134213376092766563450816417 100660032069574922588112313)
              ·
                refine ⟨75495024052181191941084235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 100660032069574922588112313 75495024052181191941084235)
                ·
                  refine ⟨113242536078271787911626353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75495024052181191941084235 113242536078271787911626353)
                  ·
                    refine ⟨84931902058703840933719765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 113242536078271787911626353 84931902058703840933719765)
                    ·
                      refine ⟨1990591454500871271884057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 84931902058703840933719765 1990591454500871271884057)
                      ·
                        rfl

theorem cell23_3876663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 2, 7].length) (baseStart_3876663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3876663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3876663 prefixEnd_3876663 := by exact prefixLift 3876663
  have htrace : WordTrace (prefixWord ++ tailWord_3876663) baseStart_3876663 baseEnd_3876663 := by
    simpa [prefixWord, tailWord_3876663, baseEnd_3876663] using wordTrace_append hprefix tailTrace_3876663
  have hstable : (prefixWord ++ tailWord_3876663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3876663).length < 2 ^ (prefixWord ++ tailWord_3876663).sum := by decide
  have hdescent : baseEnd_3876663 < baseStart_3876663 := by decide
  rcases family_descends (prefixWord ++ tailWord_3876663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3876717 : List Nat := [1, 5, 1, 1, 1, 1, 5, 1, 2, 5]
def baseStart_3876717 : Nat := 118140960795 + 3876717 * 2 ^ 59
def prefixEnd_3876717 : Nat := 4983230072969 + 3 ^ 40 * 3876717 * 2
def baseEnd_3876717 : Nat := 663539727485404686869603

theorem tailTrace_3876717 : CollatzResearch.WordTrace tailWord_3876717 prefixEnd_3876717 663539727485404686869603 := by
  unfold tailWord_3876717
  simp only [CollatzResearch.WordTrace]
  refine ⟨141395485096323874396988405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94263656730882582931325603 141395485096323874396988405)
  ·
    refine ⟨13255826727780363224717663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 141395485096323874396988405 13255826727780363224717663)
    ·
      refine ⟨19883740091670544837076495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13255826727780363224717663 19883740091670544837076495)
      ·
        refine ⟨29825610137505817255614743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19883740091670544837076495 29825610137505817255614743)
        ·
          refine ⟨44738415206258725883422115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29825610137505817255614743 44738415206258725883422115)
          ·
            refine ⟨67107622809388088825133173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44738415206258725883422115 67107622809388088825133173)
            ·
              refine ⟨6291339638380133327356235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67107622809388088825133173 6291339638380133327356235)
              ·
                refine ⟨9437009457570199991034353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6291339638380133327356235 9437009457570199991034353)
                ·
                  refine ⟨7077757093177649993275765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9437009457570199991034353 7077757093177649993275765)
                  ·
                    refine ⟨663539727485404686869603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7077757093177649993275765 663539727485404686869603)
                    ·
                      rfl

theorem cell23_3876717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 5, 1, 2, 5].length) (baseStart_3876717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3876717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3876717 prefixEnd_3876717 := by exact prefixLift 3876717
  have htrace : WordTrace (prefixWord ++ tailWord_3876717) baseStart_3876717 baseEnd_3876717 := by
    simpa [prefixWord, tailWord_3876717, baseEnd_3876717] using wordTrace_append hprefix tailTrace_3876717
  have hstable : (prefixWord ++ tailWord_3876717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3876717).length < 2 ^ (prefixWord ++ tailWord_3876717).sum := by decide
  have hdescent : baseEnd_3876717 < baseStart_3876717 := by decide
  rcases family_descends (prefixWord ++ tailWord_3876717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3876740 : List Nat := [2, 3, 2, 1, 1, 1, 2, 1, 2, 3, 5]
def baseStart_3876740 : Nat := 118140960795 + 3876740 * 2 ^ 59
def prefixEnd_3876740 : Nat := 4983230072969 + 3 ^ 40 * 3876740 * 2
def baseEnd_3876740 : Nat := 1990630992511267470621203

theorem tailTrace_3876740 : CollatzResearch.WordTrace tailWord_3876740 prefixEnd_3876740 1990630992511267470621203 := by
  unfold tailWord_3876740
  simp only [CollatzResearch.WordTrace]
  refine ⟨70698161987620274662537837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94264215983493699550050449 70698161987620274662537837)
  ·
    refine ⟨26511810745357602998451689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70698161987620274662537837 26511810745357602998451689)
    ·
      refine ⟨19883858059018202248838767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26511810745357602998451689 19883858059018202248838767)
      ·
        refine ⟨29825787088527303373258151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19883858059018202248838767 29825787088527303373258151)
        ·
          refine ⟨44738680632790955059887227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29825787088527303373258151 44738680632790955059887227)
          ·
            refine ⟨67108020949186432589830841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44738680632790955059887227 67108020949186432589830841)
            ·
              refine ⟨50331015711889824442373131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67108020949186432589830841 50331015711889824442373131)
              ·
                refine ⟨75496523567834736663559697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50331015711889824442373131 75496523567834736663559697)
                ·
                  refine ⟨56622392675876052497669773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 75496523567834736663559697 56622392675876052497669773)
                  ·
                    refine ⟨21233397253453519686626165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56622392675876052497669773 21233397253453519686626165)
                    ·
                      refine ⟨1990630992511267470621203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21233397253453519686626165 1990630992511267470621203)
                      ·
                        rfl

theorem cell23_3876740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 2, 3, 5].length) (baseStart_3876740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3876740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3876740 prefixEnd_3876740 := by exact prefixLift 3876740
  have htrace : WordTrace (prefixWord ++ tailWord_3876740) baseStart_3876740 baseEnd_3876740 := by
    simpa [prefixWord, tailWord_3876740, baseEnd_3876740] using wordTrace_append hprefix tailTrace_3876740
  have hstable : (prefixWord ++ tailWord_3876740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3876740).length < 2 ^ (prefixWord ++ tailWord_3876740).sum := by decide
  have hdescent : baseEnd_3876740 < baseStart_3876740 := by decide
  rcases family_descends (prefixWord ++ tailWord_3876740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3876764 : List Nat := [2, 2, 3, 3, 1, 1, 2, 2, 3, 4]
def baseStart_3876764 : Nat := 118140960795 + 3876764 * 2 ^ 59
def prefixEnd_3876764 : Nat := 4983230072969 + 3 ^ 40 * 3876764 * 2
def baseEnd_3876764 : Nat := 663547772015658458907031

theorem tailTrace_3876764 : CollatzResearch.WordTrace tailWord_3876764 prefixEnd_3876764 663547772015658458907031 := by
  unfold tailWord_3876764
  simp only [CollatzResearch.WordTrace]
  refine ⟨70698599663576800711974673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94264799551435734282632897 70698599663576800711974673)
  ·
    refine ⟨53023949747682600533981005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70698599663576800711974673 53023949747682600533981005)
    ·
      refine ⟨19883981155380975200242877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53023949747682600533981005 19883981155380975200242877)
      ·
        refine ⟨7456492933267865700091079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19883981155380975200242877 7456492933267865700091079)
        ·
          refine ⟨11184739399901798550136619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7456492933267865700091079 11184739399901798550136619)
          ·
            refine ⟨16777109099852697825204929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11184739399901798550136619 16777109099852697825204929)
            ·
              refine ⟨12582831824889523368903697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16777109099852697825204929 12582831824889523368903697)
              ·
                refine ⟨9437123868667142526677773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12582831824889523368903697 9437123868667142526677773)
                ·
                  refine ⟨3538921450750178447504165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9437123868667142526677773 3538921450750178447504165)
                  ·
                    refine ⟨663547772015658458907031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3538921450750178447504165 663547772015658458907031)
                    ·
                      rfl

theorem cell23_3876764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 2, 3, 4].length) (baseStart_3876764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3876764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3876764 prefixEnd_3876764 := by exact prefixLift 3876764
  have htrace : WordTrace (prefixWord ++ tailWord_3876764) baseStart_3876764 baseEnd_3876764 := by
    simpa [prefixWord, tailWord_3876764, baseEnd_3876764] using wordTrace_append hprefix tailTrace_3876764
  have hstable : (prefixWord ++ tailWord_3876764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3876764).length < 2 ^ (prefixWord ++ tailWord_3876764).sum := by decide
  have hdescent : baseEnd_3876764 < baseStart_3876764 := by decide
  rcases family_descends (prefixWord ++ tailWord_3876764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3876798 : List Nat := [4, 2, 1, 1, 1, 4, 3, 2, 1, 4]
def baseStart_3876798 : Nat := 118140960795 + 3876798 * 2 ^ 59
def prefixEnd_3876798 : Nat := 4983230072969 + 3 ^ 40 * 3876798 * 2
def baseEnd_3876798 : Nat := 663553591463076081231979

theorem tailTrace_3876798 : CollatzResearch.WordTrace tailWord_3876798 prefixEnd_3876798 663553591463076081231979 := by
  unfold tailWord_3876798
  simp only [CollatzResearch.WordTrace]
  refine ⟨17674804926128803153835881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94265626272686950153791365 17674804926128803153835881)
  ·
    refine ⟨13256103694596602365376911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17674804926128803153835881 13256103694596602365376911)
    ·
      refine ⟨19884155541894903548065367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13256103694596602365376911 19884155541894903548065367)
      ·
        refine ⟨29826233312842355322098051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19884155541894903548065367 29826233312842355322098051)
        ·
          refine ⟨44739349969263532983147077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29826233312842355322098051 44739349969263532983147077)
          ·
            refine ⟨8388628119236912434340077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44739349969263532983147077 8388628119236912434340077)
            ·
              refine ⟨3145735544713842162877529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8388628119236912434340077 3145735544713842162877529)
              ·
                refine ⟨2359301658535381622158147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3145735544713842162877529 2359301658535381622158147)
                ·
                  refine ⟨3538952487803072433237221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2359301658535381622158147 3538952487803072433237221)
                  ·
                    refine ⟨663553591463076081231979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3538952487803072433237221 663553591463076081231979)
                    ·
                      rfl

theorem cell23_3876798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 3, 2, 1, 4].length) (baseStart_3876798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3876798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3876798 prefixEnd_3876798 := by exact prefixLift 3876798
  have htrace : WordTrace (prefixWord ++ tailWord_3876798) baseStart_3876798 baseEnd_3876798 := by
    simpa [prefixWord, tailWord_3876798, baseEnd_3876798] using wordTrace_append hprefix tailTrace_3876798
  have hstable : (prefixWord ++ tailWord_3876798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3876798).length < 2 ^ (prefixWord ++ tailWord_3876798).sum := by decide
  have hdescent : baseEnd_3876798 < baseStart_3876798 := by decide
  rcases family_descends (prefixWord ++ tailWord_3876798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3876814 : List Nat := [4, 1, 1, 1, 2, 2, 1, 2, 4, 3, 2]
def baseStart_3876814 : Nat := 118140960795 + 3876814 * 2 ^ 59
def prefixEnd_3876814 : Nat := 4983230072969 + 3 ^ 40 * 3876814 * 2
def baseEnd_3876814 : Nat := 1990668990079700181095863

theorem tailTrace_3876814 : CollatzResearch.WordTrace tailWord_3876814 prefixEnd_3876814 1990668990079700181095863 := by
  unfold tailWord_3876814
  simp only [CollatzResearch.WordTrace]
  refine ⟨17674877872121557495408687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94266015317981639975512997 17674877872121557495408687)
  ·
    refine ⟨26512316808182336243113031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17674877872121557495408687 26512316808182336243113031)
    ·
      refine ⟨39768475212273504364669547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26512316808182336243113031 39768475212273504364669547)
      ·
        refine ⟨59652712818410256547004321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39768475212273504364669547 59652712818410256547004321)
        ·
          refine ⟨44739534613807692410253241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59652712818410256547004321 44739534613807692410253241)
          ·
            refine ⟨33554650960355769307689931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44739534613807692410253241 33554650960355769307689931)
            ·
              refine ⟨50331976440533653961534897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33554650960355769307689931 50331976440533653961534897)
              ·
                refine ⟨37748982330400240471151173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50331976440533653961534897 37748982330400240471151173)
                ·
                  refine ⟨7077934186950045088340845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37748982330400240471151173 7077934186950045088340845)
                  ·
                    refine ⟨2654225320106266908127817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7077934186950045088340845 2654225320106266908127817)
                    ·
                      refine ⟨1990668990079700181095863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2654225320106266908127817 1990668990079700181095863)
                      ·
                        rfl

theorem cell23_3876814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 2, 4, 3, 2].length) (baseStart_3876814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3876814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3876814 prefixEnd_3876814 := by exact prefixLift 3876814
  have htrace : WordTrace (prefixWord ++ tailWord_3876814) baseStart_3876814 baseEnd_3876814 := by
    simpa [prefixWord, tailWord_3876814, baseEnd_3876814] using wordTrace_append hprefix tailTrace_3876814
  have hstable : (prefixWord ++ tailWord_3876814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3876814).length < 2 ^ (prefixWord ++ tailWord_3876814).sum := by decide
  have hdescent : baseEnd_3876814 < baseStart_3876814 := by decide
  rcases family_descends (prefixWord ++ tailWord_3876814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3876831 : List Nat := [1, 1, 2, 3, 4, 2, 2, 1, 2, 3, 2]
def baseStart_3876831 : Nat := 118140960795 + 3876831 * 2 ^ 59
def prefixEnd_3876831 : Nat := 4983230072969 + 3 ^ 40 * 3876831 * 2
def baseEnd_3876831 : Nat := 1990677719250826614583285

theorem tailTrace_3876831 : CollatzResearch.WordTrace tailWord_3876831 prefixEnd_3876831 1990677719250826614583285 := by
  unfold tailWord_3876831
  simp only [CollatzResearch.WordTrace]
  refine ⟨141399643017910871866638347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94266428678607247911092231 141399643017910871866638347)
  ·
    refine ⟨212099464526866307799957521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141399643017910871866638347 212099464526866307799957521)
    ·
      refine ⟨159074598395149730849968141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212099464526866307799957521 159074598395149730849968141)
      ·
        refine ⟨59652974398181149068738053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159074598395149730849968141 59652974398181149068738053)
        ·
          refine ⟨11184932699658965450388385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59652974398181149068738053 11184932699658965450388385)
          ·
            refine ⟨8388699524744224087791289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11184932699658965450388385 8388699524744224087791289)
            ·
              refine ⟨6291524643558168065843467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8388699524744224087791289 6291524643558168065843467)
              ·
                refine ⟨9437286965337252098765201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6291524643558168065843467 9437286965337252098765201)
                ·
                  refine ⟨7077965224002939074073901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9437286965337252098765201 7077965224002939074073901)
                  ·
                    refine ⟨2654236959001102152777713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7077965224002939074073901 2654236959001102152777713)
                    ·
                      refine ⟨1990677719250826614583285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2654236959001102152777713 1990677719250826614583285)
                      ·
                        rfl

theorem cell23_3876831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 2, 1, 2, 3, 2].length) (baseStart_3876831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3876831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3876831 prefixEnd_3876831 := by exact prefixLift 3876831
  have htrace : WordTrace (prefixWord ++ tailWord_3876831) baseStart_3876831 baseEnd_3876831 := by
    simpa [prefixWord, tailWord_3876831, baseEnd_3876831] using wordTrace_append hprefix tailTrace_3876831
  have hstable : (prefixWord ++ tailWord_3876831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3876831).length < 2 ^ (prefixWord ++ tailWord_3876831).sum := by decide
  have hdescent : baseEnd_3876831 < baseStart_3876831 := by decide
  rcases family_descends (prefixWord ++ tailWord_3876831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3876850 : List Nat := [3, 2, 1, 17]
def baseStart_3876850 : Nat := 118140960795 + 3876850 * 2 ^ 59
def prefixEnd_3876850 : Nat := 4983230072969 + 3 ^ 40 * 3876850 * 2
def baseEnd_3876850 : Nat := 910236614258464581731

theorem tailTrace_3876850 : CollatzResearch.WordTrace tailWord_3876850 prefixEnd_3876850 910236614258464581731 := by
  unfold tailWord_3876850
  simp only [CollatzResearch.WordTrace]
  refine ⟨35350084001210509527895001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94266890669894692074386669 35350084001210509527895001)
  ·
    refine ⟨26512563000907882145921251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35350084001210509527895001 26512563000907882145921251)
    ·
      refine ⟨39768844501361823218881877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26512563000907882145921251 39768844501361823218881877)
      ·
        refine ⟨910236614258464581731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 17 39768844501361823218881877 910236614258464581731)
        ·
          rfl

theorem cell23_3876850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 17].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 17].length) (baseStart_3876850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3876850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3876850 prefixEnd_3876850 := by exact prefixLift 3876850
  have htrace : WordTrace (prefixWord ++ tailWord_3876850) baseStart_3876850 baseEnd_3876850 := by
    simpa [prefixWord, tailWord_3876850, baseEnd_3876850] using wordTrace_append hprefix tailTrace_3876850
  have hstable : (prefixWord ++ tailWord_3876850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3876850).length < 2 ^ (prefixWord ++ tailWord_3876850).sum := by decide
  have hdescent : baseEnd_3876850 < baseStart_3876850 := by decide
  rcases family_descends (prefixWord ++ tailWord_3876850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3876917 : List Nat := [1, 3, 3, 1, 1, 1, 2, 1, 1, 5, 4]
def baseStart_3876917 : Nat := 118140960795 + 3876917 * 2 ^ 59
def prefixEnd_3876917 : Nat := 4983230072969 + 3 ^ 40 * 3876917 * 2
def baseEnd_3876917 : Nat := 1990721878587113278107889

theorem tailTrace_3876917 : CollatzResearch.WordTrace tailWord_3876917 prefixEnd_3876917 1990721878587113278107889 := by
  unfold tailWord_3876917
  simp only [CollatzResearch.WordTrace]
  refine ⟨141402779695599308554269005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94268519797066205702846003 141402779695599308554269005)
  ·
    refine ⟨53026042385849740707850877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141402779695599308554269005 53026042385849740707850877)
    ·
      refine ⟨19884765894693652765444079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53026042385849740707850877 19884765894693652765444079)
      ·
        refine ⟨29827148842040479148166119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19884765894693652765444079 29827148842040479148166119)
        ·
          refine ⟨44740723263060718722249179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29827148842040479148166119 44740723263060718722249179)
          ·
            refine ⟨67111084894591078083373769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44740723263060718722249179 67111084894591078083373769)
            ·
              refine ⟨50333313670943308562530327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67111084894591078083373769 50333313670943308562530327)
              ·
                refine ⟨75499970506414962843795491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50333313670943308562530327 75499970506414962843795491)
                ·
                  refine ⟨113249955759622444265693237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75499970506414962843795491 113249955759622444265693237)
                  ·
                    refine ⟨10617183352464604149908741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 113249955759622444265693237 10617183352464604149908741)
                    ·
                      refine ⟨1990721878587113278107889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10617183352464604149908741 1990721878587113278107889)
                      ·
                        rfl

theorem cell23_3876917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 5, 4].length) (baseStart_3876917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3876917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3876917 prefixEnd_3876917 := by exact prefixLift 3876917
  have htrace : WordTrace (prefixWord ++ tailWord_3876917) baseStart_3876917 baseEnd_3876917 := by
    simpa [prefixWord, tailWord_3876917, baseEnd_3876917] using wordTrace_append hprefix tailTrace_3876917
  have hstable : (prefixWord ++ tailWord_3876917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3876917).length < 2 ^ (prefixWord ++ tailWord_3876917).sum := by decide
  have hdescent : baseEnd_3876917 < baseStart_3876917 := by decide
  rcases family_descends (prefixWord ++ tailWord_3876917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3876927 : List Nat := [1, 1, 2, 2, 3, 1, 4, 1, 2, 6]
def baseStart_3876927 : Nat := 118140960795 + 3876927 * 2 ^ 59
def prefixEnd_3876927 : Nat := 4983230072969 + 3 ^ 40 * 3876927 * 2
def baseEnd_3876927 : Nat := 663575671131219412994281

theorem tailTrace_3876927 : CollatzResearch.WordTrace tailWord_3876927 prefixEnd_3876927 663575671131219412994281 := by
  unfold tailWord_3876927
  simp only [CollatzResearch.WordTrace]
  refine ⟨141403144425563080262133035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94268762950375386841422023 141403144425563080262133035)
  ·
    refine ⟨212104716638344620393199553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141403144425563080262133035 212104716638344620393199553)
    ·
      refine ⟨159078537478758465294899665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212104716638344620393199553 159078537478758465294899665)
      ·
        refine ⟨119308903109068848971174749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159078537478758465294899665 119308903109068848971174749)
        ·
          refine ⟨44740838665900818364190531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119308903109068848971174749 44740838665900818364190531)
          ·
            refine ⟨67111257998851227546285797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44740838665900818364190531 67111257998851227546285797)
            ·
              refine ⟨12583360874784605164928587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67111257998851227546285797 12583360874784605164928587)
              ·
                refine ⟨18875041312176907747392881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12583360874784605164928587 18875041312176907747392881)
                ·
                  refine ⟨14156280984132680810544661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18875041312176907747392881 14156280984132680810544661)
                  ·
                    refine ⟨663575671131219412994281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14156280984132680810544661 663575671131219412994281)
                    ·
                      rfl

theorem cell23_3876927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 1, 2, 6].length) (baseStart_3876927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3876927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3876927 prefixEnd_3876927 := by exact prefixLift 3876927
  have htrace : WordTrace (prefixWord ++ tailWord_3876927) baseStart_3876927 baseEnd_3876927 := by
    simpa [prefixWord, tailWord_3876927, baseEnd_3876927] using wordTrace_append hprefix tailTrace_3876927
  have hstable : (prefixWord ++ tailWord_3876927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3876927).length < 2 ^ (prefixWord ++ tailWord_3876927).sum := by decide
  have hdescent : baseEnd_3876927 < baseStart_3876927 := by decide
  rcases family_descends (prefixWord ++ tailWord_3876927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3876928 : List Nat := [2, 1, 1, 2, 2, 5, 3, 1, 2, 1, 3]
def baseStart_3876928 : Nat := 118140960795 + 3876928 * 2 ^ 59
def prefixEnd_3876928 : Nat := 4983230072969 + 3 ^ 40 * 3876928 * 2
def baseEnd_3876928 : Nat := 1990727526874312735070339

theorem tailTrace_3876928 : CollatzResearch.WordTrace tailWord_3876928 prefixEnd_3876928 1990727526874312735070339 := by
  unfold tailWord_3876928
  simp only [CollatzResearch.WordTrace]
  refine ⟨70701590449279728716459719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94268787265706304955279625 70701590449279728716459719)
  ·
    refine ⟨106052385673919593074689579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70701590449279728716459719 106052385673919593074689579)
    ·
      refine ⟨159078578510879389612034369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106052385673919593074689579 159078578510879389612034369)
      ·
        refine ⟨119308933883159542209025777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159078578510879389612034369 119308933883159542209025777)
        ·
          refine ⟨89481700412369656656769333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119308933883159542209025777 89481700412369656656769333)
          ·
            refine ⟨8388909413659655311572125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 89481700412369656656769333 8388909413659655311572125)
            ·
              refine ⟨3145841030122370741839547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8388909413659655311572125 3145841030122370741839547)
              ·
                refine ⟨4718761545183556112759321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3145841030122370741839547 4718761545183556112759321)
                ·
                  refine ⟨3539071158887667084569491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4718761545183556112759321 3539071158887667084569491)
                  ·
                    refine ⟨5308606738331500626854237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3539071158887667084569491 5308606738331500626854237)
                    ·
                      refine ⟨1990727526874312735070339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5308606738331500626854237 1990727526874312735070339)
                      ·
                        rfl

theorem cell23_3876928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 3, 1, 2, 1, 3].length) (baseStart_3876928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3876928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3876928 prefixEnd_3876928 := by exact prefixLift 3876928
  have htrace : WordTrace (prefixWord ++ tailWord_3876928) baseStart_3876928 baseEnd_3876928 := by
    simpa [prefixWord, tailWord_3876928, baseEnd_3876928] using wordTrace_append hprefix tailTrace_3876928
  have hstable : (prefixWord ++ tailWord_3876928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3876928).length < 2 ^ (prefixWord ++ tailWord_3876928).sum := by decide
  have hdescent : baseEnd_3876928 < baseStart_3876928 := by decide
  rcases family_descends (prefixWord ++ tailWord_3876928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3876937 : List Nat := [1, 2, 1, 1, 2, 2, 4, 2, 2, 1, 5]
def baseStart_3876937 : Nat := 118140960795 + 3876937 * 2 ^ 59
def prefixEnd_3876937 : Nat := 4983230072969 + 3 ^ 40 * 3876937 * 2
def baseEnd_3876937 : Nat := 1990732148200203199857797

theorem tailTrace_3876937 : CollatzResearch.WordTrace tailWord_3876937 prefixEnd_3876937 1990732148200203199857797 := by
  unfold tailWord_3876937
  simp only [CollatzResearch.WordTrace]
  refine ⟨141403509155526851969997065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94269006103684567979998043 141403509155526851969997065)
  ·
    refine ⟨106052631866645138977497799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141403509155526851969997065 106052631866645138977497799)
    ·
      refine ⟨159078947799967708466246699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106052631866645138977497799 159078947799967708466246699)
      ·
        refine ⟨238618421699951562699370049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159078947799967708466246699 238618421699951562699370049)
        ·
          refine ⟨178963816274963672024527537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 238618421699951562699370049 178963816274963672024527537)
          ·
            refine ⟨134222862206222754018395653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178963816274963672024527537 134222862206222754018395653)
            ·
              refine ⟨25166786663666766378449185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 134222862206222754018395653 25166786663666766378449185)
              ·
                refine ⟨18875089997750074783836889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25166786663666766378449185 18875089997750074783836889)
                ·
                  refine ⟨14156317498312556087877667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18875089997750074783836889 14156317498312556087877667)
                  ·
                    refine ⟨21234476247468834131816501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14156317498312556087877667 21234476247468834131816501)
                    ·
                      refine ⟨1990732148200203199857797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21234476247468834131816501 1990732148200203199857797)
                      ·
                        rfl

theorem cell23_3876937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 2, 2, 1, 5].length) (baseStart_3876937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3876937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3876937 prefixEnd_3876937 := by exact prefixLift 3876937
  have htrace : WordTrace (prefixWord ++ tailWord_3876937) baseStart_3876937 baseEnd_3876937 := by
    simpa [prefixWord, tailWord_3876937, baseEnd_3876937] using wordTrace_append hprefix tailTrace_3876937
  have hstable : (prefixWord ++ tailWord_3876937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3876937).length < 2 ^ (prefixWord ++ tailWord_3876937).sum := by decide
  have hdescent : baseEnd_3876937 < baseStart_3876937 := by decide
  rcases family_descends (prefixWord ++ tailWord_3876937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3876951 : List Nat := [1, 1, 3, 2, 2, 1, 3, 2, 4, 2, 2]
def baseStart_3876951 : Nat := 118140960795 + 3876951 * 2 ^ 59
def prefixEnd_3876951 : Nat := 4983230072969 + 3 ^ 40 * 3876951 * 2
def baseEnd_3876951 : Nat := 1990739336929366145082733

theorem tailTrace_3876951 : CollatzResearch.WordTrace tailWord_3876951 prefixEnd_3876951 1990739336929366145082733 := by
  unfold tailWord_3876951
  simp only [CollatzResearch.WordTrace]
  refine ⟨141404019777476132361006707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94269346518317421574004471 141404019777476132361006707)
  ·
    refine ⟨212106029666214198541510061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141404019777476132361006707 212106029666214198541510061)
    ·
      refine ⟨79539761124830324453066273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212106029666214198541510061 79539761124830324453066273)
      ·
        refine ⟨59654820843622743339799705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79539761124830324453066273 59654820843622743339799705)
        ·
          refine ⟨44741115632717057504849779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59654820843622743339799705 44741115632717057504849779)
          ·
            refine ⟨67111673449075586257274669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44741115632717057504849779 67111673449075586257274669)
            ·
              refine ⟨25166877543403344846478001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67111673449075586257274669 25166877543403344846478001)
              ·
                refine ⟨18875158157552508634858501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25166877543403344846478001 18875158157552508634858501)
                ·
                  refine ⟨3539092154541095369035969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18875158157552508634858501 3539092154541095369035969)
                  ·
                    refine ⟨2654319115905821526776977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3539092154541095369035969 2654319115905821526776977)
                    ·
                      refine ⟨1990739336929366145082733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2654319115905821526776977 1990739336929366145082733)
                      ·
                        rfl

theorem cell23_3876951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 2, 4, 2, 2].length) (baseStart_3876951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3876951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3876951 prefixEnd_3876951 := by exact prefixLift 3876951
  have htrace : WordTrace (prefixWord ++ tailWord_3876951) baseStart_3876951 baseEnd_3876951 := by
    simpa [prefixWord, tailWord_3876951, baseEnd_3876951] using wordTrace_append hprefix tailTrace_3876951
  have hstable : (prefixWord ++ tailWord_3876951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3876951).length < 2 ^ (prefixWord ++ tailWord_3876951).sum := by decide
  have hdescent : baseEnd_3876951 < baseStart_3876951 := by decide
  rcases family_descends (prefixWord ++ tailWord_3876951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3876967 : List Nat := [1, 1, 5, 1, 1, 2, 1, 1, 1, 2, 7]
def baseStart_3876967 : Nat := 118140960795 + 3876967 * 2 ^ 59
def prefixEnd_3876967 : Nat := 4983230072969 + 3 ^ 40 * 3876967 * 2
def baseEnd_3876967 : Nat := 1990747552619838082482659

theorem tailTrace_3876967 : CollatzResearch.WordTrace tailWord_3876967 prefixEnd_3876967 1990747552619838082482659 := by
  unfold tailWord_3876967
  simp only [CollatzResearch.WordTrace]
  refine ⟨141404603345418167093589155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94269735563612111395726103 141404603345418167093589155)
  ·
    refine ⟨212106905018127250640383733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141404603345418167093589155 212106905018127250640383733)
    ·
      refine ⟨19885022345449429747535975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 212106905018127250640383733 19885022345449429747535975)
      ·
        refine ⟨29827533518174144621303963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19885022345449429747535975 29827533518174144621303963)
        ·
          refine ⟨44741300277261216931955945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29827533518174144621303963 44741300277261216931955945)
          ·
            refine ⟨33555975207945912698966959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44741300277261216931955945 33555975207945912698966959)
            ·
              refine ⟨50333962811918869048450439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33555975207945912698966959 50333962811918869048450439)
              ·
                refine ⟨75500944217878303572675659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50333962811918869048450439 75500944217878303572675659)
                ·
                  refine ⟨113251416326817455359013489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75500944217878303572675659 113251416326817455359013489)
                  ·
                    refine ⟨84938562245113091519260117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 113251416326817455359013489 84938562245113091519260117)
                    ·
                      refine ⟨1990747552619838082482659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 84938562245113091519260117 1990747552619838082482659)
                      ·
                        rfl

theorem cell23_3876967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 2, 7].length) (baseStart_3876967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3876967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3876967 prefixEnd_3876967 := by exact prefixLift 3876967
  have htrace : WordTrace (prefixWord ++ tailWord_3876967) baseStart_3876967 baseEnd_3876967 := by
    simpa [prefixWord, tailWord_3876967, baseEnd_3876967] using wordTrace_append hprefix tailTrace_3876967
  have hstable : (prefixWord ++ tailWord_3876967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3876967).length < 2 ^ (prefixWord ++ tailWord_3876967).sum := by decide
  have hdescent : baseEnd_3876967 < baseStart_3876967 := by decide
  rcases family_descends (prefixWord ++ tailWord_3876967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3876985 : List Nat := [1, 2, 1, 3, 4, 1, 4, 1, 2, 2, 2]
def baseStart_3876985 : Nat := 118140960795 + 3876985 * 2 ^ 59
def prefixEnd_3876985 : Nat := 4983230072969 + 3 ^ 40 * 3876985 * 2
def baseEnd_3876985 : Nat := 1990756795271619012057577

theorem tailTrace_3876985 : CollatzResearch.WordTrace tailWord_3876985 prefixEnd_3876985 1990756795271619012057577 := by
  unfold tailWord_3876985
  simp only [CollatzResearch.WordTrace]
  refine ⟨141405259859352956167744409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94270173239568637445162939 141405259859352956167744409)
  ·
    refine ⟨106053944894514717125808307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141405259859352956167744409 106053944894514717125808307)
    ·
      refine ⟨159080917341772075688712461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106053944894514717125808307 159080917341772075688712461)
      ·
        refine ⟨59655344003164528383267173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159080917341772075688712461 59655344003164528383267173)
        ·
          refine ⟨11185377000593349071862595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59655344003164528383267173 11185377000593349071862595)
          ·
            refine ⟨16778065500890023607793893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11185377000593349071862595 16778065500890023607793893)
            ·
              refine ⟨3145887281416879426461355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16778065500890023607793893 3145887281416879426461355)
              ·
                refine ⟨4718830922125319139692033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3145887281416879426461355 4718830922125319139692033)
                ·
                  refine ⟨3539123191593989354769025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4718830922125319139692033 3539123191593989354769025)
                  ·
                    refine ⟨2654342393695492016076769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3539123191593989354769025 2654342393695492016076769)
                    ·
                      refine ⟨1990756795271619012057577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2654342393695492016076769 1990756795271619012057577)
                      ·
                        rfl

theorem cell23_3876985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 4, 1, 2, 2, 2].length) (baseStart_3876985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3876985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3876985 prefixEnd_3876985 := by exact prefixLift 3876985
  have htrace : WordTrace (prefixWord ++ tailWord_3876985) baseStart_3876985 baseEnd_3876985 := by
    simpa [prefixWord, tailWord_3876985, baseEnd_3876985] using wordTrace_append hprefix tailTrace_3876985
  have hstable : (prefixWord ++ tailWord_3876985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3876985).length < 2 ^ (prefixWord ++ tailWord_3876985).sum := by decide
  have hdescent : baseEnd_3876985 < baseStart_3876985 := by decide
  rcases family_descends (prefixWord ++ tailWord_3876985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3877061 : List Nat := [1, 3, 1, 1, 1, 1, 7, 1, 2, 2, 3]
def baseStart_3877061 : Nat := 118140960795 + 3877061 * 2 ^ 59
def prefixEnd_3877061 : Nat := 4983230072969 + 3 ^ 40 * 3877061 * 2
def baseEnd_3877061 : Nat := 1990795819801360714707227

theorem tailTrace_3877061 : CollatzResearch.WordTrace tailWord_3877061 prefixEnd_3877061 1990795819801360714707227 := by
  unfold tailWord_3877061
  simp only [CollatzResearch.WordTrace]
  refine ⟨141408031807077621147511037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94272021204718414098340691 141408031807077621147511037)
  ·
    refine ⟨53028011927654107930316639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141408031807077621147511037 53028011927654107930316639)
    ·
      refine ⟨79542017891481161895474959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53028011927654107930316639 79542017891481161895474959)
      ·
        refine ⟨119313026837221742843212439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79542017891481161895474959 119313026837221742843212439)
        ·
          refine ⟨178969540255832614264818659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119313026837221742843212439 178969540255832614264818659)
          ·
            refine ⟨268454310383748921397227989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 178969540255832614264818659 268454310383748921397227989)
            ·
              refine ⟨6291897899619115345247531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 268454310383748921397227989 6291897899619115345247531)
              ·
                refine ⟨9437846849428673017871297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6291897899619115345247531 9437846849428673017871297)
                ·
                  refine ⟨7078385137071504763403473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9437846849428673017871297 7078385137071504763403473)
                  ·
                    refine ⟨5308788852803628572552605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7078385137071504763403473 5308788852803628572552605)
                    ·
                      refine ⟨1990795819801360714707227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5308788852803628572552605 1990795819801360714707227)
                      ·
                        rfl

theorem cell23_3877061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 7, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 7, 1, 2, 2, 3].length) (baseStart_3877061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3877061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3877061 prefixEnd_3877061 := by exact prefixLift 3877061
  have htrace : WordTrace (prefixWord ++ tailWord_3877061) baseStart_3877061 baseEnd_3877061 := by
    simpa [prefixWord, tailWord_3877061, baseEnd_3877061] using wordTrace_append hprefix tailTrace_3877061
  have hstable : (prefixWord ++ tailWord_3877061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3877061).length < 2 ^ (prefixWord ++ tailWord_3877061).sum := by decide
  have hdescent : baseEnd_3877061 < baseStart_3877061 := by decide
  rcases family_descends (prefixWord ++ tailWord_3877061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3877085 : List Nat := [1, 4, 3, 2, 1, 1, 2, 4, 1, 4]
def baseStart_3877085 : Nat := 118140960795 + 3877085 * 2 ^ 59
def prefixEnd_3877085 : Nat := 4983230072969 + 3 ^ 40 * 3877085 * 2
def baseEnd_3877085 : Nat := 663602714445689540269039

theorem tailTrace_3877085 : CollatzResearch.WordTrace tailWord_3877085 prefixEnd_3877085 663602714445689540269039 := by
  unfold tailWord_3877085
  simp only [CollatzResearch.WordTrace]
  refine ⟨141408907158990673246384709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94272604772660448830923139 141408907158990673246384709)
  ·
    refine ⟨26514170092310751233697133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141408907158990673246384709 26514170092310751233697133)
    ·
      refine ⟨9942813784616531712636425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26514170092310751233697133 9942813784616531712636425)
      ·
        refine ⟨7457110338462398784477319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9942813784616531712636425 7457110338462398784477319)
        ·
          refine ⟨11185665507693598176715979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7457110338462398784477319 11185665507693598176715979)
          ·
            refine ⟨16778498261540397265073969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11185665507693598176715979 16778498261540397265073969)
            ·
              refine ⟨12583873696155297948805477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16778498261540397265073969 12583873696155297948805477)
              ·
                refine ⟨2359476318029118365401027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12583873696155297948805477 2359476318029118365401027)
                ·
                  refine ⟨3539214477043677548101541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2359476318029118365401027 3539214477043677548101541)
                  ·
                    refine ⟨663602714445689540269039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3539214477043677548101541 663602714445689540269039)
                    ·
                      rfl

theorem cell23_3877085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 4, 1, 4].length) (baseStart_3877085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3877085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3877085 prefixEnd_3877085 := by exact prefixLift 3877085
  have htrace : WordTrace (prefixWord ++ tailWord_3877085) baseStart_3877085 baseEnd_3877085 := by
    simpa [prefixWord, tailWord_3877085, baseEnd_3877085] using wordTrace_append hprefix tailTrace_3877085
  have hstable : (prefixWord ++ tailWord_3877085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3877085).length < 2 ^ (prefixWord ++ tailWord_3877085).sum := by decide
  have hdescent : baseEnd_3877085 < baseStart_3877085 := by decide
  rcases family_descends (prefixWord ++ tailWord_3877085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3877118 : List Nat := [4, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2]
def baseStart_3877118 : Nat := 118140960795 + 3877118 * 2 ^ 59
def prefixEnd_3877118 : Nat := 4983230072969 + 3 ^ 40 * 3877118 * 2
def baseEnd_3877118 : Nat := 1990825088198666991694465

theorem tailTrace_3877118 : CollatzResearch.WordTrace tailWord_3877118 prefixEnd_3877118 1990825088198666991694465 := by
  unfold tailWord_3877118
  simp only [CollatzResearch.WordTrace]
  refine ⟨17676263845983889985292001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94273407178580746588224005 17676263845983889985292001)
  ·
    refine ⟨13257197884487917488969001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17676263845983889985292001 13257197884487917488969001)
    ·
      refine ⟨9942898413365938116726751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13257197884487917488969001 9942898413365938116726751)
      ·
        refine ⟨14914347620048907175090127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9942898413365938116726751 14914347620048907175090127)
        ·
          refine ⟨22371521430073360762635191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14914347620048907175090127 22371521430073360762635191)
          ·
            refine ⟨33557282145110041143952787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22371521430073360762635191 33557282145110041143952787)
            ·
              refine ⟨50335923217665061715929181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33557282145110041143952787 50335923217665061715929181)
              ·
                refine ⟨18875971206624398143473443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50335923217665061715929181 18875971206624398143473443)
                ·
                  refine ⟨28313956809936597215210165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18875971206624398143473443 28313956809936597215210165)
                  ·
                    refine ⟨2654433450931555988925953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28313956809936597215210165 2654433450931555988925953)
                    ·
                      refine ⟨1990825088198666991694465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2654433450931555988925953 1990825088198666991694465)
                      ·
                        rfl

theorem cell23_3877118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2].length) (baseStart_3877118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3877118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3877118 prefixEnd_3877118 := by exact prefixLift 3877118
  have htrace : WordTrace (prefixWord ++ tailWord_3877118) baseStart_3877118 baseEnd_3877118 := by
    simpa [prefixWord, tailWord_3877118, baseEnd_3877118] using wordTrace_append hprefix tailTrace_3877118
  have hstable : (prefixWord ++ tailWord_3877118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3877118).length < 2 ^ (prefixWord ++ tailWord_3877118).sum := by decide
  have hdescent : baseEnd_3877118 < baseStart_3877118 := by decide
  rcases family_descends (prefixWord ++ tailWord_3877118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3877131 : List Nat := [1, 1, 1, 1, 5, 2, 1, 5, 1, 1, 4]
def baseStart_3877131 : Nat := 118140960795 + 3877131 * 2 ^ 59
def prefixEnd_3877131 : Nat := 4983230072969 + 3 ^ 40 * 3877131 * 2
def baseEnd_3877131 : Nat := 1990831763447175440831905

theorem tailTrace_3877131 : CollatzResearch.WordTrace tailWord_3877131 prefixEnd_3877131 1990831763447175440831905 := by
  unfold tailWord_3877131
  simp only [CollatzResearch.WordTrace]
  refine ⟨141410584916824023102559247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94273723277882682068372831 141410584916824023102559247)
  ·
    refine ⟨212115877375236034653838871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141410584916824023102559247 212115877375236034653838871)
    ·
      refine ⟨318173816062854051980758307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212115877375236034653838871 318173816062854051980758307)
      ·
        refine ⟨477260724094281077971137461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318173816062854051980758307 477260724094281077971137461)
        ·
          refine ⟨44743192883838851059794137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 477260724094281077971137461 44743192883838851059794137)
          ·
            refine ⟨33557394662879138294845603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44743192883838851059794137 33557394662879138294845603)
            ·
              refine ⟨50336091994318707442268405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33557394662879138294845603 50336091994318707442268405)
              ·
                refine ⟨4719008624467378822712663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50336091994318707442268405 4719008624467378822712663)
                ·
                  refine ⟨7078512936701068234068995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4719008624467378822712663 7078512936701068234068995)
                  ·
                    refine ⟨10617769405051602351103493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7078512936701068234068995 10617769405051602351103493)
                    ·
                      refine ⟨1990831763447175440831905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10617769405051602351103493 1990831763447175440831905)
                      ·
                        rfl

theorem cell23_3877131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 5, 1, 1, 4].length) (baseStart_3877131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3877131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3877131 prefixEnd_3877131 := by exact prefixLift 3877131
  have htrace : WordTrace (prefixWord ++ tailWord_3877131) baseStart_3877131 baseEnd_3877131 := by
    simpa [prefixWord, tailWord_3877131, baseEnd_3877131] using wordTrace_append hprefix tailTrace_3877131
  have hstable : (prefixWord ++ tailWord_3877131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3877131).length < 2 ^ (prefixWord ++ tailWord_3877131).sum := by decide
  have hdescent : baseEnd_3877131 < baseStart_3877131 := by decide
  rcases family_descends (prefixWord ++ tailWord_3877131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3877141 : List Nat := [1, 3, 2, 1, 2, 1, 4, 1, 4, 4]
def baseStart_3877141 : Nat := 118140960795 + 3877141 * 2 ^ 59
def prefixEnd_3877141 : Nat := 4983230072969 + 3 ^ 40 * 3877141 * 2
def baseEnd_3877141 : Nat := 663612299417906800568953

theorem tailTrace_3877141 : CollatzResearch.WordTrace tailWord_3877141 prefixEnd_3877141 663612299417906800568953 := by
  unfold tailWord_3877141
  simp only [CollatzResearch.WordTrace]
  refine ⟨141410949646787794810423277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94273966431191863206948851 141410949646787794810423277)
  ·
    refine ⟨53029106117545423053908729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141410949646787794810423277 53029106117545423053908729)
    ·
      refine ⟨39771829588159067290431547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53029106117545423053908729 39771829588159067290431547)
      ·
        refine ⟨59657744382238600935647321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39771829588159067290431547 59657744382238600935647321)
        ·
          refine ⟨44743308286678950701735491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59657744382238600935647321 44743308286678950701735491)
          ·
            refine ⟨67114962430018426052603237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44743308286678950701735491 67114962430018426052603237)
            ·
              refine ⟨12584055455628454884863107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67114962430018426052603237 12584055455628454884863107)
              ·
                refine ⟨18876083183442682327294661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12584055455628454884863107 18876083183442682327294661)
                ·
                  refine ⟨3539265596895502936367749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18876083183442682327294661 3539265596895502936367749)
                  ·
                    refine ⟨663612299417906800568953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3539265596895502936367749 663612299417906800568953)
                    ·
                      rfl

theorem cell23_3877141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 1, 4, 4].length) (baseStart_3877141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3877141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3877141 prefixEnd_3877141 := by exact prefixLift 3877141
  have htrace : WordTrace (prefixWord ++ tailWord_3877141) baseStart_3877141 baseEnd_3877141 := by
    simpa [prefixWord, tailWord_3877141, baseEnd_3877141] using wordTrace_append hprefix tailTrace_3877141
  have hstable : (prefixWord ++ tailWord_3877141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3877141).length < 2 ^ (prefixWord ++ tailWord_3877141).sum := by decide
  have hdescent : baseEnd_3877141 < baseStart_3877141 := by decide
  rcases family_descends (prefixWord ++ tailWord_3877141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3877144 : List Nat := [2, 1, 2, 3, 1, 2, 1, 1, 3, 1, 6]
def baseStart_3877144 : Nat := 118140960795 + 3877144 * 2 ^ 59
def prefixEnd_3877144 : Nat := 4983230072969 + 3 ^ 40 * 3877144 * 2
def baseEnd_3877144 : Nat := 1990838438695683889969345

theorem tailTrace_3877144 : CollatzResearch.WordTrace tailWord_3877144 prefixEnd_3877144 1990838438695683889969345 := by
  unfold tailWord_3877144
  simp only [CollatzResearch.WordTrace]
  refine ⟨70705529532888463161391243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94274039377184617548521657 70705529532888463161391243)
  ·
    refine ⟨106058294299332694742086865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70705529532888463161391243 106058294299332694742086865)
    ·
      refine ⟨79543720724499521056565149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106058294299332694742086865 79543720724499521056565149)
      ·
        refine ⟨29828895271687320396211931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79543720724499521056565149 29828895271687320396211931)
        ·
          refine ⟨44743342907530980594317897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29828895271687320396211931 44743342907530980594317897)
          ·
            refine ⟨33557507180648235445738423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44743342907530980594317897 33557507180648235445738423)
            ·
              refine ⟨50336260770972353168607635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33557507180648235445738423 50336260770972353168607635)
              ·
                refine ⟨75504391156458529752911453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50336260770972353168607635 75504391156458529752911453)
                ·
                  refine ⟨28314146683671948657341795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 75504391156458529752911453 28314146683671948657341795)
                  ·
                    refine ⟨42471220025507922986012693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28314146683671948657341795 42471220025507922986012693)
                    ·
                      refine ⟨1990838438695683889969345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42471220025507922986012693 1990838438695683889969345)
                      ·
                        rfl

theorem cell23_3877144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 3, 1, 6].length) (baseStart_3877144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3877144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3877144 prefixEnd_3877144 := by exact prefixLift 3877144
  have htrace : WordTrace (prefixWord ++ tailWord_3877144) baseStart_3877144 baseEnd_3877144 := by
    simpa [prefixWord, tailWord_3877144, baseEnd_3877144] using wordTrace_append hprefix tailTrace_3877144
  have hstable : (prefixWord ++ tailWord_3877144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3877144).length < 2 ^ (prefixWord ++ tailWord_3877144).sum := by decide
  have hdescent : baseEnd_3877144 < baseStart_3877144 := by decide
  rcases family_descends (prefixWord ++ tailWord_3877144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3877151 : List Nat := [1, 1, 2, 4, 3, 1, 2, 2, 1, 1, 5]
def baseStart_3877151 : Nat := 118140960795 + 3877151 * 2 ^ 59
def prefixEnd_3877151 : Nat := 4983230072969 + 3 ^ 40 * 3877151 * 2
def baseEnd_3877151 : Nat := 1990842033060265362581813

theorem tailTrace_3877151 : CollatzResearch.WordTrace tailWord_3877151 prefixEnd_3877151 1990842033060265362581813 := by
  unfold tailWord_3877151
  simp only [CollatzResearch.WordTrace]
  refine ⟨141411314376751566518287307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94274209584501044345524871 141411314376751566518287307)
  ·
    refine ⟨212116971565127349777430961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141411314376751566518287307 212116971565127349777430961)
    ·
      refine ⟨159087728673845512333073221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212116971565127349777430961 159087728673845512333073221)
      ·
        refine ⟨29828949126346033562451229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 159087728673845512333073221 29828949126346033562451229)
        ·
          refine ⟨11185855922379762585919211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29828949126346033562451229 11185855922379762585919211)
          ·
            refine ⟨16778783883569643878878817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11185855922379762585919211 16778783883569643878878817)
            ·
              refine ⟨12584087912677232909159113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16778783883569643878878817 12584087912677232909159113)
              ·
                refine ⟨9438065934507924681869335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12584087912677232909159113 9438065934507924681869335)
                ·
                  refine ⟨14157098901761887022804003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9438065934507924681869335 14157098901761887022804003)
                  ·
                    refine ⟨21235648352642830534206005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14157098901761887022804003 21235648352642830534206005)
                    ·
                      refine ⟨1990842033060265362581813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21235648352642830534206005 1990842033060265362581813)
                      ·
                        rfl

theorem cell23_3877151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 2, 1, 1, 5].length) (baseStart_3877151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3877151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3877151 prefixEnd_3877151 := by exact prefixLift 3877151
  have htrace : WordTrace (prefixWord ++ tailWord_3877151) baseStart_3877151 baseEnd_3877151 := by
    simpa [prefixWord, tailWord_3877151, baseEnd_3877151] using wordTrace_append hprefix tailTrace_3877151
  have hstable : (prefixWord ++ tailWord_3877151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3877151).length < 2 ^ (prefixWord ++ tailWord_3877151).sum := by decide
  have hdescent : baseEnd_3877151 < baseStart_3877151 := by decide
  rcases family_descends (prefixWord ++ tailWord_3877151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3877162 : List Nat := [3, 1, 4, 2, 3, 1, 1, 2, 1, 5]
def baseStart_3877162 : Nat := 118140960795 + 3877162 * 2 ^ 59
def prefixEnd_3877162 : Nat := 4983230072969 + 3 ^ 40 * 3877162 * 2
def baseEnd_3877162 : Nat := 663615893782488273181421

theorem tailTrace_3877162 : CollatzResearch.WordTrace tailWord_3877162 prefixEnd_3877162 663615893782488273181421 := by
  unfold tailWord_3877162
  simp only [CollatzResearch.WordTrace]
  refine ⟨35352928894927928849234435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94274477053141143597958493 35352928894927928849234435)
  ·
    refine ⟨53029393342391893273851653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35352928894927928849234435 53029393342391893273851653)
    ·
      refine ⟨9943011251698479988847185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53029393342391893273851653 9943011251698479988847185)
      ·
        refine ⟨7457258438773859991635389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9943011251698479988847185 7457258438773859991635389)
        ·
          refine ⟨2796471914540197496863271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7457258438773859991635389 2796471914540197496863271)
          ·
            refine ⟨4194707871810296245294907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2796471914540197496863271 4194707871810296245294907)
            ·
              refine ⟨6292061807715444367942361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4194707871810296245294907 6292061807715444367942361)
              ·
                refine ⟨4719046355786583275956771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6292061807715444367942361 4719046355786583275956771)
                ·
                  refine ⟨7078569533679874913935157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4719046355786583275956771 7078569533679874913935157)
                  ·
                    refine ⟨663615893782488273181421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7078569533679874913935157 663615893782488273181421)
                    ·
                      rfl

theorem cell23_3877162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 3, 1, 1, 2, 1, 5].length) (baseStart_3877162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3877162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3877162 prefixEnd_3877162 := by exact prefixLift 3877162
  have htrace : WordTrace (prefixWord ++ tailWord_3877162) baseStart_3877162 baseEnd_3877162 := by
    simpa [prefixWord, tailWord_3877162, baseEnd_3877162] using wordTrace_append hprefix tailTrace_3877162
  have hstable : (prefixWord ++ tailWord_3877162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3877162).length < 2 ^ (prefixWord ++ tailWord_3877162).sum := by decide
  have hdescent : baseEnd_3877162 < baseStart_3877162 := by decide
  rcases family_descends (prefixWord ++ tailWord_3877162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3877165 : List Nat := [1, 5, 3, 1, 2, 1, 1, 1, 3, 1, 4]
def baseStart_3877165 : Nat := 118140960795 + 3877165 * 2 ^ 59
def prefixEnd_3877165 : Nat := 4983230072969 + 3 ^ 40 * 3877165 * 2
def baseEnd_3877165 : Nat := 1990849221789428307806749

theorem tailTrace_3877165 : CollatzResearch.WordTrace tailWord_3877165 prefixEnd_3877165 1990849221789428307806749 := by
  unfold tailWord_3877165
  simp only [CollatzResearch.WordTrace]
  refine ⟨141411824998700846909296949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94274549999133897939531299 141411824998700846909296949)
  ·
    refine ⟨13257358593628204397746589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 141411824998700846909296949 13257358593628204397746589)
    ·
      refine ⟨4971509472610576649154971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13257358593628204397746589 4971509472610576649154971)
      ·
        refine ⟨7457264208915864973732457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4971509472610576649154971 7457264208915864973732457)
        ·
          refine ⟨5592948156686898730299343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7457264208915864973732457 5592948156686898730299343)
          ·
            refine ⟨8389422235030348095449015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5592948156686898730299343 8389422235030348095449015)
            ·
              refine ⟨12584133352545522143173523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8389422235030348095449015 12584133352545522143173523)
              ·
                refine ⟨18876200028818283214760285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12584133352545522143173523 18876200028818283214760285)
                ·
                  refine ⟨7078575010806856205535107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18876200028818283214760285 7078575010806856205535107)
                  ·
                    refine ⟨10617862516210284308302661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7078575010806856205535107 10617862516210284308302661)
                    ·
                      refine ⟨1990849221789428307806749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10617862516210284308302661 1990849221789428307806749)
                      ·
                        rfl

theorem cell23_3877165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_3877165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3877165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3877165 prefixEnd_3877165 := by exact prefixLift 3877165
  have htrace : WordTrace (prefixWord ++ tailWord_3877165) baseStart_3877165 baseEnd_3877165 := by
    simpa [prefixWord, tailWord_3877165, baseEnd_3877165] using wordTrace_append hprefix tailTrace_3877165
  have hstable : (prefixWord ++ tailWord_3877165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3877165).length < 2 ^ (prefixWord ++ tailWord_3877165).sum := by decide
  have hdescent : baseEnd_3877165 < baseStart_3877165 := by decide
  rcases family_descends (prefixWord ++ tailWord_3877165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3877185 : List Nat := [1, 2, 5, 2, 2, 2, 1, 1, 1, 1, 5]
def baseStart_3877185 : Nat := 118140960795 + 3877185 * 2 ^ 59
def prefixEnd_3877185 : Nat := 4983230072969 + 3 ^ 40 * 3877185 * 2
def baseEnd_3877185 : Nat := 1990859491402518229556657

theorem tailTrace_3877185 : CollatzResearch.WordTrace tailWord_3877185 prefixEnd_3877185 1990859491402518229556657 := by
  unfold tailWord_3877185
  simp only [CollatzResearch.WordTrace]
  refine ⟨141412554458628390325025009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94275036305752260216683339 141412554458628390325025009)
  ·
    refine ⟨106059415843971292743768757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141412554458628390325025009 106059415843971292743768757)
    ·
      refine ⟨9943070235372308694728321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 106059415843971292743768757 9943070235372308694728321)
      ·
        refine ⟨7457302676529231521046241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9943070235372308694728321 7457302676529231521046241)
        ·
          refine ⟨5592977007396923640784681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7457302676529231521046241 5592977007396923640784681)
          ·
            refine ⟨4194732755547692730588511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5592977007396923640784681 4194732755547692730588511)
            ·
              refine ⟨6292099133321539095882767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4194732755547692730588511 6292099133321539095882767)
              ·
                refine ⟨9438148699982308643824151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6292099133321539095882767 9438148699982308643824151)
                ·
                  refine ⟨14157223049973462965736227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9438148699982308643824151 14157223049973462965736227)
                  ·
                    refine ⟨21235834574960194448604341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14157223049973462965736227 21235834574960194448604341)
                    ·
                      refine ⟨1990859491402518229556657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21235834574960194448604341 1990859491402518229556657)
                      ·
                        rfl

theorem cell23_3877185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_3877185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3877185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3877185 prefixEnd_3877185 := by exact prefixLift 3877185
  have htrace : WordTrace (prefixWord ++ tailWord_3877185) baseStart_3877185 baseEnd_3877185 := by
    simpa [prefixWord, tailWord_3877185, baseEnd_3877185] using wordTrace_append hprefix tailTrace_3877185
  have hstable : (prefixWord ++ tailWord_3877185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3877185).length < 2 ^ (prefixWord ++ tailWord_3877185).sum := by decide
  have hdescent : baseEnd_3877185 < baseStart_3877185 := by decide
  rcases family_descends (prefixWord ++ tailWord_3877185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3877188 : List Nat := [2, 3, 4, 1, 3, 10]
def baseStart_3877188 : Nat := 118140960795 + 3877188 * 2 ^ 59
def prefixEnd_3877188 : Nat := 4983230072969 + 3 ^ 40 * 3877188 * 2
def baseEnd_3877188 : Nat := 8192843752446426822301

theorem tailTrace_3877188 : CollatzResearch.WordTrace tailWord_3877188 prefixEnd_3877188 8192843752446426822301 := by
  unfold tailWord_3877188
  simp only [CollatzResearch.WordTrace]
  refine ⟨70706331938808760918692109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94275109251745014558256145 70706331938808760918692109)
  ·
    refine ⟨26514874477053285344509541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70706331938808760918692109 26514874477053285344509541)
    ·
      refine ⟨4971538964447491002095539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26514874477053285344509541 4971538964447491002095539)
      ·
        refine ⟨7457308446671236503143309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4971538964447491002095539 7457308446671236503143309)
        ·
          refine ⟨2796490667501713688678741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7457308446671236503143309 2796490667501713688678741)
          ·
            refine ⟨8192843752446426822301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2796490667501713688678741 8192843752446426822301)
            ·
              rfl

theorem cell23_3877188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 10].length) (baseStart_3877188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3877188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3877188 prefixEnd_3877188 := by exact prefixLift 3877188
  have htrace : WordTrace (prefixWord ++ tailWord_3877188) baseStart_3877188 baseEnd_3877188 := by
    simpa [prefixWord, tailWord_3877188, baseEnd_3877188] using wordTrace_append hprefix tailTrace_3877188
  have hstable : (prefixWord ++ tailWord_3877188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3877188).length < 2 ^ (prefixWord ++ tailWord_3877188).sum := by decide
  have hdescent : baseEnd_3877188 < baseStart_3877188 := by decide
  rcases family_descends (prefixWord ++ tailWord_3877188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3877194 : List Nat := [3, 1, 2, 1, 1, 1, 1, 1, 2, 3, 7]
def baseStart_3877194 : Nat := 118140960795 + 3877194 * 2 ^ 59
def prefixEnd_3877194 : Nat := 4983230072969 + 3 ^ 40 * 3877194 * 2
def baseEnd_3877194 : Nat := 1990864112728408694344115

theorem tailTrace_3877194 : CollatzResearch.WordTrace tailWord_3877194 prefixEnd_3877194 1990864112728408694344115 := by
  unfold tailWord_3877194
  simp only [CollatzResearch.WordTrace]
  refine ⟨35353220678898946215525659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94275255143730523241401757 35353220678898946215525659)
  ·
    refine ⟨53029831018348419323288489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35353220678898946215525659 53029831018348419323288489)
    ·
      refine ⟨39772373263761314492466367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53029831018348419323288489 39772373263761314492466367)
      ·
        refine ⟨59658559895641971738699551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39772373263761314492466367 59658559895641971738699551)
        ·
          refine ⟨89487839843462957608049327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59658559895641971738699551 89487839843462957608049327)
          ·
            refine ⟨134231759765194436412073991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89487839843462957608049327 134231759765194436412073991)
            ·
              refine ⟨201347639647791654618110987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 134231759765194436412073991 201347639647791654618110987)
              ·
                refine ⟨302021459471687481927166481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 201347639647791654618110987 302021459471687481927166481)
                ·
                  refine ⟨226516094603765611445374861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 302021459471687481927166481 226516094603765611445374861)
                  ·
                    refine ⟨84943535476412104292015573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 226516094603765611445374861 84943535476412104292015573)
                    ·
                      refine ⟨1990864112728408694344115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 84943535476412104292015573 1990864112728408694344115)
                      ·
                        rfl

theorem cell23_3877194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 2, 3, 7].length) (baseStart_3877194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3877194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3877194 prefixEnd_3877194 := by exact prefixLift 3877194
  have htrace : WordTrace (prefixWord ++ tailWord_3877194) baseStart_3877194 baseEnd_3877194 := by
    simpa [prefixWord, tailWord_3877194, baseEnd_3877194] using wordTrace_append hprefix tailTrace_3877194
  have hstable : (prefixWord ++ tailWord_3877194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3877194).length < 2 ^ (prefixWord ++ tailWord_3877194).sum := by decide
  have hdescent : baseEnd_3877194 < baseStart_3877194 := by decide
  rcases family_descends (prefixWord ++ tailWord_3877194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3877255 : List Nat := [1, 1, 4, 2, 2, 1, 3, 1, 4, 2, 2]
def baseStart_3877255 : Nat := 118140960795 + 3877255 * 2 ^ 59
def prefixEnd_3877255 : Nat := 4983230072969 + 3 ^ 40 * 3877255 * 2
def baseEnd_3877255 : Nat := 1990895435048332955681335

theorem tailTrace_3877255 : CollatzResearch.WordTrace tailWord_3877255 prefixEnd_3877255 1990895435048332955681335 := by
  unfold tailWord_3877255
  simp only [CollatzResearch.WordTrace]
  refine ⟨141415107568374792280073219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94276738378916528186715479 141415107568374792280073219)
  ·
    refine ⟨212122661352562188420109829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141415107568374792280073219 212122661352562188420109829)
    ·
      refine ⟨39772999003605410328770593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 212122661352562188420109829 39772999003605410328770593)
      ·
        refine ⟨29829749252704057746577945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39772999003605410328770593 29829749252704057746577945)
        ·
          refine ⟨22372311939528043309933459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29829749252704057746577945 22372311939528043309933459)
          ·
            refine ⟨33558467909292064964900189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22372311939528043309933459 33558467909292064964900189)
            ·
              refine ⟨12584425465984524361837571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33558467909292064964900189 12584425465984524361837571)
              ·
                refine ⟨18876638198976786542756357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12584425465984524361837571 18876638198976786542756357)
                ·
                  refine ⟨3539369662308147476766817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18876638198976786542756357 3539369662308147476766817)
                  ·
                    refine ⟨2654527246731110607575113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3539369662308147476766817 2654527246731110607575113)
                    ·
                      refine ⟨1990895435048332955681335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2654527246731110607575113 1990895435048332955681335)
                      ·
                        rfl

theorem cell23_3877255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 1, 4, 2, 2].length) (baseStart_3877255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3877255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3877255 prefixEnd_3877255 := by exact prefixLift 3877255
  have htrace : WordTrace (prefixWord ++ tailWord_3877255) baseStart_3877255 baseEnd_3877255 := by
    simpa [prefixWord, tailWord_3877255, baseEnd_3877255] using wordTrace_append hprefix tailTrace_3877255
  have hstable : (prefixWord ++ tailWord_3877255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3877255).length < 2 ^ (prefixWord ++ tailWord_3877255).sum := by decide
  have hdescent : baseEnd_3877255 < baseStart_3877255 := by decide
  rcases family_descends (prefixWord ++ tailWord_3877255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3877272 : List Nat := [2, 1, 2, 5, 1, 3, 1, 1, 1, 4, 2]
def baseStart_3877272 : Nat := 118140960795 + 3877272 * 2 ^ 59
def prefixEnd_3877272 : Nat := 4983230072969 + 3 ^ 40 * 3877272 * 2
def baseEnd_3877272 : Nat := 1990904164219459389168757

theorem tailTrace_3877272 : CollatzResearch.WordTrace tailWord_3877272 prefixEnd_3877272 1990904164219459389168757 := by
  unfold tailWord_3877272
  simp only [CollatzResearch.WordTrace]
  refine ⟨70707863804656602091721035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94277151739542136122294713 70707863804656602091721035)
  ·
    refine ⟨106061795706984903137581553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70707863804656602091721035 106061795706984903137581553)
    ·
      refine ⟨79546346780238677353186165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106061795706984903137581553 79546346780238677353186165)
      ·
        refine ⟨7457470010647376001861203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 79546346780238677353186165 7457470010647376001861203)
        ·
          refine ⟨11186205015971064002791805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7457470010647376001861203 11186205015971064002791805)
          ·
            refine ⟨4194826880989149001046927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11186205015971064002791805 4194826880989149001046927)
            ·
              refine ⟨6292240321483723501570391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4194826880989149001046927 6292240321483723501570391)
              ·
                refine ⟨9438360482225585252355587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6292240321483723501570391 9438360482225585252355587)
                ·
                  refine ⟨14157540723338377878533381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9438360482225585252355587 14157540723338377878533381)
                  ·
                    refine ⟨2654538885625945852225009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14157540723338377878533381 2654538885625945852225009)
                    ·
                      refine ⟨1990904164219459389168757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2654538885625945852225009 1990904164219459389168757)
                      ·
                        rfl

theorem cell23_3877272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 1, 1, 1, 4, 2].length) (baseStart_3877272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3877272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3877272 prefixEnd_3877272 := by exact prefixLift 3877272
  have htrace : WordTrace (prefixWord ++ tailWord_3877272) baseStart_3877272 baseEnd_3877272 := by
    simpa [prefixWord, tailWord_3877272, baseEnd_3877272] using wordTrace_append hprefix tailTrace_3877272
  have hstable : (prefixWord ++ tailWord_3877272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3877272).length < 2 ^ (prefixWord ++ tailWord_3877272).sum := by decide
  have hdescent : baseEnd_3877272 < baseStart_3877272 := by decide
  rcases family_descends (prefixWord ++ tailWord_3877272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3877308 : List Nat := [2, 2, 2, 4, 1, 1, 1, 1, 4, 5]
def baseStart_3877308 : Nat := 118140960795 + 3877308 * 2 ^ 59
def prefixEnd_3877308 : Nat := 4983230072969 + 3 ^ 40 * 3877308 * 2
def baseEnd_3877308 : Nat := 663640883174340416106197

theorem tailTrace_3877308 : CollatzResearch.WordTrace tailWord_3877308 prefixEnd_3877308 663640883174340416106197 := by
  unfold tailWord_3877308
  simp only [CollatzResearch.WordTrace]
  refine ⟨70708520318591391165876289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94278027091455188221168385 70708520318591391165876289)
  ·
    refine ⟨53031390238943543374407217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70708520318591391165876289 53031390238943543374407217)
    ·
      refine ⟨39773542679207657530805413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53031390238943543374407217 39773542679207657530805413)
      ·
        refine ⟨7457539252351435787026015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39773542679207657530805413 7457539252351435787026015)
        ·
          refine ⟨11186308878527153680539023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7457539252351435787026015 11186308878527153680539023)
          ·
            refine ⟨16779463317790730520808535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11186308878527153680539023 16779463317790730520808535)
            ·
              refine ⟨25169194976686095781212803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16779463317790730520808535 25169194976686095781212803)
              ·
                refine ⟨37753792465029143671819205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25169194976686095781212803 37753792465029143671819205)
                ·
                  refine ⟨7078836087192964438466101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37753792465029143671819205 7078836087192964438466101)
                  ·
                    refine ⟨663640883174340416106197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7078836087192964438466101 663640883174340416106197)
                    ·
                      rfl

theorem cell23_3877308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 1, 4, 5].length) (baseStart_3877308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3877308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3877308 prefixEnd_3877308 := by exact prefixLift 3877308
  have htrace : WordTrace (prefixWord ++ tailWord_3877308) baseStart_3877308 baseEnd_3877308 := by
    simpa [prefixWord, tailWord_3877308, baseEnd_3877308] using wordTrace_append hprefix tailTrace_3877308
  have hstable : (prefixWord ++ tailWord_3877308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3877308).length < 2 ^ (prefixWord ++ tailWord_3877308).sum := by decide
  have hdescent : baseEnd_3877308 < baseStart_3877308 := by decide
  rcases family_descends (prefixWord ++ tailWord_3877308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3877338 : List Nat := [3, 1, 1, 2, 3, 1, 2, 1, 5, 4]
def baseStart_3877338 : Nat := 118140960795 + 3877338 * 2 ^ 59
def prefixEnd_3877338 : Nat := 4983230072969 + 3 ^ 40 * 3877338 * 2
def baseEnd_3877338 : Nat := 663646017980885376981151

theorem tailTrace_3877338 : CollatzResearch.WordTrace tailWord_3877338 prefixEnd_3877338 663646017980885376981151 := by
  unfold tailWord_3877338
  simp only [CollatzResearch.WordTrace]
  refine ⟨35354533706768524363836167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94278756551382731636896445 35354533706768524363836167)
  ·
    refine ⟨53031800560152786545754251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35354533706768524363836167 53031800560152786545754251)
    ·
      refine ⟨79547700840229179818631377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53031800560152786545754251 79547700840229179818631377)
      ·
        refine ⟨59660775630171884863973533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79547700840229179818631377 59660775630171884863973533)
        ·
          refine ⟨22372790861314456823990075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59660775630171884863973533 22372790861314456823990075)
          ·
            refine ⟨33559186291971685235985113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22372790861314456823990075 33559186291971685235985113)
            ·
              refine ⟨25169389718978763926988835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33559186291971685235985113 25169389718978763926988835)
              ·
                refine ⟨37754084578468145890483253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25169389718978763926988835 37754084578468145890483253)
                ·
                  refine ⟨3539445429231388677232805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37754084578468145890483253 3539445429231388677232805)
                  ·
                    refine ⟨663646017980885376981151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3539445429231388677232805 663646017980885376981151)
                    ·
                      rfl

theorem cell23_3877338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 1, 5, 4].length) (baseStart_3877338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3877338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3877338 prefixEnd_3877338 := by exact prefixLift 3877338
  have htrace : WordTrace (prefixWord ++ tailWord_3877338) baseStart_3877338 baseEnd_3877338 := by
    simpa [prefixWord, tailWord_3877338, baseEnd_3877338] using wordTrace_append hprefix tailTrace_3877338
  have hstable : (prefixWord ++ tailWord_3877338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3877338).length < 2 ^ (prefixWord ++ tailWord_3877338).sum := by decide
  have hdescent : baseEnd_3877338 < baseStart_3877338 := by decide
  rcases family_descends (prefixWord ++ tailWord_3877338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3877355 : List Nat := [1, 1, 1, 1, 2, 3, 4, 5, 1, 4]
def baseStart_3877355 : Nat := 118140960795 + 3877355 * 2 ^ 59
def prefixEnd_3877355 : Nat := 4983230072969 + 3 ^ 40 * 3877355 * 2
def baseEnd_3877355 : Nat := 663648927704594188143625

theorem tailTrace_3877355 : CollatzResearch.WordTrace tailWord_3877355 prefixEnd_3877355 663648927704594188143625 := by
  unfold tailWord_3877355
  simp only [CollatzResearch.WordTrace]
  refine ⟨141418754868012509358713519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94279169912008339572475679 141418754868012509358713519)
  ·
    refine ⟨212128132302018764038070279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141418754868012509358713519 212128132302018764038070279)
    ·
      refine ⟨318192198453028146057105419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212128132302018764038070279 318192198453028146057105419)
      ·
        refine ⟨477288297679542219085658129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318192198453028146057105419 477288297679542219085658129)
        ·
          refine ⟨357966223259656664314243597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 477288297679542219085658129 357966223259656664314243597)
          ·
            refine ⟨134237333722371249117841349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 357966223259656664314243597 134237333722371249117841349)
            ·
              refine ⟨25169500072944609209595253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 134237333722371249117841349 25169500072944609209595253)
              ·
                refine ⟨2359640631838557113399555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25169500072944609209595253 2359640631838557113399555)
                ·
                  refine ⟨3539460947757835670099333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2359640631838557113399555 3539460947757835670099333)
                  ·
                    refine ⟨663648927704594188143625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3539460947757835670099333 663648927704594188143625)
                    ·
                      rfl

theorem cell23_3877355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 5, 1, 4].length) (baseStart_3877355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3877355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3877355 prefixEnd_3877355 := by exact prefixLift 3877355
  have htrace : WordTrace (prefixWord ++ tailWord_3877355) baseStart_3877355 baseEnd_3877355 := by
    simpa [prefixWord, tailWord_3877355, baseEnd_3877355] using wordTrace_append hprefix tailTrace_3877355
  have hstable : (prefixWord ++ tailWord_3877355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3877355).length < 2 ^ (prefixWord ++ tailWord_3877355).sum := by decide
  have hdescent : baseEnd_3877355 < baseStart_3877355 := by decide
  rcases family_descends (prefixWord ++ tailWord_3877355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3877368 : List Nat := [2, 1, 2, 1, 1, 4, 4, 2, 6]
def baseStart_3877368 : Nat := 118140960795 + 3877368 * 2 ^ 59
def prefixEnd_3877368 : Nat := 4983230072969 + 3 ^ 40 * 3877368 * 2
def baseEnd_3877368 : Nat := 221217050929143445952035

theorem tailTrace_3877368 : CollatzResearch.WordTrace tailWord_3877368 prefixEnd_3877368 221217050929143445952035 := by
  unfold tailWord_3877368
  simp only [CollatzResearch.WordTrace]
  refine ⟨70709614508482706289468379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94279486011310275052624505 70709614508482706289468379)
  ·
    refine ⟨106064421762724059434202569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70709614508482706289468379 106064421762724059434202569)
    ·
      refine ⟨79548316322043044575651927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106064421762724059434202569 79548316322043044575651927)
      ·
        refine ⟨119322474483064566863477891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79548316322043044575651927 119322474483064566863477891)
        ·
          refine ⟨178983711724596850295216837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119322474483064566863477891 178983711724596850295216837)
          ·
            refine ⟨33559445948361909430353157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 178983711724596850295216837 33559445948361909430353157)
            ·
              refine ⟨6292396115317858018191217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33559445948361909430353157 6292396115317858018191217)
              ·
                refine ⟨4719297086488393513643413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6292396115317858018191217 4719297086488393513643413)
                ·
                  refine ⟨221217050929143445952035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4719297086488393513643413 221217050929143445952035)
                  ·
                    rfl

theorem cell23_3877368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 4, 2, 6].length) (baseStart_3877368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3877368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3877368 prefixEnd_3877368 := by exact prefixLift 3877368
  have htrace : WordTrace (prefixWord ++ tailWord_3877368) baseStart_3877368 baseEnd_3877368 := by
    simpa [prefixWord, tailWord_3877368, baseEnd_3877368] using wordTrace_append hprefix tailTrace_3877368
  have hstable : (prefixWord ++ tailWord_3877368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3877368).length < 2 ^ (prefixWord ++ tailWord_3877368).sum := by decide
  have hdescent : baseEnd_3877368 < baseStart_3877368 := by decide
  rcases family_descends (prefixWord ++ tailWord_3877368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3877389 : List Nat := [1, 7, 1, 1, 1, 2, 1, 2, 3, 4]
def baseStart_3877389 : Nat := 118140960795 + 3877389 * 2 ^ 59
def prefixEnd_3877389 : Nat := 4983230072969 + 3 ^ 40 * 3877389 * 2
def baseEnd_3877389 : Nat := 663654747152011810468573

theorem tailTrace_3877389 : CollatzResearch.WordTrace tailWord_3877389 prefixEnd_3877389 663654747152011810468573 := by
  unfold tailWord_3877389
  simp only [CollatzResearch.WordTrace]
  refine ⟨141419994949889333165451221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94279996633259555443634147 141419994949889333165451221)
  ·
    refine ⟨3314531131638031246065263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 141419994949889333165451221 3314531131638031246065263)
    ·
      refine ⟨4971796697457046869097895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3314531131638031246065263 4971796697457046869097895)
      ·
        refine ⟨7457695046185570303646843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4971796697457046869097895 7457695046185570303646843)
        ·
          refine ⟨11186542569278355455470265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7457695046185570303646843 11186542569278355455470265)
          ·
            refine ⟨8389906926958766591602699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11186542569278355455470265 8389906926958766591602699)
            ·
              refine ⟨12584860390438149887404049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8389906926958766591602699 12584860390438149887404049)
              ·
                refine ⟨9438645292828612415553037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12584860390438149887404049 9438645292828612415553037)
                ·
                  refine ⟨3539491984810729655832389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9438645292828612415553037 3539491984810729655832389)
                  ·
                    refine ⟨663654747152011810468573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3539491984810729655832389 663654747152011810468573)
                    ·
                      rfl

theorem cell23_3877389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_3877389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3877389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3877389 prefixEnd_3877389 := by exact prefixLift 3877389
  have htrace : WordTrace (prefixWord ++ tailWord_3877389) baseStart_3877389 baseEnd_3877389 := by
    simpa [prefixWord, tailWord_3877389, baseEnd_3877389] using wordTrace_append hprefix tailTrace_3877389
  have hstable : (prefixWord ++ tailWord_3877389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3877389).length < 2 ^ (prefixWord ++ tailWord_3877389).sum := by decide
  have hdescent : baseEnd_3877389 < baseStart_3877389 := by decide
  rcases family_descends (prefixWord ++ tailWord_3877389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3877395 : List Nat := [1, 1, 1, 2, 1, 5, 3, 2, 3, 1, 3]
def baseStart_3877395 : Nat := 118140960795 + 3877395 * 2 ^ 59
def prefixEnd_3877395 : Nat := 4983230072969 + 3 ^ 40 * 3877395 * 2
def baseEnd_3877395 : Nat := 1990967322339962407930691

theorem tailTrace_3877395 : CollatzResearch.WordTrace tailWord_3877395 prefixEnd_3877395 1990967322339962407930691 := by
  unfold tailWord_3877395
  simp only [CollatzResearch.WordTrace]
  refine ⟨141420213787867596190169639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94280142525245064126779759 141420213787867596190169639)
  ·
    refine ⟨212130320681801394285254459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141420213787867596190169639 212130320681801394285254459)
    ·
      refine ⟨318195481022702091427881689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212130320681801394285254459 318195481022702091427881689)
      ·
        refine ⟨238646610767026568570911267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 318195481022702091427881689 238646610767026568570911267)
        ·
          refine ⟨357969916150539852856366901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238646610767026568570911267 357969916150539852856366901)
          ·
            refine ⟨33559679639113111205284397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 357969916150539852856366901 33559679639113111205284397)
            ·
              refine ⟨12584879864667416701981649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33559679639113111205284397 12584879864667416701981649)
              ·
                refine ⟨9438659898500562526486237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12584879864667416701981649 9438659898500562526486237)
                ·
                  refine ⟨3539497461937710947432339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9438659898500562526486237 3539497461937710947432339)
                  ·
                    refine ⟨5309246192906566421148509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3539497461937710947432339 5309246192906566421148509)
                    ·
                      refine ⟨1990967322339962407930691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5309246192906566421148509 1990967322339962407930691)
                      ·
                        rfl

theorem cell23_3877395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 2, 3, 1, 3].length) (baseStart_3877395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3877395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3877395 prefixEnd_3877395 := by exact prefixLift 3877395
  have htrace : WordTrace (prefixWord ++ tailWord_3877395) baseStart_3877395 baseEnd_3877395 := by
    simpa [prefixWord, tailWord_3877395, baseEnd_3877395] using wordTrace_append hprefix tailTrace_3877395
  have hstable : (prefixWord ++ tailWord_3877395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3877395).length < 2 ^ (prefixWord ++ tailWord_3877395).sum := by decide
  have hdescent : baseEnd_3877395 < baseStart_3877395 := by decide
  rcases family_descends (prefixWord ++ tailWord_3877395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3877399 : List Nat := [1, 1, 3, 6, 1, 2, 1, 1, 2, 2, 3]
def baseStart_3877399 : Nat := 118140960795 + 3877399 * 2 ^ 59
def prefixEnd_3877399 : Nat := 4983230072969 + 3 ^ 40 * 3877399 * 2
def baseEnd_3877399 : Nat := 1990969376262580392280673

theorem tailTrace_3877399 : CollatzResearch.WordTrace tailWord_3877399 prefixEnd_3877399 1990969376262580392280673 := by
  unfold tailWord_3877399
  simp only [CollatzResearch.WordTrace]
  refine ⟨141420359679853104873315251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94280239786568736582210167 141420359679853104873315251)
  ·
    refine ⟨212130539519779657309972877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141420359679853104873315251 212130539519779657309972877)
    ·
      refine ⟨79548952319917371491239829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212130539519779657309972877 79548952319917371491239829)
      ·
        refine ⟨3728857139996126788651867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 79548952319917371491239829 3728857139996126788651867)
        ·
          refine ⟨5593285709994190182977801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3728857139996126788651867 5593285709994190182977801)
          ·
            refine ⟨4194964282495642637233351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5593285709994190182977801 4194964282495642637233351)
            ·
              refine ⟨6292446423743463955850027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4194964282495642637233351 6292446423743463955850027)
              ·
                refine ⟨9438669635615195933775041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6292446423743463955850027 9438669635615195933775041)
                ·
                  refine ⟨7079002226711396950331281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9438669635615195933775041 7079002226711396950331281)
                  ·
                    refine ⟨5309251670033547712748461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7079002226711396950331281 5309251670033547712748461)
                    ·
                      refine ⟨1990969376262580392280673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5309251670033547712748461 1990969376262580392280673)
                      ·
                        rfl

theorem cell23_3877399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_3877399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3877399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3877399 prefixEnd_3877399 := by exact prefixLift 3877399
  have htrace : WordTrace (prefixWord ++ tailWord_3877399) baseStart_3877399 baseEnd_3877399 := by
    simpa [prefixWord, tailWord_3877399, baseEnd_3877399] using wordTrace_append hprefix tailTrace_3877399
  have hstable : (prefixWord ++ tailWord_3877399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3877399).length < 2 ^ (prefixWord ++ tailWord_3877399).sum := by decide
  have hdescent : baseEnd_3877399 < baseStart_3877399 := by decide
  rcases family_descends (prefixWord ++ tailWord_3877399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3877445 : List Nat := [1, 3, 1, 1, 1, 7, 1, 1, 1, 6]
def baseStart_3877445 : Nat := 118140960795 + 3877445 * 2 ^ 59
def prefixEnd_3877445 : Nat := 4983230072969 + 3 ^ 40 * 3877445 * 2
def baseEnd_3877445 : Nat := 663664332124229070768487

theorem tailTrace_3877445 : CollatzResearch.WordTrace tailWord_3877445 prefixEnd_3877445 663664332124229070768487 := by
  unfold tailWord_3877445
  simp only [CollatzResearch.WordTrace]
  refine ⟨141422037437686454729489789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94281358291790969819659859 141422037437686454729489789)
  ·
    refine ⟨53033264039132420523558671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141422037437686454729489789 53033264039132420523558671)
    ·
      refine ⟨79549896058698630785338007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53033264039132420523558671 79549896058698630785338007)
      ·
        refine ⟨119324844088047946178007011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79549896058698630785338007 119324844088047946178007011)
        ·
          refine ⟨178987266132071919267010517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119324844088047946178007011 178987266132071919267010517)
          ·
            refine ⟨4195014049970435607820559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 178987266132071919267010517 4195014049970435607820559)
            ·
              refine ⟨6292521074955653411730839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4195014049970435607820559 6292521074955653411730839)
              ·
                refine ⟨9438781612433480117596259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6292521074955653411730839 9438781612433480117596259)
                ·
                  refine ⟨14158172418650220176394389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9438781612433480117596259 14158172418650220176394389)
                  ·
                    refine ⟨663664332124229070768487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14158172418650220176394389 663664332124229070768487)
                    ·
                      rfl

theorem cell23_3877445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 1, 1, 1, 6].length) (baseStart_3877445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3877445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3877445 prefixEnd_3877445 := by exact prefixLift 3877445
  have htrace : WordTrace (prefixWord ++ tailWord_3877445) baseStart_3877445 baseEnd_3877445 := by
    simpa [prefixWord, tailWord_3877445, baseEnd_3877445] using wordTrace_append hprefix tailTrace_3877445
  have hstable : (prefixWord ++ tailWord_3877445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3877445).length < 2 ^ (prefixWord ++ tailWord_3877445).sum := by decide
  have hdescent : baseEnd_3877445 < baseStart_3877445 := by decide
  rcases family_descends (prefixWord ++ tailWord_3877445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3877452 : List Nat := [2, 2, 1, 3, 1, 2, 1, 4, 3, 2, 2]
def baseStart_3877452 : Nat := 118140960795 + 3877452 * 2 ^ 59
def prefixEnd_3877452 : Nat := 4983230072969 + 3 ^ 40 * 3877452 * 2
def baseEnd_3877452 : Nat := 1990996590737268684917929

theorem tailTrace_3877452 : CollatzResearch.WordTrace tailWord_3877452 prefixEnd_3877452 1990996590737268684917929 := by
  unfold tailWord_3877452
  simp only [CollatzResearch.WordTrace]
  refine ⟨70711146374330547462497305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94281528499107396616663073 70711146374330547462497305)
  ·
    refine ⟨53033359780747910596872979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70711146374330547462497305 53033359780747910596872979)
    ·
      refine ⟨79550039671121865895309469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53033359780747910596872979 79550039671121865895309469)
      ·
        refine ⟨29831264876670699710741051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 79550039671121865895309469 29831264876670699710741051)
        ·
          refine ⟨44746897315006049566111577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29831264876670699710741051 44746897315006049566111577)
          ·
            refine ⟨33560172986254537174583683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44746897315006049566111577 33560172986254537174583683)
            ·
              refine ⟨50340259479381805761875525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33560172986254537174583683 50340259479381805761875525)
              ·
                refine ⟨9438798652384088580351661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50340259479381805761875525 9438798652384088580351661)
                ·
                  refine ⟨3539549494644033217631873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9438798652384088580351661 3539549494644033217631873)
                  ·
                    refine ⟨2654662120983024913223905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3539549494644033217631873 2654662120983024913223905)
                    ·
                      refine ⟨1990996590737268684917929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2654662120983024913223905 1990996590737268684917929)
                      ·
                        rfl

theorem cell23_3877452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 4, 3, 2, 2].length) (baseStart_3877452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3877452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3877452 prefixEnd_3877452 := by exact prefixLift 3877452
  have htrace : WordTrace (prefixWord ++ tailWord_3877452) baseStart_3877452 baseEnd_3877452 := by
    simpa [prefixWord, tailWord_3877452, baseEnd_3877452] using wordTrace_append hprefix tailTrace_3877452
  have hstable : (prefixWord ++ tailWord_3877452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3877452).length < 2 ^ (prefixWord ++ tailWord_3877452).sum := by decide
  have hdescent : baseEnd_3877452 < baseStart_3877452 := by decide
  rcases family_descends (prefixWord ++ tailWord_3877452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3877455 : List Nat := [1, 1, 2, 1, 1, 2, 5, 4, 1, 2, 3]
def baseStart_3877455 : Nat := 118140960795 + 3877455 * 2 ^ 59
def prefixEnd_3877455 : Nat := 4983230072969 + 3 ^ 40 * 3877455 * 2
def baseEnd_3877455 : Nat := 1990998131179232173180415

theorem tailTrace_3877455 : CollatzResearch.WordTrace tailWord_3877455 prefixEnd_3877455 1990998131179232173180415 := by
  unfold tailWord_3877455
  simp only [CollatzResearch.WordTrace]
  refine ⟨141422402167650226437353819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94281601445100150958235879 141422402167650226437353819)
  ·
    refine ⟨212133603251475339656030729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141422402167650226437353819 212133603251475339656030729)
    ·
      refine ⟨159100202438606504742023047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212133603251475339656030729 159100202438606504742023047)
      ·
        refine ⟨238650303657909757113034571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159100202438606504742023047 238650303657909757113034571)
        ·
          refine ⟨357975455486864635669551857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238650303657909757113034571 357975455486864635669551857)
          ·
            refine ⟨268481591615148476752163893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 357975455486864635669551857 268481591615148476752163893)
            ·
              refine ⟨25170149213920169695515365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 268481591615148476752163893 25170149213920169695515365)
              ·
                refine ⟨4719402977610031817909131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25170149213920169695515365 4719402977610031817909131)
                ·
                  refine ⟨7079104466415047726863697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4719402977610031817909131 7079104466415047726863697)
                  ·
                    refine ⟨5309328349811285795147773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7079104466415047726863697 5309328349811285795147773)
                    ·
                      refine ⟨1990998131179232173180415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5309328349811285795147773 1990998131179232173180415)
                      ·
                        rfl

theorem cell23_3877455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 4, 1, 2, 3].length) (baseStart_3877455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3877455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3877455 prefixEnd_3877455 := by exact prefixLift 3877455
  have htrace : WordTrace (prefixWord ++ tailWord_3877455) baseStart_3877455 baseEnd_3877455 := by
    simpa [prefixWord, tailWord_3877455, baseEnd_3877455] using wordTrace_append hprefix tailTrace_3877455
  have hstable : (prefixWord ++ tailWord_3877455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3877455).length < 2 ^ (prefixWord ++ tailWord_3877455).sum := by decide
  have hdescent : baseEnd_3877455 < baseStart_3877455 := by decide
  rcases family_descends (prefixWord ++ tailWord_3877455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3877458 : List Nat := [3, 2, 2, 1, 2, 1, 3, 9]
def baseStart_3877458 : Nat := 118140960795 + 3877458 * 2 ^ 59
def prefixEnd_3877458 : Nat := 4983230072969 + 3 ^ 40 * 3877458 * 2
def baseEnd_3877458 : Nat := 73740728578562802275663

theorem tailTrace_3877458 : CollatzResearch.WordTrace tailWord_3877458 prefixEnd_3877458 73740728578562802275663 := by
  unfold tailWord_3877458
  simp only [CollatzResearch.WordTrace]
  refine ⟨35355627896659839487428257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94281674391092905299808685 35355627896659839487428257)
  ·
    refine ⟨26516720922494879615571193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35355627896659839487428257 26516720922494879615571193)
    ·
      refine ⟨19887540691871159711678395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26516720922494879615571193 19887540691871159711678395)
      ·
        refine ⟨29831311037806739567517593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19887540691871159711678395 29831311037806739567517593)
        ·
          refine ⟨22373483278355054675638195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29831311037806739567517593 22373483278355054675638195)
          ·
            refine ⟨33560224917532582013457293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22373483278355054675638195 33560224917532582013457293)
            ·
              refine ⟨12585084344074718255046485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33560224917532582013457293 12585084344074718255046485)
              ·
                refine ⟨73740728578562802275663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12585084344074718255046485 73740728578562802275663)
                ·
                  rfl

theorem cell23_3877458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 9].length) (baseStart_3877458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3877458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3877458 prefixEnd_3877458 := by exact prefixLift 3877458
  have htrace : WordTrace (prefixWord ++ tailWord_3877458) baseStart_3877458 baseEnd_3877458 := by
    simpa [prefixWord, tailWord_3877458, baseEnd_3877458] using wordTrace_append hprefix tailTrace_3877458
  have hstable : (prefixWord ++ tailWord_3877458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3877458).length < 2 ^ (prefixWord ++ tailWord_3877458).sum := by decide
  have hdescent : baseEnd_3877458 < baseStart_3877458 := by decide
  rcases family_descends (prefixWord ++ tailWord_3877458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3877486 : List Nat := [4, 1, 2, 2, 2, 3, 1, 1, 3, 2, 2]
def baseStart_3877486 : Nat := 118140960795 + 3877486 * 2 ^ 59
def prefixEnd_3877486 : Nat := 4983230072969 + 3 ^ 40 * 3877486 * 2
def baseEnd_3877486 : Nat := 1991014049079521551892773

theorem tailTrace_3877486 : CollatzResearch.WordTrace tailWord_3877486 prefixEnd_3877486 1991014049079521551892773 := by
  unfold tailWord_3877486
  simp only [CollatzResearch.WordTrace]
  refine ⟨17677941603817239841466539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94282355220358612487821541 17677941603817239841466539)
  ·
    refine ⟨26516912405725859762199809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17677941603817239841466539 26516912405725859762199809)
    ·
      refine ⟨19887684304294394821649857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26516912405725859762199809 19887684304294394821649857)
      ·
        refine ⟨14915763228220796116237393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19887684304294394821649857 14915763228220796116237393)
        ·
          refine ⟨11186822421165597087178045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14915763228220796116237393 11186822421165597087178045)
          ·
            refine ⟨4195058407937098907691767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11186822421165597087178045 4195058407937098907691767)
            ·
              refine ⟨6292587611905648361537651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4195058407937098907691767 6292587611905648361537651)
              ·
                refine ⟨9438881417858472542306477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6292587611905648361537651 9438881417858472542306477)
                ·
                  refine ⟨3539580531696927203364929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9438881417858472542306477 3539580531696927203364929)
                  ·
                    refine ⟨2654685398772695402523697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3539580531696927203364929 2654685398772695402523697)
                    ·
                      refine ⟨1991014049079521551892773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2654685398772695402523697 1991014049079521551892773)
                      ·
                        rfl

theorem cell23_3877486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 1, 1, 3, 2, 2].length) (baseStart_3877486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3877486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3877486 prefixEnd_3877486 := by exact prefixLift 3877486
  have htrace : WordTrace (prefixWord ++ tailWord_3877486) baseStart_3877486 baseEnd_3877486 := by
    simpa [prefixWord, tailWord_3877486, baseEnd_3877486] using wordTrace_append hprefix tailTrace_3877486
  have hstable : (prefixWord ++ tailWord_3877486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3877486).length < 2 ^ (prefixWord ++ tailWord_3877486).sum := by decide
  have hdescent : baseEnd_3877486 < baseStart_3877486 := by decide
  rcases family_descends (prefixWord ++ tailWord_3877486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3877529 : List Nat := [1, 2, 1, 2, 1, 2, 7, 1, 1, 3, 2]
def baseStart_3877529 : Nat := 118140960795 + 3877529 * 2 ^ 59
def prefixEnd_3877529 : Nat := 4983230072969 + 3 ^ 40 * 3877529 * 2
def baseEnd_3877529 : Nat := 1991036128747664883655075

theorem tailTrace_3877529 : CollatzResearch.WordTrace tailWord_3877529 prefixEnd_3877529 1991036128747664883655075 := by
  unfold tailWord_3877529
  simp only [CollatzResearch.WordTrace]
  refine ⟨141425101169382137075547641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94283400779588091383698427 141425101169382137075547641)
  ·
    refine ⟨106068825877036602806660731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141425101169382137075547641 106068825877036602806660731)
    ·
      refine ⟨159103238815554904209991097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106068825877036602806660731 159103238815554904209991097)
      ·
        refine ⟨119327429111666178157493323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159103238815554904209991097 119327429111666178157493323)
        ·
          refine ⟨178991143667499267236239985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119327429111666178157493323 178991143667499267236239985)
          ·
            refine ⟨134243357750624450427179989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 178991143667499267236239985 134243357750624450427179989)
            ·
              refine ⟨3146328697280260556887031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 134243357750624450427179989 3146328697280260556887031)
              ·
                refine ⟨4719493045920390835330547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3146328697280260556887031 4719493045920390835330547)
                ·
                  refine ⟨7079239568880586252995821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4719493045920390835330547 7079239568880586252995821)
                  ·
                    refine ⟨2654714838330219844873433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7079239568880586252995821 2654714838330219844873433)
                    ·
                      refine ⟨1991036128747664883655075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2654714838330219844873433 1991036128747664883655075)
                      ·
                        rfl

theorem cell23_3877529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 7, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 7, 1, 1, 3, 2].length) (baseStart_3877529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3877529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3877529 prefixEnd_3877529 := by exact prefixLift 3877529
  have htrace : WordTrace (prefixWord ++ tailWord_3877529) baseStart_3877529 baseEnd_3877529 := by
    simpa [prefixWord, tailWord_3877529, baseEnd_3877529] using wordTrace_append hprefix tailTrace_3877529
  have hstable : (prefixWord ++ tailWord_3877529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3877529).length < 2 ^ (prefixWord ++ tailWord_3877529).sum := by decide
  have hdescent : baseEnd_3877529 < baseStart_3877529 := by decide
  rcases family_descends (prefixWord ++ tailWord_3877529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3877555 : List Nat := [1, 1, 1, 2, 3, 5, 1, 1, 2, 2, 4]
def baseStart_3877555 : Nat := 118140960795 + 3877555 * 2 ^ 59
def prefixEnd_3877555 : Nat := 4983230072969 + 3 ^ 40 * 3877555 * 2
def baseEnd_3877555 : Nat := 1991049479244681781929955

theorem tailTrace_3877555 : CollatzResearch.WordTrace tailWord_3877555 prefixEnd_3877555 1991049479244681781929955 := by
  unfold tailWord_3877555
  simp only [CollatzResearch.WordTrace]
  refine ⟨141426049467287943515994119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94284032978191962343996079 141426049467287943515994119)
  ·
    refine ⟨212139074200931915273991179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141426049467287943515994119 212139074200931915273991179)
    ·
      refine ⟨318208611301397872910986769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212139074200931915273991179 318208611301397872910986769)
      ·
        refine ⟨238656458476048404683240077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 318208611301397872910986769 238656458476048404683240077)
        ·
          refine ⟨89496171928518151756215029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 238656458476048404683240077 89496171928518151756215029)
          ·
            refine ⟨8390266118298576727145159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 89496171928518151756215029 8390266118298576727145159)
            ·
              refine ⟨12585399177447865090717739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8390266118298576727145159 12585399177447865090717739)
              ·
                refine ⟨18878098766171797636076609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12585399177447865090717739 18878098766171797636076609)
                ·
                  refine ⟨14158574074628848227057457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18878098766171797636076609 14158574074628848227057457)
                  ·
                    refine ⟨10618930555971636170293093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14158574074628848227057457 10618930555971636170293093)
                    ·
                      refine ⟨1991049479244681781929955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10618930555971636170293093 1991049479244681781929955)
                      ·
                        rfl

theorem cell23_3877555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 1, 2, 2, 4].length) (baseStart_3877555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3877555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3877555 prefixEnd_3877555 := by exact prefixLift 3877555
  have htrace : WordTrace (prefixWord ++ tailWord_3877555) baseStart_3877555 baseEnd_3877555 := by
    simpa [prefixWord, tailWord_3877555, baseEnd_3877555] using wordTrace_append hprefix tailTrace_3877555
  have hstable : (prefixWord ++ tailWord_3877555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3877555).length < 2 ^ (prefixWord ++ tailWord_3877555).sum := by decide
  have hdescent : baseEnd_3877555 < baseStart_3877555 := by decide
  rcases family_descends (prefixWord ++ tailWord_3877555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3877559 : List Nat := [1, 1, 3, 1, 6, 1, 2, 1, 1, 4, 2]
def baseStart_3877559 : Nat := 118140960795 + 3877559 * 2 ^ 59
def prefixEnd_3877559 : Nat := 4983230072969 + 3 ^ 40 * 3877559 * 2
def baseEnd_3877559 : Nat := 1991051533167299766279937

theorem tailTrace_3877559 : CollatzResearch.WordTrace tailWord_3877559 prefixEnd_3877559 1991051533167299766279937 := by
  unfold tailWord_3877559
  simp only [CollatzResearch.WordTrace]
  refine ⟨141426195359273452199139731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94284130239515634799426487 141426195359273452199139731)
  ·
    refine ⟨212139293038910178298709597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141426195359273452199139731 212139293038910178298709597)
    ·
      refine ⟨79552234889591316862016099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 212139293038910178298709597 79552234889591316862016099)
      ·
        refine ⟨119328352334386975293024149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79552234889591316862016099 119328352334386975293024149)
        ·
          refine ⟨5593516515674389466860507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 119328352334386975293024149 5593516515674389466860507)
          ·
            refine ⟨8390274773511584200290761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5593516515674389466860507 8390274773511584200290761)
            ·
              refine ⟨6292706080133688150218071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8390274773511584200290761 6292706080133688150218071)
              ·
                refine ⟨9439059120200532225327107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6292706080133688150218071 9439059120200532225327107)
                ·
                  refine ⟨14158588680300798337990661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9439059120200532225327107 14158588680300798337990661)
                  ·
                    refine ⟨2654735377556399688373249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14158588680300798337990661 2654735377556399688373249)
                    ·
                      refine ⟨1991051533167299766279937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2654735377556399688373249 1991051533167299766279937)
                      ·
                        rfl

theorem cell23_3877559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 2, 1, 1, 4, 2].length) (baseStart_3877559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3877559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3877559 prefixEnd_3877559 := by exact prefixLift 3877559
  have htrace : WordTrace (prefixWord ++ tailWord_3877559) baseStart_3877559 baseEnd_3877559 := by
    simpa [prefixWord, tailWord_3877559, baseEnd_3877559] using wordTrace_append hprefix tailTrace_3877559
  have hstable : (prefixWord ++ tailWord_3877559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3877559).length < 2 ^ (prefixWord ++ tailWord_3877559).sum := by decide
  have hdescent : baseEnd_3877559 < baseStart_3877559 := by decide
  rcases family_descends (prefixWord ++ tailWord_3877559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3877565 : List Nat := [1, 4, 1, 2, 1, 4, 1, 2, 7]
def baseStart_3877565 : Nat := 118140960795 + 3877565 * 2 ^ 59
def prefixEnd_3877565 : Nat := 4983230072969 + 3 ^ 40 * 3877565 * 2
def baseEnd_3877565 : Nat := 221228290450136304756101

theorem tailTrace_3877565 : CollatzResearch.WordTrace tailWord_3877565 prefixEnd_3877565 221228290450136304756101 := by
  unfold tailWord_3877565
  simp only [CollatzResearch.WordTrace]
  refine ⟨141426414197251715223858149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94284276131501143482572099 141426414197251715223858149)
  ·
    refine ⟨26517452661984696604473403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141426414197251715223858149 26517452661984696604473403)
    ·
      refine ⟨39776178992977044906710105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26517452661984696604473403 39776178992977044906710105)
      ·
        refine ⟨29832134244732783680032579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39776178992977044906710105 29832134244732783680032579)
        ·
          refine ⟨44748201367099175520048869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29832134244732783680032579 44748201367099175520048869)
          ·
            refine ⟨8390287756331095410009163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44748201367099175520048869 8390287756331095410009163)
            ·
              refine ⟨12585431634496643115013745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8390287756331095410009163 12585431634496643115013745)
              ·
                refine ⟨9439073725872482336260309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12585431634496643115013745 9439073725872482336260309)
                ·
                  refine ⟨221228290450136304756101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9439073725872482336260309 221228290450136304756101)
                  ·
                    rfl

theorem cell23_3877565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 2, 7].length) (baseStart_3877565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3877565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3877565 prefixEnd_3877565 := by exact prefixLift 3877565
  have htrace : WordTrace (prefixWord ++ tailWord_3877565) baseStart_3877565 baseEnd_3877565 := by
    simpa [prefixWord, tailWord_3877565, baseEnd_3877565] using wordTrace_append hprefix tailTrace_3877565
  have hstable : (prefixWord ++ tailWord_3877565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3877565).length < 2 ^ (prefixWord ++ tailWord_3877565).sum := by decide
  have hdescent : baseEnd_3877565 < baseStart_3877565 := by decide
  rcases family_descends (prefixWord ++ tailWord_3877565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3877582 : List Nat := [4, 1, 1, 1, 3, 2, 1, 5, 5]
def baseStart_3877582 : Nat := 118140960795 + 3877582 * 2 ^ 59
def prefixEnd_3877582 : Nat := 4983230072969 + 3 ^ 40 * 3877582 * 2
def baseEnd_3877582 : Nat := 221229260358039241810259

theorem tailTrace_3877582 : CollatzResearch.WordTrace tailWord_3877582 prefixEnd_3877582 221229260358039241810259 := by
  unfold tailWord_3877582
  simp only [CollatzResearch.WordTrace]
  refine ⟨17678379279773765890903375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94284689492126751418151333 17678379279773765890903375)
  ·
    refine ⟨26517568919660648836355063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17678379279773765890903375 26517568919660648836355063)
    ·
      refine ⟨39776353379490973254532595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26517568919660648836355063 39776353379490973254532595)
      ·
        refine ⟨59664530069236459881798893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39776353379490973254532595 59664530069236459881798893)
        ·
          refine ⟨22374198775963672455674585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59664530069236459881798893 22374198775963672455674585)
          ·
            refine ⟨16780649081972754341755939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22374198775963672455674585 16780649081972754341755939)
            ·
              refine ⟨25170973622959131512633909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16780649081972754341755939 25170973622959131512633909)
              ·
                refine ⟨2359778777152418579309429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25170973622959131512633909 2359778777152418579309429)
                ·
                  refine ⟨221229260358039241810259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2359778777152418579309429 221229260358039241810259)
                  ·
                    rfl

theorem cell23_3877582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 5, 5].length) (baseStart_3877582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3877582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3877582 prefixEnd_3877582 := by exact prefixLift 3877582
  have htrace : WordTrace (prefixWord ++ tailWord_3877582) baseStart_3877582 baseEnd_3877582 := by
    simpa [prefixWord, tailWord_3877582, baseEnd_3877582] using wordTrace_append hprefix tailTrace_3877582
  have hstable : (prefixWord ++ tailWord_3877582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3877582).length < 2 ^ (prefixWord ++ tailWord_3877582).sum := by decide
  have hdescent : baseEnd_3877582 < baseStart_3877582 := by decide
  rcases family_descends (prefixWord ++ tailWord_3877582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3877615 : List Nat := [1, 1, 2, 1, 5, 2, 1, 2, 1, 3, 4]
def baseStart_3877615 : Nat := 118140960795 + 3877615 * 2 ^ 59
def prefixEnd_3877615 : Nat := 4983230072969 + 3 ^ 40 * 3877615 * 2
def baseEnd_3877615 : Nat := 1991080288083951547179679

theorem tailTrace_3877615 : CollatzResearch.WordTrace tailWord_3877615 prefixEnd_3877615 1991080288083951547179679 := by
  unfold tailWord_3877615
  simp only [CollatzResearch.WordTrace]
  refine ⟨141428237847070573763178299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94285491898047049175452199 141428237847070573763178299)
  ·
    refine ⟨212142356770605860644767449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141428237847070573763178299 212142356770605860644767449)
    ·
      refine ⟨159106767577954395483575587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212142356770605860644767449 159106767577954395483575587)
      ·
        refine ⟨238660151366931593225363381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159106767577954395483575587 238660151366931593225363381)
        ·
          refine ⟨22374389190649836864877817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 238660151366931593225363381 22374389190649836864877817)
          ·
            refine ⟨16780791892987377648658363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22374389190649836864877817 16780791892987377648658363)
            ·
              refine ⟨25171187839481066472987545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16780791892987377648658363 25171187839481066472987545)
              ·
                refine ⟨18878390879610799854740659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25171187839481066472987545 18878390879610799854740659)
                ·
                  refine ⟨28317586319416199782110989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18878390879610799854740659 28317586319416199782110989)
                  ·
                    refine ⟨10619094869781074918291621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28317586319416199782110989 10619094869781074918291621)
                    ·
                      refine ⟨1991080288083951547179679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10619094869781074918291621 1991080288083951547179679)
                      ·
                        rfl

theorem cell23_3877615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 2, 1, 3, 4].length) (baseStart_3877615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3877615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3877615 prefixEnd_3877615 := by exact prefixLift 3877615
  have htrace : WordTrace (prefixWord ++ tailWord_3877615) baseStart_3877615 baseEnd_3877615 := by
    simpa [prefixWord, tailWord_3877615, baseEnd_3877615] using wordTrace_append hprefix tailTrace_3877615
  have hstable : (prefixWord ++ tailWord_3877615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3877615).length < 2 ^ (prefixWord ++ tailWord_3877615).sum := by decide
  have hdescent : baseEnd_3877615 < baseStart_3877615 := by decide
  rcases family_descends (prefixWord ++ tailWord_3877615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3877672 : List Nat := [2, 1, 5, 1, 1, 1, 3, 3, 6]
def baseStart_3877672 : Nat := 118140960795 + 3877672 * 2 ^ 59
def prefixEnd_3877672 : Nat := 4983230072969 + 3 ^ 40 * 3877672 * 2
def baseEnd_3877672 : Nat := 221234395164584202685213

theorem tailTrace_3877672 : CollatzResearch.WordTrace tailWord_3877672 prefixEnd_3877672 221234395164584202685213 := by
  unfold tailWord_3877672
  simp only [CollatzResearch.WordTrace]
  refine ⟨70715158403932036249001635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94286877871909381665335513 70715158403932036249001635)
  ·
    refine ⟨106072737605898054373502453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70715158403932036249001635 106072737605898054373502453)
    ·
      refine ⟨9944319150552942597515855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 106072737605898054373502453 9944319150552942597515855)
      ·
        refine ⟨14916478725829413896273783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9944319150552942597515855 14916478725829413896273783)
        ·
          refine ⟨22374718088744120844410675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14916478725829413896273783 22374718088744120844410675)
          ·
            refine ⟨33562077133116181266616013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22374718088744120844410675 33562077133116181266616013)
            ·
              refine ⟨12585778924918567974981005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33562077133116181266616013 12585778924918567974981005)
              ·
                refine ⟨4719667096844462990617877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12585778924918567974981005 4719667096844462990617877)
                ·
                  refine ⟨221234395164584202685213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4719667096844462990617877 221234395164584202685213)
                  ·
                    rfl

theorem cell23_3877672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 3, 6].length) (baseStart_3877672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3877672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3877672 prefixEnd_3877672 := by exact prefixLift 3877672
  have htrace : WordTrace (prefixWord ++ tailWord_3877672) baseStart_3877672 baseEnd_3877672 := by
    simpa [prefixWord, tailWord_3877672, baseEnd_3877672] using wordTrace_append hprefix tailTrace_3877672
  have hstable : (prefixWord ++ tailWord_3877672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3877672).length < 2 ^ (prefixWord ++ tailWord_3877672).sum := by decide
  have hdescent : baseEnd_3877672 < baseStart_3877672 := by decide
  rcases family_descends (prefixWord ++ tailWord_3877672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3877722 : List Nat := [3, 1, 1, 2, 1, 4, 1, 2, 3, 1, 4]
def baseStart_3877722 : Nat := 118140960795 + 3877722 * 2 ^ 59
def prefixEnd_3877722 : Nat := 4983230072969 + 3 ^ 40 * 3877722 * 2
def baseEnd_3877722 : Nat := 1991135230513982628541687

theorem tailTrace_3877722 : CollatzResearch.WordTrace tailWord_3877722 prefixEnd_3877722 1991135230513982628541687 := by
  unfold tailWord_3877722
  simp only [CollatzResearch.WordTrace]
  refine ⟨35358035114420732759330855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94288093638455287358215613 35358035114420732759330855)
  ·
    refine ⟨53037052671631099138996283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35358035114420732759330855 53037052671631099138996283)
    ·
      refine ⟨79555579007446648708494425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53037052671631099138996283 79555579007446648708494425)
      ·
        refine ⟨59666684255584986531370819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79555579007446648708494425 59666684255584986531370819)
        ·
          refine ⟨89500026383377479797056229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59666684255584986531370819 89500026383377479797056229)
          ·
            refine ⟨16781254946883277461948043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89500026383377479797056229 16781254946883277461948043)
            ·
              refine ⟨25171882420324916192922065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16781254946883277461948043 25171882420324916192922065)
              ·
                refine ⟨18878911815243687144691549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25171882420324916192922065 18878911815243687144691549)
                ·
                  refine ⟨7079591930716382679259331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18878911815243687144691549 7079591930716382679259331)
                  ·
                    refine ⟨10619387896074574018888997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7079591930716382679259331 10619387896074574018888997)
                    ·
                      refine ⟨1991135230513982628541687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10619387896074574018888997 1991135230513982628541687)
                      ·
                        rfl

theorem cell23_3877722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 2, 3, 1, 4].length) (baseStart_3877722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3877722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3877722 prefixEnd_3877722 := by exact prefixLift 3877722
  have htrace : WordTrace (prefixWord ++ tailWord_3877722) baseStart_3877722 baseEnd_3877722 := by
    simpa [prefixWord, tailWord_3877722, baseEnd_3877722] using wordTrace_append hprefix tailTrace_3877722
  have hstable : (prefixWord ++ tailWord_3877722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3877722).length < 2 ^ (prefixWord ++ tailWord_3877722).sum := by decide
  have hdescent : baseEnd_3877722 < baseStart_3877722 := by decide
  rcases family_descends (prefixWord ++ tailWord_3877722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3877732 : List Nat := [2, 3, 1, 1, 4, 1, 1, 3, 1, 6]
def baseStart_3877732 : Nat := 118140960795 + 3877732 * 2 ^ 59
def prefixEnd_3877732 : Nat := 4983230072969 + 3 ^ 40 * 3877732 * 2
def baseEnd_3877732 : Nat := 663713455106842529805547

theorem tailTrace_3877732 : CollatzResearch.WordTrace tailWord_3877732 prefixEnd_3877732 663713455106842529805547 := by
  unfold tailWord_3877732
  simp only [CollatzResearch.WordTrace]
  refine ⟨70716252593823351372593725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94288336791764468496791633 70716252593823351372593725)
  ·
    refine ⟨26518594722683756764722647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70716252593823351372593725 26518594722683756764722647)
    ·
      refine ⟨39777892084025635147083971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26518594722683756764722647 39777892084025635147083971)
      ·
        refine ⟨59666838126038452720625957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39777892084025635147083971 59666838126038452720625957)
        ·
          refine ⟨11187532148632209885117367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59666838126038452720625957 11187532148632209885117367)
          ·
            refine ⟨16781298222948314827676051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11187532148632209885117367 16781298222948314827676051)
            ·
              refine ⟨25171947334422472241514077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16781298222948314827676051 25171947334422472241514077)
              ·
                refine ⟨9439480250408427090567779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25171947334422472241514077 9439480250408427090567779)
                ·
                  refine ⟨14159220375612640635851669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9439480250408427090567779 14159220375612640635851669)
                  ·
                    refine ⟨663713455106842529805547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14159220375612640635851669 663713455106842529805547)
                    ·
                      rfl

theorem cell23_3877732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 3, 1, 6].length) (baseStart_3877732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3877732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3877732 prefixEnd_3877732 := by exact prefixLift 3877732
  have htrace : WordTrace (prefixWord ++ tailWord_3877732) baseStart_3877732 baseEnd_3877732 := by
    simpa [prefixWord, tailWord_3877732, baseEnd_3877732] using wordTrace_append hprefix tailTrace_3877732
  have hstable : (prefixWord ++ tailWord_3877732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3877732).length < 2 ^ (prefixWord ++ tailWord_3877732).sum := by decide
  have hdescent : baseEnd_3877732 < baseStart_3877732 := by decide
  rcases family_descends (prefixWord ++ tailWord_3877732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3877739 : List Nat := [1, 1, 1, 1, 2, 2, 5, 1, 5, 2, 2]
def baseStart_3877739 : Nat := 118140960795 + 3877739 * 2 ^ 59
def prefixEnd_3877739 : Nat := 4983230072969 + 3 ^ 40 * 3877739 * 2
def baseEnd_3877739 : Nat := 1991143959685109062029109

theorem tailTrace_3877739 : CollatzResearch.WordTrace tailWord_3877739 prefixEnd_3877739 1991143959685109062029109 := by
  unfold tailWord_3877739
  simp only [CollatzResearch.WordTrace]
  refine ⟨141432760498621342940692271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94288506999080895293794847 141432760498621342940692271)
  ·
    refine ⟨212149140747932014411038407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141432760498621342940692271 212149140747932014411038407)
    ·
      refine ⟨318223711121898021616557611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212149140747932014411038407 318223711121898021616557611)
      ·
        refine ⟨477335566682847032424836417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318223711121898021616557611 477335566682847032424836417)
        ·
          refine ⟨358001675012135274318627313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 477335566682847032424836417 358001675012135274318627313)
          ·
            refine ⟨268501256259101455738970485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 358001675012135274318627313 268501256259101455738970485)
            ·
              refine ⟨25171992774290761475528483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 268501256259101455738970485 25171992774290761475528483)
              ·
                refine ⟨37757989161436142213292725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25171992774290761475528483 37757989161436142213292725)
                ·
                  refine ⟨3539811483884638332496193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 37757989161436142213292725 3539811483884638332496193)
                  ·
                    refine ⟨2654858612913478749372145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3539811483884638332496193 2654858612913478749372145)
                    ·
                      refine ⟨1991143959685109062029109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2654858612913478749372145 1991143959685109062029109)
                      ·
                        rfl

theorem cell23_3877739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 1, 5, 2, 2].length) (baseStart_3877739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3877739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3877739 prefixEnd_3877739 := by exact prefixLift 3877739
  have htrace : WordTrace (prefixWord ++ tailWord_3877739) baseStart_3877739 baseEnd_3877739 := by
    simpa [prefixWord, tailWord_3877739, baseEnd_3877739] using wordTrace_append hprefix tailTrace_3877739
  have hstable : (prefixWord ++ tailWord_3877739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3877739).length < 2 ^ (prefixWord ++ tailWord_3877739).sum := by decide
  have hdescent : baseEnd_3877739 < baseStart_3877739 := by decide
  rcases family_descends (prefixWord ++ tailWord_3877739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3877750 : List Nat := [5, 1, 1, 3, 1, 2, 2, 3, 1, 1, 3]
def baseStart_3877750 : Nat := 118140960795 + 3877750 * 2 ^ 59
def prefixEnd_3877750 : Nat := 4983230072969 + 3 ^ 40 * 3877750 * 2
def baseEnd_3877750 : Nat := 1991149607972308518991559

theorem tailTrace_3877750 : CollatzResearch.WordTrace tailWord_3877750 prefixEnd_3877750 1991149607972308518991559 := by
  unfold tailWord_3877750
  simp only [CollatzResearch.WordTrace]
  refine ⟨8839572606348843238708919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 94288774467720994546228469 8839572606348843238708919)
  ·
    refine ⟨13259358909523264858063379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8839572606348843238708919 13259358909523264858063379)
    ·
      refine ⟨19889038364284897287095069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13259358909523264858063379 19889038364284897287095069)
      ·
        refine ⟨7458389386606836482660651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19889038364284897287095069 7458389386606836482660651)
        ·
          refine ⟨11187584079910254723990977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7458389386606836482660651 11187584079910254723990977)
          ·
            refine ⟨8390688059932691042993233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11187584079910254723990977 8390688059932691042993233)
            ·
              refine ⟨6293016044949518282244925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8390688059932691042993233 6293016044949518282244925)
              ·
                refine ⟨2359881016856069355841847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6293016044949518282244925 2359881016856069355841847)
                ·
                  refine ⟨3539821525284104033762771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2359881016856069355841847 3539821525284104033762771)
                  ·
                    refine ⟨5309732287926156050644157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3539821525284104033762771 5309732287926156050644157)
                    ·
                      refine ⟨1991149607972308518991559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5309732287926156050644157 1991149607972308518991559)
                      ·
                        rfl

theorem cell23_3877750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 2, 3, 1, 1, 3].length) (baseStart_3877750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3877750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3877750 prefixEnd_3877750 := by exact prefixLift 3877750
  have htrace : WordTrace (prefixWord ++ tailWord_3877750) baseStart_3877750 baseEnd_3877750 := by
    simpa [prefixWord, tailWord_3877750, baseEnd_3877750] using wordTrace_append hprefix tailTrace_3877750
  have hstable : (prefixWord ++ tailWord_3877750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3877750).length < 2 ^ (prefixWord ++ tailWord_3877750).sum := by decide
  have hdescent : baseEnd_3877750 < baseStart_3877750 := by decide
  rcases family_descends (prefixWord ++ tailWord_3877750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3877772 : List Nat := [2, 2, 1, 2, 1, 2, 2, 2, 3, 3, 3]
def baseStart_3877772 : Nat := 118140960795 + 3877772 * 2 ^ 59
def prefixEnd_3877772 : Nat := 4983230072969 + 3 ^ 40 * 3877772 * 2
def baseEnd_3877772 : Nat := 1991160904546707432916457

theorem tailTrace_3877772 : CollatzResearch.WordTrace tailWord_3877772 prefixEnd_3877772 1991160904546707432916457 := by
  unfold tailWord_3877772
  simp only [CollatzResearch.WordTrace]
  refine ⟨70716982053750894788321785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94289309405001193051095713 70716982053750894788321785)
  ·
    refine ⟨53037736540313171091241339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70716982053750894788321785 53037736540313171091241339)
    ·
      refine ⟨79556604810469756636862009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53037736540313171091241339 79556604810469756636862009)
      ·
        refine ⟨59667453607852317477646507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79556604810469756636862009 59667453607852317477646507)
        ·
          refine ⟨89501180411778476216469761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59667453607852317477646507 89501180411778476216469761)
          ·
            refine ⟨67125885308833857162352321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 89501180411778476216469761 67125885308833857162352321)
            ·
              refine ⟨50344413981625392871764241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67125885308833857162352321 50344413981625392871764241)
              ·
                refine ⟨37758310486219044653823181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50344413981625392871764241 37758310486219044653823181)
                ·
                  refine ⟨14159366432332141745183693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37758310486219044653823181 14159366432332141745183693)
                  ·
                    refine ⟨5309762412124553154443885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14159366432332141745183693 5309762412124553154443885)
                    ·
                      refine ⟨1991160904546707432916457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5309762412124553154443885 1991160904546707432916457)
                      ·
                        rfl

theorem cell23_3877772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 2, 3, 3, 3].length) (baseStart_3877772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3877772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3877772 prefixEnd_3877772 := by exact prefixLift 3877772
  have htrace : WordTrace (prefixWord ++ tailWord_3877772) baseStart_3877772 baseEnd_3877772 := by
    simpa [prefixWord, tailWord_3877772, baseEnd_3877772] using wordTrace_append hprefix tailTrace_3877772
  have hstable : (prefixWord ++ tailWord_3877772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3877772).length < 2 ^ (prefixWord ++ tailWord_3877772).sum := by decide
  have hdescent : baseEnd_3877772 < baseStart_3877772 := by decide
  rcases family_descends (prefixWord ++ tailWord_3877772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3877786 : List Nat := [3, 1, 1, 4, 3, 2, 1, 1, 1, 2, 4]
def baseStart_3877786 : Nat := 118140960795 + 3877786 * 2 ^ 59
def prefixEnd_3877786 : Nat := 4983230072969 + 3 ^ 40 * 3877786 * 2
def baseEnd_3877786 : Nat := 1991168093275870378141393

theorem tailTrace_3877786 : CollatzResearch.WordTrace tailWord_3877786 prefixEnd_3877786 1991168093275870378141393 := by
  unfold tailWord_3877786
  simp only [CollatzResearch.WordTrace]
  refine ⟨35358618682362767491913303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94289649819634046645102141 35358618682362767491913303)
  ·
    refine ⟨53037928023544151237869955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35358618682362767491913303 53037928023544151237869955)
    ·
      refine ⟨79556892035316226856804933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53037928023544151237869955 79556892035316226856804933)
      ·
        refine ⟨14916917256621792535650925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 79556892035316226856804933 14916917256621792535650925)
        ·
          refine ⟨5593843971233172200869097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14916917256621792535650925 5593843971233172200869097)
          ·
            refine ⟨4195382978424879150651823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5593843971233172200869097 4195382978424879150651823)
            ·
              refine ⟨6293074467637318725977735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4195382978424879150651823 6293074467637318725977735)
              ·
                refine ⟨9439611701455978088966603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6293074467637318725977735 9439611701455978088966603)
                ·
                  refine ⟨14159417552183967133449905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9439611701455978088966603 14159417552183967133449905)
                  ·
                    refine ⟨10619563164137975350087429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14159417552183967133449905 10619563164137975350087429)
                    ·
                      refine ⟨1991168093275870378141393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10619563164137975350087429 1991168093275870378141393)
                      ·
                        rfl

theorem cell23_3877786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 1, 1, 1, 2, 4].length) (baseStart_3877786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3877786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3877786 prefixEnd_3877786 := by exact prefixLift 3877786
  have htrace : WordTrace (prefixWord ++ tailWord_3877786) baseStart_3877786 baseEnd_3877786 := by
    simpa [prefixWord, tailWord_3877786, baseEnd_3877786] using wordTrace_append hprefix tailTrace_3877786
  have hstable : (prefixWord ++ tailWord_3877786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3877786).length < 2 ^ (prefixWord ++ tailWord_3877786).sum := by decide
  have hdescent : baseEnd_3877786 < baseStart_3877786 := by decide
  rcases family_descends (prefixWord ++ tailWord_3877786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3877816 : List Nat := [2, 1, 2, 1, 2, 4, 2, 3, 1, 3, 2]
def baseStart_3877816 : Nat := 118140960795 + 3877816 * 2 ^ 59
def prefixEnd_3877816 : Nat := 4983230072969 + 3 ^ 40 * 3877816 * 2
def baseEnd_3877816 : Nat := 1991183497695505260766255

theorem tailTrace_3877816 : CollatzResearch.WordTrace tailWord_3877816 prefixEnd_3877816 1991183497695505260766255 := by
  unfold tailWord_3877816
  simp only [CollatzResearch.WordTrace]
  refine ⟨70717784459671192545622651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94290379279561590060830201 70717784459671192545622651)
  ·
    refine ⟨106076676689506788818433977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70717784459671192545622651 106076676689506788818433977)
    ·
      refine ⟨79557507517130091613825483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106076676689506788818433977 79557507517130091613825483)
      ·
        refine ⟨119336261275695137420738225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79557507517130091613825483 119336261275695137420738225)
        ·
          refine ⟨89502195956771353065553669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119336261275695137420738225 89502195956771353065553669)
          ·
            refine ⟨16781661741894628699791313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89502195956771353065553669 16781661741894628699791313)
            ·
              refine ⟨12586246306420971524843485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16781661741894628699791313 12586246306420971524843485)
              ·
                refine ⟨4719842364907864321816307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12586246306420971524843485 4719842364907864321816307)
                ·
                  refine ⟨7079763547361796482724461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4719842364907864321816307 7079763547361796482724461)
                  ·
                    refine ⟨2654911330260673681021673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7079763547361796482724461 2654911330260673681021673)
                    ·
                      refine ⟨1991183497695505260766255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2654911330260673681021673 1991183497695505260766255)
                      ·
                        rfl

theorem cell23_3877816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 3, 1, 3, 2].length) (baseStart_3877816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3877816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3877816 prefixEnd_3877816 := by exact prefixLift 3877816
  have htrace : WordTrace (prefixWord ++ tailWord_3877816) baseStart_3877816 baseEnd_3877816 := by
    simpa [prefixWord, tailWord_3877816, baseEnd_3877816] using wordTrace_append hprefix tailTrace_3877816
  have hstable : (prefixWord ++ tailWord_3877816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3877816).length < 2 ^ (prefixWord ++ tailWord_3877816).sum := by decide
  have hdescent : baseEnd_3877816 < baseStart_3877816 := by decide
  rcases family_descends (prefixWord ++ tailWord_3877816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3877830 : List Nat := [6, 1, 3, 1, 1, 1, 2, 8]
def baseStart_3877830 : Nat := 118140960795 + 3877830 * 2 ^ 59
def prefixEnd_3877830 : Nat := 4983230072969 + 3 ^ 40 * 3877830 * 2
def baseEnd_3877830 : Nat := 73747803200913637258933

theorem tailTrace_3877830 : CollatzResearch.WordTrace tailWord_3877830 prefixEnd_3877830 73747803200913637258933 := by
  unfold tailWord_3877830
  simp only [CollatzResearch.WordTrace]
  refine ⟨4419877485665364546320467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 94290719694194443654836629 4419877485665364546320467)
  ·
    refine ⟨6629816228498046819480701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4419877485665364546320467 6629816228498046819480701)
    ·
      refine ⟨2486181085686767557305263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6629816228498046819480701 2486181085686767557305263)
      ·
        refine ⟨3729271628530151335957895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2486181085686767557305263 3729271628530151335957895)
        ·
          refine ⟨5593907442795227003936843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3729271628530151335957895 5593907442795227003936843)
          ·
            refine ⟨8390861164192840505905265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5593907442795227003936843 8390861164192840505905265)
            ·
              refine ⟨6293145873144630379428949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8390861164192840505905265 6293145873144630379428949)
              ·
                refine ⟨73747803200913637258933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6293145873144630379428949 73747803200913637258933)
                ·
                  rfl

theorem cell23_3877830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 2, 8].length) (baseStart_3877830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3877830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3877830 prefixEnd_3877830 := by exact prefixLift 3877830
  have htrace : WordTrace (prefixWord ++ tailWord_3877830) baseStart_3877830 baseEnd_3877830 := by
    simpa [prefixWord, tailWord_3877830, baseEnd_3877830] using wordTrace_append hprefix tailTrace_3877830
  have hstable : (prefixWord ++ tailWord_3877830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3877830).length < 2 ^ (prefixWord ++ tailWord_3877830).sum := by decide
  have hdescent : baseEnd_3877830 < baseStart_3877830 := by decide
  rcases family_descends (prefixWord ++ tailWord_3877830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3877919 : List Nat := [1, 1, 2, 4, 1, 4, 1, 1, 1, 3, 4]
def baseStart_3877919 : Nat := 118140960795 + 3877919 * 2 ^ 59
def prefixEnd_3877919 : Nat := 4983230072969 + 3 ^ 40 * 3877919 * 2
def baseEnd_3877919 : Nat := 1991236386202918357778281

theorem tailTrace_3877919 : CollatzResearch.WordTrace tailWord_3877919 prefixEnd_3877919 1991236386202918357778281 := by
  unfold tailWord_3877919
  simp only [CollatzResearch.WordTrace]
  refine ⟨141439325637969233682244811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94292883758646155788163207 141439325637969233682244811)
  ·
    refine ⟨212158988456953850523367217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141439325637969233682244811 212158988456953850523367217)
    ·
      refine ⟨159119241342715387892525413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212158988456953850523367217 159119241342715387892525413)
      ·
        refine ⟨29834857751759135229848515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 159119241342715387892525413 29834857751759135229848515)
        ·
          refine ⟨44752286627638702844772773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29834857751759135229848515 44752286627638702844772773)
          ·
            refine ⟨8391053742682256783394895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44752286627638702844772773 8391053742682256783394895)
            ·
              refine ⟨12586580614023385175092343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8391053742682256783394895 12586580614023385175092343)
              ·
                refine ⟨18879870921035077762638515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12586580614023385175092343 18879870921035077762638515)
                ·
                  refine ⟨28319806381552616643957773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18879870921035077762638515 28319806381552616643957773)
                  ·
                    refine ⟨10619927393082231241484165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28319806381552616643957773 10619927393082231241484165)
                    ·
                      refine ⟨1991236386202918357778281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10619927393082231241484165 1991236386202918357778281)
                      ·
                        rfl

theorem cell23_3877919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 1, 1, 3, 4].length) (baseStart_3877919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3877919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3877919 prefixEnd_3877919 := by exact prefixLift 3877919
  have htrace : WordTrace (prefixWord ++ tailWord_3877919) baseStart_3877919 baseEnd_3877919 := by
    simpa [prefixWord, tailWord_3877919, baseEnd_3877919] using wordTrace_append hprefix tailTrace_3877919
  have hstable : (prefixWord ++ tailWord_3877919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3877919).length < 2 ^ (prefixWord ++ tailWord_3877919).sum := by decide
  have hdescent : baseEnd_3877919 < baseStart_3877919 := by decide
  rcases family_descends (prefixWord ++ tailWord_3877919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3877932 : List Nat := [2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 6]
def baseStart_3877932 : Nat := 118140960795 + 3877932 * 2 ^ 59
def prefixEnd_3877932 : Nat := 4983230072969 + 3 ^ 40 * 3877932 * 2
def baseEnd_3877932 : Nat := 1991243061451426806915721

theorem tailTrace_3877932 : CollatzResearch.WordTrace tailWord_3877932 prefixEnd_3877932 1991243061451426806915721 := by
  unfold tailWord_3877932
  simp only [CollatzResearch.WordTrace]
  refine ⟨70719899893461068451234025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94293199857948091268312033 70719899893461068451234025)
  ·
    refine ⟨53039924920095801338425519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70719899893461068451234025 53039924920095801338425519)
    ·
      refine ⟨79559887380143702007638279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53039924920095801338425519 79559887380143702007638279)
      ·
        refine ⟨119339831070215553011457419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79559887380143702007638279 119339831070215553011457419)
        ·
          refine ⟨179009746605323329517186129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119339831070215553011457419 179009746605323329517186129)
          ·
            refine ⟨134257309953992497137889597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 179009746605323329517186129 134257309953992497137889597)
            ·
              refine ⟨50346491232747186426708599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 134257309953992497137889597 50346491232747186426708599)
              ·
                refine ⟨75519736849120779640062899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50346491232747186426708599 75519736849120779640062899)
                ·
                  refine ⟨113279605273681169460094349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 75519736849120779640062899 113279605273681169460094349)
                  ·
                    refine ⟨42479851977630438547535381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 113279605273681169460094349 42479851977630438547535381)
                    ·
                      refine ⟨1991243061451426806915721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42479851977630438547535381 1991243061451426806915721)
                      ·
                        rfl

theorem cell23_3877932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 6].length) (baseStart_3877932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3877932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3877932 prefixEnd_3877932 := by exact prefixLift 3877932
  have htrace : WordTrace (prefixWord ++ tailWord_3877932) baseStart_3877932 baseEnd_3877932 := by
    simpa [prefixWord, tailWord_3877932, baseEnd_3877932] using wordTrace_append hprefix tailTrace_3877932
  have hstable : (prefixWord ++ tailWord_3877932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3877932).length < 2 ^ (prefixWord ++ tailWord_3877932).sum := by decide
  have hdescent : baseEnd_3877932 < baseStart_3877932 := by decide
  rcases family_descends (prefixWord ++ tailWord_3877932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3877939 : List Nat := [1, 1, 1, 2, 4, 1, 1, 3, 4, 2, 3]
def baseStart_3877939 : Nat := 118140960795 + 3877939 * 2 ^ 59
def prefixEnd_3877939 : Nat := 4983230072969 + 3 ^ 40 * 3877939 * 2
def baseEnd_3877939 : Nat := 1991246655816008279528189

theorem tailTrace_3877939 : CollatzResearch.WordTrace tailWord_3877939 prefixEnd_3877939 1991246655816008279528189 := by
  unfold tailWord_3877939
  simp only [CollatzResearch.WordTrace]
  refine ⟨141440055097896777097972871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94293370065264518065315247 141440055097896777097972871)
  ·
    refine ⟨212160082646845165646959307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141440055097896777097972871 212160082646845165646959307)
    ·
      refine ⟨318240123970267748470438961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212160082646845165646959307 318240123970267748470438961)
      ·
        refine ⟨238680092977700811352829221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 318240123970267748470438961 238680092977700811352829221)
        ·
          refine ⟨44752517433318902128655479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 238680092977700811352829221 44752517433318902128655479)
          ·
            refine ⟨67128776149978353192983219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44752517433318902128655479 67128776149978353192983219)
            ·
              refine ⟨100693164224967529789474829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67128776149978353192983219 100693164224967529789474829)
              ·
                refine ⟨37759936584362823671053061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 100693164224967529789474829 37759936584362823671053061)
                ·
                  refine ⟨7079988109568029438322449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37759936584362823671053061 7079988109568029438322449)
                  ·
                    refine ⟨5309991082176022078741837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7079988109568029438322449 5309991082176022078741837)
                    ·
                      refine ⟨1991246655816008279528189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5309991082176022078741837 1991246655816008279528189)
                      ·
                        rfl

theorem cell23_3877939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 3, 4, 2, 3].length) (baseStart_3877939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3877939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3877939 prefixEnd_3877939 := by exact prefixLift 3877939
  have htrace : WordTrace (prefixWord ++ tailWord_3877939) baseStart_3877939 baseEnd_3877939 := by
    simpa [prefixWord, tailWord_3877939, baseEnd_3877939] using wordTrace_append hprefix tailTrace_3877939
  have hstable : (prefixWord ++ tailWord_3877939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3877939).length < 2 ^ (prefixWord ++ tailWord_3877939).sum := by decide
  have hdescent : baseEnd_3877939 < baseStart_3877939 := by decide
  rcases family_descends (prefixWord ++ tailWord_3877939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3878006 : List Nat := [5, 1, 1, 2, 1, 1, 2, 2, 3, 5]
def baseStart_3878006 : Nat := 118140960795 + 3878006 * 2 ^ 59
def prefixEnd_3878006 : Nat := 4983230072969 + 3 ^ 40 * 3878006 * 2
def baseEnd_3878006 : Nat := 663760353006619839130127

theorem tailTrace_3878006 : CollatzResearch.WordTrace tailWord_3878006 prefixEnd_3878006 663760353006619839130127 := by
  unfold tailWord_3878006
  simp only [CollatzResearch.WordTrace]
  refine ⟨8840156174290877971291367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 94294999192436031693774581 8840156174290877971291367)
  ·
    refine ⟨13260234261436316956937051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8840156174290877971291367 13260234261436316956937051)
    ·
      refine ⟨19890351392154475435405577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13260234261436316956937051 19890351392154475435405577)
      ·
        refine ⟨14917763544115856576554183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19890351392154475435405577 14917763544115856576554183)
        ·
          refine ⟨22376645316173784864831275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14917763544115856576554183 22376645316173784864831275)
          ·
            refine ⟨33564967974260677297246913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22376645316173784864831275 33564967974260677297246913)
            ·
              refine ⟨25173725980695507972935185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33564967974260677297246913 25173725980695507972935185)
              ·
                refine ⟨18880294485521630979701389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25173725980695507972935185 18880294485521630979701389)
                ·
                  refine ⟨7080110432070611617388021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18880294485521630979701389 7080110432070611617388021)
                  ·
                    refine ⟨663760353006619839130127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7080110432070611617388021 663760353006619839130127)
                    ·
                      rfl

theorem cell23_3878006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 2, 3, 5].length) (baseStart_3878006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3878006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3878006 prefixEnd_3878006 := by exact prefixLift 3878006
  have htrace : WordTrace (prefixWord ++ tailWord_3878006) baseStart_3878006 baseEnd_3878006 := by
    simpa [prefixWord, tailWord_3878006, baseEnd_3878006] using wordTrace_append hprefix tailTrace_3878006
  have hstable : (prefixWord ++ tailWord_3878006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3878006).length < 2 ^ (prefixWord ++ tailWord_3878006).sum := by decide
  have hdescent : baseEnd_3878006 < baseStart_3878006 := by decide
  rcases family_descends (prefixWord ++ tailWord_3878006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3878019 : List Nat := [1, 1, 1, 3, 3, 2, 2, 3, 1, 6]
def baseStart_3878019 : Nat := 118140960795 + 3878019 * 2 ^ 59
def prefixEnd_3878019 : Nat := 4983230072969 + 3 ^ 40 * 3878019 * 2
def baseEnd_3878019 : Nat := 663762578089455988842607

theorem tailTrace_3878019 : CollatzResearch.WordTrace tailWord_3878019 prefixEnd_3878019 663762578089455988842607 := by
  unfold tailWord_3878019
  simp only [CollatzResearch.WordTrace]
  refine ⟨141442972937606950760885111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94295315291737967173923407 141442972937606950760885111)
  ·
    refine ⟨212164459406410426141327667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141442972937606950760885111 212164459406410426141327667)
    ·
      refine ⟨318246689109615639211991501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212164459406410426141327667 318246689109615639211991501)
      ·
        refine ⟨119342508416105864704496813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 318246689109615639211991501 119342508416105864704496813)
        ·
          refine ⟨44753440656039699264186305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119342508416105864704496813 44753440656039699264186305)
          ·
            refine ⟨33565080492029774448139729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44753440656039699264186305 33565080492029774448139729)
            ·
              refine ⟨25173810369022330836104797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33565080492029774448139729 25173810369022330836104797)
              ·
                refine ⟨9440178888383374063539299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25173810369022330836104797 9440178888383374063539299)
                ·
                  refine ⟨14160268332575061095308949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9440178888383374063539299 14160268332575061095308949)
                  ·
                    refine ⟨663762578089455988842607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14160268332575061095308949 663762578089455988842607)
                    ·
                      rfl

theorem cell23_3878019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 3, 1, 6].length) (baseStart_3878019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3878019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3878019 prefixEnd_3878019 := by exact prefixLift 3878019
  have htrace : WordTrace (prefixWord ++ tailWord_3878019) baseStart_3878019 baseEnd_3878019 := by
    simpa [prefixWord, tailWord_3878019, baseEnd_3878019] using wordTrace_append hprefix tailTrace_3878019
  have hstable : (prefixWord ++ tailWord_3878019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3878019).length < 2 ^ (prefixWord ++ tailWord_3878019).sum := by decide
  have hdescent : baseEnd_3878019 < baseStart_3878019 := by decide
  rcases family_descends (prefixWord ++ tailWord_3878019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3878026 : List Nat := [3, 1, 2, 3, 1, 1, 3, 1, 3, 1, 4]
def baseStart_3878026 : Nat := 118140960795 + 3878026 * 2 ^ 59
def prefixEnd_3878026 : Nat := 4983230072969 + 3 ^ 40 * 3878026 * 2
def baseEnd_3878026 : Nat := 1991291328632949439140289

theorem tailTrace_3878026 : CollatzResearch.WordTrace tailWord_3878026 prefixEnd_3878026 1991291328632949439140289 := by
  unfold tailWord_3878026
  simp only [CollatzResearch.WordTrace]
  refine ⟨35360807062145397739097483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94295485499054393970926621 35360807062145397739097483)
  ·
    refine ⟨53041210593218096608646225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35360807062145397739097483 53041210593218096608646225)
    ·
      refine ⟨39780907944913572456484669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53041210593218096608646225 39780907944913572456484669)
      ·
        refine ⟨14917840479342589671181751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39780907944913572456484669 14917840479342589671181751)
        ·
          refine ⟨22376760719013884506772627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14917840479342589671181751 22376760719013884506772627)
          ·
            refine ⟨33565141078520826760158941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22376760719013884506772627 33565141078520826760158941)
            ·
              refine ⟨12586927904445310035059603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33565141078520826760158941 12586927904445310035059603)
              ·
                refine ⟨18880391856667965052589405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12586927904445310035059603 18880391856667965052589405)
                ·
                  refine ⟨7080146946250486894721027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18880391856667965052589405 7080146946250486894721027)
                  ·
                    refine ⟨10620220419375730342081541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7080146946250486894721027 10620220419375730342081541)
                    ·
                      refine ⟨1991291328632949439140289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10620220419375730342081541 1991291328632949439140289)
                      ·
                        rfl

theorem cell23_3878026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_3878026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3878026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3878026 prefixEnd_3878026 := by exact prefixLift 3878026
  have htrace : WordTrace (prefixWord ++ tailWord_3878026) baseStart_3878026 baseEnd_3878026 := by
    simpa [prefixWord, tailWord_3878026, baseEnd_3878026] using wordTrace_append hprefix tailTrace_3878026
  have hstable : (prefixWord ++ tailWord_3878026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3878026).length < 2 ^ (prefixWord ++ tailWord_3878026).sum := by decide
  have hdescent : baseEnd_3878026 < baseStart_3878026 := by decide
  rcases family_descends (prefixWord ++ tailWord_3878026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3878030 : List Nat := [4, 1, 1, 3, 2, 2, 2, 1, 2, 3, 2]
def baseStart_3878030 : Nat := 118140960795 + 3878030 * 2 ^ 59
def prefixEnd_3878030 : Nat := 4983230072969 + 3 ^ 40 * 3878030 * 2
def baseEnd_3878030 : Nat := 1991293382555567423490271

theorem tailTrace_3878030 : CollatzResearch.WordTrace tailWord_3878030 prefixEnd_3878030 1991293382555567423490271 := by
  unfold tailWord_3878030
  simp only [CollatzResearch.WordTrace]
  refine ⟨17680421767570887454941943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94295582760378066426357029 17680421767570887454941943)
  ·
    refine ⟨26520632651356331182412915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17680421767570887454941943 26520632651356331182412915)
    ·
      refine ⟨39780948977034496773619373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26520632651356331182412915 39780948977034496773619373)
      ·
        refine ⟨14917855866387936290107265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39780948977034496773619373 14917855866387936290107265)
        ·
          refine ⟨11188391899790952217580449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14917855866387936290107265 11188391899790952217580449)
          ·
            refine ⟨8391293924843214163185337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11188391899790952217580449 8391293924843214163185337)
            ·
              refine ⟨6293470443632410622389003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8391293924843214163185337 6293470443632410622389003)
              ·
                refine ⟨9440205665448615933583505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6293470443632410622389003 9440205665448615933583505)
                ·
                  refine ⟨7080154249086461950187629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9440205665448615933583505 7080154249086461950187629)
                  ·
                    refine ⟨2655057843407423231320361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7080154249086461950187629 2655057843407423231320361)
                    ·
                      refine ⟨1991293382555567423490271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2655057843407423231320361 1991293382555567423490271)
                      ·
                        rfl

theorem cell23_3878030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 2, 1, 2, 3, 2].length) (baseStart_3878030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3878030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3878030 prefixEnd_3878030 := by exact prefixLift 3878030
  have htrace : WordTrace (prefixWord ++ tailWord_3878030) baseStart_3878030 baseEnd_3878030 := by
    simpa [prefixWord, tailWord_3878030, baseEnd_3878030] using wordTrace_append hprefix tailTrace_3878030
  have hstable : (prefixWord ++ tailWord_3878030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3878030).length < 2 ^ (prefixWord ++ tailWord_3878030).sum := by decide
  have hdescent : baseEnd_3878030 < baseStart_3878030 := by decide
  rcases family_descends (prefixWord ++ tailWord_3878030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3878053 : List Nat := [1, 3, 1, 2, 1, 5, 2, 2, 2, 4]
def baseStart_3878053 : Nat := 118140960795 + 3878053 * 2 ^ 59
def prefixEnd_3878053 : Nat := 4983230072969 + 3 ^ 40 * 3878053 * 2
def baseEnd_3878053 : Nat := 663768397536873611167555

theorem tailTrace_3878053 : CollatzResearch.WordTrace tailWord_3878053 prefixEnd_3878053 663768397536873611167555 := by
  unfold tailWord_3878053
  simp only [CollatzResearch.WordTrace]
  refine ⟨141444213019483774567622813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94296142012989183045081875 141444213019483774567622813)
  ·
    refine ⟨53041579882306415462858555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141444213019483774567622813 53041579882306415462858555)
    ·
      refine ⟨79562369823459623194287833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53041579882306415462858555 79562369823459623194287833)
      ·
        refine ⟨59671777367594717395715875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79562369823459623194287833 59671777367594717395715875)
        ·
          refine ⟨89507666051392076093573813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59671777367594717395715875 89507666051392076093573813)
          ·
            refine ⟨8391343692318007133772545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 89507666051392076093573813 8391343692318007133772545)
            ·
              refine ⟨6293507769238505350329409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8391343692318007133772545 6293507769238505350329409)
              ·
                refine ⟨4720130826928879012747057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6293507769238505350329409 4720130826928879012747057)
                ·
                  refine ⟨3540098120196659259560293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4720130826928879012747057 3540098120196659259560293)
                  ·
                    refine ⟨663768397536873611167555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3540098120196659259560293 663768397536873611167555)
                    ·
                      rfl

theorem cell23_3878053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 2, 2, 2, 4].length) (baseStart_3878053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3878053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3878053 prefixEnd_3878053 := by exact prefixLift 3878053
  have htrace : WordTrace (prefixWord ++ tailWord_3878053) baseStart_3878053 baseEnd_3878053 := by
    simpa [prefixWord, tailWord_3878053, baseEnd_3878053] using wordTrace_append hprefix tailTrace_3878053
  have hstable : (prefixWord ++ tailWord_3878053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3878053).length < 2 ^ (prefixWord ++ tailWord_3878053).sum := by decide
  have hdescent : baseEnd_3878053 < baseStart_3878053 := by decide
  rcases family_descends (prefixWord ++ tailWord_3878053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3878066 : List Nat := [3, 2, 1, 1, 1, 6, 1, 8]
def baseStart_3878066 : Nat := 118140960795 + 3878066 * 2 ^ 59
def prefixEnd_3878066 : Nat := 4983230072969 + 3 ^ 40 * 3878066 * 2
def baseEnd_3878066 : Nat := 73752291402189973431115

theorem tailTrace_3878066 : CollatzResearch.WordTrace tailWord_3878066 prefixEnd_3878066 73752291402189973431115 := by
  unfold tailWord_3878066
  simp only [CollatzResearch.WordTrace]
  refine ⟨35361171792109169446961513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94296458112291118525230701 35361171792109169446961513)
  ·
    refine ⟨26520878844081877085221135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35361171792109169446961513 26520878844081877085221135)
    ·
      refine ⟨39781318266122815627831703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26520878844081877085221135 39781318266122815627831703)
      ·
        refine ⟨59671977399184223441747555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39781318266122815627831703 59671977399184223441747555)
        ·
          refine ⟨89507966098776335162621333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59671977399184223441747555 89507966098776335162621333)
          ·
            refine ⟨4195685910880140710747875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 89507966098776335162621333 4195685910880140710747875)
            ·
              refine ⟨6293528866320211066121813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4195685910880140710747875 6293528866320211066121813)
              ·
                refine ⟨73752291402189973431115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6293528866320211066121813 73752291402189973431115)
                ·
                  rfl

theorem cell23_3878066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 6, 1, 8].length) (baseStart_3878066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3878066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3878066 prefixEnd_3878066 := by exact prefixLift 3878066
  have htrace : WordTrace (prefixWord ++ tailWord_3878066) baseStart_3878066 baseEnd_3878066 := by
    simpa [prefixWord, tailWord_3878066, baseEnd_3878066] using wordTrace_append hprefix tailTrace_3878066
  have hstable : (prefixWord ++ tailWord_3878066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3878066).length < 2 ^ (prefixWord ++ tailWord_3878066).sum := by decide
  have hdescent : baseEnd_3878066 < baseStart_3878066 := by decide
  rcases family_descends (prefixWord ++ tailWord_3878066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3878094 : List Nat := [4, 1, 1, 1, 5, 1, 2, 3, 1, 2, 2]
def baseStart_3878094 : Nat := 118140960795 + 3878094 * 2 ^ 59
def prefixEnd_3878094 : Nat := 4983230072969 + 3 ^ 40 * 3878094 * 2
def baseEnd_3878094 : Nat := 1991326245317455173089977

theorem tailTrace_3878094 : CollatzResearch.WordTrace tailWord_3878094 prefixEnd_3878094 1991326245317455173089977 := by
  unfold tailWord_3878094
  simp only [CollatzResearch.WordTrace]
  refine ⟨17680713551541904821233167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94297138941556825713243557 17680713551541904821233167)
  ·
    refine ⟨26521070327312857231849751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17680713551541904821233167 26521070327312857231849751)
    ·
      refine ⟨39781605490969285847774627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26521070327312857231849751 39781605490969285847774627)
      ·
        refine ⟨59672408236453928771661941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39781605490969285847774627 59672408236453928771661941)
        ·
          refine ⟨5594288272167555822343307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 59672408236453928771661941 5594288272167555822343307)
          ·
            refine ⟨8391432408251333733514961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5594288272167555822343307 8391432408251333733514961)
            ·
              refine ⟨6293574306188500300136221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8391432408251333733514961 6293574306188500300136221)
              ·
                refine ⟨2360090364820687612551083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6293574306188500300136221 2360090364820687612551083)
                ·
                  refine ⟨3540135547231031418826625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2360090364820687612551083 3540135547231031418826625)
                  ·
                    refine ⟨2655101660423273564119969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3540135547231031418826625 2655101660423273564119969)
                    ·
                      refine ⟨1991326245317455173089977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2655101660423273564119969 1991326245317455173089977)
                      ·
                        rfl

theorem cell23_3878094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 2, 3, 1, 2, 2].length) (baseStart_3878094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3878094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3878094 prefixEnd_3878094 := by exact prefixLift 3878094
  have htrace : WordTrace (prefixWord ++ tailWord_3878094) baseStart_3878094 baseEnd_3878094 := by
    simpa [prefixWord, tailWord_3878094, baseEnd_3878094] using wordTrace_append hprefix tailTrace_3878094
  have hstable : (prefixWord ++ tailWord_3878094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3878094).length < 2 ^ (prefixWord ++ tailWord_3878094).sum := by decide
  have hdescent : baseEnd_3878094 < baseStart_3878094 := by decide
  rcases family_descends (prefixWord ++ tailWord_3878094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3878099 : List Nat := [1, 1, 1, 2, 1, 1, 1, 4, 4, 3, 4]
def baseStart_3878099 : Nat := 118140960795 + 3878099 * 2 ^ 59
def prefixEnd_3878099 : Nat := 4983230072969 + 3 ^ 40 * 3878099 * 2
def baseEnd_3878099 : Nat := 1991328812720727653527453

theorem tailTrace_3878099 : CollatzResearch.WordTrace tailWord_3878099 prefixEnd_3878099 1991328812720727653527453 := by
  unfold tailWord_3878099
  simp only [CollatzResearch.WordTrace]
  refine ⟨141445890777317124423797351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94297260518211416282531567 141445890777317124423797351)
  ·
    refine ⟨212168836165975686635696027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141445890777317124423797351 212168836165975686635696027)
    ·
      refine ⟨318253254248963529953544041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212168836165975686635696027 318253254248963529953544041)
      ·
        refine ⟨238689940686722647465158031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 318253254248963529953544041 238689940686722647465158031)
        ·
          refine ⟨358034911030083971197737047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238689940686722647465158031 358034911030083971197737047)
          ·
            refine ⟨537052366545125956796605571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 358034911030083971197737047 537052366545125956796605571)
            ·
              refine ⟨805578549817688935194908357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 537052366545125956796605571 805578549817688935194908357)
              ·
                refine ⟨151045978090816675349045317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 805578549817688935194908357 151045978090816675349045317)
                ·
                  refine ⟨28321120892028126627945997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 151045978090816675349045317 28321120892028126627945997)
                  ·
                    refine ⟨10620420334510547485479749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28321120892028126627945997 10620420334510547485479749)
                    ·
                      refine ⟨1991328812720727653527453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10620420334510547485479749 1991328812720727653527453)
                      ·
                        rfl

theorem cell23_3878099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 4, 3, 4].length) (baseStart_3878099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3878099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3878099 prefixEnd_3878099 := by exact prefixLift 3878099
  have htrace : WordTrace (prefixWord ++ tailWord_3878099) baseStart_3878099 baseEnd_3878099 := by
    simpa [prefixWord, tailWord_3878099, baseEnd_3878099] using wordTrace_append hprefix tailTrace_3878099
  have hstable : (prefixWord ++ tailWord_3878099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3878099).length < 2 ^ (prefixWord ++ tailWord_3878099).sum := by decide
  have hdescent : baseEnd_3878099 < baseStart_3878099 := by decide
  rcases family_descends (prefixWord ++ tailWord_3878099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3878126 : List Nat := [4, 1, 2, 1, 1, 1, 4, 1, 2, 6]
def baseStart_3878126 : Nat := 118140960795 + 3878126 * 2 ^ 59
def prefixEnd_3878126 : Nat := 4983230072969 + 3 ^ 40 * 3878126 * 2
def baseEnd_3878126 : Nat := 663780892232799682629943

theorem tailTrace_3878126 : CollatzResearch.WordTrace tailWord_3878126 prefixEnd_3878126 663780892232799682629943 := by
  unfold tailWord_3878126
  simp only [CollatzResearch.WordTrace]
  refine ⟨17680859443527413504378779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94297917032146205356686821 17680859443527413504378779)
  ·
    refine ⟨26521289165291120256568169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17680859443527413504378779 26521289165291120256568169)
    ·
      refine ⟨19890966873968340192426127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26521289165291120256568169 19890966873968340192426127)
      ·
        refine ⟨29836450310952510288639191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19890966873968340192426127 29836450310952510288639191)
        ·
          refine ⟨44754675466428765432958787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29836450310952510288639191 44754675466428765432958787)
          ·
            refine ⟨67132013199643148149438181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44754675466428765432958787 67132013199643148149438181)
            ·
              refine ⟨12587252474933090278019659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67132013199643148149438181 12587252474933090278019659)
              ·
                refine ⟨18880878712399635417029489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12587252474933090278019659 18880878712399635417029489)
                ·
                  refine ⟨14160659034299726562772117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18880878712399635417029489 14160659034299726562772117)
                  ·
                    refine ⟨663780892232799682629943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14160659034299726562772117 663780892232799682629943)
                    ·
                      rfl

theorem cell23_3878126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 1, 2, 6].length) (baseStart_3878126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3878126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3878126 prefixEnd_3878126 := by exact prefixLift 3878126
  have htrace : WordTrace (prefixWord ++ tailWord_3878126) baseStart_3878126 baseEnd_3878126 := by
    simpa [prefixWord, tailWord_3878126, baseEnd_3878126] using wordTrace_append hprefix tailTrace_3878126
  have hstable : (prefixWord ++ tailWord_3878126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3878126).length < 2 ^ (prefixWord ++ tailWord_3878126).sum := by decide
  have hdescent : baseEnd_3878126 < baseStart_3878126 := by decide
  rcases family_descends (prefixWord ++ tailWord_3878126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3878127 : List Nat := [1, 1, 2, 1, 7, 1, 3, 1, 2, 1, 3]
def baseStart_3878127 : Nat := 118140960795 + 3878127 * 2 ^ 59
def prefixEnd_3878127 : Nat := 4983230072969 + 3 ^ 40 * 3878127 * 2
def baseEnd_3878127 : Nat := 1991343190179053543977325

theorem tailTrace_3878127 : CollatzResearch.WordTrace tailWord_3878127 prefixEnd_3878127 1991343190179053543977325 := by
  unfold tailWord_3878127
  simp only [CollatzResearch.WordTrace]
  refine ⟨141446912021215685205816635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94297941347477123470544423 141446912021215685205816635)
  ·
    refine ⟨212170368031823527808724953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141446912021215685205816635 212170368031823527808724953)
    ·
      refine ⟨159127776023867645856543715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212170368031823527808724953 159127776023867645856543715)
      ·
        refine ⟨238691664035801468784815573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159127776023867645856543715 238691664035801468784815573)
        ·
          refine ⟨5594335875839096924644115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 238691664035801468784815573 5594335875839096924644115)
          ·
            refine ⟨8391503813758645386966173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5594335875839096924644115 8391503813758645386966173)
            ·
              refine ⟨3146813930159492020112315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8391503813758645386966173 3146813930159492020112315)
              ·
                refine ⟨4720220895239238030168473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3146813930159492020112315 4720220895239238030168473)
                ·
                  refine ⟨3540165671429428522626355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4720220895239238030168473 3540165671429428522626355)
                  ·
                    refine ⟨5310248507144142783939533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3540165671429428522626355 5310248507144142783939533)
                    ·
                      refine ⟨1991343190179053543977325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5310248507144142783939533 1991343190179053543977325)
                      ·
                        rfl

theorem cell23_3878127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 3, 1, 2, 1, 3].length) (baseStart_3878127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3878127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3878127 prefixEnd_3878127 := by exact prefixLift 3878127
  have htrace : WordTrace (prefixWord ++ tailWord_3878127) baseStart_3878127 baseEnd_3878127 := by
    simpa [prefixWord, tailWord_3878127, baseEnd_3878127] using wordTrace_append hprefix tailTrace_3878127
  have hstable : (prefixWord ++ tailWord_3878127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3878127).length < 2 ^ (prefixWord ++ tailWord_3878127).sum := by decide
  have hdescent : baseEnd_3878127 < baseStart_3878127 := by decide
  rcases family_descends (prefixWord ++ tailWord_3878127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3878159 : List Nat := [1, 1, 2, 1, 1, 1, 3, 1, 2, 4, 6]
def baseStart_3878159 : Nat := 118140960795 + 3878159 * 2 ^ 59
def prefixEnd_3878159 : Nat := 4983230072969 + 3 ^ 40 * 3878159 * 2
def baseEnd_3878159 : Nat := 1991359621559997418777177

theorem tailTrace_3878159 : CollatzResearch.WordTrace tailWord_3878159 prefixEnd_3878159 1991359621559997418777177 := by
  unfold tailWord_3878159
  simp only [CollatzResearch.WordTrace]
  refine ⟨141448079157099754670981531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94298719438066503113987687 141448079157099754670981531)
  ·
    refine ⟨212172118735649632006472297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141448079157099754670981531 212172118735649632006472297)
    ·
      refine ⟨159129089051737224004854223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212172118735649632006472297 159129089051737224004854223)
      ·
        refine ⟨238693633577605836007281335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159129089051737224004854223 238693633577605836007281335)
        ·
          refine ⟨358040450366408754010922003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238693633577605836007281335 358040450366408754010922003)
          ·
            refine ⟨537060675549613131016383005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 358040450366408754010922003 537060675549613131016383005)
            ·
              refine ⟨201397753331104924131143627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 537060675549613131016383005 201397753331104924131143627)
              ·
                refine ⟨302096629996657386196715441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 201397753331104924131143627 302096629996657386196715441)
                ·
                  refine ⟨226572472497493039647536581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 302096629996657386196715441 226572472497493039647536581)
                  ·
                    refine ⟨42482338593279944933913109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 226572472497493039647536581 42482338593279944933913109)
                    ·
                      refine ⟨1991359621559997418777177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42482338593279944933913109 1991359621559997418777177)
                      ·
                        rfl

theorem cell23_3878159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 4, 6].length) (baseStart_3878159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3878159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3878159 prefixEnd_3878159 := by exact prefixLift 3878159
  have htrace : WordTrace (prefixWord ++ tailWord_3878159) baseStart_3878159 baseEnd_3878159 := by
    simpa [prefixWord, tailWord_3878159, baseEnd_3878159] using wordTrace_append hprefix tailTrace_3878159
  have hstable : (prefixWord ++ tailWord_3878159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3878159).length < 2 ^ (prefixWord ++ tailWord_3878159).sum := by decide
  have hdescent : baseEnd_3878159 < baseStart_3878159 := by decide
  rcases family_descends (prefixWord ++ tailWord_3878159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3878169 : List Nat := [1, 2, 1, 2, 1, 1, 1, 1, 2, 11]
def baseStart_3878169 : Nat := 118140960795 + 3878169 * 2 ^ 59
def prefixEnd_3878169 : Nat := 4983230072969 + 3 ^ 40 * 3878169 * 2
def baseEnd_3878169 : Nat := 663788252122180793217377

theorem tailTrace_3878169 : CollatzResearch.WordTrace tailWord_3878169 prefixEnd_3878169 663788252122180793217377 := by
  unfold tailWord_3878169
  simp only [CollatzResearch.WordTrace]
  refine ⟨141448443887063526378845561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94298962591375684252563707 141448443887063526378845561)
  ·
    refine ⟨106086332915297644784134171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 141448443887063526378845561 106086332915297644784134171)
    ·
      refine ⟨159129499372946467176201257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106086332915297644784134171 159129499372946467176201257)
      ·
        refine ⟨119347124529709850382150943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159129499372946467176201257 119347124529709850382150943)
        ·
          refine ⟨179020686794564775573226415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 119347124529709850382150943 179020686794564775573226415)
          ·
            refine ⟨268531030191847163359839623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 179020686794564775573226415 268531030191847163359839623)
            ·
              refine ⟨402796545287770745039759435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 268531030191847163359839623 402796545287770745039759435)
              ·
                refine ⟨604194817931656117559639153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 402796545287770745039759435 604194817931656117559639153)
                ·
                  refine ⟨453146113448742088169729365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 604194817931656117559639153 453146113448742088169729365)
                  ·
                    refine ⟨663788252122180793217377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 453146113448742088169729365 663788252122180793217377)
                    ·
                      rfl

theorem cell23_3878169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 11].length) (baseStart_3878169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3878169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3878169 prefixEnd_3878169 := by exact prefixLift 3878169
  have htrace : WordTrace (prefixWord ++ tailWord_3878169) baseStart_3878169 baseEnd_3878169 := by
    simpa [prefixWord, tailWord_3878169, baseEnd_3878169] using wordTrace_append hprefix tailTrace_3878169
  have hstable : (prefixWord ++ tailWord_3878169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3878169).length < 2 ^ (prefixWord ++ tailWord_3878169).sum := by decide
  have hdescent : baseEnd_3878169 < baseStart_3878169 := by decide
  rcases family_descends (prefixWord ++ tailWord_3878169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3878173 : List Nat := [1, 4, 2, 3, 1, 1, 3, 1, 7]
def baseStart_3878173 : Nat := 118140960795 + 3878173 * 2 ^ 59
def prefixEnd_3878173 : Nat := 4983230072969 + 3 ^ 40 * 3878173 * 2
def baseEnd_3878173 : Nat := 221262978921017818222457

theorem tailTrace_3878173 : CollatzResearch.WordTrace tailWord_3878173 prefixEnd_3878173 221262978921017818222457 := by
  unfold tailWord_3878173
  simp only [CollatzResearch.WordTrace]
  refine ⟨141448589779049035061991173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94299059852699356707994115 141448589779049035061991173)
  ·
    refine ⟨26521610583571694074123345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141448589779049035061991173 26521610583571694074123345)
    ·
      refine ⟨19891207937678770555592509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26521610583571694074123345 19891207937678770555592509)
      ·
        refine ⟨7459202976629538958347191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19891207937678770555592509 7459202976629538958347191)
        ·
          refine ⟨11188804464944308437520787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7459202976629538958347191 11188804464944308437520787)
          ·
            refine ⟨16783206697416462656281181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11188804464944308437520787 16783206697416462656281181)
            ·
              refine ⟨6293702511531173496105443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16783206697416462656281181 6293702511531173496105443)
              ·
                refine ⟨9440553767296760244158165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6293702511531173496105443 9440553767296760244158165)
                ·
                  refine ⟨221262978921017818222457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9440553767296760244158165 221262978921017818222457)
                  ·
                    rfl

theorem cell23_3878173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 3, 1, 7].length) (baseStart_3878173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3878173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3878173 prefixEnd_3878173 := by exact prefixLift 3878173
  have htrace : WordTrace (prefixWord ++ tailWord_3878173) baseStart_3878173 baseEnd_3878173 := by
    simpa [prefixWord, tailWord_3878173, baseEnd_3878173] using wordTrace_append hprefix tailTrace_3878173
  have hstable : (prefixWord ++ tailWord_3878173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3878173).length < 2 ^ (prefixWord ++ tailWord_3878173).sum := by decide
  have hdescent : baseEnd_3878173 < baseStart_3878173 := by decide
  rcases family_descends (prefixWord ++ tailWord_3878173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3878184 : List Nat := [2, 1, 5, 1, 2, 1, 4, 1, 2, 2, 2]
def baseStart_3878184 : Nat := 118140960795 + 3878184 * 2 ^ 59
def prefixEnd_3878184 : Nat := 4983230072969 + 3 ^ 40 * 3878184 * 2
def baseEnd_3878184 : Nat := 1991372458576359820964563

theorem tailTrace_3878184 : CollatzResearch.WordTrace tailWord_3878184 prefixEnd_3878184 1991372458576359820964563 := by
  unfold tailWord_3878184
  simp only [CollatzResearch.WordTrace]
  refine ⟨70724495491004591970320803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94299327321339455960427737 70724495491004591970320803)
  ·
    refine ⟨106086743236506887955481205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70724495491004591970320803 106086743236506887955481205)
    ·
      refine ⟨9945632178422520745826363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 106086743236506887955481205 9945632178422520745826363)
      ·
        refine ⟨14918448267633781118739545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9945632178422520745826363 14918448267633781118739545)
        ·
          refine ⟨11188836200725335839054659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14918448267633781118739545 11188836200725335839054659)
          ·
            refine ⟨16783254301088003758581989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11188836200725335839054659 16783254301088003758581989)
            ·
              refine ⟨3146860181454000704734123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16783254301088003758581989 3146860181454000704734123)
              ·
                refine ⟨4720290272181001057101185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3146860181454000704734123 4720290272181001057101185)
                ·
                  refine ⟨3540217704135750792825889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4720290272181001057101185 3540217704135750792825889)
                  ·
                    refine ⟨2655163278101813094619417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3540217704135750792825889 2655163278101813094619417)
                    ·
                      refine ⟨1991372458576359820964563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2655163278101813094619417 1991372458576359820964563)
                      ·
                        rfl

theorem cell23_3878184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 4, 1, 2, 2, 2].length) (baseStart_3878184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3878184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3878184 prefixEnd_3878184 := by exact prefixLift 3878184
  have htrace : WordTrace (prefixWord ++ tailWord_3878184) baseStart_3878184 baseEnd_3878184 := by
    simpa [prefixWord, tailWord_3878184, baseEnd_3878184] using wordTrace_append hprefix tailTrace_3878184
  have hstable : (prefixWord ++ tailWord_3878184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3878184).length < 2 ^ (prefixWord ++ tailWord_3878184).sum := by decide
  have hdescent : baseEnd_3878184 < baseStart_3878184 := by decide
  rcases family_descends (prefixWord ++ tailWord_3878184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3878226 : List Nat := [3, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5]
def baseStart_3878226 : Nat := 118140960795 + 3878226 * 2 ^ 59
def prefixEnd_3878226 : Nat := 4983230072969 + 3 ^ 40 * 3878226 * 2
def baseEnd_3878226 : Nat := 1991394024763848656639369

theorem tailTrace_3878226 : CollatzResearch.WordTrace tailWord_3878226 prefixEnd_3878226 1991394024763848656639369 := by
  unfold tailWord_3878226
  simp only [CollatzResearch.WordTrace]
  refine ⟨35362630711964256278417633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 94300348565238016742447021 35362630711964256278417633)
  ·
    refine ⟨26521973033973192208813225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35362630711964256278417633 26521973033973192208813225)
    ·
      refine ⟨19891479775479894156609919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26521973033973192208813225 19891479775479894156609919)
      ·
        refine ⟨29837219663219841234914879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19891479775479894156609919 29837219663219841234914879)
        ·
          refine ⟨44755829494829761852372319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29837219663219841234914879 44755829494829761852372319)
          ·
            refine ⟨67133744242244642778558479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44755829494829761852372319 67133744242244642778558479)
            ·
              refine ⟨100700616363366964167837719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67133744242244642778558479 100700616363366964167837719)
              ·
                refine ⟨151050924545050446251756579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 100700616363366964167837719 151050924545050446251756579)
                ·
                  refine ⟨226576386817575669377634869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 151050924545050446251756579 226576386817575669377634869)
                  ·
                    refine ⟨21241536264147719004153269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 226576386817575669377634869 21241536264147719004153269)
                    ·
                      refine ⟨1991394024763848656639369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21241536264147719004153269 1991394024763848656639369)
                      ·
                        rfl

theorem cell23_3878226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5].length) (baseStart_3878226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3878226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3878226 prefixEnd_3878226 := by exact prefixLift 3878226
  have htrace : WordTrace (prefixWord ++ tailWord_3878226) baseStart_3878226 baseEnd_3878226 := by
    simpa [prefixWord, tailWord_3878226, baseEnd_3878226] using wordTrace_append hprefix tailTrace_3878226
  have hstable : (prefixWord ++ tailWord_3878226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3878226).length < 2 ^ (prefixWord ++ tailWord_3878226).sum := by decide
  have hdescent : baseEnd_3878226 < baseStart_3878226 := by decide
  rcases family_descends (prefixWord ++ tailWord_3878226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3878240 : List Nat := [2, 1, 1, 3, 4, 2, 1, 1, 2, 4, 2]
def baseStart_3878240 : Nat := 118140960795 + 3878240 * 2 ^ 59
def prefixEnd_3878240 : Nat := 4983230072969 + 3 ^ 40 * 3878240 * 2
def baseEnd_3878240 : Nat := 1991401213493011601864305

theorem tailTrace_3878240 : CollatzResearch.WordTrace tailWord_3878240 prefixEnd_3878240 1991401213493011601864305 := by
  unfold tailWord_3878240
  simp only [CollatzResearch.WordTrace]
  refine ⟨70725516734903152752340087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94300688979870870336453449 70725516734903152752340087)
  ·
    refine ⟨106088275102354729128510131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70725516734903152752340087 106088275102354729128510131)
    ·
      refine ⟨159132412653532093692765197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106088275102354729128510131 159132412653532093692765197)
      ·
        refine ⟨59674654745074535134786949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 159132412653532093692765197 59674654745074535134786949)
        ·
          refine ⟨11188997764701475337772553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59674654745074535134786949 11188997764701475337772553)
          ·
            refine ⟨8391748323526106503329415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11188997764701475337772553 8391748323526106503329415)
            ·
              refine ⟨12587622485289159754994123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8391748323526106503329415 12587622485289159754994123)
              ·
                refine ⟨18881433727933739632491185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12587622485289159754994123 18881433727933739632491185)
                ·
                  refine ⟨14161075295950304724368389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18881433727933739632491185 14161075295950304724368389)
                  ·
                    refine ⟨2655201617990682135819073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14161075295950304724368389 2655201617990682135819073)
                    ·
                      refine ⟨1991401213493011601864305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2655201617990682135819073 1991401213493011601864305)
                      ·
                        rfl

theorem cell23_3878240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 1, 2, 4, 2].length) (baseStart_3878240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3878240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3878240 prefixEnd_3878240 := by exact prefixLift 3878240
  have htrace : WordTrace (prefixWord ++ tailWord_3878240) baseStart_3878240 baseEnd_3878240 := by
    simpa [prefixWord, tailWord_3878240, baseEnd_3878240] using wordTrace_append hprefix tailTrace_3878240
  have hstable : (prefixWord ++ tailWord_3878240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3878240).length < 2 ^ (prefixWord ++ tailWord_3878240).sum := by decide
  have hdescent : baseEnd_3878240 < baseStart_3878240 := by decide
  rcases family_descends (prefixWord ++ tailWord_3878240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3878254 : List Nat := [4, 1, 2, 4, 2, 1, 1, 1, 2, 5]
def baseStart_3878254 : Nat := 118140960795 + 3878254 * 2 ^ 59
def prefixEnd_3878254 : Nat := 4983230072969 + 3 ^ 40 * 3878254 * 2
def baseEnd_3878254 : Nat := 663802800740724849029747

theorem tailTrace_3878254 : CollatzResearch.WordTrace tailWord_3878254 prefixEnd_3878254 663802800740724849029747 := by
  unfold tailWord_3878254
  simp only [CollatzResearch.WordTrace]
  refine ⟨17681443011469448236961227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 94301029394503723930459877 17681443011469448236961227)
  ·
    refine ⟨26522164517204172355441841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17681443011469448236961227 26522164517204172355441841)
    ·
      refine ⟨19891623387903129266581381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26522164517204172355441841 19891623387903129266581381)
      ·
        refine ⟨3729679385231836737484009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19891623387903129266581381 3729679385231836737484009)
        ·
          refine ⟨2797259538923877553113007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3729679385231836737484009 2797259538923877553113007)
          ·
            refine ⟨4195889308385816329669511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2797259538923877553113007 4195889308385816329669511)
            ·
              refine ⟨6293833962578724494504267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4195889308385816329669511 6293833962578724494504267)
              ·
                refine ⟨9440750943868086741756401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6293833962578724494504267 9440750943868086741756401)
                ·
                  refine ⟨7080563207901065056317301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9440750943868086741756401 7080563207901065056317301)
                  ·
                    refine ⟨663802800740724849029747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7080563207901065056317301 663802800740724849029747)
                    ·
                      rfl

theorem cell23_3878254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 1, 1, 2, 5].length) (baseStart_3878254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3878254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3878254 prefixEnd_3878254 := by exact prefixLift 3878254
  have htrace : WordTrace (prefixWord ++ tailWord_3878254) baseStart_3878254 baseEnd_3878254 := by
    simpa [prefixWord, tailWord_3878254, baseEnd_3878254] using wordTrace_append hprefix tailTrace_3878254
  have hstable : (prefixWord ++ tailWord_3878254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3878254).length < 2 ^ (prefixWord ++ tailWord_3878254).sum := by decide
  have hdescent : baseEnd_3878254 < baseStart_3878254 := by decide
  rcases family_descends (prefixWord ++ tailWord_3878254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3878280 : List Nat := [2, 1, 3, 3, 1, 4, 1, 2, 6]
def baseStart_3878280 : Nat := 118140960795 + 3878280 * 2 ^ 59
def prefixEnd_3878280 : Nat := 4983230072969 + 3 ^ 40 * 3878280 * 2
def baseEnd_3878280 : Nat := 221269083635465716151569

theorem tailTrace_3878280 : CollatzResearch.WordTrace tailWord_3878280 prefixEnd_3878280 221269083635465716151569 := by
  unfold tailWord_3878280
  simp only [CollatzResearch.WordTrace]
  refine ⟨70726246194830696168068147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94301661593107594890757529 70726246194830696168068147)
  ·
    refine ⟨106089369292246044252102221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70726246194830696168068147 106089369292246044252102221)
    ·
      refine ⟨39783513484592266594538333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106089369292246044252102221 39783513484592266594538333)
      ·
        refine ⟨14918817556722099972951875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39783513484592266594538333 14918817556722099972951875)
        ·
          refine ⟨22378226335083149959427813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14918817556722099972951875 22378226335083149959427813)
          ·
            refine ⟨4195917437828090617392715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22378226335083149959427813 4195917437828090617392715)
            ·
              refine ⟨6293876156742135926089073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4195917437828090617392715 6293876156742135926089073)
              ·
                refine ⟨4720407117556601944566805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6293876156742135926089073 4720407117556601944566805)
                ·
                  refine ⟨221269083635465716151569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4720407117556601944566805 221269083635465716151569)
                  ·
                    rfl

theorem cell23_3878280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 1, 2, 6].length) (baseStart_3878280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3878280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3878280 prefixEnd_3878280 := by exact prefixLift 3878280
  have htrace : WordTrace (prefixWord ++ tailWord_3878280) baseStart_3878280 baseEnd_3878280 := by
    simpa [prefixWord, tailWord_3878280, baseEnd_3878280] using wordTrace_append hprefix tailTrace_3878280
  have hstable : (prefixWord ++ tailWord_3878280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3878280).length < 2 ^ (prefixWord ++ tailWord_3878280).sum := by decide
  have hdescent : baseEnd_3878280 < baseStart_3878280 := by decide
  rcases family_descends (prefixWord ++ tailWord_3878280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3878317 : List Nat := [1, 5, 2, 2, 1, 1, 2, 1, 1, 5, 2]
def baseStart_3878317 : Nat := 118140960795 + 3878317 * 2 ^ 59
def prefixEnd_3878317 : Nat := 4983230072969 + 3 ^ 40 * 3878317 * 2
def baseEnd_3878317 : Nat := 1991440751503407800601451

theorem tailTrace_3878317 : CollatzResearch.WordTrace tailWord_3878317 prefixEnd_3878317 1991440751503407800601451 := by
  unfold tailWord_3878317
  simp only [CollatzResearch.WordTrace]
  refine ⟨141453841890527347655233205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94302561260351565103488803 141453841890527347655233205)
  ·
    refine ⟨13261297677236938842678113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 141453841890527347655233205 13261297677236938842678113)
    ·
      refine ⟨9945973257927704132008585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13261297677236938842678113 9945973257927704132008585)
      ·
        refine ⟨7459479943445778099006439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9945973257927704132008585 7459479943445778099006439)
        ·
          refine ⟨11189219915168667148509659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7459479943445778099006439 11189219915168667148509659)
          ·
            refine ⟨16783829872753000722764489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11189219915168667148509659 16783829872753000722764489)
            ·
              refine ⟨12587872404564750542073367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16783829872753000722764489 12587872404564750542073367)
              ·
                refine ⟨18881808606847125813110051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12587872404564750542073367 18881808606847125813110051)
                ·
                  refine ⟨28322712910270688719665077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18881808606847125813110051 28322712910270688719665077)
                  ·
                    refine ⟨2655254335337877067468601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28322712910270688719665077 2655254335337877067468601)
                    ·
                      refine ⟨1991440751503407800601451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2655254335337877067468601 1991440751503407800601451)
                      ·
                        rfl

theorem cell23_3878317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 1, 1, 5, 2].length) (baseStart_3878317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3878317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3878317 prefixEnd_3878317 := by exact prefixLift 3878317
  have htrace : WordTrace (prefixWord ++ tailWord_3878317) baseStart_3878317 baseEnd_3878317 := by
    simpa [prefixWord, tailWord_3878317, baseEnd_3878317] using wordTrace_append hprefix tailTrace_3878317
  have hstable : (prefixWord ++ tailWord_3878317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3878317).length < 2 ^ (prefixWord ++ tailWord_3878317).sum := by decide
  have hdescent : baseEnd_3878317 < baseStart_3878317 := by decide
  rcases family_descends (prefixWord ++ tailWord_3878317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3878336 : List Nat := [2, 1, 1, 2, 3, 1, 13]
def baseStart_3878336 : Nat := 118140960795 + 3878336 * 2 ^ 59
def prefixEnd_3878336 : Nat := 4983230072969 + 3 ^ 40 * 3878336 * 2
def baseEnd_3878336 : Nat := 24585808736244978102023

theorem tailTrace_3878336 : CollatzResearch.WordTrace tailWord_3878336 prefixEnd_3878336 24585808736244978102023 := by
  unfold tailWord_3878336
  simp only [CollatzResearch.WordTrace]
  refine ⟨70727267438729256950087431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94303023251639009266783241 70727267438729256950087431)
  ·
    refine ⟨106090901158093885425131147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70727267438729256950087431 106090901158093885425131147)
    ·
      refine ⟨159136351737140828137696721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106090901158093885425131147 159136351737140828137696721)
      ·
        refine ⟨119352263802855621103272541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 159136351737140828137696721 119352263802855621103272541)
        ·
          refine ⟨44757098926070857913727203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 119352263802855621103272541 44757098926070857913727203)
          ·
            refine ⟨67135648389106286870590805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44757098926070857913727203 67135648389106286870590805)
            ·
              refine ⟨24585808736244978102023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 67135648389106286870590805 24585808736244978102023)
              ·
                rfl

theorem cell23_3878336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 13].length) (baseStart_3878336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3878336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3878336 prefixEnd_3878336 := by exact prefixLift 3878336
  have htrace : WordTrace (prefixWord ++ tailWord_3878336) baseStart_3878336 baseEnd_3878336 := by
    simpa [prefixWord, tailWord_3878336, baseEnd_3878336] using wordTrace_append hprefix tailTrace_3878336
  have hstable : (prefixWord ++ tailWord_3878336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3878336).length < 2 ^ (prefixWord ++ tailWord_3878336).sum := by decide
  have hdescent : baseEnd_3878336 < baseStart_3878336 := by decide
  rcases family_descends (prefixWord ++ tailWord_3878336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3878347 : List Nat := [1, 1, 1, 1, 3, 3, 5, 1, 3, 2, 2]
def baseStart_3878347 : Nat := 118140960795 + 3878347 * 2 ^ 59
def prefixEnd_3878347 : Nat := 4983230072969 + 3 ^ 40 * 3878347 * 2
def baseEnd_3878347 : Nat := 1991456155923042683226313

theorem tailTrace_3878347 : CollatzResearch.WordTrace tailWord_3878347 prefixEnd_3878347 1991456155923042683226313 := by
  unfold tailWord_3878347
  simp only [CollatzResearch.WordTrace]
  refine ⟨141454936080418662778825295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94303290720279108519216863 141454936080418662778825295)
  ·
    refine ⟨212182404120627994168237943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141454936080418662778825295 212182404120627994168237943)
    ·
      refine ⟨318273606180941991252356915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212182404120627994168237943 318273606180941991252356915)
      ·
        refine ⟨477410409271412986878535373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318273606180941991252356915 477410409271412986878535373)
        ·
          refine ⟨179028903476779870079450765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 477410409271412986878535373 179028903476779870079450765)
          ·
            refine ⟨67135838803792451279794037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 179028903476779870079450765 67135838803792451279794037)
            ·
              refine ⟨6293984887855542307480691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67135838803792451279794037 6293984887855542307480691)
              ·
                refine ⟨9440977331783313461221037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6293984887855542307480691 9440977331783313461221037)
                ·
                  refine ⟨3540366499418742547957889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9440977331783313461221037 3540366499418742547957889)
                  ·
                    refine ⟨2655274874564056910968417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3540366499418742547957889 2655274874564056910968417)
                    ·
                      refine ⟨1991456155923042683226313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2655274874564056910968417 1991456155923042683226313)
                      ·
                        rfl

theorem cell23_3878347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 5, 1, 3, 2, 2].length) (baseStart_3878347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3878347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3878347 prefixEnd_3878347 := by exact prefixLift 3878347
  have htrace : WordTrace (prefixWord ++ tailWord_3878347) baseStart_3878347 baseEnd_3878347 := by
    simpa [prefixWord, tailWord_3878347, baseEnd_3878347] using wordTrace_append hprefix tailTrace_3878347
  have hstable : (prefixWord ++ tailWord_3878347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3878347).length < 2 ^ (prefixWord ++ tailWord_3878347).sum := by decide
  have hdescent : baseEnd_3878347 < baseStart_3878347 := by decide
  rcases family_descends (prefixWord ++ tailWord_3878347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3878380 : List Nat := [2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 3]
def baseStart_3878380 : Nat := 118140960795 + 3878380 * 2 ^ 59
def prefixEnd_3878380 : Nat := 4983230072969 + 3 ^ 40 * 3878380 * 2
def baseEnd_3878380 : Nat := 1991473100784641054113661

theorem tailTrace_3878380 : CollatzResearch.WordTrace tailWord_3878380 prefixEnd_3878380 1991473100784641054113661 := by
  unfold tailWord_3878380
  simp only [CollatzResearch.WordTrace]
  refine ⟨70728069844649554707388297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 94304093126199406276517729 70728069844649554707388297)
  ·
    refine ⟨53046052383487166030541223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70728069844649554707388297 53046052383487166030541223)
    ·
      refine ⟨79569078575230749045811835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53046052383487166030541223 79569078575230749045811835)
      ·
        refine ⟨119353617862846123568717753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 79569078575230749045811835 119353617862846123568717753)
        ·
          refine ⟨89515213397134592676538315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 119353617862846123568717753 89515213397134592676538315)
          ·
            refine ⟨134272820095701889014807473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 89515213397134592676538315 134272820095701889014807473)
            ·
              refine ⟨100704615071776416761105605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 134272820095701889014807473 100704615071776416761105605)
              ·
                refine ⟨18882115325958078142707301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100704615071776416761105605 18882115325958078142707301)
                ·
                  refine ⟨3540396623617139651757619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18882115325958078142707301 3540396623617139651757619)
                  ·
                    refine ⟨5310594935425709477636429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3540396623617139651757619 5310594935425709477636429)
                    ·
                      refine ⟨1991473100784641054113661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5310594935425709477636429 1991473100784641054113661)
                      ·
                        rfl

theorem cell23_3878380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 3].length) (baseStart_3878380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3878380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3878380 prefixEnd_3878380 := by exact prefixLift 3878380
  have htrace : WordTrace (prefixWord ++ tailWord_3878380) baseStart_3878380 baseEnd_3878380 := by
    simpa [prefixWord, tailWord_3878380, baseEnd_3878380] using wordTrace_append hprefix tailTrace_3878380
  have hstable : (prefixWord ++ tailWord_3878380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3878380).length < 2 ^ (prefixWord ++ tailWord_3878380).sum := by decide
  have hdescent : baseEnd_3878380 < baseStart_3878380 := by decide
  rcases family_descends (prefixWord ++ tailWord_3878380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3878397 : List Nat := [1, 4, 1, 1, 1, 4, 1, 4, 2, 1, 3]
def baseStart_3878397 : Nat := 118140960795 + 3878397 * 2 ^ 59
def prefixEnd_3878397 : Nat := 4983230072969 + 3 ^ 40 * 3878397 * 2
def baseEnd_3878397 : Nat := 1991481829955767487601083

theorem tailTrace_3878397 : CollatzResearch.WordTrace tailWord_3878397 prefixEnd_3878397 1991481829955767487601083 := by
  unfold tailWord_3878397
  simp only [CollatzResearch.WordTrace]
  refine ⟨141456759730237521318145445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94304506486825014212096963 141456759730237521318145445)
  ·
    refine ⟨26523142449419535247152271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 141456759730237521318145445 26523142449419535247152271)
    ·
      refine ⟨39784713674129302870728407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26523142449419535247152271 39784713674129302870728407)
      ·
        refine ⟨59677070511193954306092611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39784713674129302870728407 59677070511193954306092611)
        ·
          refine ⟨89515605766790931459138917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59677070511193954306092611 89515605766790931459138917)
          ·
            refine ⟨16784176081273299648588547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 89515605766790931459138917 16784176081273299648588547)
            ·
              refine ⟨25176264121909949472882821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16784176081273299648588547 25176264121909949472882821)
              ·
                refine ⟨4720549522858115526165529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25176264121909949472882821 4720549522858115526165529)
                ·
                  refine ⟨3540412142143586644624147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4720549522858115526165529 3540412142143586644624147)
                  ·
                    refine ⟨5310618213215379966936221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3540412142143586644624147 5310618213215379966936221)
                    ·
                      refine ⟨1991481829955767487601083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5310618213215379966936221 1991481829955767487601083)
                      ·
                        rfl

theorem cell23_3878397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 4, 2, 1, 3].length) (baseStart_3878397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3878397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3878397 prefixEnd_3878397 := by exact prefixLift 3878397
  have htrace : WordTrace (prefixWord ++ tailWord_3878397) baseStart_3878397 baseEnd_3878397 := by
    simpa [prefixWord, tailWord_3878397, baseEnd_3878397] using wordTrace_append hprefix tailTrace_3878397
  have hstable : (prefixWord ++ tailWord_3878397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3878397).length < 2 ^ (prefixWord ++ tailWord_3878397).sum := by decide
  have hdescent : baseEnd_3878397 < baseStart_3878397 := by decide
  rcases family_descends (prefixWord ++ tailWord_3878397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3878407 : List Nat := [1, 1, 4, 3, 2, 1, 1, 2, 3, 3, 2]
def baseStart_3878407 : Nat := 118140960795 + 3878407 * 2 ^ 59
def prefixEnd_3878407 : Nat := 4983230072969 + 3 ^ 40 * 3878407 * 2
def baseEnd_3878407 : Nat := 1991486964762312448476037

theorem tailTrace_3878407 : CollatzResearch.WordTrace tailWord_3878407 prefixEnd_3878407 1991486964762312448476037 := by
  unfold tailWord_3878407
  simp only [CollatzResearch.WordTrace]
  refine ⟨141457124460201293026009475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94304749640134195350672983 141457124460201293026009475)
  ·
    refine ⟨212185686690301939539014213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141457124460201293026009475 212185686690301939539014213)
    ·
      refine ⟨39784816254431613663565165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 212185686690301939539014213 39784816254431613663565165)
      ·
        refine ⟨14919306095411855123836937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39784816254431613663565165 14919306095411855123836937)
        ·
          refine ⟨11189479571558891342877703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14919306095411855123836937 11189479571558891342877703)
          ·
            refine ⟨16784219357338337014316555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11189479571558891342877703 16784219357338337014316555)
            ·
              refine ⟨25176329036007505521474833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16784219357338337014316555 25176329036007505521474833)
              ·
                refine ⟨18882246777005629141106125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25176329036007505521474833 18882246777005629141106125)
                ·
                  refine ⟨7080842541377110927914797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18882246777005629141106125 7080842541377110927914797)
                  ·
                    refine ⟨2655315953016416597968049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7080842541377110927914797 2655315953016416597968049)
                    ·
                      refine ⟨1991486964762312448476037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2655315953016416597968049 1991486964762312448476037)
                      ·
                        rfl

theorem cell23_3878407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 2, 3, 3, 2].length) (baseStart_3878407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3878407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3878407 prefixEnd_3878407 := by exact prefixLift 3878407
  have htrace : WordTrace (prefixWord ++ tailWord_3878407) baseStart_3878407 baseEnd_3878407 := by
    simpa [prefixWord, tailWord_3878407, baseEnd_3878407] using wordTrace_append hprefix tailTrace_3878407
  have hstable : (prefixWord ++ tailWord_3878407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3878407).length < 2 ^ (prefixWord ++ tailWord_3878407).sum := by decide
  have hdescent : baseEnd_3878407 < baseStart_3878407 := by decide
  rcases family_descends (prefixWord ++ tailWord_3878407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3878437 : List Nat := [1, 3, 1, 2, 2, 1, 1, 4, 4, 2, 2]
def baseStart_3878437 : Nat := 118140960795 + 3878437 * 2 ^ 59
def prefixEnd_3878437 : Nat := 4983230072969 + 3 ^ 40 * 3878437 * 2
def baseEnd_3878437 : Nat := 1991502369181947331100899

theorem tailTrace_3878437 : CollatzResearch.WordTrace tailWord_3878437 prefixEnd_3878437 1991502369181947331100899 := by
  unfold tailWord_3878437
  simp only [CollatzResearch.WordTrace]
  refine ⟨141458218650092608149601565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94305479100061738766401043 141458218650092608149601565)
  ·
    refine ⟨53046831993784728056100587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141458218650092608149601565 53046831993784728056100587)
    ·
      refine ⟨79570247990677092084150881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53046831993784728056100587 79570247990677092084150881)
      ·
        refine ⟨59677685993007819063113161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 79570247990677092084150881 59677685993007819063113161)
        ·
          refine ⟨44758264494755864297334871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59677685993007819063113161 44758264494755864297334871)
          ·
            refine ⟨67137396742133796446002307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44758264494755864297334871 67137396742133796446002307)
            ·
              refine ⟨100706095113200694669003461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67137396742133796446002307 100706095113200694669003461)
              ·
                refine ⟨18882392833725130250438149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 100706095113200694669003461 18882392833725130250438149)
                ·
                  refine ⟨3540448656323461921957153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18882392833725130250438149 3540448656323461921957153)
                  ·
                    refine ⟨2655336492242596441467865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3540448656323461921957153 2655336492242596441467865)
                    ·
                      refine ⟨1991502369181947331100899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2655336492242596441467865 1991502369181947331100899)
                      ·
                        rfl

theorem cell23_3878437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 4, 4, 2, 2].length) (baseStart_3878437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3878437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3878437 prefixEnd_3878437 := by exact prefixLift 3878437
  have htrace : WordTrace (prefixWord ++ tailWord_3878437) baseStart_3878437 baseEnd_3878437 := by
    simpa [prefixWord, tailWord_3878437, baseEnd_3878437] using wordTrace_append hprefix tailTrace_3878437
  have hstable : (prefixWord ++ tailWord_3878437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3878437).length < 2 ^ (prefixWord ++ tailWord_3878437).sum := by decide
  have hdescent : baseEnd_3878437 < baseStart_3878437 := by decide
  rcases family_descends (prefixWord ++ tailWord_3878437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3878471 : List Nat := [1, 1, 4, 1, 6, 1, 1, 1, 1, 4, 2]
def baseStart_3878471 : Nat := 118140960795 + 3878471 * 2 ^ 59
def prefixEnd_3878471 : Nat := 4983230072969 + 3 ^ 40 * 3878471 * 2
def baseEnd_3878471 : Nat := 1991519827524200198075743

theorem tailTrace_3878471 : CollatzResearch.WordTrace tailWord_3878471 prefixEnd_3878471 1991519827524200198075743 := by
  unfold tailWord_3878471
  simp only [CollatzResearch.WordTrace]
  refine ⟨141459458731969431956339267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94306305821312954637559511 141459458731969431956339267)
  ·
    refine ⟨212189188097954147934508901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141459458731969431956339267 212189188097954147934508901)
    ·
      refine ⟨39785472768366402737720419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 212189188097954147934508901 39785472768366402737720419)
      ·
        refine ⟨59678209152549604106580629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39785472768366402737720419 59678209152549604106580629)
        ·
          refine ⟨2797416054025762692495967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 59678209152549604106580629 2797416054025762692495967)
          ·
            refine ⟨4196124081038644038743951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2797416054025762692495967 4196124081038644038743951)
            ·
              refine ⟨6294186121557966058115927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4196124081038644038743951 6294186121557966058115927)
              ·
                refine ⟨9441279182336949087173891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6294186121557966058115927 9441279182336949087173891)
                ·
                  refine ⟨14161918773505423630760837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9441279182336949087173891 14161918773505423630760837)
                  ·
                    refine ⟨2655359770032266930767657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14161918773505423630760837 2655359770032266930767657)
                    ·
                      refine ⟨1991519827524200198075743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2655359770032266930767657 1991519827524200198075743)
                      ·
                        rfl

theorem cell23_3878471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 1, 1, 1, 4, 2].length) (baseStart_3878471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3878471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3878471 prefixEnd_3878471 := by exact prefixLift 3878471
  have htrace : WordTrace (prefixWord ++ tailWord_3878471) baseStart_3878471 baseEnd_3878471 := by
    simpa [prefixWord, tailWord_3878471, baseEnd_3878471] using wordTrace_append hprefix tailTrace_3878471
  have hstable : (prefixWord ++ tailWord_3878471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3878471).length < 2 ^ (prefixWord ++ tailWord_3878471).sum := by decide
  have hdescent : baseEnd_3878471 < baseStart_3878471 := by decide
  rcases family_descends (prefixWord ++ tailWord_3878471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3878517 : List Nat := [1, 3, 4, 2, 1, 2, 1, 1, 1, 2, 5]
def baseStart_3878517 : Nat := 118140960795 + 3878517 * 2 ^ 59
def prefixEnd_3878517 : Nat := 4983230072969 + 3 ^ 40 * 3878517 * 2
def baseEnd_3878517 : Nat := 1991543447634307018100531

theorem tailTrace_3878517 : CollatzResearch.WordTrace tailWord_3878517 prefixEnd_3878517 1991543447634307018100531 := by
  unfold tailWord_3878517
  simp only [CollatzResearch.WordTrace]
  refine ⟨141461136489802781812513805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94307424326535187875009203 141461136489802781812513805)
  ·
    refine ⟨53047926183676043179692677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 141461136489802781812513805 53047926183676043179692677)
    ·
      refine ⟨9946486159439258096192377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53047926183676043179692677 9946486159439258096192377)
      ·
        refine ⟨7459864619579443572144283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9946486159439258096192377 7459864619579443572144283)
        ·
          refine ⟨11189796929369165358216425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7459864619579443572144283 11189796929369165358216425)
          ·
            refine ⟨8392347697026874018662319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11189796929369165358216425 8392347697026874018662319)
            ·
              refine ⟨12588521545540311027993479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8392347697026874018662319 12588521545540311027993479)
              ·
                refine ⟨18882782318310466541990219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12588521545540311027993479 18882782318310466541990219)
                ·
                  refine ⟨28324173477465699812985329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18882782318310466541990219 28324173477465699812985329)
                  ·
                    refine ⟨21243130108099274859738997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28324173477465699812985329 21243130108099274859738997)
                    ·
                      refine ⟨1991543447634307018100531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21243130108099274859738997 1991543447634307018100531)
                      ·
                        rfl

theorem cell23_3878517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_3878517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3878517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3878517 prefixEnd_3878517 := by exact prefixLift 3878517
  have htrace : WordTrace (prefixWord ++ tailWord_3878517) baseStart_3878517 baseEnd_3878517 := by
    simpa [prefixWord, tailWord_3878517, baseEnd_3878517] using wordTrace_append hprefix tailTrace_3878517
  have hstable : (prefixWord ++ tailWord_3878517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3878517).length < 2 ^ (prefixWord ++ tailWord_3878517).sum := by decide
  have hdescent : baseEnd_3878517 < baseStart_3878517 := by decide
  rcases family_descends (prefixWord ++ tailWord_3878517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3878543 : List Nat := [1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 9]
def baseStart_3878543 : Nat := 118140960795 + 3878543 * 2 ^ 59
def prefixEnd_3878543 : Nat := 4983230072969 + 3 ^ 40 * 3878543 * 2
def baseEnd_3878543 : Nat := 1991556798131323916375411

theorem tailTrace_3878543 : CollatzResearch.WordTrace tailWord_3878543 prefixEnd_3878543 1991556798131323916375411 := by
  unfold tailWord_3878543
  simp only [CollatzResearch.WordTrace]
  refine ⟨141462084787708588252960283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94308056525139058835306855 141462084787708588252960283)
  ·
    refine ⟨212193127181562882379440425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141462084787708588252960283 212193127181562882379440425)
    ·
      refine ⟨159144845386172161784580319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 212193127181562882379440425 159144845386172161784580319)
      ·
        refine ⟨238717268079258242676870479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 159144845386172161784580319 238717268079258242676870479)
        ·
          refine ⟨358075902118887364015305719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 238717268079258242676870479 358075902118887364015305719)
          ·
            refine ⟨537113853178331046022958579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 358075902118887364015305719 537113853178331046022958579)
            ·
              refine ⟨805670779767496569034437869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 537113853178331046022958579 805670779767496569034437869)
              ·
                refine ⟨302126542412811213387914201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 805670779767496569034437869 302126542412811213387914201)
                ·
                  refine ⟨226594906809608410040935651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 302126542412811213387914201 226594906809608410040935651)
                  ·
                    refine ⟨339892360214412615061403477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 226594906809608410040935651 339892360214412615061403477)
                    ·
                      refine ⟨1991556798131323916375411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 339892360214412615061403477 1991556798131323916375411)
                      ·
                        rfl

theorem cell23_3878543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 9].length) (baseStart_3878543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3878543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3878543 prefixEnd_3878543 := by exact prefixLift 3878543
  have htrace : WordTrace (prefixWord ++ tailWord_3878543) baseStart_3878543 baseEnd_3878543 := by
    simpa [prefixWord, tailWord_3878543, baseEnd_3878543] using wordTrace_append hprefix tailTrace_3878543
  have hstable : (prefixWord ++ tailWord_3878543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3878543).length < 2 ^ (prefixWord ++ tailWord_3878543).sum := by decide
  have hdescent : baseEnd_3878543 < baseStart_3878543 := by decide
  rcases family_descends (prefixWord ++ tailWord_3878543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3878587 : List Nat := [1, 1, 1, 1, 1, 2, 3, 4, 4, 3, 2]
def baseStart_3878587 : Nat := 118140960795 + 3878587 * 2 ^ 59
def prefixEnd_3878587 : Nat := 4983230072969 + 3 ^ 40 * 3878587 * 2
def baseEnd_3878587 : Nat := 1991579391280121744225209

theorem tailTrace_3878587 : CollatzResearch.WordTrace tailWord_3878587 prefixEnd_3878587 1991579391280121744225209 := by
  unfold tailWord_3878587
  simp only [CollatzResearch.WordTrace]
  refine ⟨141463689599549183767562015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94309126399699455845041343 141463689599549183767562015)
  ·
    refine ⟨212195534399323775651343023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 141463689599549183767562015 212195534399323775651343023)
    ·
      refine ⟨318293301598985663477014535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 212195534399323775651343023 318293301598985663477014535)
      ·
        refine ⟨477439952398478495215521803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318293301598985663477014535 477439952398478495215521803)
        ·
          refine ⟨716159928597717742823282705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 477439952398478495215521803 716159928597717742823282705)
          ·
            refine ⟨537119946448288307117462029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 716159928597717742823282705 537119946448288307117462029)
            ·
              refine ⟨201419979918108115169048261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 537119946448288307117462029 201419979918108115169048261)
              ·
                refine ⟨37766246234645271594196549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 201419979918108115169048261 37766246234645271594196549)
                ·
                  refine ⟨7081171168995988423911853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37766246234645271594196549 7081171168995988423911853)
                  ·
                    refine ⟨2655439188373495658966945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7081171168995988423911853 2655439188373495658966945)
                    ·
                      refine ⟨1991579391280121744225209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2655439188373495658966945 1991579391280121744225209)
                      ·
                        rfl

theorem cell23_3878587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 4, 3, 2].length) (baseStart_3878587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3878587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3878587 prefixEnd_3878587 := by exact prefixLift 3878587
  have htrace : WordTrace (prefixWord ++ tailWord_3878587) baseStart_3878587 baseEnd_3878587 := by
    simpa [prefixWord, tailWord_3878587, baseEnd_3878587] using wordTrace_append hprefix tailTrace_3878587
  have hstable : (prefixWord ++ tailWord_3878587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3878587).length < 2 ^ (prefixWord ++ tailWord_3878587).sum := by decide
  have hdescent : baseEnd_3878587 < baseStart_3878587 := by decide
  rcases family_descends (prefixWord ++ tailWord_3878587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3878598 : List Nat := [6, 1, 2, 1, 1, 1, 3, 1, 2, 2, 3]
def baseStart_3878598 : Nat := 118140960795 + 3878598 * 2 ^ 59
def prefixEnd_3878598 : Nat := 4983230072969 + 3 ^ 40 * 3878598 * 2
def baseEnd_3878598 : Nat := 1991585039567321201187659

theorem tailTrace_3878598 : CollatzResearch.WordTrace tailWord_3878598 prefixEnd_3878598 1991585039567321201187659 := by
  unfold tailWord_3878598
  simp only [CollatzResearch.WordTrace]
  refine ⟨4420752837578416645194139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 94309393868339555097474965 4420752837578416645194139)
  ·
    refine ⟨6631129256367624967791209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4420752837578416645194139 6631129256367624967791209)
    ·
      refine ⟨4973346942275718725843407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6631129256367624967791209 4973346942275718725843407)
      ·
        refine ⟨7460020413413578088765111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4973346942275718725843407 7460020413413578088765111)
        ·
          refine ⟨11190030620120367133147667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7460020413413578088765111 11190030620120367133147667)
          ·
            refine ⟨16785045930180550699721501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11190030620120367133147667 16785045930180550699721501)
            ·
              refine ⟨6294392223817706512395563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16785045930180550699721501 6294392223817706512395563)
              ·
                refine ⟨9441588335726559768593345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6294392223817706512395563 9441588335726559768593345)
                ·
                  refine ⟨7081191251794919826445009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9441588335726559768593345 7081191251794919826445009)
                  ·
                    refine ⟨5310893438846189869833757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7081191251794919826445009 5310893438846189869833757)
                    ·
                      refine ⟨1991585039567321201187659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5310893438846189869833757 1991585039567321201187659)
                      ·
                        rfl

theorem cell23_3878598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_3878598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3878598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3878598 prefixEnd_3878598 := by exact prefixLift 3878598
  have htrace : WordTrace (prefixWord ++ tailWord_3878598) baseStart_3878598 baseEnd_3878598 := by
    simpa [prefixWord, tailWord_3878598, baseEnd_3878598] using wordTrace_append hprefix tailTrace_3878598
  have hstable : (prefixWord ++ tailWord_3878598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3878598).length < 2 ^ (prefixWord ++ tailWord_3878598).sum := by decide
  have hdescent : baseEnd_3878598 < baseStart_3878598 := by decide
  rcases family_descends (prefixWord ++ tailWord_3878598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3878637 : List Nat := [1, 5, 1, 2, 1, 2, 1, 1, 3, 1, 5]
def baseStart_3878637 : Nat := 118140960795 + 3878637 * 2 ^ 59
def prefixEnd_3878637 : Nat := 4983230072969 + 3 ^ 40 * 3878637 * 2
def baseEnd_3878637 : Nat := 1991605065312846548599979

theorem tailTrace_3878637 : CollatzResearch.WordTrace tailWord_3878637 prefixEnd_3878637 1991605065312846548599979 := by
  unfold tailWord_3878637
  simp only [CollatzResearch.WordTrace]
  refine ⟨141465513249368042306882165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 94310342166245361537921443 141465513249368042306882165)
  ·
    refine ⟨13262391867128253966270203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 141465513249368042306882165 13262391867128253966270203)
    ·
      refine ⟨19893587800692380949405305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13262391867128253966270203 19893587800692380949405305)
      ·
        refine ⟨14920190850519285712053979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19893587800692380949405305 14920190850519285712053979)
        ·
          refine ⟨22380286275778928568080969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14920190850519285712053979 22380286275778928568080969)
          ·
            refine ⟨16785214706834196426060727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22380286275778928568080969 16785214706834196426060727)
            ·
              refine ⟨25177822060251294639091091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16785214706834196426060727 25177822060251294639091091)
              ·
                refine ⟨37766733090376941958636637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25177822060251294639091091 37766733090376941958636637)
                ·
                  refine ⟨14162524908891353234488739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37766733090376941958636637 14162524908891353234488739)
                  ·
                    refine ⟨21243787363337029851733109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14162524908891353234488739 21243787363337029851733109)
                    ·
                      refine ⟨1991605065312846548599979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21243787363337029851733109 1991605065312846548599979)
                      ·
                        rfl

theorem cell23_3878637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_3878637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3878637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3878637 prefixEnd_3878637 := by exact prefixLift 3878637
  have htrace : WordTrace (prefixWord ++ tailWord_3878637) baseStart_3878637 baseEnd_3878637 := by
    simpa [prefixWord, tailWord_3878637, baseEnd_3878637] using wordTrace_append hprefix tailTrace_3878637
  have hstable : (prefixWord ++ tailWord_3878637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3878637).length < 2 ^ (prefixWord ++ tailWord_3878637).sum := by decide
  have hdescent : baseEnd_3878637 < baseStart_3878637 := by decide
  rcases family_descends (prefixWord ++ tailWord_3878637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
