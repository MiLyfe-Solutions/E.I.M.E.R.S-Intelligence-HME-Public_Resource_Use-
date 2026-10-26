import V185TrunkScan23Chunk1252

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7421994 : List Nat := [3, 1, 4, 1, 2, 2, 1, 2, 2, 1, 4]
def baseStart_7421994 : Nat := 118140960795 + 7421994 * 2 ^ 59
def prefixEnd_7421994 : Nat := 4983230072969 + 3 ^ 40 * 7421994 * 2
def baseEnd_7421994 : Nat := 3811050336786139648041877

theorem tailTrace_7421994 : CollatzResearch.WordTrace tailWord_7421994 prefixEnd_7421994 3811050336786139648041877 := by
  unfold tailWord_7421994
  simp only [CollatzResearch.WordTrace]
  refine ⟨67675590068347697125864259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180468240182260525668971357 67675590068347697125864259)
  ·
    refine ⟨101513385102521545688796389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67675590068347697125864259 101513385102521545688796389)
    ·
      refine ⟨19033759706722789816649323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101513385102521545688796389 19033759706722789816649323)
      ·
        refine ⟨28550639560084184724973985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19033759706722789816649323 28550639560084184724973985)
        ·
          refine ⟨21412979670063138543730489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28550639560084184724973985 21412979670063138543730489)
          ·
            refine ⟨16059734752547353907797867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21412979670063138543730489 16059734752547353907797867)
            ·
              refine ⟨24089602128821030861696801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16059734752547353907797867 24089602128821030861696801)
              ·
                refine ⟨18067201596615773146272601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24089602128821030861696801 18067201596615773146272601)
                ·
                  refine ⟨13550401197461829859704451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18067201596615773146272601 13550401197461829859704451)
                  ·
                    refine ⟨20325601796192744789556677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13550401197461829859704451 20325601796192744789556677)
                    ·
                      refine ⟨3811050336786139648041877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20325601796192744789556677 3811050336786139648041877)
                      ·
                        rfl

theorem cell23_7421994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_7421994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7421994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7421994 prefixEnd_7421994 := by exact prefixLift 7421994
  have htrace : WordTrace (prefixWord ++ tailWord_7421994) baseStart_7421994 baseEnd_7421994 := by
    simpa [prefixWord, tailWord_7421994, baseEnd_7421994] using wordTrace_append hprefix tailTrace_7421994
  have hstable : (prefixWord ++ tailWord_7421994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7421994).length < 2 ^ (prefixWord ++ tailWord_7421994).sum := by decide
  have hdescent : baseEnd_7421994 < baseStart_7421994 := by decide
  rcases family_descends (prefixWord ++ tailWord_7421994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7422000 : List Nat := [2, 1, 1, 1, 2, 5, 2, 1, 8]
def baseStart_7422000 : Nat := 118140960795 + 7422000 * 2 ^ 59
def prefixEnd_7422000 : Nat := 4983230072969 + 3 ^ 40 * 7422000 * 2
def baseEnd_7422000 : Nat := 423450379741118513840761

theorem tailTrace_7422000 : CollatzResearch.WordTrace tailWord_7422000 prefixEnd_7422000 423450379741118513840761 := by
  unfold tailWord_7422000
  simp only [CollatzResearch.WordTrace]
  refine ⟨135351289555684525764087727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180468386074246034352116969 135351289555684525764087727)
  ·
    refine ⟨203026934333526788646131591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135351289555684525764087727 203026934333526788646131591)
    ·
      refine ⟨304540401500290182969197387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203026934333526788646131591 304540401500290182969197387)
      ·
        refine ⟨456810602250435274453796081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304540401500290182969197387 456810602250435274453796081)
        ·
          refine ⟨342607951687826455840347061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 456810602250435274453796081 342607951687826455840347061)
          ·
            refine ⟨32119495470733730235032537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 342607951687826455840347061 32119495470733730235032537)
            ·
              refine ⟨24089621603050297676274403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32119495470733730235032537 24089621603050297676274403)
              ·
                refine ⟨36134432404575446514411605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24089621603050297676274403 36134432404575446514411605)
                ·
                  refine ⟨423450379741118513840761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36134432404575446514411605 423450379741118513840761)
                  ·
                    rfl

theorem cell23_7422000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 1, 8].length) (baseStart_7422000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7422000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7422000 prefixEnd_7422000 := by exact prefixLift 7422000
  have htrace : WordTrace (prefixWord ++ tailWord_7422000) baseStart_7422000 baseEnd_7422000 := by
    simpa [prefixWord, tailWord_7422000, baseEnd_7422000] using wordTrace_append hprefix tailTrace_7422000
  have hstable : (prefixWord ++ tailWord_7422000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7422000).length < 2 ^ (prefixWord ++ tailWord_7422000).sum := by decide
  have hdescent : baseEnd_7422000 < baseStart_7422000 := by decide
  rcases family_descends (prefixWord ++ tailWord_7422000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7422077 : List Nat := [1, 4, 1, 1, 3, 2, 1, 3, 1, 6]
def baseStart_7422077 : Nat := 118140960795 + 7422077 * 2 ^ 59
def prefixEnd_7422077 : Nat := 4983230072969 + 3 ^ 40 * 7422077 * 2
def baseEnd_7422077 : Nat := 1270364318560154274434665

theorem tailTrace_7422077 : CollatzResearch.WordTrace tailWord_7422077 prefixEnd_7422077 1270364318560154274434665 := by
  unfold tailWord_7422077
  simp only [CollatzResearch.WordTrace]
  refine ⟨270705387532090093678728485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180470258354726729119152323 270705387532090093678728485)
  ·
    refine ⟨50757260162266892564761591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 270705387532090093678728485 50757260162266892564761591)
    ·
      refine ⟨76135890243400338847142387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50757260162266892564761591 76135890243400338847142387)
      ·
        refine ⟨114203835365100508270713581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76135890243400338847142387 114203835365100508270713581)
        ·
          refine ⟨42826438261912690601517593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114203835365100508270713581 42826438261912690601517593)
          ·
            refine ⟨32119828696434517951138195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42826438261912690601517593 32119828696434517951138195)
            ·
              refine ⟨48179743044651776926707293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32119828696434517951138195 48179743044651776926707293)
              ·
                refine ⟨18067403641744416347515235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48179743044651776926707293 18067403641744416347515235)
                ·
                  refine ⟨27101105462616624521272853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18067403641744416347515235 27101105462616624521272853)
                  ·
                    refine ⟨1270364318560154274434665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27101105462616624521272853 1270364318560154274434665)
                    ·
                      rfl

theorem cell23_7422077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 3, 1, 6].length) (baseStart_7422077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7422077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7422077 prefixEnd_7422077 := by exact prefixLift 7422077
  have htrace : WordTrace (prefixWord ++ tailWord_7422077) baseStart_7422077 baseEnd_7422077 := by
    simpa [prefixWord, tailWord_7422077, baseEnd_7422077] using wordTrace_append hprefix tailTrace_7422077
  have hstable : (prefixWord ++ tailWord_7422077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7422077).length < 2 ^ (prefixWord ++ tailWord_7422077).sum := by decide
  have hdescent : baseEnd_7422077 < baseStart_7422077 := by decide
  rcases family_descends (prefixWord ++ tailWord_7422077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7422084 : List Nat := [2, 3, 2, 1, 2, 1, 2, 4, 1, 1, 4]
def baseStart_7422084 : Nat := 118140960795 + 7422084 * 2 ^ 59
def prefixEnd_7422084 : Nat := 4983230072969 + 3 ^ 40 * 7422084 * 2
def baseEnd_7422084 : Nat := 3811096550045044295916463

theorem tailTrace_7422084 : CollatzResearch.WordTrace tailWord_7422084 prefixEnd_7422084 3811096550045044295916463 := by
  unfold tailWord_7422084
  simp only [CollatzResearch.WordTrace]
  refine ⟨135352821421532366937116653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180470428562043155916155537 135352821421532366937116653)
  ·
    refine ⟨50757308033074637601418745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135352821421532366937116653 50757308033074637601418745)
    ·
      refine ⟨38067981024805978201064059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50757308033074637601418745 38067981024805978201064059)
      ·
        refine ⟨57101971537208967301596089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38067981024805978201064059 57101971537208967301596089)
        ·
          refine ⟨42826478652906725476197067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57101971537208967301596089 42826478652906725476197067)
          ·
            refine ⟨64239717979360088214295601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42826478652906725476197067 64239717979360088214295601)
            ·
              refine ⟨48179788484520066160721701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64239717979360088214295601 48179788484520066160721701)
              ·
                refine ⟨9033710340847512405135319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48179788484520066160721701 9033710340847512405135319)
                ·
                  refine ⟨13550565511271268607702979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9033710340847512405135319 13550565511271268607702979)
                  ·
                    refine ⟨20325848266906902911554469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13550565511271268607702979 20325848266906902911554469)
                    ·
                      refine ⟨3811096550045044295916463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20325848266906902911554469 3811096550045044295916463)
                      ·
                        rfl

theorem cell23_7422084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 4, 1, 1, 4].length) (baseStart_7422084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7422084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7422084 prefixEnd_7422084 := by exact prefixLift 7422084
  have htrace : WordTrace (prefixWord ++ tailWord_7422084) baseStart_7422084 baseEnd_7422084 := by
    simpa [prefixWord, tailWord_7422084, baseEnd_7422084] using wordTrace_append hprefix tailTrace_7422084
  have hstable : (prefixWord ++ tailWord_7422084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7422084).length < 2 ^ (prefixWord ++ tailWord_7422084).sum := by decide
  have hdescent : baseEnd_7422084 < baseStart_7422084 := by decide
  rcases family_descends (prefixWord ++ tailWord_7422084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7422088 : List Nat := [2, 1, 3, 4, 1, 3, 1, 1, 2, 3, 2]
def baseStart_7422088 : Nat := 118140960795 + 7422088 * 2 ^ 59
def prefixEnd_7422088 : Nat := 4983230072969 + 3 ^ 40 * 7422088 * 2
def baseEnd_7422088 : Nat := 3811098603967662280266445

theorem tailTrace_7422088 : CollatzResearch.WordTrace tailWord_7422088 prefixEnd_7422088 3811098603967662280266445 := by
  unfold tailWord_7422088
  simp only [CollatzResearch.WordTrace]
  refine ⟨135352894367525121278689459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180470525823366828371585945 135352894367525121278689459)
  ·
    refine ⟨203029341551287681918034189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135352894367525121278689459 203029341551287681918034189)
    ·
      refine ⟨76136003081732880719262821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 203029341551287681918034189 76136003081732880719262821)
      ·
        refine ⟨14275500577824915134861779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76136003081732880719262821 14275500577824915134861779)
        ·
          refine ⟨21413250866737372702292669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14275500577824915134861779 21413250866737372702292669)
          ·
            refine ⟨8029969075026514763359751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21413250866737372702292669 8029969075026514763359751)
            ·
              refine ⟨12044953612539772145039627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8029969075026514763359751 12044953612539772145039627)
              ·
                refine ⟨18067430418809658217559441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12044953612539772145039627 18067430418809658217559441)
                ·
                  refine ⟨13550572814107243663169581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18067430418809658217559441 13550572814107243663169581)
                  ·
                    refine ⟨5081464805290216373688593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13550572814107243663169581 5081464805290216373688593)
                    ·
                      refine ⟨3811098603967662280266445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5081464805290216373688593 3811098603967662280266445)
                      ·
                        rfl

theorem cell23_7422088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 1, 1, 2, 3, 2].length) (baseStart_7422088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7422088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7422088 prefixEnd_7422088 := by exact prefixLift 7422088
  have htrace : WordTrace (prefixWord ++ tailWord_7422088) baseStart_7422088 baseEnd_7422088 := by
    simpa [prefixWord, tailWord_7422088, baseEnd_7422088] using wordTrace_append hprefix tailTrace_7422088
  have hstable : (prefixWord ++ tailWord_7422088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7422088).length < 2 ^ (prefixWord ++ tailWord_7422088).sum := by decide
  have hdescent : baseEnd_7422088 < baseStart_7422088 := by decide
  rcases family_descends (prefixWord ++ tailWord_7422088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7422102 : List Nat := [5, 3, 2, 1, 1, 2, 1, 2, 6]
def baseStart_7422102 : Nat := 118140960795 + 7422102 * 2 ^ 59
def prefixEnd_7422102 : Nat := 4983230072969 + 3 ^ 40 * 7422102 * 2
def baseEnd_7422102 : Nat := 423456199188536136165709

theorem tailTrace_7422102 : CollatzResearch.WordTrace tailWord_7422102 prefixEnd_7422102 423456199188536136165709 := by
  unfold tailWord_7422102
  simp only [CollatzResearch.WordTrace]
  refine ⟨16919143709812470184274285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 180470866237999681965592373 16919143709812470184274285)
  ·
    refine ⟨6344678891179676319102857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16919143709812470184274285 6344678891179676319102857)
    ·
      refine ⟨4758509168384757239327143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6344678891179676319102857 4758509168384757239327143)
      ·
        refine ⟨7137763752577135858990715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4758509168384757239327143 7137763752577135858990715)
        ·
          refine ⟨10706645628865703788486073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7137763752577135858990715 10706645628865703788486073)
          ·
            refine ⟨8029984221649277841364555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10706645628865703788486073 8029984221649277841364555)
            ·
              refine ⟨12044976332473916762046833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8029984221649277841364555 12044976332473916762046833)
              ·
                refine ⟨9033732249355437571535125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12044976332473916762046833 9033732249355437571535125)
                ·
                  refine ⟨423456199188536136165709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9033732249355437571535125 423456199188536136165709)
                  ·
                    rfl

theorem cell23_7422102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 1, 2, 6].length) (baseStart_7422102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7422102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7422102 prefixEnd_7422102 := by exact prefixLift 7422102
  have htrace : WordTrace (prefixWord ++ tailWord_7422102) baseStart_7422102 baseEnd_7422102 := by
    simpa [prefixWord, tailWord_7422102, baseEnd_7422102] using wordTrace_append hprefix tailTrace_7422102
  have hstable : (prefixWord ++ tailWord_7422102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7422102).length < 2 ^ (prefixWord ++ tailWord_7422102).sum := by decide
  have hdescent : baseEnd_7422102 < baseStart_7422102 := by decide
  rcases family_descends (prefixWord ++ tailWord_7422102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7422111 : List Nat := [1, 1, 2, 6, 1, 1, 3, 2, 2, 4]
def baseStart_7422111 : Nat := 118140960795 + 7422111 * 2 ^ 59
def prefixEnd_7422111 : Nat := 4983230072969 + 3 ^ 40 * 7422111 * 2
def baseEnd_7422111 : Nat := 1270370138007571896759613

theorem tailTrace_7422111 : CollatzResearch.WordTrace tailWord_7422111 prefixEnd_7422111 1270370138007571896759613 := by
  unfold tailWord_7422111
  simp only [CollatzResearch.WordTrace]
  refine ⟨270706627613966917485466187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180471085075977944990310791 270706627613966917485466187)
  ·
    refine ⟨406059941420950376228199281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270706627613966917485466187 406059941420950376228199281)
    ·
      refine ⟨304544956065712782171149461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 406059941420950376228199281 304544956065712782171149461)
      ·
        refine ⟨14275544815580286664272631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 304544956065712782171149461 14275544815580286664272631)
        ·
          refine ⟨21413317223370429996408947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14275544815580286664272631 21413317223370429996408947)
          ·
            refine ⟨32119975835055644994613421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21413317223370429996408947 32119975835055644994613421)
            ·
              refine ⟨12044990938145866872980033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32119975835055644994613421 12044990938145866872980033)
              ·
                refine ⟨9033743203609400154735025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12044990938145866872980033 9033743203609400154735025)
                ·
                  refine ⟨6775307402707050116051269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9033743203609400154735025 6775307402707050116051269)
                  ·
                    refine ⟨1270370138007571896759613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6775307402707050116051269 1270370138007571896759613)
                    ·
                      rfl

theorem cell23_7422111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 3, 2, 2, 4].length) (baseStart_7422111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7422111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7422111 prefixEnd_7422111 := by exact prefixLift 7422111
  have htrace : WordTrace (prefixWord ++ tailWord_7422111) baseStart_7422111 baseEnd_7422111 := by
    simpa [prefixWord, tailWord_7422111, baseEnd_7422111] using wordTrace_append hprefix tailTrace_7422111
  have hstable : (prefixWord ++ tailWord_7422111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7422111).length < 2 ^ (prefixWord ++ tailWord_7422111).sum := by decide
  have hdescent : baseEnd_7422111 < baseStart_7422111 := by decide
  rcases family_descends (prefixWord ++ tailWord_7422111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7422161 : List Nat := [1, 2, 2, 1, 2, 2, 4, 3, 1, 3, 2]
def baseStart_7422161 : Nat := 118140960795 + 7422161 * 2 ^ 59
def prefixEnd_7422161 : Nat := 4983230072969 + 3 ^ 40 * 7422161 * 2
def baseEnd_7422161 : Nat := 3811136088055440494653609

theorem tailTrace_7422161 : CollatzResearch.WordTrace tailWord_7422161 prefixEnd_7422161 3811136088055440494653609 := by
  unfold tailWord_7422161
  simp only [CollatzResearch.WordTrace]
  refine ⟨270708451263785776024786337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180472300842523850683190891 270708451263785776024786337)
  ·
    refine ⟨203031338447839332018589753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270708451263785776024786337 203031338447839332018589753)
    ·
      refine ⟨152273503835879499013942315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203031338447839332018589753 152273503835879499013942315)
      ·
        refine ⟨228410255753819248520913473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152273503835879499013942315 228410255753819248520913473)
        ·
          refine ⟨171307691815364436390685105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228410255753819248520913473 171307691815364436390685105)
          ·
            refine ⟨128480768861523327293013829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171307691815364436390685105 128480768861523327293013829)
            ·
              refine ⟨24090144161535623867440093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 128480768861523327293013829 24090144161535623867440093)
              ·
                refine ⟨9033804060575858950290035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24090144161535623867440093 9033804060575858950290035)
                ·
                  refine ⟨13550706090863788425435053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9033804060575858950290035 13550706090863788425435053)
                  ·
                    refine ⟨5081514784073920659538145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13550706090863788425435053 5081514784073920659538145)
                    ·
                      refine ⟨3811136088055440494653609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5081514784073920659538145 3811136088055440494653609)
                      ·
                        rfl

theorem cell23_7422161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 3, 1, 3, 2].length) (baseStart_7422161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7422161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7422161 prefixEnd_7422161 := by exact prefixLift 7422161
  have htrace : WordTrace (prefixWord ++ tailWord_7422161) baseStart_7422161 baseEnd_7422161 := by
    simpa [prefixWord, tailWord_7422161, baseEnd_7422161] using wordTrace_append hprefix tailTrace_7422161
  have hstable : (prefixWord ++ tailWord_7422161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7422161).length < 2 ^ (prefixWord ++ tailWord_7422161).sum := by decide
  have hdescent : baseEnd_7422161 < baseStart_7422161 := by decide
  rcases family_descends (prefixWord ++ tailWord_7422161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7422177 : List Nat := [1, 2, 3, 1, 3, 1, 1, 2, 1, 3, 5]
def baseStart_7422177 : Nat := 118140960795 + 7422177 * 2 ^ 59
def prefixEnd_7422177 : Nat := 4983230072969 + 3 ^ 40 * 7422177 * 2
def baseEnd_7422177 : Nat := 3811144303745912432053535

theorem tailTrace_7422177 : CollatzResearch.WordTrace tailWord_7422177 prefixEnd_7422177 3811144303745912432053535 := by
  unfold tailWord_7422177
  simp only [CollatzResearch.WordTrace]
  refine ⟨270709034831727810757368785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180472689887818540504912523 270709034831727810757368785)
  ·
    refine ⟨203031776123795858068026589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270709034831727810757368785 203031776123795858068026589)
    ·
      refine ⟨76136916046423446775509971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 203031776123795858068026589 76136916046423446775509971)
      ·
        refine ⟨114205374069635170163264957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76136916046423446775509971 114205374069635170163264957)
        ·
          refine ⟨42827015276113188811224359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114205374069635170163264957 42827015276113188811224359)
          ·
            refine ⟨64240522914169783216836539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42827015276113188811224359 64240522914169783216836539)
            ·
              refine ⟨96360784371254674825254809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64240522914169783216836539 96360784371254674825254809)
              ·
                refine ⟨72270588278441006118941107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96360784371254674825254809 72270588278441006118941107)
                ·
                  refine ⟨108405882417661509178411661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72270588278441006118941107 108405882417661509178411661)
                  ·
                    refine ⟨40652205906623065941904373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 108405882417661509178411661 40652205906623065941904373)
                    ·
                      refine ⟨3811144303745912432053535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40652205906623065941904373 3811144303745912432053535)
                      ·
                        rfl

theorem cell23_7422177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 2, 1, 3, 5].length) (baseStart_7422177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7422177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7422177 prefixEnd_7422177 := by exact prefixLift 7422177
  have htrace : WordTrace (prefixWord ++ tailWord_7422177) baseStart_7422177 baseEnd_7422177 := by
    simpa [prefixWord, tailWord_7422177, baseEnd_7422177] using wordTrace_append hprefix tailTrace_7422177
  have hstable : (prefixWord ++ tailWord_7422177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7422177).length < 2 ^ (prefixWord ++ tailWord_7422177).sum := by decide
  have hdescent : baseEnd_7422177 < baseStart_7422177 := by decide
  rcases family_descends (prefixWord ++ tailWord_7422177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7422187 : List Nat := [1, 1, 1, 1, 2, 5, 2, 1, 1, 4, 4]
def baseStart_7422187 : Nat := 118140960795 + 7422187 * 2 ^ 59
def prefixEnd_7422187 : Nat := 4983230072969 + 3 ^ 40 * 7422187 * 2
def baseEnd_7422187 : Nat := 3811149438552457392928489

theorem tailTrace_7422187 : CollatzResearch.WordTrace tailWord_7422187 prefixEnd_7422187 3811149438552457392928489 := by
  unfold tailWord_7422187
  simp only [CollatzResearch.WordTrace]
  refine ⟨270709399561691582465232815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180472933041127721643488543 270709399561691582465232815)
  ·
    refine ⟨406064099342537373697849223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270709399561691582465232815 406064099342537373697849223)
    ·
      refine ⟨609096149013806060546773835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 406064099342537373697849223 609096149013806060546773835)
      ·
        refine ⟨913644223520709090820160753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 609096149013806060546773835 913644223520709090820160753)
        ·
          refine ⟨685233167640531818115120565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 913644223520709090820160753 685233167640531818115120565)
          ·
            refine ⟨64240609466299857948292553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 685233167640531818115120565 64240609466299857948292553)
            ·
              refine ⟨48180457099724893461219415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64240609466299857948292553 48180457099724893461219415)
              ·
                refine ⟨72270685649587340191829123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48180457099724893461219415 72270685649587340191829123)
                ·
                  refine ⟨108406028474381010287743685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72270685649587340191829123 108406028474381010287743685)
                  ·
                    refine ⟨20326130338946439428951941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 108406028474381010287743685 20326130338946439428951941)
                    ·
                      refine ⟨3811149438552457392928489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20326130338946439428951941 3811149438552457392928489)
                      ·
                        rfl

theorem cell23_7422187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 1, 1, 4, 4].length) (baseStart_7422187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7422187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7422187 prefixEnd_7422187 := by exact prefixLift 7422187
  have htrace : WordTrace (prefixWord ++ tailWord_7422187) baseStart_7422187 baseEnd_7422187 := by
    simpa [prefixWord, tailWord_7422187, baseEnd_7422187] using wordTrace_append hprefix tailTrace_7422187
  have hstable : (prefixWord ++ tailWord_7422187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7422187).length < 2 ^ (prefixWord ++ tailWord_7422187).sum := by decide
  have hdescent : baseEnd_7422187 < baseStart_7422187 := by decide
  rcases family_descends (prefixWord ++ tailWord_7422187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7422194 : List Nat := [3, 2, 1, 3, 2, 1, 1, 2, 2, 1, 5]
def baseStart_7422194 : Nat := 118140960795 + 7422194 * 2 ^ 59
def prefixEnd_7422194 : Nat := 4983230072969 + 3 ^ 40 * 7422194 * 2
def baseEnd_7422194 : Nat := 3811153032917038865540957

theorem tailTrace_7422194 : CollatzResearch.WordTrace tailWord_7422194 prefixEnd_7422194 3811153032917038865540957 := by
  unfold tailWord_7422194
  simp only [CollatzResearch.WordTrace]
  refine ⟨67677413718166555665184409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180473103248444148440491757 67677413718166555665184409)
  ·
    refine ⟨50758060288624916748888307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67677413718166555665184409 50758060288624916748888307)
    ·
      refine ⟨76137090432937375123332461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50758060288624916748888307 76137090432937375123332461)
      ·
        refine ⟨28551408912351515671249673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76137090432937375123332461 28551408912351515671249673)
        ·
          refine ⟨21413556684263636753437255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28551408912351515671249673 21413556684263636753437255)
          ·
            refine ⟨32120335026395455130155883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21413556684263636753437255 32120335026395455130155883)
            ·
              refine ⟨48180502539593182695233825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32120335026395455130155883 48180502539593182695233825)
              ·
                refine ⟨36135376904694887021425369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48180502539593182695233825 36135376904694887021425369)
                ·
                  refine ⟨27101532678521165266069027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36135376904694887021425369 27101532678521165266069027)
                  ·
                    refine ⟨40652299017781747899103541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27101532678521165266069027 40652299017781747899103541)
                    ·
                      refine ⟨3811153032917038865540957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40652299017781747899103541 3811153032917038865540957)
                      ·
                        rfl

theorem cell23_7422194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_7422194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7422194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7422194 prefixEnd_7422194 := by exact prefixLift 7422194
  have htrace : WordTrace (prefixWord ++ tailWord_7422194) baseStart_7422194 baseEnd_7422194 := by
    simpa [prefixWord, tailWord_7422194, baseEnd_7422194] using wordTrace_append hprefix tailTrace_7422194
  have hstable : (prefixWord ++ tailWord_7422194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7422194).length < 2 ^ (prefixWord ++ tailWord_7422194).sum := by decide
  have hdescent : baseEnd_7422194 < baseStart_7422194 := by decide
  rcases family_descends (prefixWord ++ tailWord_7422194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7422231 : List Nat := [1, 1, 3, 4, 1, 3, 1, 4, 5]
def baseStart_7422231 : Nat := 118140960795 + 7422231 * 2 ^ 59
def prefixEnd_7422231 : Nat := 4983230072969 + 3 ^ 40 * 7422231 * 2
def baseEnd_7422231 : Nat := 423463559077917246753143

theorem tailTrace_7422231 : CollatzResearch.WordTrace tailWord_7422231 prefixEnd_7422231 423463559077917246753143 := by
  unfold tailWord_7422231
  simp only [CollatzResearch.WordTrace]
  refine ⟨270711004373532177979834547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180474002915688118653223031 270711004373532177979834547)
  ·
    refine ⟨406066506560298266969751821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270711004373532177979834547 406066506560298266969751821)
    ·
      refine ⟨152274939960111850113656933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 406066506560298266969751821 152274939960111850113656933)
      ·
        refine ⟨28551551242520971896310675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 152274939960111850113656933 28551551242520971896310675)
        ·
          refine ⟨42827326863781457844466013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28551551242520971896310675 42827326863781457844466013)
          ·
            refine ⟨16060247573918046691674755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42827326863781457844466013 16060247573918046691674755)
            ·
              refine ⟨24090371360877070037512133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16060247573918046691674755 24090371360877070037512133)
              ·
                refine ⟨4516944630164450632033525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24090371360877070037512133 4516944630164450632033525)
                ·
                  refine ⟨423463559077917246753143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4516944630164450632033525 423463559077917246753143)
                  ·
                    rfl

theorem cell23_7422231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 4, 5].length) (baseStart_7422231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7422231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7422231 prefixEnd_7422231 := by exact prefixLift 7422231
  have htrace : WordTrace (prefixWord ++ tailWord_7422231) baseStart_7422231 baseEnd_7422231 := by
    simpa [prefixWord, tailWord_7422231, baseEnd_7422231] using wordTrace_append hprefix tailTrace_7422231
  have hstable : (prefixWord ++ tailWord_7422231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7422231).length < 2 ^ (prefixWord ++ tailWord_7422231).sum := by decide
  have hdescent : baseEnd_7422231 < baseStart_7422231 := by decide
  rcases family_descends (prefixWord ++ tailWord_7422231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7422238 : List Nat := [4, 3, 2, 1, 1, 2, 1, 1, 2, 2, 4]
def baseStart_7422238 : Nat := 118140960795 + 7422238 * 2 ^ 59
def prefixEnd_7422238 : Nat := 4983230072969 + 3 ^ 40 * 7422238 * 2
def baseEnd_7422238 : Nat := 3811175626065836693390755

theorem tailTrace_7422238 : CollatzResearch.WordTrace tailWord_7422238 prefixEnd_7422238 3811175626065836693390755 := by
  unfold tailWord_7422238
  simp only [CollatzResearch.WordTrace]
  refine ⟨33838907460563352271917421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180474173123004545450226245 33838907460563352271917421)
  ·
    refine ⟨12689590297711257101969033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33838907460563352271917421 12689590297711257101969033)
    ·
      refine ⟨9517192723283442826476775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12689590297711257101969033 9517192723283442826476775)
      ·
        refine ⟨14275789084925164239715163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9517192723283442826476775 14275789084925164239715163)
        ·
          refine ⟨21413683627387746359572745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14275789084925164239715163 21413683627387746359572745)
          ·
            refine ⟨16060262720540809769679559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21413683627387746359572745 16060262720540809769679559)
            ·
              refine ⟨24090394080811214654519339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16060262720540809769679559 24090394080811214654519339)
              ·
                refine ⟨36135591121216821981779009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24090394080811214654519339 36135591121216821981779009)
                ·
                  refine ⟨27101693340912616486334257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36135591121216821981779009 27101693340912616486334257)
                  ·
                    refine ⟨20326270005684462364750693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27101693340912616486334257 20326270005684462364750693)
                    ·
                      refine ⟨3811175626065836693390755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20326270005684462364750693 3811175626065836693390755)
                      ·
                        rfl

theorem cell23_7422238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_7422238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7422238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7422238 prefixEnd_7422238 := by exact prefixLift 7422238
  have htrace : WordTrace (prefixWord ++ tailWord_7422238) baseStart_7422238 baseEnd_7422238 := by
    simpa [prefixWord, tailWord_7422238, baseEnd_7422238] using wordTrace_append hprefix tailTrace_7422238
  have hstable : (prefixWord ++ tailWord_7422238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7422238).length < 2 ^ (prefixWord ++ tailWord_7422238).sum := by decide
  have hdescent : baseEnd_7422238 < baseStart_7422238 := by decide
  rcases family_descends (prefixWord ++ tailWord_7422238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7422325 : List Nat := [1, 3, 4, 1, 2, 1, 3, 3, 1, 4]
def baseStart_7422325 : Nat := 118140960795 + 7422325 * 2 ^ 59
def prefixEnd_7422325 : Nat := 4983230072969 + 3 ^ 40 * 7422325 * 2
def baseEnd_7422325 : Nat := 1270406766294259284334285

theorem tailTrace_7422325 : CollatzResearch.WordTrace tailWord_7422325 prefixEnd_7422325 1270406766294259284334285 := by
  unfold tailWord_7422325
  simp only [CollatzResearch.WordTrace]
  refine ⟨270714432835191632033756429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180476288556794421355837619 270714432835191632033756429)
  ·
    refine ⟨101517912313196862012658661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 270714432835191632033756429 101517912313196862012658661)
    ·
      refine ⟨19034608558724411627373499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101517912313196862012658661 19034608558724411627373499)
      ·
        refine ⟨28551912838086617441060249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19034608558724411627373499 28551912838086617441060249)
        ·
          refine ⟨21413934628564963080795187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28551912838086617441060249 21413934628564963080795187)
          ·
            refine ⟨32120901942847444621192781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21413934628564963080795187 32120901942847444621192781)
            ·
              refine ⟨12045338228567791732947293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32120901942847444621192781 12045338228567791732947293)
              ·
                refine ⟨4517001835712921899855235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12045338228567791732947293 4517001835712921899855235)
                ·
                  refine ⟨6775502753569382849782853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4517001835712921899855235 6775502753569382849782853)
                  ·
                    refine ⟨1270406766294259284334285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6775502753569382849782853 1270406766294259284334285)
                    ·
                      rfl

theorem cell23_7422325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 3, 3, 1, 4].length) (baseStart_7422325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7422325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7422325 prefixEnd_7422325 := by exact prefixLift 7422325
  have htrace : WordTrace (prefixWord ++ tailWord_7422325) baseStart_7422325 baseEnd_7422325 := by
    simpa [prefixWord, tailWord_7422325, baseEnd_7422325] using wordTrace_append hprefix tailTrace_7422325
  have hstable : (prefixWord ++ tailWord_7422325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7422325).length < 2 ^ (prefixWord ++ tailWord_7422325).sum := by decide
  have hdescent : baseEnd_7422325 < baseStart_7422325 := by decide
  rcases family_descends (prefixWord ++ tailWord_7422325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7422348 : List Nat := [2, 2, 1, 2, 1, 4, 3, 1, 3, 1, 3]
def baseStart_7422348 : Nat := 118140960795 + 7422348 * 2 ^ 59
def prefixEnd_7422348 : Nat := 4983230072969 + 3 ^ 40 * 7422348 * 2
def baseEnd_7422348 : Nat := 3811232108937831263015249

theorem tailTrace_7422348 : CollatzResearch.WordTrace tailWord_7422348 prefixEnd_7422348 3811232108937831263015249 := by
  unfold tailWord_7422348
  simp only [CollatzResearch.WordTrace]
  refine ⟨135357635857054153480921849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180476847809405537974562465 135357635857054153480921849)
  ·
    refine ⟨101518226892790615110691387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135357635857054153480921849 101518226892790615110691387)
    ·
      refine ⟨152277340339185922666037081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101518226892790615110691387 152277340339185922666037081)
      ·
        refine ⟨114208005254389441999527811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152277340339185922666037081 114208005254389441999527811)
        ·
          refine ⟨171312007881584162999291717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114208005254389441999527811 171312007881584162999291717)
          ·
            refine ⟨32121001477797030562367197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 171312007881584162999291717 32121001477797030562367197)
            ·
              refine ⟨12045375554173886460887699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32121001477797030562367197 12045375554173886460887699)
              ·
                refine ⟨18068063331260829691331549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12045375554173886460887699 18068063331260829691331549)
                ·
                  refine ⟨6775523749222811134249331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18068063331260829691331549 6775523749222811134249331)
                  ·
                    refine ⟨10163285623834216701373997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6775523749222811134249331 10163285623834216701373997)
                    ·
                      refine ⟨3811232108937831263015249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10163285623834216701373997 3811232108937831263015249)
                      ·
                        rfl

theorem cell23_7422348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 3, 1, 3, 1, 3].length) (baseStart_7422348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7422348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7422348 prefixEnd_7422348 := by exact prefixLift 7422348
  have htrace : WordTrace (prefixWord ++ tailWord_7422348) baseStart_7422348 baseEnd_7422348 := by
    simpa [prefixWord, tailWord_7422348, baseEnd_7422348] using wordTrace_append hprefix tailTrace_7422348
  have hstable : (prefixWord ++ tailWord_7422348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7422348).length < 2 ^ (prefixWord ++ tailWord_7422348).sum := by decide
  have hdescent : baseEnd_7422348 < baseStart_7422348 := by decide
  rcases family_descends (prefixWord ++ tailWord_7422348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7422368 : List Nat := [2, 1, 1, 4, 1, 5, 1, 2, 1, 5]
def baseStart_7422368 : Nat := 118140960795 + 7422368 * 2 ^ 59
def prefixEnd_7422368 : Nat := 4983230072969 + 3 ^ 40 * 7422368 * 2
def baseEnd_7422368 : Nat := 1270414126183640394921719

theorem tailTrace_7422368 : CollatzResearch.WordTrace tailWord_7422368 prefixEnd_7422368 1270414126183640394921719 := by
  unfold tailWord_7422368
  simp only [CollatzResearch.WordTrace]
  refine ⟨135358000587017925188785879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180477334116023900251714505 135358000587017925188785879)
  ·
    refine ⟨203037000880526887783178819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135358000587017925188785879 203037000880526887783178819)
    ·
      refine ⟨304555501320790331674768229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203037000880526887783178819 304555501320790331674768229)
      ·
        refine ⟨57104156497648187189019043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 304555501320790331674768229 57104156497648187189019043)
        ·
          refine ⟨85656234746472280783528565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57104156497648187189019043 85656234746472280783528565)
          ·
            refine ⟨8030272007481776323455803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 85656234746472280783528565 8030272007481776323455803)
            ·
              refine ⟨12045408011222664485183705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8030272007481776323455803 12045408011222664485183705)
              ·
                refine ⟨9034056008416998363887779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12045408011222664485183705 9034056008416998363887779)
                ·
                  refine ⟨13551084012625497545831669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9034056008416998363887779 13551084012625497545831669)
                  ·
                    refine ⟨1270414126183640394921719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13551084012625497545831669 1270414126183640394921719)
                    ·
                      rfl

theorem cell23_7422368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 1, 2, 1, 5].length) (baseStart_7422368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7422368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7422368 prefixEnd_7422368 := by exact prefixLift 7422368
  have htrace : WordTrace (prefixWord ++ tailWord_7422368) baseStart_7422368 baseEnd_7422368 := by
    simpa [prefixWord, tailWord_7422368, baseEnd_7422368] using wordTrace_append hprefix tailTrace_7422368
  have hstable : (prefixWord ++ tailWord_7422368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7422368).length < 2 ^ (prefixWord ++ tailWord_7422368).sum := by decide
  have hdescent : baseEnd_7422368 < baseStart_7422368 := by decide
  rcases family_descends (prefixWord ++ tailWord_7422368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7422371 : List Nat := [1, 1, 1, 4, 1, 5, 1, 1, 3, 1, 4]
def baseStart_7422371 : Nat := 118140960795 + 7422371 * 2 ^ 59
def prefixEnd_7422371 : Nat := 4983230072969 + 3 ^ 40 * 7422371 * 2
def baseEnd_7422371 : Nat := 3811243918992884673027643

theorem tailTrace_7422371 : CollatzResearch.WordTrace tailWord_7422371 prefixEnd_7422371 3811243918992884673027643 := by
  unfold tailWord_7422371
  simp only [CollatzResearch.WordTrace]
  refine ⟨270716110593024981889930967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180477407062016654593287311 270716110593024981889930967)
  ·
    refine ⟨406074165889537472834896451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270716110593024981889930967 406074165889537472834896451)
    ·
      refine ⟨609111248834306209252344677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 406074165889537472834896451 609111248834306209252344677)
      ·
        refine ⟨114208359156432414234814627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 609111248834306209252344677 114208359156432414234814627)
        ·
          refine ⟨171312538734648621352221941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114208359156432414234814627 171312538734648621352221941)
          ·
            refine ⟨16060550506373308251770807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 171312538734648621352221941 16060550506373308251770807)
            ·
              refine ⟨24090825759559962377656211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16060550506373308251770807 24090825759559962377656211)
              ·
                refine ⟨36136238639339943566484317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24090825759559962377656211 36136238639339943566484317)
                ·
                  refine ⟨13551089489752478837431619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36136238639339943566484317 13551089489752478837431619)
                  ·
                    refine ⟨20326634234628718256147429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13551089489752478837431619 20326634234628718256147429)
                    ·
                      refine ⟨3811243918992884673027643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20326634234628718256147429 3811243918992884673027643)
                      ·
                        rfl

theorem cell23_7422371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 1, 3, 1, 4].length) (baseStart_7422371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7422371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7422371 prefixEnd_7422371 := by exact prefixLift 7422371
  have htrace : WordTrace (prefixWord ++ tailWord_7422371) baseStart_7422371 baseEnd_7422371 := by
    simpa [prefixWord, tailWord_7422371, baseEnd_7422371] using wordTrace_append hprefix tailTrace_7422371
  have hstable : (prefixWord ++ tailWord_7422371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7422371).length < 2 ^ (prefixWord ++ tailWord_7422371).sum := by decide
  have hdescent : baseEnd_7422371 < baseStart_7422371 := by decide
  rcases family_descends (prefixWord ++ tailWord_7422371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7422375 : List Nat := [1, 1, 6, 1, 1, 3, 2, 1, 2, 3, 2]
def baseStart_7422375 : Nat := 118140960795 + 7422375 * 2 ^ 59
def prefixEnd_7422375 : Nat := 4983230072969 + 3 ^ 40 * 7422375 * 2
def baseEnd_7422375 : Nat := 3811245972915502657377625

theorem tailTrace_7422375 : CollatzResearch.WordTrace tailWord_7422375 prefixEnd_7422375 3811245972915502657377625 := by
  unfold tailWord_7422375
  simp only [CollatzResearch.WordTrace]
  refine ⟨270716256485010490573076579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180477504323340327048717719 270716256485010490573076579)
  ·
    refine ⟨406074384727515735859614869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270716256485010490573076579 406074384727515735859614869)
    ·
      refine ⟨19034736784102300118419447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 406074384727515735859614869 19034736784102300118419447)
      ·
        refine ⟨28552105176153450177629171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19034736784102300118419447 28552105176153450177629171)
        ·
          refine ⟨42828157764230175266443757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28552105176153450177629171 42828157764230175266443757)
          ·
            refine ⟨16060559161586315724916409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42828157764230175266443757 16060559161586315724916409)
            ·
              refine ⟨12045419371189736793687307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16060559161586315724916409 12045419371189736793687307)
              ·
                refine ⟨18068129056784605190530961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12045419371189736793687307 18068129056784605190530961)
                ·
                  refine ⟨13551096792588453892898221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18068129056784605190530961 13551096792588453892898221)
                  ·
                    refine ⟨5081661297220670209836833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13551096792588453892898221 5081661297220670209836833)
                    ·
                      refine ⟨3811245972915502657377625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5081661297220670209836833 3811245972915502657377625)
                      ·
                        rfl

theorem cell23_7422375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 2, 1, 2, 3, 2].length) (baseStart_7422375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7422375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7422375 prefixEnd_7422375 := by exact prefixLift 7422375
  have htrace : WordTrace (prefixWord ++ tailWord_7422375) baseStart_7422375 baseEnd_7422375 := by
    simpa [prefixWord, tailWord_7422375, baseEnd_7422375] using wordTrace_append hprefix tailTrace_7422375
  have hstable : (prefixWord ++ tailWord_7422375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7422375).length < 2 ^ (prefixWord ++ tailWord_7422375).sum := by decide
  have hdescent : baseEnd_7422375 < baseStart_7422375 := by decide
  rcases family_descends (prefixWord ++ tailWord_7422375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7422391 : List Nat := [1, 1, 3, 1, 3, 3, 3, 1, 1, 1, 5]
def baseStart_7422391 : Nat := 118140960795 + 7422391 * 2 ^ 59
def prefixEnd_7422391 : Nat := 4983230072969 + 3 ^ 40 * 7422391 * 2
def baseEnd_7422391 : Nat := 3811254188605974594777551

theorem tailTrace_7422391 : CollatzResearch.WordTrace tailWord_7422391 prefixEnd_7422391 3811254188605974594777551 := by
  unfold tailWord_7422391
  simp only [CollatzResearch.WordTrace]
  refine ⟨270716840052952525305659027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180477893368635016870439351 270716840052952525305659027)
  ·
    refine ⟨406075260079428787958488541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270716840052952525305659027 406075260079428787958488541)
    ·
      refine ⟨152278222529785795484433203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 406075260079428787958488541 152278222529785795484433203)
      ·
        refine ⟨228417333794678693226649805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152278222529785795484433203 228417333794678693226649805)
        ·
          refine ⟨85656500173004509959993677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 228417333794678693226649805 85656500173004509959993677)
          ·
            refine ⟨32121187564876691234997629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85656500173004509959993677 32121187564876691234997629)
            ·
              refine ⟨12045445336828759213124111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32121187564876691234997629 12045445336828759213124111)
              ·
                refine ⟨18068168005243138819686167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12045445336828759213124111 18068168005243138819686167)
                ·
                  refine ⟨27102252007864708229529251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18068168005243138819686167 27102252007864708229529251)
                  ·
                    refine ⟨40653378011797062344293877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27102252007864708229529251 40653378011797062344293877)
                    ·
                      refine ⟨3811254188605974594777551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40653378011797062344293877 3811254188605974594777551)
                      ·
                        rfl

theorem cell23_7422391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 3, 1, 1, 1, 5].length) (baseStart_7422391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7422391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7422391 prefixEnd_7422391 := by exact prefixLift 7422391
  have htrace : WordTrace (prefixWord ++ tailWord_7422391) baseStart_7422391 baseEnd_7422391 := by
    simpa [prefixWord, tailWord_7422391, baseEnd_7422391] using wordTrace_append hprefix tailTrace_7422391
  have hstable : (prefixWord ++ tailWord_7422391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7422391).length < 2 ^ (prefixWord ++ tailWord_7422391).sum := by decide
  have hdescent : baseEnd_7422391 < baseStart_7422391 := by decide
  rcases family_descends (prefixWord ++ tailWord_7422391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7422398 : List Nat := [4, 2, 1, 1, 1, 1, 3, 4, 2, 4]
def baseStart_7422398 : Nat := 118140960795 + 7422398 * 2 ^ 59
def prefixEnd_7422398 : Nat := 4983230072969 + 3 ^ 40 * 7422398 * 2
def baseEnd_7422398 : Nat := 1270419260990185355796673

theorem tailTrace_7422398 : CollatzResearch.WordTrace tailWord_7422398 prefixEnd_7422398 1270419260990185355796673 := by
  unfold tailWord_7422398
  simp only [CollatzResearch.WordTrace]
  refine ⟨33839636920490895687645481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180478063575951443667442565 33839636920490895687645481)
  ·
    refine ⟨25379727690368171765734111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33839636920490895687645481 25379727690368171765734111)
    ·
      refine ⟨38069591535552257648601167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25379727690368171765734111 38069591535552257648601167)
      ·
        refine ⟨57104387303328386472901751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38069591535552257648601167 57104387303328386472901751)
        ·
          refine ⟨85656580954992579709352627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57104387303328386472901751 85656580954992579709352627)
          ·
            refine ⟨128484871432488869564028941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85656580954992579709352627 128484871432488869564028941)
            ·
              refine ⟨48181826787183326086510853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128484871432488869564028941 48181826787183326086510853)
              ·
                refine ⟨9034092522596873641220785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48181826787183326086510853 9034092522596873641220785)
                ·
                  refine ⟨6775569391947655230915589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9034092522596873641220785 6775569391947655230915589)
                  ·
                    refine ⟨1270419260990185355796673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6775569391947655230915589 1270419260990185355796673)
                    ·
                      rfl

theorem cell23_7422398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 4, 2, 4].length) (baseStart_7422398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7422398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7422398 prefixEnd_7422398 := by exact prefixLift 7422398
  have htrace : WordTrace (prefixWord ++ tailWord_7422398) baseStart_7422398 baseEnd_7422398 := by
    simpa [prefixWord, tailWord_7422398, baseEnd_7422398] using wordTrace_append hprefix tailTrace_7422398
  have hstable : (prefixWord ++ tailWord_7422398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7422398).length < 2 ^ (prefixWord ++ tailWord_7422398).sum := by decide
  have hdescent : baseEnd_7422398 < baseStart_7422398 := by decide
  rcases family_descends (prefixWord ++ tailWord_7422398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7422422 : List Nat := [5, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2]
def baseStart_7422422 : Nat := 118140960795 + 7422422 * 2 ^ 59
def prefixEnd_7422422 : Nat := 4983230072969 + 3 ^ 40 * 7422422 * 2
def baseEnd_7422422 : Nat := 3811270106506263973489909

theorem tailTrace_7422422 : CollatzResearch.WordTrace tailWord_7422422 prefixEnd_7422422 3811270106506263973489909 := by
  unfold tailWord_7422422
  simp only [CollatzResearch.WordTrace]
  refine ⟨16919873169740013600002345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 180478647143893478400025013 16919873169740013600002345)
  ·
    refine ⟨12689904877305010200001759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16919873169740013600002345 12689904877305010200001759)
    ·
      refine ⟨19034857315957515300002639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12689904877305010200001759 19034857315957515300002639)
      ·
        refine ⟨28552285973936272950003959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19034857315957515300002639 28552285973936272950003959)
        ·
          refine ⟨42828428960904409425005939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28552285973936272950003959 42828428960904409425005939)
          ·
            refine ⟨64242643441356614137508909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42828428960904409425005939 64242643441356614137508909)
            ·
              refine ⟨24090991290508730301565841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64242643441356614137508909 24090991290508730301565841)
              ·
                refine ⟨18068243467881547726174381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24090991290508730301565841 18068243467881547726174381)
                ·
                  refine ⟨6775591300455580397315393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18068243467881547726174381 6775591300455580397315393)
                  ·
                    refine ⟨5081693475341685297986545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6775591300455580397315393 5081693475341685297986545)
                    ·
                      refine ⟨3811270106506263973489909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5081693475341685297986545 3811270106506263973489909)
                      ·
                        rfl

theorem cell23_7422422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2].length) (baseStart_7422422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7422422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7422422 prefixEnd_7422422 := by exact prefixLift 7422422
  have htrace : WordTrace (prefixWord ++ tailWord_7422422) baseStart_7422422 baseEnd_7422422 := by
    simpa [prefixWord, tailWord_7422422, baseEnd_7422422] using wordTrace_append hprefix tailTrace_7422422
  have hstable : (prefixWord ++ tailWord_7422422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7422422).length < 2 ^ (prefixWord ++ tailWord_7422422).sum := by decide
  have hdescent : baseEnd_7422422 < baseStart_7422422 := by decide
  rcases family_descends (prefixWord ++ tailWord_7422422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7422424 : List Nat := [2, 1, 2, 2, 2, 1, 1, 1, 4, 7]
def baseStart_7422424 : Nat := 118140960795 + 7422424 * 2 ^ 59
def prefixEnd_7422424 : Nat := 4983230072969 + 3 ^ 40 * 7422424 * 2
def baseEnd_7422424 : Nat := 1270423711155857655221633

theorem tailTrace_7422424 : CollatzResearch.WordTrace tailWord_7422424 prefixEnd_7422424 1270423711155857655221633 := by
  unfold tailWord_7422424
  simp only [CollatzResearch.WordTrace]
  refine ⟨135359021830916485970805163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180478695774555314627740217 135359021830916485970805163)
  ·
    refine ⟨203038532746374728956207745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135359021830916485970805163 203038532746374728956207745)
    ·
      refine ⟨152278899559781046717155809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203038532746374728956207745 152278899559781046717155809)
      ·
        refine ⟨114209174669835785037866857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152278899559781046717155809 114209174669835785037866857)
        ·
          refine ⟨85656881002376838778400143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114209174669835785037866857 85656881002376838778400143)
          ·
            refine ⟨128485321503565258167600215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85656881002376838778400143 128485321503565258167600215)
            ·
              refine ⟨192727982255347887251400323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128485321503565258167600215 192727982255347887251400323)
              ·
                refine ⟨289091973383021830877100485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 192727982255347887251400323 289091973383021830877100485)
                ·
                  refine ⟨54204745009316593289456341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 289091973383021830877100485 54204745009316593289456341)
                  ·
                    refine ⟨1270423711155857655221633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54204745009316593289456341 1270423711155857655221633)
                    ·
                      rfl

theorem cell23_7422424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 4, 7].length) (baseStart_7422424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7422424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7422424 prefixEnd_7422424 := by exact prefixLift 7422424
  have htrace : WordTrace (prefixWord ++ tailWord_7422424) baseStart_7422424 baseEnd_7422424 := by
    simpa [prefixWord, tailWord_7422424, baseEnd_7422424] using wordTrace_append hprefix tailTrace_7422424
  have hstable : (prefixWord ++ tailWord_7422424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7422424).length < 2 ^ (prefixWord ++ tailWord_7422424).sum := by decide
  have hdescent : baseEnd_7422424 < baseStart_7422424 := by decide
  rcases family_descends (prefixWord ++ tailWord_7422424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7422442 : List Nat := [3, 1, 3, 1, 3, 3, 2, 1, 1, 2, 3]
def baseStart_7422442 : Nat := 118140960795 + 7422442 * 2 ^ 59
def prefixEnd_7422442 : Nat := 4983230072969 + 3 ^ 40 * 7422442 * 2
def baseEnd_7422442 : Nat := 3811280376119353895239817

theorem tailTrace_7422442 : CollatzResearch.WordTrace tailWord_7422442 prefixEnd_7422442 3811280376119353895239817 := by
  unfold tailWord_7422442
  simp only [CollatzResearch.WordTrace]
  refine ⟨67679675043941940253941395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180479133450511840677177053 67679675043941940253941395)
  ·
    refine ⟨101519512565912910380912093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67679675043941940253941395 101519512565912910380912093)
    ·
      refine ⟨38069817212217341392842035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101519512565912910380912093 38069817212217341392842035)
      ·
        refine ⟨57104725818326012089263053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38069817212217341392842035 57104725818326012089263053)
        ·
          refine ⟨21414272181872254533473645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57104725818326012089263053 21414272181872254533473645)
          ·
            refine ⟨8030352068202095450052617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21414272181872254533473645 8030352068202095450052617)
            ·
              refine ⟨6022764051151571587539463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8030352068202095450052617 6022764051151571587539463)
              ·
                refine ⟨9034146076727357381309195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6022764051151571587539463 9034146076727357381309195)
                ·
                  refine ⟨13551219115091036071963793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9034146076727357381309195 13551219115091036071963793)
                  ·
                    refine ⟨10163414336318277053972845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13551219115091036071963793 10163414336318277053972845)
                    ·
                      refine ⟨3811280376119353895239817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10163414336318277053972845 3811280376119353895239817)
                      ·
                        rfl

theorem cell23_7422442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 2, 1, 1, 2, 3].length) (baseStart_7422442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7422442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7422442 prefixEnd_7422442 := by exact prefixLift 7422442
  have htrace : WordTrace (prefixWord ++ tailWord_7422442) baseStart_7422442 baseEnd_7422442 := by
    simpa [prefixWord, tailWord_7422442, baseEnd_7422442] using wordTrace_append hprefix tailTrace_7422442
  have hstable : (prefixWord ++ tailWord_7422442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7422442).length < 2 ^ (prefixWord ++ tailWord_7422442).sum := by decide
  have hdescent : baseEnd_7422442 < baseStart_7422442 := by decide
  rcases family_descends (prefixWord ++ tailWord_7422442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7422529 : List Nat := [1, 2, 5, 1, 1, 2, 4, 1, 2, 2, 2]
def baseStart_7422529 : Nat := 118140960795 + 7422529 * 2 ^ 59
def prefixEnd_7422529 : Nat := 4983230072969 + 3 ^ 40 * 7422529 * 2
def baseEnd_7422529 : Nat := 3811325048936295054851917

theorem tailTrace_7422529 : CollatzResearch.WordTrace tailWord_7422529 prefixEnd_7422529 3811325048936295054851917 := by
  unfold tailWord_7422529
  simp only [CollatzResearch.WordTrace]
  refine ⟨270721873326452574874182641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180481248884301716582788427 270721873326452574874182641)
  ·
    refine ⟨203041404994839431155636981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270721873326452574874182641 203041404994839431155636981)
    ·
      refine ⟨19035131718266196670840967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 203041404994839431155636981 19035131718266196670840967)
      ·
        refine ⟨28552697577399295006261451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19035131718266196670840967 28552697577399295006261451)
        ·
          refine ⟨42829046366098942509392177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28552697577399295006261451 42829046366098942509392177)
          ·
            refine ⟨32121784774574206882044133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42829046366098942509392177 32121784774574206882044133)
            ·
              refine ⟨6022834645232663790383275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32121784774574206882044133 6022834645232663790383275)
              ·
                refine ⟨9034251967848995685574913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6022834645232663790383275 9034251967848995685574913)
                ·
                  refine ⟨6775688975886746764181185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9034251967848995685574913 6775688975886746764181185)
                  ·
                    refine ⟨5081766731915060073135889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6775688975886746764181185 5081766731915060073135889)
                    ·
                      refine ⟨3811325048936295054851917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5081766731915060073135889 3811325048936295054851917)
                      ·
                        rfl

theorem cell23_7422529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 4, 1, 2, 2, 2].length) (baseStart_7422529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7422529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7422529 prefixEnd_7422529 := by exact prefixLift 7422529
  have htrace : WordTrace (prefixWord ++ tailWord_7422529) baseStart_7422529 baseEnd_7422529 := by
    simpa [prefixWord, tailWord_7422529, baseEnd_7422529] using wordTrace_append hprefix tailTrace_7422529
  have hstable : (prefixWord ++ tailWord_7422529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7422529).length < 2 ^ (prefixWord ++ tailWord_7422529).sum := by decide
  have hdescent : baseEnd_7422529 < baseStart_7422529 := by decide
  rcases family_descends (prefixWord ++ tailWord_7422529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7422548 : List Nat := [2, 4, 1, 1, 1, 3, 1, 3, 2, 5]
def baseStart_7422548 : Nat := 118140960795 + 7422548 * 2 ^ 59
def prefixEnd_7422548 : Nat := 4983230072969 + 3 ^ 40 * 7422548 * 2
def baseEnd_7422548 : Nat := 1270444935022910160171443

theorem tailTrace_7422548 : CollatzResearch.WordTrace tailWord_7422548 prefixEnd_7422548 1270444935022910160171443 := by
  unfold tailWord_7422548
  simp only [CollatzResearch.WordTrace]
  refine ⟨135361283156691870559562149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180481710875589160746082865 135361283156691870559562149)
  ·
    refine ⟨25380240591879725729917903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135361283156691870559562149 25380240591879725729917903)
    ·
      refine ⟨38070360887819588594876855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25380240591879725729917903 38070360887819588594876855)
      ·
        refine ⟨57105541331729382892315283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38070360887819588594876855 57105541331729382892315283)
        ·
          refine ⟨85658311997594074338472925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57105541331729382892315283 85658311997594074338472925)
          ·
            refine ⟨32121866999097777876927347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85658311997594074338472925 32121866999097777876927347)
            ·
              refine ⟨48182800498646666815391021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32121866999097777876927347 48182800498646666815391021)
              ·
                refine ⟨18068550186992500055771633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48182800498646666815391021 18068550186992500055771633)
                ·
                  refine ⟨13551412640244375041828725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18068550186992500055771633 13551412640244375041828725)
                  ·
                    refine ⟨1270444935022910160171443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13551412640244375041828725 1270444935022910160171443)
                    ·
                      rfl

theorem cell23_7422548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 3, 2, 5].length) (baseStart_7422548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7422548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7422548 prefixEnd_7422548 := by exact prefixLift 7422548
  have htrace : WordTrace (prefixWord ++ tailWord_7422548) baseStart_7422548 baseEnd_7422548 := by
    simpa [prefixWord, tailWord_7422548, baseEnd_7422548] using wordTrace_append hprefix tailTrace_7422548
  have hstable : (prefixWord ++ tailWord_7422548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7422548).length < 2 ^ (prefixWord ++ tailWord_7422548).sum := by decide
  have hdescent : baseEnd_7422548 < baseStart_7422548 := by decide
  rcases family_descends (prefixWord ++ tailWord_7422548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7422585 : List Nat := [1, 2, 1, 3, 3, 3, 1, 1, 2, 4, 2]
def baseStart_7422585 : Nat := 118140960795 + 7422585 * 2 ^ 59
def prefixEnd_7422585 : Nat := 4983230072969 + 3 ^ 40 * 7422585 * 2
def baseEnd_7422585 : Nat := 3811353803852946835751659

theorem tailTrace_7422585 : CollatzResearch.WordTrace tailWord_7422585 prefixEnd_7422585 3811353803852946835751659 := by
  unfold tailWord_7422585
  simp only [CollatzResearch.WordTrace]
  refine ⟨270723915814249696438221209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180482610542833130958814139 270723915814249696438221209)
  ·
    refine ⟨203042936860687272328665907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270723915814249696438221209 203042936860687272328665907)
    ·
      refine ⟨304564405291030908492998861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203042936860687272328665907 304564405291030908492998861)
      ·
        refine ⟨114211651984136590684874573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 304564405291030908492998861 114211651984136590684874573)
        ·
          refine ⟨42829369494051221506827965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114211651984136590684874573 42829369494051221506827965)
          ·
            refine ⟨16061013560269208065060487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42829369494051221506827965 16061013560269208065060487)
            ·
              refine ⟨24091520340403812097590731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16061013560269208065060487 24091520340403812097590731)
              ·
                refine ⟨36137280510605718146386097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24091520340403812097590731 36137280510605718146386097)
                ·
                  refine ⟨27102960382954288609789573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36137280510605718146386097 27102960382954288609789573)
                  ·
                    refine ⟨5081805071803929114335545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27102960382954288609789573 5081805071803929114335545)
                    ·
                      refine ⟨3811353803852946835751659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5081805071803929114335545 3811353803852946835751659)
                      ·
                        rfl

theorem cell23_7422585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 1, 2, 4, 2].length) (baseStart_7422585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7422585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7422585 prefixEnd_7422585 := by exact prefixLift 7422585
  have htrace : WordTrace (prefixWord ++ tailWord_7422585) baseStart_7422585 baseEnd_7422585 := by
    simpa [prefixWord, tailWord_7422585, baseEnd_7422585] using wordTrace_append hprefix tailTrace_7422585
  have hstable : (prefixWord ++ tailWord_7422585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7422585).length < 2 ^ (prefixWord ++ tailWord_7422585).sum := by decide
  have hdescent : baseEnd_7422585 < baseStart_7422585 := by decide
  rcases family_descends (prefixWord ++ tailWord_7422585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7422588 : List Nat := [2, 2, 2, 1, 1, 2, 2, 2, 4, 2, 3]
def baseStart_7422588 : Nat := 118140960795 + 7422588 * 2 ^ 59
def prefixEnd_7422588 : Nat := 4983230072969 + 3 ^ 40 * 7422588 * 2
def baseEnd_7422588 : Nat := 3811355344294910324014145

theorem tailTrace_7422588 : CollatzResearch.WordTrace tailWord_7422588 prefixEnd_7422588 3811355344294910324014145 := by
  unfold tailWord_7422588
  simp only [CollatzResearch.WordTrace]
  refine ⟨135362012616619413975290209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180482683488825885300386945 135362012616619413975290209)
  ·
    refine ⟨101521509462464560481467657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135362012616619413975290209 101521509462464560481467657)
    ·
      refine ⟨76141132096848420361100743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101521509462464560481467657 76141132096848420361100743)
      ·
        refine ⟨114211698145272630541651115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76141132096848420361100743 114211698145272630541651115)
        ·
          refine ⟨171317547217908945812476673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114211698145272630541651115 171317547217908945812476673)
          ·
            refine ⟨128488160413431709359357505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171317547217908945812476673 128488160413431709359357505)
            ·
              refine ⟨96366120310073782019518129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128488160413431709359357505 96366120310073782019518129)
              ·
                refine ⟨72274590232555336514638597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96366120310073782019518129 72274590232555336514638597)
                ·
                  refine ⟨13551485668604125596494737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72274590232555336514638597 13551485668604125596494737)
                  ·
                    refine ⟨10163614251453094197371053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13551485668604125596494737 10163614251453094197371053)
                    ·
                      refine ⟨3811355344294910324014145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10163614251453094197371053 3811355344294910324014145)
                      ·
                        rfl

theorem cell23_7422588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 2, 4, 2, 3].length) (baseStart_7422588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7422588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7422588 prefixEnd_7422588 := by exact prefixLift 7422588
  have htrace : WordTrace (prefixWord ++ tailWord_7422588) baseStart_7422588 baseEnd_7422588 := by
    simpa [prefixWord, tailWord_7422588, baseEnd_7422588] using wordTrace_append hprefix tailTrace_7422588
  have hstable : (prefixWord ++ tailWord_7422588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7422588).length < 2 ^ (prefixWord ++ tailWord_7422588).sum := by decide
  have hdescent : baseEnd_7422588 < baseStart_7422588 := by decide
  rcases family_descends (prefixWord ++ tailWord_7422588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7422602 : List Nat := [3, 1, 2, 3, 3, 2, 1, 1, 2, 1, 4]
def baseStart_7422602 : Nat := 118140960795 + 7422602 * 2 ^ 59
def prefixEnd_7422602 : Nat := 4983230072969 + 3 ^ 40 * 7422602 * 2
def baseEnd_7422602 : Nat := 3811362533024073269239081

theorem tailTrace_7422602 : CollatzResearch.WordTrace tailWord_7422602 prefixEnd_7422602 3811362533024073269239081 := by
  unfold tailWord_7422602
  simp only [CollatzResearch.WordTrace]
  refine ⟨67681133963797027085397515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180483023903458738894393373 67681133963797027085397515)
  ·
    refine ⟨101521700945695540628096273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67681133963797027085397515 101521700945695540628096273)
    ·
      refine ⟨76141275709271655471072205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101521700945695540628096273 76141275709271655471072205)
      ·
        refine ⟨28552978390976870801652077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76141275709271655471072205 28552978390976870801652077)
        ·
          refine ⟨10707366896616326550619529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28552978390976870801652077 10707366896616326550619529)
          ·
            refine ⟨8030525172462244912964647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10707366896616326550619529 8030525172462244912964647)
            ·
              refine ⟨12045787758693367369446971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8030525172462244912964647 12045787758693367369446971)
              ·
                refine ⟨18068681638040051054170457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12045787758693367369446971 18068681638040051054170457)
                ·
                  refine ⟨13551511228530038290627843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18068681638040051054170457 13551511228530038290627843)
                  ·
                    refine ⟨20327266842795057435941765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13551511228530038290627843 20327266842795057435941765)
                    ·
                      refine ⟨3811362533024073269239081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20327266842795057435941765 3811362533024073269239081)
                      ·
                        rfl

theorem cell23_7422602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 1, 1, 2, 1, 4].length) (baseStart_7422602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7422602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7422602 prefixEnd_7422602 := by exact prefixLift 7422602
  have htrace : WordTrace (prefixWord ++ tailWord_7422602) baseStart_7422602 baseEnd_7422602 := by
    simpa [prefixWord, tailWord_7422602, baseEnd_7422602] using wordTrace_append hprefix tailTrace_7422602
  have hstable : (prefixWord ++ tailWord_7422602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7422602).length < 2 ^ (prefixWord ++ tailWord_7422602).sum := by decide
  have hdescent : baseEnd_7422602 < baseStart_7422602 := by decide
  rcases family_descends (prefixWord ++ tailWord_7422602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7422655 : List Nat := [1, 1, 2, 2, 2, 5, 2, 2, 1, 5]
def baseStart_7422655 : Nat := 118140960795 + 7422655 * 2 ^ 59
def prefixEnd_7422655 : Nat := 4983230072969 + 3 ^ 40 * 7422655 * 2
def baseEnd_7422655 : Nat := 1270463249166253853958779

theorem tailTrace_7422655 : CollatzResearch.WordTrace tailWord_7422655 prefixEnd_7422655 1270463249166253853958779 := by
  unfold tailWord_7422655
  simp only [CollatzResearch.WordTrace]
  refine ⟨270726468923996098393269419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180484312615997398928846279 270726468923996098393269419)
  ·
    refine ⟨406089703385994147589904129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270726468923996098393269419 406089703385994147589904129)
    ·
      refine ⟨304567277539495610692428097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 406089703385994147589904129 304567277539495610692428097)
      ·
        refine ⟨228425458154621708019321073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 304567277539495610692428097 228425458154621708019321073)
        ·
          refine ⟨171319093615966281014490805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228425458154621708019321073 171319093615966281014490805)
          ·
            refine ⟨16061165026496838845108513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 171319093615966281014490805 16061165026496838845108513)
            ·
              refine ⟨12045873769872629133831385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16061165026496838845108513 12045873769872629133831385)
              ·
                refine ⟨9034405327404471850373539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12045873769872629133831385 9034405327404471850373539)
                ·
                  refine ⟨13551607991106707775560309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9034405327404471850373539 13551607991106707775560309)
                  ·
                    refine ⟨1270463249166253853958779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13551607991106707775560309 1270463249166253853958779)
                    ·
                      rfl

theorem cell23_7422655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 2, 2, 1, 5].length) (baseStart_7422655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7422655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7422655 prefixEnd_7422655 := by exact prefixLift 7422655
  have htrace : WordTrace (prefixWord ++ tailWord_7422655) baseStart_7422655 baseEnd_7422655 := by
    simpa [prefixWord, tailWord_7422655, baseEnd_7422655] using wordTrace_append hprefix tailTrace_7422655
  have hstable : (prefixWord ++ tailWord_7422655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7422655).length < 2 ^ (prefixWord ++ tailWord_7422655).sum := by decide
  have hdescent : baseEnd_7422655 < baseStart_7422655 := by decide
  rcases family_descends (prefixWord ++ tailWord_7422655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7422702 : List Nat := [4, 1, 2, 1, 1, 4, 1, 3, 2, 4]
def baseStart_7422702 : Nat := 118140960795 + 7422702 * 2 ^ 59
def prefixEnd_7422702 : Nat := 4983230072969 + 3 ^ 40 * 7422702 * 2
def baseEnd_7422702 : Nat := 1270471293696507625996207

theorem tailTrace_7422702 : CollatzResearch.WordTrace tailWord_7422702 prefixEnd_7422702 1270471293696507625996207 := by
  unfold tailWord_7422702
  simp only [CollatzResearch.WordTrace]
  refine ⟨33841022894353228177528795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180485455436550550280153573 33841022894353228177528795)
  ·
    refine ⟨50761534341529842266293193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33841022894353228177528795 50761534341529842266293193)
    ·
      refine ⟨38071150756147381699719895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50761534341529842266293193 38071150756147381699719895)
      ·
        refine ⟨57106726134221072549579843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38071150756147381699719895 57106726134221072549579843)
        ·
          refine ⟨85660089201331608824369765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57106726134221072549579843 85660089201331608824369765)
          ·
            refine ⟨16061266725249676654569331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85660089201331608824369765 16061266725249676654569331)
            ·
              refine ⟨24091900087874514981853997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16061266725249676654569331 24091900087874514981853997)
              ·
                refine ⟨9034462532952943118195249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24091900087874514981853997 9034462532952943118195249)
                ·
                  refine ⟨6775846899714707338646437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9034462532952943118195249 6775846899714707338646437)
                  ·
                    refine ⟨1270471293696507625996207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6775846899714707338646437 1270471293696507625996207)
                    ·
                      rfl

theorem cell23_7422702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 3, 2, 4].length) (baseStart_7422702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7422702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7422702 prefixEnd_7422702 := by exact prefixLift 7422702
  have htrace : WordTrace (prefixWord ++ tailWord_7422702) baseStart_7422702 baseEnd_7422702 := by
    simpa [prefixWord, tailWord_7422702, baseEnd_7422702] using wordTrace_append hprefix tailTrace_7422702
  have hstable : (prefixWord ++ tailWord_7422702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7422702).length < 2 ^ (prefixWord ++ tailWord_7422702).sum := by decide
  have hdescent : baseEnd_7422702 < baseStart_7422702 := by decide
  rcases family_descends (prefixWord ++ tailWord_7422702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7422722 : List Nat := [3, 4, 1, 1, 1, 3, 1, 2, 1, 2, 4]
def baseStart_7422722 : Nat := 118140960795 + 7422722 * 2 ^ 59
def prefixEnd_7422722 : Nat := 4983230072969 + 3 ^ 40 * 7422722 * 2
def baseEnd_7422722 : Nat := 3811424150702612799738529

theorem tailTrace_7422722 : CollatzResearch.WordTrace tailWord_7422722 prefixEnd_7422722 3811424150702612799738529 := by
  unfold tailWord_7422722
  simp only [CollatzResearch.WordTrace]
  refine ⟨67682228153688342208989605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180485941743168912557305613 67682228153688342208989605)
  ·
    refine ⟨12690417778816564164185551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 67682228153688342208989605 12690417778816564164185551)
    ·
      refine ⟨19035626668224846246278327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12690417778816564164185551 19035626668224846246278327)
      ·
        refine ⟨28553440002337269369417491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19035626668224846246278327 28553440002337269369417491)
        ·
          refine ⟨42830160003505904054126237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28553440002337269369417491 42830160003505904054126237)
          ·
            refine ⟨16061310001314714020297339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42830160003505904054126237 16061310001314714020297339)
            ·
              refine ⟨24091965001972071030446009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16061310001314714020297339 24091965001972071030446009)
              ·
                refine ⟨18068973751479053272834507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24091965001972071030446009 18068973751479053272834507)
                ·
                  refine ⟨27103460627218579909251761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18068973751479053272834507 27103460627218579909251761)
                  ·
                    refine ⟨20327595470413934931938821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27103460627218579909251761 20327595470413934931938821)
                    ·
                      refine ⟨3811424150702612799738529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20327595470413934931938821 3811424150702612799738529)
                      ·
                        rfl

theorem cell23_7422722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_7422722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7422722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7422722 prefixEnd_7422722 := by exact prefixLift 7422722
  have htrace : WordTrace (prefixWord ++ tailWord_7422722) baseStart_7422722 baseEnd_7422722 := by
    simpa [prefixWord, tailWord_7422722, baseEnd_7422722] using wordTrace_append hprefix tailTrace_7422722
  have hstable : (prefixWord ++ tailWord_7422722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7422722).length < 2 ^ (prefixWord ++ tailWord_7422722).sum := by decide
  have hdescent : baseEnd_7422722 < baseStart_7422722 := by decide
  rcases family_descends (prefixWord ++ tailWord_7422722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7422725 : List Nat := [1, 3, 1, 1, 2, 1, 1, 3, 6, 1, 3]
def baseStart_7422725 : Nat := 118140960795 + 7422725 * 2 ^ 59
def prefixEnd_7422725 : Nat := 4983230072969 + 3 ^ 40 * 7422725 * 2
def baseEnd_7422725 : Nat := 3811425691144576288001015

theorem tailTrace_7422725 : CollatzResearch.WordTrace tailWord_7422725 prefixEnd_7422725 3811425691144576288001015 := by
  unfold tailWord_7422725
  simp only [CollatzResearch.WordTrace]
  refine ⟨270729022033742500348317629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180486014689161666898878419 270729022033742500348317629)
  ·
    refine ⟨101523383262653437630619111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 270729022033742500348317629 101523383262653437630619111)
    ·
      refine ⟨152285074893980156445928667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101523383262653437630619111 152285074893980156445928667)
      ·
        refine ⟨228427612340970234668893001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152285074893980156445928667 228427612340970234668893001)
        ·
          refine ⟨171320709255727676001669751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228427612340970234668893001 171320709255727676001669751)
          ·
            refine ⟨256981063883591514002504627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171320709255727676001669751 256981063883591514002504627)
            ·
              refine ⟨385471595825387271003756941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 256981063883591514002504627 385471595825387271003756941)
              ·
                refine ⟨144551848434520226626408853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 385471595825387271003756941 144551848434520226626408853)
                ·
                  refine ⟨6775867895368135623112915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 144551848434520226626408853 6775867895368135623112915)
                  ·
                    refine ⟨10163801843052203434669373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6775867895368135623112915 10163801843052203434669373)
                    ·
                      refine ⟨3811425691144576288001015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10163801843052203434669373 3811425691144576288001015)
                      ·
                        rfl

theorem cell23_7422725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 6, 1, 3].length) (baseStart_7422725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7422725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7422725 prefixEnd_7422725 := by exact prefixLift 7422725
  have htrace : WordTrace (prefixWord ++ tailWord_7422725) baseStart_7422725 baseEnd_7422725 := by
    simpa [prefixWord, tailWord_7422725, baseEnd_7422725] using wordTrace_append hprefix tailTrace_7422725
  have hstable : (prefixWord ++ tailWord_7422725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7422725).length < 2 ^ (prefixWord ++ tailWord_7422725).sum := by decide
  have hdescent : baseEnd_7422725 < baseStart_7422725 := by decide
  rcases family_descends (prefixWord ++ tailWord_7422725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7422749 : List Nat := [1, 4, 2, 4, 2, 1, 1, 8]
def baseStart_7422749 : Nat := 118140960795 + 7422749 * 2 ^ 59
def prefixEnd_7422749 : Nat := 4983230072969 + 3 ^ 40 * 7422749 * 2
def baseEnd_7422749 : Nat := 141164370914084599781515

theorem tailTrace_7422749 : CollatzResearch.WordTrace tailWord_7422749 prefixEnd_7422749 141164370914084599781515 := by
  unfold tailWord_7422749
  simp only [CollatzResearch.WordTrace]
  refine ⟨270729897385655552447191301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180486598257103701631460867 270729897385655552447191301)
  ·
    refine ⟨50761855759810416083848369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 270729897385655552447191301 50761855759810416083848369)
    ·
      refine ⟨38071391819857812062886277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50761855759810416083848369 38071391819857812062886277)
      ·
        refine ⟨7138385966223339761791177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38071391819857812062886277 7138385966223339761791177)
        ·
          refine ⟨5353789474667504821343383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7138385966223339761791177 5353789474667504821343383)
          ·
            refine ⟨8030684212001257232015075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5353789474667504821343383 8030684212001257232015075)
            ·
              refine ⟨12046026318001885848022613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8030684212001257232015075 12046026318001885848022613)
              ·
                refine ⟨141164370914084599781515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12046026318001885848022613 141164370914084599781515)
                ·
                  rfl

theorem cell23_7422749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 1, 8].length) (baseStart_7422749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7422749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7422749 prefixEnd_7422749 := by exact prefixLift 7422749
  have htrace : WordTrace (prefixWord ++ tailWord_7422749) baseStart_7422749 baseEnd_7422749 := by
    simpa [prefixWord, tailWord_7422749, baseEnd_7422749] using wordTrace_append hprefix tailTrace_7422749
  have hstable : (prefixWord ++ tailWord_7422749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7422749).length < 2 ^ (prefixWord ++ tailWord_7422749).sum := by decide
  have hdescent : baseEnd_7422749 < baseStart_7422749 := by decide
  rcases family_descends (prefixWord ++ tailWord_7422749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7422752 : List Nat := [2, 1, 1, 5, 1, 2, 1, 2, 3, 3, 2]
def baseStart_7422752 : Nat := 118140960795 + 7422752 * 2 ^ 59
def prefixEnd_7422752 : Nat := 4983230072969 + 3 ^ 40 * 7422752 * 2
def baseEnd_7422752 : Nat := 3811439555122247682363391

theorem tailTrace_7422752 : CollatzResearch.WordTrace tailWord_7422752 prefixEnd_7422752 3811439555122247682363391 := by
  unfold tailWord_7422752
  simp only [CollatzResearch.WordTrace]
  refine ⟨135365003402322341979775255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180486671203096455973033673 135365003402322341979775255)
  ·
    refine ⟨203047505103483512969662883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135365003402322341979775255 203047505103483512969662883)
    ·
      refine ⟨304571257655225269454494325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203047505103483512969662883 304571257655225269454494325)
      ·
        refine ⟨28553555405177369011358843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 304571257655225269454494325 28553555405177369011358843)
        ·
          refine ⟨42830333107766053517038265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28553555405177369011358843 42830333107766053517038265)
          ·
            refine ⟨32122749830824540137778699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42830333107766053517038265 32122749830824540137778699)
            ·
              refine ⟨48184124746236810206668049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32122749830824540137778699 48184124746236810206668049)
              ·
                refine ⟨36138093559677607655001037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48184124746236810206668049 36138093559677607655001037)
                ·
                  refine ⟨13551785084879102870625389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36138093559677607655001037 13551785084879102870625389)
                  ·
                    refine ⟨5081919406829663576484521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13551785084879102870625389 5081919406829663576484521)
                    ·
                      refine ⟨3811439555122247682363391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5081919406829663576484521 3811439555122247682363391)
                      ·
                        rfl

theorem cell23_7422752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 2, 3, 3, 2].length) (baseStart_7422752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7422752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7422752 prefixEnd_7422752 := by exact prefixLift 7422752
  have htrace : WordTrace (prefixWord ++ tailWord_7422752) baseStart_7422752 baseEnd_7422752 := by
    simpa [prefixWord, tailWord_7422752, baseEnd_7422752] using wordTrace_append hprefix tailTrace_7422752
  have hstable : (prefixWord ++ tailWord_7422752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7422752).length < 2 ^ (prefixWord ++ tailWord_7422752).sum := by decide
  have hdescent : baseEnd_7422752 < baseStart_7422752 := by decide
  rcases family_descends (prefixWord ++ tailWord_7422752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7422768 : List Nat := [2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 5]
def baseStart_7422768 : Nat := 118140960795 + 7422768 * 2 ^ 59
def prefixEnd_7422768 : Nat := 4983230072969 + 3 ^ 40 * 7422768 * 2
def baseEnd_7422768 : Nat := 3811447770812719619763317

theorem tailTrace_7422768 : CollatzResearch.WordTrace tailWord_7422768 prefixEnd_7422768 3811447770812719619763317 := by
  unfold tailWord_7422768
  simp only [CollatzResearch.WordTrace]
  refine ⟨135365295186293359346066479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180487060248391145794755305 135365295186293359346066479)
  ·
    refine ⟨203047942779440039019099719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135365295186293359346066479 203047942779440039019099719)
    ·
      refine ⟨304571914169160058528649579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203047942779440039019099719 304571914169160058528649579)
      ·
        refine ⟨456857871253740087792974369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304571914169160058528649579 456857871253740087792974369)
        ·
          refine ⟨342643403440305065844730777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 456857871253740087792974369 342643403440305065844730777)
          ·
            refine ⟨256982552580228799383548083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 342643403440305065844730777 256982552580228799383548083)
            ·
              refine ⟨385473828870343199075322125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 256982552580228799383548083 385473828870343199075322125)
              ·
                refine ⟨144552685826378699653245797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 385473828870343199075322125 144552685826378699653245797)
                ·
                  refine ⟨27103628592446006184983587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 144552685826378699653245797 27103628592446006184983587)
                  ·
                    refine ⟨40655442888669009277475381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27103628592446006184983587 40655442888669009277475381)
                    ·
                      refine ⟨3811447770812719619763317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40655442888669009277475381 3811447770812719619763317)
                      ·
                        rfl

theorem cell23_7422768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 5].length) (baseStart_7422768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7422768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7422768 prefixEnd_7422768 := by exact prefixLift 7422768
  have htrace : WordTrace (prefixWord ++ tailWord_7422768) baseStart_7422768 baseEnd_7422768 := by
    simpa [prefixWord, tailWord_7422768, baseEnd_7422768] using wordTrace_append hprefix tailTrace_7422768
  have hstable : (prefixWord ++ tailWord_7422768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7422768).length < 2 ^ (prefixWord ++ tailWord_7422768).sum := by decide
  have hdescent : baseEnd_7422768 < baseStart_7422768 := by decide
  rcases family_descends (prefixWord ++ tailWord_7422768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7422805 : List Nat := [1, 3, 2, 2, 2, 1, 4, 1, 7]
def baseStart_7422805 : Nat := 118140960795 + 7422805 * 2 ^ 59
def prefixEnd_7422805 : Nat := 4983230072969 + 3 ^ 40 * 7422805 * 2
def baseEnd_7422805 : Nat := 423496307732992886111183

theorem tailTrace_7422805 : CollatzResearch.WordTrace tailWord_7422805 prefixEnd_7422805 423496307732992886111183 := by
  unfold tailWord_7422805
  simp only [CollatzResearch.WordTrace]
  refine ⟨270731939873452674011229869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180487959915635116007486579 270731939873452674011229869)
  ·
    refine ⟨101524477452544752754211201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 270731939873452674011229869 101524477452544752754211201)
    ·
      refine ⟨76143358089408564565658401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101524477452544752754211201 76143358089408564565658401)
      ·
        refine ⟨57107518567056423424243801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76143358089408564565658401 57107518567056423424243801)
        ·
          refine ⟨42830638925292317568182851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57107518567056423424243801 42830638925292317568182851)
          ·
            refine ⟨64245958387938476352274277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42830638925292317568182851 64245958387938476352274277)
            ·
              refine ⟨12046117197738464316051427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64245958387938476352274277 12046117197738464316051427)
              ·
                refine ⟨18069175796607696474077141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12046117197738464316051427 18069175796607696474077141)
                ·
                  refine ⟨423496307732992886111183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18069175796607696474077141 423496307732992886111183)
                  ·
                    rfl

theorem cell23_7422805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 4, 1, 7].length) (baseStart_7422805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7422805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7422805 prefixEnd_7422805 := by exact prefixLift 7422805
  have htrace : WordTrace (prefixWord ++ tailWord_7422805) baseStart_7422805 baseEnd_7422805 := by
    simpa [prefixWord, tailWord_7422805, baseEnd_7422805] using wordTrace_append hprefix tailTrace_7422805
  have hstable : (prefixWord ++ tailWord_7422805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7422805).length < 2 ^ (prefixWord ++ tailWord_7422805).sum := by decide
  have hdescent : baseEnd_7422805 < baseStart_7422805 := by decide
  rcases family_descends (prefixWord ++ tailWord_7422805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7422812 : List Nat := [2, 2, 4, 2, 1, 1, 2, 1, 2, 2, 4]
def baseStart_7422812 : Nat := 118140960795 + 7422812 * 2 ^ 59
def prefixEnd_7422812 : Nat := 4983230072969 + 3 ^ 40 * 7422812 * 2
def baseEnd_7422812 : Nat := 3811470363961517447613115

theorem tailTrace_7422812 : CollatzResearch.WordTrace tailWord_7422812 prefixEnd_7422812 3811470363961517447613115 := by
  unfold tailWord_7422812
  simp only [CollatzResearch.WordTrace]
  refine ⟨135366097592213657103367345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180488130122951542804489793 135366097592213657103367345)
  ·
    refine ⟨101524573194160242827525509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135366097592213657103367345 101524573194160242827525509)
    ·
      refine ⟨19035857473905045530161033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101524573194160242827525509 19035857473905045530161033)
      ·
        refine ⟨14276893105428784147620775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19035857473905045530161033 14276893105428784147620775)
        ·
          refine ⟨21415339658143176221431163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14276893105428784147620775 21415339658143176221431163)
          ·
            refine ⟨32123009487214764332146745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21415339658143176221431163 32123009487214764332146745)
            ·
              refine ⟨24092257115411073249110059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32123009487214764332146745 24092257115411073249110059)
              ·
                refine ⟨36138385673116609873665089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24092257115411073249110059 36138385673116609873665089)
                ·
                  refine ⟨27103789254837457405248817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36138385673116609873665089 27103789254837457405248817)
                  ·
                    refine ⟨20327841941128093053936613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27103789254837457405248817 20327841941128093053936613)
                    ·
                      refine ⟨3811470363961517447613115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20327841941128093053936613 3811470363961517447613115)
                      ·
                        rfl

theorem cell23_7422812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_7422812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7422812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7422812 prefixEnd_7422812 := by exact prefixLift 7422812
  have htrace : WordTrace (prefixWord ++ tailWord_7422812) baseStart_7422812 baseEnd_7422812 := by
    simpa [prefixWord, tailWord_7422812, baseEnd_7422812] using wordTrace_append hprefix tailTrace_7422812
  have hstable : (prefixWord ++ tailWord_7422812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7422812).length < 2 ^ (prefixWord ++ tailWord_7422812).sum := by decide
  have hdescent : baseEnd_7422812 < baseStart_7422812 := by decide
  rcases family_descends (prefixWord ++ tailWord_7422812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7422815 : List Nat := [1, 1, 2, 3, 1, 3, 1, 3, 2, 3, 3]
def baseStart_7422815 : Nat := 118140960795 + 7422815 * 2 ^ 59
def prefixEnd_7422815 : Nat := 4983230072969 + 3 ^ 40 * 7422815 * 2
def baseEnd_7422815 : Nat := 3811471904403480935875601

theorem tailTrace_7422815 : CollatzResearch.WordTrace tailWord_7422815 prefixEnd_7422815 3811471904403480935875601 := by
  unfold tailWord_7422815
  simp only [CollatzResearch.WordTrace]
  refine ⟨270732304603416445719093899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180488203068944297146062599 270732304603416445719093899)
  ·
    refine ⟨406098456905124668578640849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270732304603416445719093899 406098456905124668578640849)
    ·
      refine ⟨304573842678843501433980637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 406098456905124668578640849 304573842678843501433980637)
      ·
        refine ⟨114215191004566313037742739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 304573842678843501433980637 114215191004566313037742739)
        ·
          refine ⟨171322786506849469556614109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114215191004566313037742739 171322786506849469556614109)
          ·
            refine ⟨64246044940068551083730291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 171322786506849469556614109 64246044940068551083730291)
            ·
              refine ⟨96369067410102826625595437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64246044940068551083730291 96369067410102826625595437)
              ·
                refine ⟨36138400278788559984598289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96369067410102826625595437 36138400278788559984598289)
                ·
                  refine ⟨27103800209091419988448717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36138400278788559984598289 27103800209091419988448717)
                  ·
                    refine ⟨10163925078409282495668269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27103800209091419988448717 10163925078409282495668269)
                    ·
                      refine ⟨3811471904403480935875601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10163925078409282495668269 3811471904403480935875601)
                      ·
                        rfl

theorem cell23_7422815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 3, 2, 3, 3].length) (baseStart_7422815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7422815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7422815 prefixEnd_7422815 := by exact prefixLift 7422815
  have htrace : WordTrace (prefixWord ++ tailWord_7422815) baseStart_7422815 baseEnd_7422815 := by
    simpa [prefixWord, tailWord_7422815, baseEnd_7422815] using wordTrace_append hprefix tailTrace_7422815
  have hstable : (prefixWord ++ tailWord_7422815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7422815).length < 2 ^ (prefixWord ++ tailWord_7422815).sum := by decide
  have hdescent : baseEnd_7422815 < baseStart_7422815 := by decide
  rcases family_descends (prefixWord ++ tailWord_7422815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7422816 : List Nat := [2, 1, 1, 3, 3, 1, 5, 1, 2, 2, 2]
def baseStart_7422816 : Nat := 118140960795 + 7422816 * 2 ^ 59
def prefixEnd_7422816 : Nat := 4983230072969 + 3 ^ 40 * 7422816 * 2
def baseEnd_7422816 : Nat := 3811472417884135431963097

theorem tailTrace_7422816 : CollatzResearch.WordTrace tailWord_7422816 prefixEnd_7422816 3811472417884135431963097 := by
  unfold tailWord_7422816
  simp only [CollatzResearch.WordTrace]
  refine ⟨135366170538206411444940151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180488227384275215259920201 135366170538206411444940151)
  ·
    refine ⟨203049255807309617167410227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135366170538206411444940151 203049255807309617167410227)
    ·
      refine ⟨304573883710964425751115341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203049255807309617167410227 304573883710964425751115341)
      ·
        refine ⟨114215206391611659656668253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 304573883710964425751115341 114215206391611659656668253)
        ·
          refine ⟨42830702396854372371250595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114215206391611659656668253 42830702396854372371250595)
          ·
            refine ⟨64246053595281558556875893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42830702396854372371250595 64246053595281558556875893)
            ·
              refine ⟨6023067524557646114707115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64246053595281558556875893 6023067524557646114707115)
              ·
                refine ⟨9034601286836469172060673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6023067524557646114707115 9034601286836469172060673)
                ·
                  refine ⟨6775950965127351879045505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9034601286836469172060673 6775950965127351879045505)
                  ·
                    refine ⟨5081963223845513909284129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6775950965127351879045505 5081963223845513909284129)
                    ·
                      refine ⟨3811472417884135431963097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5081963223845513909284129 3811472417884135431963097)
                      ·
                        rfl

theorem cell23_7422816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 5, 1, 2, 2, 2].length) (baseStart_7422816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7422816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7422816 prefixEnd_7422816 := by exact prefixLift 7422816
  have htrace : WordTrace (prefixWord ++ tailWord_7422816) baseStart_7422816 baseEnd_7422816 := by
    simpa [prefixWord, tailWord_7422816, baseEnd_7422816] using wordTrace_append hprefix tailTrace_7422816
  have hstable : (prefixWord ++ tailWord_7422816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7422816).length < 2 ^ (prefixWord ++ tailWord_7422816).sum := by decide
  have hdescent : baseEnd_7422816 < baseStart_7422816 := by decide
  rcases family_descends (prefixWord ++ tailWord_7422816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7422912 : List Nat := [2, 1, 1, 2, 3, 4, 2, 2, 6]
def baseStart_7422912 : Nat := 118140960795 + 7422912 * 2 ^ 59
def prefixEnd_7422912 : Nat := 4983230072969 + 3 ^ 40 * 7422912 * 2
def baseEnd_7422912 : Nat := 423502412447440784040295

theorem tailTrace_7422912 : CollatzResearch.WordTrace tailWord_7422912 prefixEnd_7422912 423502412447440784040295 := by
  unfold tailWord_7422912
  simp only [CollatzResearch.WordTrace]
  refine ⟨135367921242032515642687495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180490561656043354190249993 135367921242032515642687495)
  ·
    refine ⟨203051881863048773464031243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135367921242032515642687495 203051881863048773464031243)
    ·
      refine ⟨304577822794573160196046865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203051881863048773464031243 304577822794573160196046865)
      ·
        refine ⟨228433367095929870147035149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 304577822794573160196046865 228433367095929870147035149)
        ·
          refine ⟨85662512660973701305138181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 228433367095929870147035149 85662512660973701305138181)
          ·
            refine ⟨16061721123932568994713409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85662512660973701305138181 16061721123932568994713409)
            ·
              refine ⟨12046290842949426746035057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16061721123932568994713409 12046290842949426746035057)
              ·
                refine ⟨9034718132212070059526293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12046290842949426746035057 9034718132212070059526293)
                ·
                  refine ⟨423502412447440784040295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9034718132212070059526293 423502412447440784040295)
                  ·
                    rfl

theorem cell23_7422912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 2, 2, 6].length) (baseStart_7422912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7422912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7422912 prefixEnd_7422912 := by exact prefixLift 7422912
  have htrace : WordTrace (prefixWord ++ tailWord_7422912) baseStart_7422912 baseEnd_7422912 := by
    simpa [prefixWord, tailWord_7422912, baseEnd_7422912] using wordTrace_append hprefix tailTrace_7422912
  have hstable : (prefixWord ++ tailWord_7422912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7422912).length < 2 ^ (prefixWord ++ tailWord_7422912).sum := by decide
  have hdescent : baseEnd_7422912 < baseStart_7422912 := by decide
  rcases family_descends (prefixWord ++ tailWord_7422912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7422959 : List Nat := [1, 1, 2, 1, 4, 3, 4, 1, 1, 5]
def baseStart_7422959 : Nat := 118140960795 + 7422959 * 2 ^ 59
def prefixEnd_7422959 : Nat := 4983230072969 + 3 ^ 40 * 7422959 * 2
def baseEnd_7422959 : Nat := 1270515281872576124158313

theorem tailTrace_7422959 : CollatzResearch.WordTrace tailWord_7422959 prefixEnd_7422959 1270515281872576124158313 := by
  unfold tailWord_7422959
  simp only [CollatzResearch.WordTrace]
  refine ⟨270737556714894758312335931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180491704476596505541557287 270737556714894758312335931)
  ·
    refine ⟨406106335072342137468503897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270737556714894758312335931 406106335072342137468503897)
    ·
      refine ⟨304579751304256603101377923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 406106335072342137468503897 304579751304256603101377923)
      ·
        refine ⟨456869626956384904652066885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304579751304256603101377923 456869626956384904652066885)
        ·
          refine ⟨85663055054322169622262541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 456869626956384904652066885 85663055054322169622262541)
          ·
            refine ⟨32123645645370813608348453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85663055054322169622262541 32123645645370813608348453)
            ·
              refine ⟨6023183558507027551565335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32123645645370813608348453 6023183558507027551565335)
              ·
                refine ⟨9034775337760541327348003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6023183558507027551565335 9034775337760541327348003)
                ·
                  refine ⟨13552163006640811991022005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9034775337760541327348003 13552163006640811991022005)
                  ·
                    refine ⟨1270515281872576124158313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13552163006640811991022005 1270515281872576124158313)
                    ·
                      rfl

theorem cell23_7422959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 4, 1, 1, 5].length) (baseStart_7422959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7422959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7422959 prefixEnd_7422959 := by exact prefixLift 7422959
  have htrace : WordTrace (prefixWord ++ tailWord_7422959) baseStart_7422959 baseEnd_7422959 := by
    simpa [prefixWord, tailWord_7422959, baseEnd_7422959] using wordTrace_append hprefix tailTrace_7422959
  have hstable : (prefixWord ++ tailWord_7422959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7422959).length < 2 ^ (prefixWord ++ tailWord_7422959).sum := by decide
  have hdescent : baseEnd_7422959 < baseStart_7422959 := by decide
  rcases family_descends (prefixWord ++ tailWord_7422959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7422975 : List Nat := [1, 1, 2, 2, 1, 2, 1, 1, 2, 6, 4]
def baseStart_7422975 : Nat := 118140960795 + 7422975 * 2 ^ 59
def prefixEnd_7422975 : Nat := 4983230072969 + 3 ^ 40 * 7422975 * 2
def baseEnd_7422975 : Nat := 3811554061308200309874865

theorem tailTrace_7422975 : CollatzResearch.WordTrace tailWord_7422975 prefixEnd_7422975 3811554061308200309874865 := by
  unfold tailWord_7422975
  simp only [CollatzResearch.WordTrace]
  refine ⟨270738140282836793044918379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180492093521891195363278919 270738140282836793044918379)
  ·
    refine ⟨406107210424255189567377569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270738140282836793044918379 406107210424255189567377569)
    ·
      refine ⟨304580407818191392175533177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 406107210424255189567377569 304580407818191392175533177)
      ·
        refine ⟨228435305863643544131649883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 304580407818191392175533177 228435305863643544131649883)
        ·
          refine ⟨342652958795465316197474825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228435305863643544131649883 342652958795465316197474825)
          ·
            refine ⟨256989719096598987148106119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 342652958795465316197474825 256989719096598987148106119)
            ·
              refine ⟨385484578644898480722159179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 256989719096598987148106119 385484578644898480722159179)
              ·
                refine ⟨578226867967347721083238769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 385484578644898480722159179 578226867967347721083238769)
                ·
                  refine ⟨433670150975510790812429077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 578226867967347721083238769 433670150975510790812429077)
                  ·
                    refine ⟨20328288326977068319332613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 433670150975510790812429077 20328288326977068319332613)
                    ·
                      refine ⟨3811554061308200309874865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20328288326977068319332613 3811554061308200309874865)
                      ·
                        rfl

theorem cell23_7422975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 6, 4].length) (baseStart_7422975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7422975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7422975 prefixEnd_7422975 := by exact prefixLift 7422975
  have htrace : WordTrace (prefixWord ++ tailWord_7422975) baseStart_7422975 baseEnd_7422975 := by
    simpa [prefixWord, tailWord_7422975, baseEnd_7422975] using wordTrace_append hprefix tailTrace_7422975
  have hstable : (prefixWord ++ tailWord_7422975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7422975).length < 2 ^ (prefixWord ++ tailWord_7422975).sum := by decide
  have hdescent : baseEnd_7422975 < baseStart_7422975 := by decide
  rcases family_descends (prefixWord ++ tailWord_7422975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7423030 : List Nat := [5, 1, 2, 1, 1, 4, 1, 1, 3, 2, 2]
def baseStart_7423030 : Nat := 118140960795 + 7423030 * 2 ^ 59
def prefixEnd_7423030 : Nat := 4983230072969 + 3 ^ 40 * 7423030 * 2
def baseEnd_7423030 : Nat := 3811582302744197594687113

theorem tailTrace_7423030 : CollatzResearch.WordTrace tailWord_7423030 prefixEnd_7423030 3811582302744197594687113 := by
  unfold tailWord_7423030
  simp only [CollatzResearch.WordTrace]
  refine ⟨16921259143602346089885659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 180493430865091691625447029 16921259143602346089885659)
  ·
    refine ⟨25381888715403519134828489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16921259143602346089885659 25381888715403519134828489)
    ·
      refine ⟨19036416536552639351121367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25381888715403519134828489 19036416536552639351121367)
      ·
        refine ⟨28554624804828959026682051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19036416536552639351121367 28554624804828959026682051)
        ·
          refine ⟨42831937207243438540023077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28554624804828959026682051 42831937207243438540023077)
          ·
            refine ⟨8030988226358144726254327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42831937207243438540023077 8030988226358144726254327)
            ·
              refine ⟨12046482339537217089381491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8030988226358144726254327 12046482339537217089381491)
              ·
                refine ⟨18069723509305825634072237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12046482339537217089381491 18069723509305825634072237)
                ·
                  refine ⟨6776146315989684612777089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18069723509305825634072237 6776146315989684612777089)
                  ·
                    refine ⟨5082109736992263459582817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6776146315989684612777089 5082109736992263459582817)
                    ·
                      refine ⟨3811582302744197594687113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5082109736992263459582817 3811582302744197594687113)
                      ·
                        rfl

theorem cell23_7423030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 1, 1, 3, 2, 2].length) (baseStart_7423030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7423030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7423030 prefixEnd_7423030 := by exact prefixLift 7423030
  have htrace : WordTrace (prefixWord ++ tailWord_7423030) baseStart_7423030 baseEnd_7423030 := by
    simpa [prefixWord, tailWord_7423030, baseEnd_7423030] using wordTrace_append hprefix tailTrace_7423030
  have hstable : (prefixWord ++ tailWord_7423030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7423030).length < 2 ^ (prefixWord ++ tailWord_7423030).sum := by decide
  have hdescent : baseEnd_7423030 < baseStart_7423030 := by decide
  rcases family_descends (prefixWord ++ tailWord_7423030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7423039 : List Nat := [1, 1, 2, 2, 3, 1, 1, 4, 3, 3, 2]
def baseStart_7423039 : Nat := 118140960795 + 7423039 * 2 ^ 59
def prefixEnd_7423039 : Nat := 4983230072969 + 3 ^ 40 * 7423039 * 2
def baseEnd_7423039 : Nat := 3811586924070088059474571

theorem tailTrace_7423039 : CollatzResearch.WordTrace tailWord_7423039 prefixEnd_7423039 3811586924070088059474571 := by
  unfold tailWord_7423039
  simp only [CollatzResearch.WordTrace]
  refine ⟨270740474554604931975248171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180493649703069954650165447 270740474554604931975248171)
  ·
    refine ⟨406110711831907397962872257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270740474554604931975248171 406110711831907397962872257)
    ·
      refine ⟨304583033873930548472154193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 406110711831907397962872257 304583033873930548472154193)
      ·
        refine ⟨228437275405447911354115645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 304583033873930548472154193 228437275405447911354115645)
        ·
          refine ⟨85663978277042966757793367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 228437275405447911354115645 85663978277042966757793367)
          ·
            refine ⟨128495967415564450136690051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85663978277042966757793367 128495967415564450136690051)
            ·
              refine ⟨192743951123346675205035077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128495967415564450136690051 192743951123346675205035077)
              ·
                refine ⟨36139490835627501600944077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 192743951123346675205035077 36139490835627501600944077)
                ·
                  refine ⟨13552309063360313100354029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36139490835627501600944077 13552309063360313100354029)
                  ·
                    refine ⟨5082115898760117412632761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13552309063360313100354029 5082115898760117412632761)
                    ·
                      refine ⟨3811586924070088059474571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5082115898760117412632761 3811586924070088059474571)
                      ·
                        rfl

theorem cell23_7423039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 4, 3, 3, 2].length) (baseStart_7423039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7423039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7423039 prefixEnd_7423039 := by exact prefixLift 7423039
  have htrace : WordTrace (prefixWord ++ tailWord_7423039) baseStart_7423039 baseEnd_7423039 := by
    simpa [prefixWord, tailWord_7423039, baseEnd_7423039] using wordTrace_append hprefix tailTrace_7423039
  have hstable : (prefixWord ++ tailWord_7423039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7423039).length < 2 ^ (prefixWord ++ tailWord_7423039).sum := by decide
  have hdescent : baseEnd_7423039 < baseStart_7423039 := by decide
  rcases family_descends (prefixWord ++ tailWord_7423039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7423072 : List Nat := [2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 5]
def baseStart_7423072 : Nat := 118140960795 + 7423072 * 2 ^ 59
def prefixEnd_7423072 : Nat := 4983230072969 + 3 ^ 40 * 7423072 * 2
def baseEnd_7423072 : Nat := 3811603868931686430361919

theorem tailTrace_7423072 : CollatzResearch.WordTrace tailWord_7423072 prefixEnd_7423072 3811603868931686430361919 := by
  unfold tailWord_7423072
  simp only [CollatzResearch.WordTrace]
  refine ⟨135370839081742689305599735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180494452108990252407466313 135370839081742689305599735)
  ·
    refine ⟨203056258622614033958399603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135370839081742689305599735 203056258622614033958399603)
    ·
      refine ⟨304584387933921050937599405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203056258622614033958399603 304584387933921050937599405)
      ·
        refine ⟨114219145475220394101599777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 304584387933921050937599405 114219145475220394101599777)
        ·
          refine ⟨85664359106415295576199833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114219145475220394101599777 85664359106415295576199833)
          ·
            refine ⟨64248269329811471682149875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85664359106415295576199833 64248269329811471682149875)
            ·
              refine ⟨96372403994717207523224813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64248269329811471682149875 96372403994717207523224813)
              ·
                refine ⟨36139651498018952821209305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96372403994717207523224813 36139651498018952821209305)
                ·
                  refine ⟨27104738623514214615906979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36139651498018952821209305 27104738623514214615906979)
                  ·
                    refine ⟨40657107935271321923860469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27104738623514214615906979 40657107935271321923860469)
                    ·
                      refine ⟨3811603868931686430361919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40657107935271321923860469 3811603868931686430361919)
                      ·
                        rfl

theorem cell23_7423072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 5].length) (baseStart_7423072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7423072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7423072 prefixEnd_7423072 := by exact prefixLift 7423072
  have htrace : WordTrace (prefixWord ++ tailWord_7423072) baseStart_7423072 baseEnd_7423072 := by
    simpa [prefixWord, tailWord_7423072, baseEnd_7423072] using wordTrace_append hprefix tailTrace_7423072
  have hstable : (prefixWord ++ tailWord_7423072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7423072).length < 2 ^ (prefixWord ++ tailWord_7423072).sum := by decide
  have hdescent : baseEnd_7423072 < baseStart_7423072 := by decide
  rcases family_descends (prefixWord ++ tailWord_7423072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7423080 : List Nat := [2, 1, 4, 4, 1, 1, 2, 2, 2, 1, 3]
def baseStart_7423080 : Nat := 118140960795 + 7423080 * 2 ^ 59
def prefixEnd_7423080 : Nat := 4983230072969 + 3 ^ 40 * 7423080 * 2
def baseEnd_7423080 : Nat := 3811607976776922399061883

theorem tailTrace_7423080 : CollatzResearch.WordTrace tailWord_7423080 prefixEnd_7423080 3811607976776922399061883 := by
  unfold tailWord_7423080
  simp only [CollatzResearch.WordTrace]
  refine ⟨135370984973728197988745347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180494646631637597318327129 135370984973728197988745347)
  ·
    refine ⟨203056477460592296983118021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135370984973728197988745347 203056477460592296983118021)
    ·
      refine ⟨38073089523861055684334629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 203056477460592296983118021 38073089523861055684334629)
      ·
        refine ⟨7138704285723947940812743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38073089523861055684334629 7138704285723947940812743)
        ·
          refine ⟨10708056428585921911219115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7138704285723947940812743 10708056428585921911219115)
          ·
            refine ⟨16062084642878882866828673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10708056428585921911219115 16062084642878882866828673)
            ·
              refine ⟨12046563482159162150121505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16062084642878882866828673 12046563482159162150121505)
              ·
                refine ⟨9034922611619371612591129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12046563482159162150121505 9034922611619371612591129)
                ·
                  refine ⟨6776191958714528709443347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9034922611619371612591129 6776191958714528709443347)
                  ·
                    refine ⟨10164287938071793064165021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6776191958714528709443347 10164287938071793064165021)
                    ·
                      refine ⟨3811607976776922399061883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10164287938071793064165021 3811607976776922399061883)
                      ·
                        rfl

theorem cell23_7423080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_7423080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7423080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7423080 prefixEnd_7423080 := by exact prefixLift 7423080
  have htrace : WordTrace (prefixWord ++ tailWord_7423080) baseStart_7423080 baseEnd_7423080 := by
    simpa [prefixWord, tailWord_7423080, baseEnd_7423080] using wordTrace_append hprefix tailTrace_7423080
  have hstable : (prefixWord ++ tailWord_7423080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7423080).length < 2 ^ (prefixWord ++ tailWord_7423080).sum := by decide
  have hdescent : baseEnd_7423080 < baseStart_7423080 := by decide
  rcases family_descends (prefixWord ++ tailWord_7423080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7423109 : List Nat := [1, 3, 1, 1, 6, 1, 1, 2, 7]
def baseStart_7423109 : Nat := 118140960795 + 7423109 * 2 ^ 59
def prefixEnd_7423109 : Nat := 4983230072969 + 3 ^ 40 * 7423109 * 2
def baseEnd_7423109 : Nat := 423513651968433642844361

theorem tailTrace_7423109 : CollatzResearch.WordTrace tailWord_7423109 prefixEnd_7423109 423513651968433642844361 := by
  unfold tailWord_7423109
  simp only [CollatzResearch.WordTrace]
  refine ⟨270743027664351333930296381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180495351776234222620197587 270743027664351333930296381)
  ·
    refine ⟨101528635374131750223861143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 270743027664351333930296381 101528635374131750223861143)
    ·
      refine ⟨152292953061197625335791715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101528635374131750223861143 152292953061197625335791715)
      ·
        refine ⟨228439429591796438003687573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152292953061197625335791715 228439429591796438003687573)
        ·
          refine ⟨10708098262115458031422855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 228439429591796438003687573 10708098262115458031422855)
          ·
            refine ⟨16062147393173187047134283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10708098262115458031422855 16062147393173187047134283)
            ·
              refine ⟨24093221089759780570701425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16062147393173187047134283 24093221089759780570701425)
              ·
                refine ⟨18069915817319835428026069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24093221089759780570701425 18069915817319835428026069)
                ·
                  refine ⟨423513651968433642844361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18069915817319835428026069 423513651968433642844361)
                  ·
                    rfl

theorem cell23_7423109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 2, 7].length) (baseStart_7423109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7423109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7423109 prefixEnd_7423109 := by exact prefixLift 7423109
  have htrace : WordTrace (prefixWord ++ tailWord_7423109) baseStart_7423109 baseEnd_7423109 := by
    simpa [prefixWord, tailWord_7423109, baseEnd_7423109] using wordTrace_append hprefix tailTrace_7423109
  have hstable : (prefixWord ++ tailWord_7423109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7423109).length < 2 ^ (prefixWord ++ tailWord_7423109).sum := by decide
  have hdescent : baseEnd_7423109 < baseStart_7423109 := by decide
  rcases family_descends (prefixWord ++ tailWord_7423109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7423226 : List Nat := [3, 1, 1, 1, 1, 4, 2, 1, 5, 1, 3]
def baseStart_7423226 : Nat := 118140960795 + 7423226 * 2 ^ 59
def prefixEnd_7423226 : Nat := 4983230072969 + 3 ^ 40 * 7423226 * 2
def baseEnd_7423226 : Nat := 3811682944952478827836211

theorem tailTrace_7423226 : CollatzResearch.WordTrace tailWord_7423226 prefixEnd_7423226 3811682944952478827836211 := by
  unfold tailWord_7423226
  simp only [CollatzResearch.WordTrace]
  refine ⟨67686823751231865728076383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180498196669951641941537021 67686823751231865728076383)
  ·
    refine ⟨101530235626847798592114575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67686823751231865728076383 101530235626847798592114575)
    ·
      refine ⟨152295353440271697888171863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101530235626847798592114575 152295353440271697888171863)
      ·
        refine ⟨228443030160407546832257795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152295353440271697888171863 228443030160407546832257795)
        ·
          refine ⟨342664545240611320248386693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228443030160407546832257795 342664545240611320248386693)
          ·
            refine ⟨64249602232614622546572505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 342664545240611320248386693 64249602232614622546572505)
            ·
              refine ⟨48187201674460966909929379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64249602232614622546572505 48187201674460966909929379)
              ·
                refine ⟨72280802511691450364894069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48187201674460966909929379 72280802511691450364894069)
                ·
                  refine ⟨6776325235471073471708819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 72280802511691450364894069 6776325235471073471708819)
                  ·
                    refine ⟨10164487853206610207563229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6776325235471073471708819 10164487853206610207563229)
                    ·
                      refine ⟨3811682944952478827836211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10164487853206610207563229 3811682944952478827836211)
                      ·
                        rfl

theorem cell23_7423226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 1, 5, 1, 3].length) (baseStart_7423226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7423226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7423226 prefixEnd_7423226 := by exact prefixLift 7423226
  have htrace : WordTrace (prefixWord ++ tailWord_7423226) baseStart_7423226 baseEnd_7423226 := by
    simpa [prefixWord, tailWord_7423226, baseEnd_7423226] using wordTrace_append hprefix tailTrace_7423226
  have hstable : (prefixWord ++ tailWord_7423226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7423226).length < 2 ^ (prefixWord ++ tailWord_7423226).sum := by decide
  have hdescent : baseEnd_7423226 < baseStart_7423226 := by decide
  rcases family_descends (prefixWord ++ tailWord_7423226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7423250 : List Nat := [3, 2, 4, 2, 1, 1, 2, 2, 6]
def baseStart_7423250 : Nat := 118140960795 + 7423250 * 2 ^ 59
def prefixEnd_7423250 : Nat := 4983230072969 + 3 ^ 40 * 7423250 * 2
def baseEnd_7423250 : Nat := 423521696498687414881789

theorem tailTrace_7423250 : CollatzResearch.WordTrace tailWord_7423250 prefixEnd_7423250 423521696498687414881789 := by
  unfold tailWord_7423250
  simp only [CollatzResearch.WordTrace]
  refine ⟨67687042589210128752794801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180498780237893676674119469 67687042589210128752794801)
  ·
    refine ⟨50765281941907596564596101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67687042589210128752794801 50765281941907596564596101)
    ·
      refine ⟨9518490364107674355861769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50765281941907596564596101 9518490364107674355861769)
      ·
        refine ⟨7138867773080755766896327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9518490364107674355861769 7138867773080755766896327)
        ·
          refine ⟨10708301659621133650344491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7138867773080755766896327 10708301659621133650344491)
          ·
            refine ⟨16062452489431700475516737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10708301659621133650344491 16062452489431700475516737)
            ·
              refine ⟨12046839367073775356637553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16062452489431700475516737 12046839367073775356637553)
              ·
                refine ⟨9035129525305331517478165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12046839367073775356637553 9035129525305331517478165)
                ·
                  refine ⟨423521696498687414881789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9035129525305331517478165 423521696498687414881789)
                  ·
                    rfl

theorem cell23_7423250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 2, 2, 6].length) (baseStart_7423250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7423250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7423250 prefixEnd_7423250 := by exact prefixLift 7423250
  have htrace : WordTrace (prefixWord ++ tailWord_7423250) baseStart_7423250 baseEnd_7423250 := by
    simpa [prefixWord, tailWord_7423250, baseEnd_7423250] using wordTrace_append hprefix tailTrace_7423250
  have hstable : (prefixWord ++ tailWord_7423250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7423250).length < 2 ^ (prefixWord ++ tailWord_7423250).sum := by decide
  have hdescent : baseEnd_7423250 < baseStart_7423250 := by decide
  rcases family_descends (prefixWord ++ tailWord_7423250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7423283 : List Nat := [1, 1, 1, 2, 5, 2, 1, 1, 5, 2, 2]
def baseStart_7423283 : Nat := 118140960795 + 7423283 * 2 ^ 59
def prefixEnd_7423283 : Nat := 4983230072969 + 3 ^ 40 * 7423283 * 2
def baseEnd_7423283 : Nat := 3811712213349785104823449

theorem tailTrace_7423283 : CollatzResearch.WordTrace tailWord_7423283 prefixEnd_7423283 3811712213349785104823449 := by
  unfold tailWord_7423283
  simp only [CollatzResearch.WordTrace]
  refine ⟨270749373965720961647130503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180499582643813974431420335 270749373965720961647130503)
  ·
    refine ⟨406124060948581442470695755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270749373965720961647130503 406124060948581442470695755)
    ·
      refine ⟨609186091422872163706043633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 406124060948581442470695755 609186091422872163706043633)
      ·
        refine ⟨456889568567154122779532725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 609186091422872163706043633 456889568567154122779532725)
        ·
          refine ⟨42833397053170699010581193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 456889568567154122779532725 42833397053170699010581193)
          ·
            refine ⟨32125047789878024257935895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42833397053170699010581193 32125047789878024257935895)
            ·
              refine ⟨48187571684817036386903843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32125047789878024257935895 48187571684817036386903843)
              ·
                refine ⟨72281357527225554580355765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48187571684817036386903843 72281357527225554580355765)
                ·
                  refine ⟨6776377268177395741908353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 72281357527225554580355765 6776377268177395741908353)
                  ·
                    refine ⟨5082282951133046806431265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6776377268177395741908353 5082282951133046806431265)
                    ·
                      refine ⟨3811712213349785104823449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5082282951133046806431265 3811712213349785104823449)
                      ·
                        rfl

theorem cell23_7423283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 1, 5, 2, 2].length) (baseStart_7423283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7423283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7423283 prefixEnd_7423283 := by exact prefixLift 7423283
  have htrace : WordTrace (prefixWord ++ tailWord_7423283) baseStart_7423283 baseEnd_7423283 := by
    simpa [prefixWord, tailWord_7423283, baseEnd_7423283] using wordTrace_append hprefix tailTrace_7423283
  have hstable : (prefixWord ++ tailWord_7423283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7423283).length < 2 ^ (prefixWord ++ tailWord_7423283).sum := by decide
  have hdescent : baseEnd_7423283 < baseStart_7423283 := by decide
  rcases family_descends (prefixWord ++ tailWord_7423283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7423300 : List Nat := [2, 3, 4, 1, 1, 2, 1, 3, 1, 1, 4]
def baseStart_7423300 : Nat := 118140960795 + 7423300 * 2 ^ 59
def prefixEnd_7423300 : Nat := 4983230072969 + 3 ^ 40 * 7423300 * 2
def baseEnd_7423300 : Nat := 3811720942520911538310871

theorem tailTrace_7423300 : CollatzResearch.WordTrace tailWord_7423300 prefixEnd_7423300 3811720942520911538310871 := by
  unfold tailWord_7423300
  simp only [CollatzResearch.WordTrace]
  refine ⟨135374997003329686775249677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180499996004439582366999569 135374997003329686775249677)
  ·
    refine ⟨50765623876248632540718629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135374997003329686775249677 50765623876248632540718629)
    ·
      refine ⟨9518554476796618601384743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50765623876248632540718629 9518554476796618601384743)
      ·
        refine ⟨14277831715194927902077115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9518554476796618601384743 14277831715194927902077115)
        ·
          refine ⟨21416747572792391853115673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14277831715194927902077115 21416747572792391853115673)
          ·
            refine ⟨16062560679594293889836755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21416747572792391853115673 16062560679594293889836755)
            ·
              refine ⟨24093841019391440834755133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16062560679594293889836755 24093841019391440834755133)
              ·
                refine ⟨9035190382271790313033175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24093841019391440834755133 9035190382271790313033175)
                ·
                  refine ⟨13552785573407685469549763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9035190382271790313033175 13552785573407685469549763)
                  ·
                    refine ⟨20329178360111528204324645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13552785573407685469549763 20329178360111528204324645)
                    ·
                      refine ⟨3811720942520911538310871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20329178360111528204324645 3811720942520911538310871)
                      ·
                        rfl

theorem cell23_7423300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_7423300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7423300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7423300 prefixEnd_7423300 := by exact prefixLift 7423300
  have htrace : WordTrace (prefixWord ++ tailWord_7423300) baseStart_7423300 baseEnd_7423300 := by
    simpa [prefixWord, tailWord_7423300, baseEnd_7423300] using wordTrace_append hprefix tailTrace_7423300
  have hstable : (prefixWord ++ tailWord_7423300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7423300).length < 2 ^ (prefixWord ++ tailWord_7423300).sum := by decide
  have hdescent : baseEnd_7423300 < baseStart_7423300 := by decide
  rcases family_descends (prefixWord ++ tailWord_7423300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7423303 : List Nat := [1, 1, 4, 1, 2, 4, 1, 3, 1, 2, 3]
def baseStart_7423303 : Nat := 118140960795 + 7423303 * 2 ^ 59
def prefixEnd_7423303 : Nat := 4983230072969 + 3 ^ 40 * 7423303 * 2
def baseEnd_7423303 : Nat := 3811722482962875026573357

theorem tailTrace_7423303 : CollatzResearch.WordTrace tailWord_7423303 prefixEnd_7423303 3811722482962875026573357 := by
  unfold tailWord_7423303
  simp only [CollatzResearch.WordTrace]
  refine ⟨270750103425648505062858563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180500068950432336708572375 270750103425648505062858563)
  ·
    refine ⟨406125155138472757594287845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270750103425648505062858563 406125155138472757594287845)
    ·
      refine ⟨76148466588463642048928971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 406125155138472757594287845 76148466588463642048928971)
      ·
        refine ⟨114222699882695463073393457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76148466588463642048928971 114222699882695463073393457)
        ·
          refine ⟨85667024912021597305045093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114222699882695463073393457 85667024912021597305045093)
          ·
            refine ⟨16062567171004049494695955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85667024912021597305045093 16062567171004049494695955)
            ·
              refine ⟨24093850756506074242043933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16062567171004049494695955 24093850756506074242043933)
              ·
                refine ⟨9035194033689777840766475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24093850756506074242043933 9035194033689777840766475)
                ·
                  refine ⟨13552791050534666761149713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9035194033689777840766475 13552791050534666761149713)
                  ·
                    refine ⟨10164593287901000070862285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13552791050534666761149713 10164593287901000070862285)
                    ·
                      refine ⟨3811722482962875026573357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10164593287901000070862285 3811722482962875026573357)
                      ·
                        rfl

theorem cell23_7423303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 3, 1, 2, 3].length) (baseStart_7423303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7423303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7423303 prefixEnd_7423303 := by exact prefixLift 7423303
  have htrace : WordTrace (prefixWord ++ tailWord_7423303) baseStart_7423303 baseEnd_7423303 := by
    simpa [prefixWord, tailWord_7423303, baseEnd_7423303] using wordTrace_append hprefix tailTrace_7423303
  have hstable : (prefixWord ++ tailWord_7423303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7423303).length < 2 ^ (prefixWord ++ tailWord_7423303).sum := by decide
  have hdescent : baseEnd_7423303 < baseStart_7423303 := by decide
  rcases family_descends (prefixWord ++ tailWord_7423303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7423317 : List Nat := [1, 3, 2, 2, 3, 1, 2, 4, 1, 2, 2]
def baseStart_7423317 : Nat := 118140960795 + 7423317 * 2 ^ 59
def prefixEnd_7423317 : Nat := 4983230072969 + 3 ^ 40 * 7423317 * 2
def baseEnd_7423317 : Nat := 3811729671692037971798293

theorem tailTrace_7423317 : CollatzResearch.WordTrace tailWord_7423317 prefixEnd_7423317 3811729671692037971798293 := by
  unfold tailWord_7423317
  simp only [CollatzResearch.WordTrace]
  refine ⟨270750614047597785453868205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180500409365065190302578803 270750614047597785453868205)
  ·
    refine ⟨101531480267849169545200577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 270750614047597785453868205 101531480267849169545200577)
    ·
      refine ⟨76148610200886877158900433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101531480267849169545200577 76148610200886877158900433)
      ·
        refine ⟨57111457650665157869175325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76148610200886877158900433 57111457650665157869175325)
        ·
          refine ⟨21416796618999434200940747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57111457650665157869175325 21416796618999434200940747)
          ·
            refine ⟨32125194928499151301411121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21416796618999434200940747 32125194928499151301411121)
            ·
              refine ⟨24093896196374363476058341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32125194928499151301411121 24093896196374363476058341)
              ·
                refine ⟨4517605536820193151760939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24093896196374363476058341 4517605536820193151760939)
                ·
                  refine ⟨6776408305230289727641409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4517605536820193151760939 6776408305230289727641409)
                  ·
                    refine ⟨5082306228922717295731057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6776408305230289727641409 5082306228922717295731057)
                    ·
                      refine ⟨3811729671692037971798293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5082306228922717295731057 3811729671692037971798293)
                      ·
                        rfl

theorem cell23_7423317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 2, 4, 1, 2, 2].length) (baseStart_7423317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7423317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7423317 prefixEnd_7423317 := by exact prefixLift 7423317
  have htrace : WordTrace (prefixWord ++ tailWord_7423317) baseStart_7423317 baseEnd_7423317 := by
    simpa [prefixWord, tailWord_7423317, baseEnd_7423317] using wordTrace_append hprefix tailTrace_7423317
  have hstable : (prefixWord ++ tailWord_7423317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7423317).length < 2 ^ (prefixWord ++ tailWord_7423317).sum := by decide
  have hdescent : baseEnd_7423317 < baseStart_7423317 := by decide
  rcases family_descends (prefixWord ++ tailWord_7423317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7423329 : List Nat := [1, 2, 3, 1, 1, 1, 1, 2, 4, 2, 5]
def baseStart_7423329 : Nat := 118140960795 + 7423329 * 2 ^ 59
def prefixEnd_7423329 : Nat := 4983230072969 + 3 ^ 40 * 7423329 * 2
def baseEnd_7423329 : Nat := 3811735833459891924848237

theorem tailTrace_7423329 : CollatzResearch.WordTrace tailWord_7423329 prefixEnd_7423329 3811735833459891924848237 := by
  unfold tailWord_7423329
  simp only [CollatzResearch.WordTrace]
  refine ⟨270751051723554311503305041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180500701149036207668870027 270751051723554311503305041)
  ·
    refine ⟨203063288792665733627478781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270751051723554311503305041 203063288792665733627478781)
    ·
      refine ⟨76148733297249650110304543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 203063288792665733627478781 76148733297249650110304543)
      ·
        refine ⟨114223099945874475165456815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76148733297249650110304543 114223099945874475165456815)
        ·
          refine ⟨171334649918811712748185223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114223099945874475165456815 171334649918811712748185223)
          ·
            refine ⟨257001974878217569122277835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171334649918811712748185223 257001974878217569122277835)
            ·
              refine ⟨385502962317326353683416753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 257001974878217569122277835 385502962317326353683416753)
              ·
                refine ⟨289127221737994765262562565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 385502962317326353683416753 289127221737994765262562565)
                ·
                  refine ⟨54211354075874018486730481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 289127221737994765262562565 54211354075874018486730481)
                  ·
                    refine ⟨40658515556905513865047861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54211354075874018486730481 40658515556905513865047861)
                    ·
                      refine ⟨3811735833459891924848237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40658515556905513865047861 3811735833459891924848237)
                      ·
                        rfl

theorem cell23_7423329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 4, 2, 5].length) (baseStart_7423329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7423329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7423329 prefixEnd_7423329 := by exact prefixLift 7423329
  have htrace : WordTrace (prefixWord ++ tailWord_7423329) baseStart_7423329 baseEnd_7423329 := by
    simpa [prefixWord, tailWord_7423329, baseEnd_7423329] using wordTrace_append hprefix tailTrace_7423329
  have hstable : (prefixWord ++ tailWord_7423329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7423329).length < 2 ^ (prefixWord ++ tailWord_7423329).sum := by decide
  have hdescent : baseEnd_7423329 < baseStart_7423329 := by decide
  rcases family_descends (prefixWord ++ tailWord_7423329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7423384 : List Nat := [2, 1, 2, 5, 2, 2, 2, 1, 2, 1, 3]
def baseStart_7423384 : Nat := 118140960795 + 7423384 * 2 ^ 59
def prefixEnd_7423384 : Nat := 4983230072969 + 3 ^ 40 * 7423384 * 2
def baseEnd_7423384 : Nat := 3811764074895889209660485

theorem tailTrace_7423384 : CollatzResearch.WordTrace tailWord_7423384 prefixEnd_7423384 3811764074895889209660485 := by
  unfold tailWord_7423384
  simp only [CollatzResearch.WordTrace]
  refine ⟨135376528869177527948278603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180502038492236703931038137 135376528869177527948278603)
  ·
    refine ⟨203064793303766291922417905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135376528869177527948278603 203064793303766291922417905)
    ·
      refine ⟨152298594977824718941813429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203064793303766291922417905 152298594977824718941813429)
      ·
        refine ⟨14277993279171067400795009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 152298594977824718941813429 14277993279171067400795009)
        ·
          refine ⟨10708494959378300550596257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14277993279171067400795009 10708494959378300550596257)
          ·
            refine ⟨8031371219533725412947193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10708494959378300550596257 8031371219533725412947193)
            ·
              refine ⟨6023528414650294059710395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8031371219533725412947193 6023528414650294059710395)
              ·
                refine ⟨9035292621975441089565593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6023528414650294059710395 9035292621975441089565593)
                ·
                  refine ⟨6776469466481580817174195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9035292621975441089565593 6776469466481580817174195)
                  ·
                    refine ⟨10164704199722371225761293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6776469466481580817174195 10164704199722371225761293)
                    ·
                      refine ⟨3811764074895889209660485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10164704199722371225761293 3811764074895889209660485)
                      ·
                        rfl

theorem cell23_7423384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 2, 1, 2, 1, 3].length) (baseStart_7423384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7423384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7423384 prefixEnd_7423384 := by exact prefixLift 7423384
  have htrace : WordTrace (prefixWord ++ tailWord_7423384) baseStart_7423384 baseEnd_7423384 := by
    simpa [prefixWord, tailWord_7423384, baseEnd_7423384] using wordTrace_append hprefix tailTrace_7423384
  have hstable : (prefixWord ++ tailWord_7423384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7423384).length < 2 ^ (prefixWord ++ tailWord_7423384).sum := by decide
  have hdescent : baseEnd_7423384 < baseStart_7423384 := by decide
  rcases family_descends (prefixWord ++ tailWord_7423384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7423386 : List Nat := [3, 1, 1, 4, 1, 1, 2, 1, 1, 4, 4]
def baseStart_7423386 : Nat := 118140960795 + 7423386 * 2 ^ 59
def prefixEnd_7423386 : Nat := 4983230072969 + 3 ^ 40 * 7423386 * 2
def baseEnd_7423386 : Nat := 3811765101857198201835475

theorem tailTrace_7423386 : CollatzResearch.WordTrace tailWord_7423386 prefixEnd_7423386 3811765101857198201835475 := by
  unfold tailWord_7423386
  simp only [CollatzResearch.WordTrace]
  refine ⟨67688282671086952559532503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180502087122898540158753341 67688282671086952559532503)
  ·
    refine ⟨101532424006630428839298755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67688282671086952559532503 101532424006630428839298755)
    ·
      refine ⟨152298636009945643258948133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101532424006630428839298755 152298636009945643258948133)
      ·
        refine ⟨28555994251864808111052775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 152298636009945643258948133 28555994251864808111052775)
        ·
          refine ⟨42833991377797212166579163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28555994251864808111052775 42833991377797212166579163)
          ·
            refine ⟨64250987066695818249868745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42833991377797212166579163 64250987066695818249868745)
            ·
              refine ⟨48188240300021863687401559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64250987066695818249868745 48188240300021863687401559)
              ·
                refine ⟨72282360450032795531102339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48188240300021863687401559 72282360450032795531102339)
                ·
                  refine ⟨108423540675049193296653509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72282360450032795531102339 108423540675049193296653509)
                  ·
                    refine ⟨20329413876571723743122533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 108423540675049193296653509 20329413876571723743122533)
                    ·
                      refine ⟨3811765101857198201835475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20329413876571723743122533 3811765101857198201835475)
                      ·
                        rfl

theorem cell23_7423386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_7423386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7423386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7423386 prefixEnd_7423386 := by exact prefixLift 7423386
  have htrace : WordTrace (prefixWord ++ tailWord_7423386) baseStart_7423386 baseEnd_7423386 := by
    simpa [prefixWord, tailWord_7423386, baseEnd_7423386] using wordTrace_append hprefix tailTrace_7423386
  have hstable : (prefixWord ++ tailWord_7423386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7423386).length < 2 ^ (prefixWord ++ tailWord_7423386).sum := by decide
  have hdescent : baseEnd_7423386 < baseStart_7423386 := by decide
  rcases family_descends (prefixWord ++ tailWord_7423386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7423463 : List Nat := [1, 1, 5, 2, 1, 3, 1, 1, 1, 3, 4]
def baseStart_7423463 : Nat := 118140960795 + 7423463 * 2 ^ 59
def prefixEnd_7423463 : Nat := 4983230072969 + 3 ^ 40 * 7423463 * 2
def baseEnd_7423463 : Nat := 3811804639867594400572621

theorem tailTrace_7423463 : CollatzResearch.WordTrace tailWord_7423463 prefixEnd_7423463 3811804639867594400572621 := by
  unfold tailWord_7423463
  simp only [CollatzResearch.WordTrace]
  refine ⟨270755939105068852388683043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180503959403379234925788695 270755939105068852388683043)
  ·
    refine ⟨406133908657603278583024565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270755939105068852388683043 406133908657603278583024565)
    ·
      refine ⟨38075053936650307367158553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 406133908657603278583024565 38075053936650307367158553)
      ·
        refine ⟨28556290452487730525368915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38075053936650307367158553 28556290452487730525368915)
        ·
          refine ⟨42834435678731595788053373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28556290452487730525368915 42834435678731595788053373)
          ·
            refine ⟨16062913379524348420520015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42834435678731595788053373 16062913379524348420520015)
            ·
              refine ⟨24094370069286522630780023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16062913379524348420520015 24094370069286522630780023)
              ·
                refine ⟨36141555103929783946170035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24094370069286522630780023 36141555103929783946170035)
                ·
                  refine ⟨54212332655894675919255053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36141555103929783946170035 54212332655894675919255053)
                  ·
                    refine ⟨20329624745960503469720645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54212332655894675919255053 20329624745960503469720645)
                    ·
                      refine ⟨3811804639867594400572621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20329624745960503469720645 3811804639867594400572621)
                      ·
                        rfl

theorem cell23_7423463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_7423463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7423463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7423463 prefixEnd_7423463 := by exact prefixLift 7423463
  have htrace : WordTrace (prefixWord ++ tailWord_7423463) baseStart_7423463 baseEnd_7423463 := by
    simpa [prefixWord, tailWord_7423463, baseEnd_7423463] using wordTrace_append hprefix tailTrace_7423463
  have hstable : (prefixWord ++ tailWord_7423463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7423463).length < 2 ^ (prefixWord ++ tailWord_7423463).sum := by decide
  have hdescent : baseEnd_7423463 < baseStart_7423463 := by decide
  rcases family_descends (prefixWord ++ tailWord_7423463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7423570 : List Nat := [3, 2, 2, 1, 2, 3, 1, 1, 3, 1, 4]
def baseStart_7423570 : Nat := 118140960795 + 7423570 * 2 ^ 59
def prefixEnd_7423570 : Nat := 4983230072969 + 3 ^ 40 * 7423570 * 2
def baseEnd_7423570 : Nat := 3811859582297625481934629

theorem tailTrace_7423570 : CollatzResearch.WordTrace tailWord_7423570 prefixEnd_7423570 3811859582297625481934629 := by
  unfold tailWord_7423570
  simp only [CollatzResearch.WordTrace]
  refine ⟨67689960428920302415707041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180506561143787473108552109 67689960428920302415707041)
  ·
    refine ⟨50767470321690226811780281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67689960428920302415707041 50767470321690226811780281)
    ·
      refine ⟨38075602741267670108835211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50767470321690226811780281 38075602741267670108835211)
      ·
        refine ⟨57113404111901505163252817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38075602741267670108835211 57113404111901505163252817)
        ·
          refine ⟨42835053083926128872439613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57113404111901505163252817 42835053083926128872439613)
          ·
            refine ⟨16063144906472298327164855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42835053083926128872439613 16063144906472298327164855)
            ·
              refine ⟨24094717359708447490747283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16063144906472298327164855 24094717359708447490747283)
              ·
                refine ⟨36142076039562671236120925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24094717359708447490747283 36142076039562671236120925)
                ·
                  refine ⟨13553278514836001713545347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36142076039562671236120925 13553278514836001713545347)
                  ·
                    refine ⟨20329917772254002570318021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13553278514836001713545347 20329917772254002570318021)
                    ·
                      refine ⟨3811859582297625481934629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20329917772254002570318021 3811859582297625481934629)
                      ·
                        rfl

theorem cell23_7423570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 1, 3, 1, 4].length) (baseStart_7423570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7423570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7423570 prefixEnd_7423570 := by exact prefixLift 7423570
  have htrace : WordTrace (prefixWord ++ tailWord_7423570) baseStart_7423570 baseEnd_7423570 := by
    simpa [prefixWord, tailWord_7423570, baseEnd_7423570] using wordTrace_append hprefix tailTrace_7423570
  have hstable : (prefixWord ++ tailWord_7423570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7423570).length < 2 ^ (prefixWord ++ tailWord_7423570).sum := by decide
  have hdescent : baseEnd_7423570 < baseStart_7423570 := by decide
  rcases family_descends (prefixWord ++ tailWord_7423570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7423580 : List Nat := [2, 2, 4, 1, 2, 2, 1, 2, 1, 6]
def baseStart_7423580 : Nat := 118140960795 + 7423580 * 2 ^ 59
def prefixEnd_7423580 : Nat := 4983230072969 + 3 ^ 40 * 7423580 * 2
def baseEnd_7423580 : Nat := 1270621572368056814269861

theorem tailTrace_7423580 : CollatzResearch.WordTrace tailWord_7423580 prefixEnd_7423580 1270621572368056814269861 := by
  unfold tailWord_7423580
  simp only [CollatzResearch.WordTrace]
  refine ⟨135380103222822490685346097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180506804297096654247128129 135380103222822490685346097)
  ·
    refine ⟨101535077417116868014009573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135380103222822490685346097 101535077417116868014009573)
    ·
      refine ⟨19037827015709412752626795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101535077417116868014009573 19037827015709412752626795)
      ·
        refine ⟨28556740523564119128940193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19037827015709412752626795 28556740523564119128940193)
        ·
          refine ⟨21417555392673089346705145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28556740523564119128940193 21417555392673089346705145)
          ·
            refine ⟨16063166544504817010028859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21417555392673089346705145 16063166544504817010028859)
            ·
              refine ⟨24094749816757225515043289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16063166544504817010028859 24094749816757225515043289)
              ·
                refine ⟨18071062362567919136282467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24094749816757225515043289 18071062362567919136282467)
                ·
                  refine ⟨27106593543851878704423701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18071062362567919136282467 27106593543851878704423701)
                  ·
                    refine ⟨1270621572368056814269861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27106593543851878704423701 1270621572368056814269861)
                    ·
                      rfl

theorem cell23_7423580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 2, 1, 6].length) (baseStart_7423580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7423580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7423580 prefixEnd_7423580 := by exact prefixLift 7423580
  have htrace : WordTrace (prefixWord ++ tailWord_7423580) baseStart_7423580 baseEnd_7423580 := by
    simpa [prefixWord, tailWord_7423580, baseEnd_7423580] using wordTrace_append hprefix tailTrace_7423580
  have hstable : (prefixWord ++ tailWord_7423580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7423580).length < 2 ^ (prefixWord ++ tailWord_7423580).sum := by decide
  have hdescent : baseEnd_7423580 < baseStart_7423580 := by decide
  rcases family_descends (prefixWord ++ tailWord_7423580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7423587 : List Nat := [1, 1, 1, 5, 1, 4, 3, 1, 1, 1, 4]
def baseStart_7423587 : Nat := 118140960795 + 7423587 * 2 ^ 59
def prefixEnd_7423587 : Nat := 4983230072969 + 3 ^ 40 * 7423587 * 2
def baseEnd_7423587 : Nat := 3811868311468751915422051

theorem tailTrace_7423587 : CollatzResearch.WordTrace tailWord_7423587 prefixEnd_7423587 3811868311468751915422051 := by
  unfold tailWord_7423587
  simp only [CollatzResearch.WordTrace]
  refine ⟨270760461756619621566197015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180506974504413081044131343 270760461756619621566197015)
  ·
    refine ⟨406140692634929432349295523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270760461756619621566197015 406140692634929432349295523)
    ·
      refine ⟨609211038952394148523943285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 406140692634929432349295523 609211038952394148523943285)
      ·
        refine ⟨57113534901786951424119683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 609211038952394148523943285 57113534901786951424119683)
        ·
          refine ⟨85670302352680427136179525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57113534901786951424119683 85670302352680427136179525)
          ·
            refine ⟨16063181691127580088033661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85670302352680427136179525 16063181691127580088033661)
            ·
              refine ⟨6023693134172842533012623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16063181691127580088033661 6023693134172842533012623)
              ·
                refine ⟨9035539701259263799518935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6023693134172842533012623 9035539701259263799518935)
                ·
                  refine ⟨13553309551888895699278403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9035539701259263799518935 13553309551888895699278403)
                  ·
                    refine ⟨20329964327833343548917605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13553309551888895699278403 20329964327833343548917605)
                    ·
                      refine ⟨3811868311468751915422051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20329964327833343548917605 3811868311468751915422051)
                      ·
                        rfl

theorem cell23_7423587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 3, 1, 1, 1, 4].length) (baseStart_7423587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7423587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7423587 prefixEnd_7423587 := by exact prefixLift 7423587
  have htrace : WordTrace (prefixWord ++ tailWord_7423587) baseStart_7423587 baseEnd_7423587 := by
    simpa [prefixWord, tailWord_7423587, baseEnd_7423587] using wordTrace_append hprefix tailTrace_7423587
  have hstable : (prefixWord ++ tailWord_7423587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7423587).length < 2 ^ (prefixWord ++ tailWord_7423587).sum := by decide
  have hdescent : baseEnd_7423587 < baseStart_7423587 := by decide
  rcases family_descends (prefixWord ++ tailWord_7423587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7423598 : List Nat := [4, 1, 2, 2, 3, 2, 2, 2, 1, 1, 3]
def baseStart_7423598 : Nat := 118140960795 + 7423598 * 2 ^ 59
def prefixEnd_7423598 : Nat := 4983230072969 + 3 ^ 40 * 7423598 * 2
def baseEnd_7423598 : Nat := 3811873959755951372384501

theorem tailTrace_7423598 : CollatzResearch.WordTrace tailWord_7423598 prefixEnd_7423598 3811873959755951372384501 := by
  unfold tailWord_7423598
  simp only [CollatzResearch.WordTrace]
  refine ⟨33845107869947471305605931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180507241973053180296564965 33845107869947471305605931)
  ·
    refine ⟨50767661804921206958408897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33845107869947471305605931 50767661804921206958408897)
    ·
      refine ⟨38075746353690905218806673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50767661804921206958408897 38075746353690905218806673)
      ·
        refine ⟨28556809765268178914105005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38075746353690905218806673 28556809765268178914105005)
        ·
          refine ⟨10708803661975567092789377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28556809765268178914105005 10708803661975567092789377)
          ·
            refine ⟨8031602746481675319592033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10708803661975567092789377 8031602746481675319592033)
            ·
              refine ⟨6023702059861256489694025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8031602746481675319592033 6023702059861256489694025)
              ·
                refine ⟨4517776544895942367270519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6023702059861256489694025 4517776544895942367270519)
                ·
                  refine ⟨6776664817343913550905779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4517776544895942367270519 6776664817343913550905779)
                  ·
                    refine ⟨10164997226015870326358669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6776664817343913550905779 10164997226015870326358669)
                    ·
                      refine ⟨3811873959755951372384501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10164997226015870326358669 3811873959755951372384501)
                      ·
                        rfl

theorem cell23_7423598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 2, 2, 1, 1, 3].length) (baseStart_7423598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7423598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7423598 prefixEnd_7423598 := by exact prefixLift 7423598
  have htrace : WordTrace (prefixWord ++ tailWord_7423598) baseStart_7423598 baseEnd_7423598 := by
    simpa [prefixWord, tailWord_7423598, baseEnd_7423598] using wordTrace_append hprefix tailTrace_7423598
  have hstable : (prefixWord ++ tailWord_7423598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7423598).length < 2 ^ (prefixWord ++ tailWord_7423598).sum := by decide
  have hdescent : baseEnd_7423598 < baseStart_7423598 := by decide
  rcases family_descends (prefixWord ++ tailWord_7423598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7423653 : List Nat := [1, 3, 1, 2, 1, 2, 3, 2, 2, 6]
def baseStart_7423653 : Nat := 118140960795 + 7423653 * 2 ^ 59
def prefixEnd_7423653 : Nat := 4983230072969 + 3 ^ 40 * 7423653 * 2
def baseEnd_7423653 : Nat := 1270634067063982885732249

theorem tailTrace_7423653 : CollatzResearch.WordTrace tailWord_7423653 prefixEnd_7423653 1270634067063982885732249 := by
  unfold tailWord_7423653
  simp only [CollatzResearch.WordTrace]
  refine ⟨270762868974380514838099613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180508579316253676558733075 270762868974380514838099613)
  ·
    refine ⟨101536075865392693064287355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 270762868974380514838099613 101536075865392693064287355)
    ·
      refine ⟨152304113798089039596431033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101536075865392693064287355 152304113798089039596431033)
      ·
        refine ⟨114228085348566779697323275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152304113798089039596431033 114228085348566779697323275)
        ·
          refine ⟨171342128022850169545984913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114228085348566779697323275 171342128022850169545984913)
          ·
            refine ⟨128506596017137627159488685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171342128022850169545984913 128506596017137627159488685)
            ·
              refine ⟨48189973506426610184808257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128506596017137627159488685 48189973506426610184808257)
              ·
                refine ⟨36142480129819957638606193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48189973506426610184808257 36142480129819957638606193)
                ·
                  refine ⟨27106860097364968228954645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36142480129819957638606193 27106860097364968228954645)
                  ·
                    refine ⟨1270634067063982885732249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27106860097364968228954645 1270634067063982885732249)
                    ·
                      rfl

theorem cell23_7423653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 2, 2, 6].length) (baseStart_7423653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7423653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7423653 prefixEnd_7423653 := by exact prefixLift 7423653
  have htrace : WordTrace (prefixWord ++ tailWord_7423653) baseStart_7423653 baseEnd_7423653 := by
    simpa [prefixWord, tailWord_7423653, baseEnd_7423653] using wordTrace_append hprefix tailTrace_7423653
  have hstable : (prefixWord ++ tailWord_7423653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7423653).length < 2 ^ (prefixWord ++ tailWord_7423653).sum := by decide
  have hdescent : baseEnd_7423653 < baseStart_7423653 := by decide
  rcases family_descends (prefixWord ++ tailWord_7423653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7423723 : List Nat := [1, 1, 1, 1, 2, 4, 3, 1, 1, 1, 7]
def baseStart_7423723 : Nat := 118140960795 + 7423723 * 2 ^ 59
def prefixEnd_7423723 : Nat := 4983230072969 + 3 ^ 40 * 7423723 * 2
def baseEnd_7423723 : Nat := 3811938144837763383321425

theorem tailTrace_7423723 : CollatzResearch.WordTrace tailWord_7423723 prefixEnd_7423723 3811938144837763383321425 := by
  unfold tailWord_7423723
  simp only [CollatzResearch.WordTrace]
  refine ⟨270765422084126916793147823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180510281389417944528765215 270765422084126916793147823)
  ·
    refine ⟨406148133126190375189721735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270765422084126916793147823 406148133126190375189721735)
    ·
      refine ⟨609222199689285562784582603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 406148133126190375189721735 609222199689285562784582603)
      ·
        refine ⟨913833299533928344176873905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 609222199689285562784582603 913833299533928344176873905)
        ·
          refine ⟨685374974650446258132655429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 913833299533928344176873905 685374974650446258132655429)
          ·
            refine ⟨128507807746958673399872893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 685374974650446258132655429 128507807746958673399872893)
            ·
              refine ⟨48190427905109502524952335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128507807746958673399872893 48190427905109502524952335)
              ·
                refine ⟨72285641857664253787428503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48190427905109502524952335 72285641857664253787428503)
                ·
                  refine ⟨108428462786496380681142755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72285641857664253787428503 108428462786496380681142755)
                  ·
                    refine ⟨162642694179744571021714133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 108428462786496380681142755 162642694179744571021714133)
                    ·
                      refine ⟨3811938144837763383321425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 162642694179744571021714133 3811938144837763383321425)
                      ·
                        rfl

theorem cell23_7423723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 1, 1, 1, 7].length) (baseStart_7423723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7423723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7423723 prefixEnd_7423723 := by exact prefixLift 7423723
  have htrace : WordTrace (prefixWord ++ tailWord_7423723) baseStart_7423723 baseEnd_7423723 := by
    simpa [prefixWord, tailWord_7423723, baseEnd_7423723] using wordTrace_append hprefix tailTrace_7423723
  have hstable : (prefixWord ++ tailWord_7423723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7423723).length < 2 ^ (prefixWord ++ tailWord_7423723).sum := by decide
  have hdescent : baseEnd_7423723 < baseStart_7423723 := by decide
  rcases family_descends (prefixWord ++ tailWord_7423723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7423730 : List Nat := [3, 2, 1, 3, 1, 1, 1, 2, 4, 5]
def baseStart_7423730 : Nat := 118140960795 + 7423730 * 2 ^ 59
def prefixEnd_7423730 : Nat := 4983230072969 + 3 ^ 40 * 7423730 * 2
def baseEnd_7423730 : Nat := 1270647246400781618644631

theorem tailTrace_7423730 : CollatzResearch.WordTrace tailWord_7423730 prefixEnd_7423730 1270647246400781618644631 := by
  unfold tailWord_7423730
  simp only [CollatzResearch.WordTrace]
  refine ⟨67691419348775389247163161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180510451596734371325768429 67691419348775389247163161)
  ·
    refine ⟨50768564511581541935372371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67691419348775389247163161 50768564511581541935372371)
    ·
      refine ⟨76152846767372312903058557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50768564511581541935372371 76152846767372312903058557)
      ·
        refine ⟨28557317537764617338646959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76152846767372312903058557 28557317537764617338646959)
        ·
          refine ⟨42835976306646926007970439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28557317537764617338646959 42835976306646926007970439)
          ·
            refine ⟨64253964459970389011955659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42835976306646926007970439 64253964459970389011955659)
            ·
              refine ⟨96380946689955583517933489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64253964459970389011955659 96380946689955583517933489)
              ·
                refine ⟨72285710017466687638450117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96380946689955583517933489 72285710017466687638450117)
                ·
                  refine ⟨13553570628275003932209397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72285710017466687638450117 13553570628275003932209397)
                  ·
                    refine ⟨1270647246400781618644631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13553570628275003932209397 1270647246400781618644631)
                    ·
                      rfl

theorem cell23_7423730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 2, 4, 5].length) (baseStart_7423730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7423730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7423730 prefixEnd_7423730 := by exact prefixLift 7423730
  have htrace : WordTrace (prefixWord ++ tailWord_7423730) baseStart_7423730 baseEnd_7423730 := by
    simpa [prefixWord, tailWord_7423730, baseEnd_7423730] using wordTrace_append hprefix tailTrace_7423730
  have hstable : (prefixWord ++ tailWord_7423730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7423730).length < 2 ^ (prefixWord ++ tailWord_7423730).sum := by decide
  have hdescent : baseEnd_7423730 < baseStart_7423730 := by decide
  rcases family_descends (prefixWord ++ tailWord_7423730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7423743 : List Nat := [1, 1, 2, 2, 1, 3, 2, 1, 2, 8]
def baseStart_7423743 : Nat := 118140960795 + 7423743 * 2 ^ 59
def prefixEnd_7423743 : Nat := 4983230072969 + 3 ^ 40 * 7423743 * 2
def baseEnd_7423743 : Nat := 1270649471483617768357111

theorem tailTrace_7423743 : CollatzResearch.WordTrace tailWord_7423743 prefixEnd_7423743 1270649471483617768357111 := by
  unfold tailWord_7423743
  simp only [CollatzResearch.WordTrace]
  refine ⟨270766151544054460208875883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180510767696036306805917255 270766151544054460208875883)
  ·
    refine ⟨406149227316081690313313825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270766151544054460208875883 406149227316081690313313825)
    ·
      refine ⟨304611920487061267734985369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 406149227316081690313313825 304611920487061267734985369)
      ·
        refine ⟨228458940365295950801239027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 304611920487061267734985369 228458940365295950801239027)
        ·
          refine ⟨342688410547943926201858541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228458940365295950801239027 342688410547943926201858541)
          ·
            refine ⟨128508153955478972325696953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 342688410547943926201858541 128508153955478972325696953)
            ·
              refine ⟨96381115466609229244272715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128508153955478972325696953 96381115466609229244272715)
              ·
                refine ⟨144571673199913843866409073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96381115466609229244272715 144571673199913843866409073)
                ·
                  refine ⟨108428754899935382899806805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 144571673199913843866409073 108428754899935382899806805)
                  ·
                    refine ⟨1270649471483617768357111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 108428754899935382899806805 1270649471483617768357111)
                    ·
                      rfl

theorem cell23_7423743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 2, 8].length) (baseStart_7423743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7423743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7423743 prefixEnd_7423743 := by exact prefixLift 7423743
  have htrace : WordTrace (prefixWord ++ tailWord_7423743) baseStart_7423743 baseEnd_7423743 := by
    simpa [prefixWord, tailWord_7423743, baseEnd_7423743] using wordTrace_append hprefix tailTrace_7423743
  have hstable : (prefixWord ++ tailWord_7423743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7423743).length < 2 ^ (prefixWord ++ tailWord_7423743).sum := by decide
  have hdescent : baseEnd_7423743 < baseStart_7423743 := by decide
  rcases family_descends (prefixWord ++ tailWord_7423743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7423767 : List Nat := [1, 1, 3, 4, 2, 1, 2, 2, 2, 1, 4]
def baseStart_7423767 : Nat := 118140960795 + 7423767 * 2 ^ 59
def prefixEnd_7423767 : Nat := 4983230072969 + 3 ^ 40 * 7423767 * 2
def baseEnd_7423767 : Nat := 3811960737986561211171223

theorem tailTrace_7423767 : CollatzResearch.WordTrace tailWord_7423767 prefixEnd_7423767 3811960737986561211171223 := by
  unfold tailWord_7423767
  simp only [CollatzResearch.WordTrace]
  refine ⟨270767026895967512307749555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180511351263978341538499703 270767026895967512307749555)
  ·
    refine ⟨406150540343951268461624333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270767026895967512307749555 406150540343951268461624333)
    ·
      refine ⟨152306452628981725673109125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 406150540343951268461624333 152306452628981725673109125)
      ·
        refine ⟨28557459867934073563707961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 152306452628981725673109125 28557459867934073563707961)
        ·
          refine ⟨21418094900950555172780971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28557459867934073563707961 21418094900950555172780971)
          ·
            refine ⟨32127142351425832759171457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21418094900950555172780971 32127142351425832759171457)
            ·
              refine ⟨24095356763569374569378593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32127142351425832759171457 24095356763569374569378593)
              ·
                refine ⟨18071517572677030927033945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24095356763569374569378593 18071517572677030927033945)
                ·
                  refine ⟨13553638179507773195275459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18071517572677030927033945 13553638179507773195275459)
                  ·
                    refine ⟨20330457269261659792913189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13553638179507773195275459 20330457269261659792913189)
                    ·
                      refine ⟨3811960737986561211171223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20330457269261659792913189 3811960737986561211171223)
                      ·
                        rfl

theorem cell23_7423767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_7423767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7423767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7423767 prefixEnd_7423767 := by exact prefixLift 7423767
  have htrace : WordTrace (prefixWord ++ tailWord_7423767) baseStart_7423767 baseEnd_7423767 := by
    simpa [prefixWord, tailWord_7423767, baseEnd_7423767] using wordTrace_append hprefix tailTrace_7423767
  have hstable : (prefixWord ++ tailWord_7423767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7423767).length < 2 ^ (prefixWord ++ tailWord_7423767).sum := by decide
  have hdescent : baseEnd_7423767 < baseStart_7423767 := by decide
  rcases family_descends (prefixWord ++ tailWord_7423767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7423784 : List Nat := [2, 1, 5, 1, 1, 3, 1, 1, 2, 4, 2]
def baseStart_7423784 : Nat := 118140960795 + 7423784 * 2 ^ 59
def prefixEnd_7423784 : Nat := 4983230072969 + 3 ^ 40 * 7423784 * 2
def baseEnd_7423784 : Nat := 3811969467157687644658645

theorem tailTrace_7423784 : CollatzResearch.WordTrace tailWord_7423784 prefixEnd_7423784 3811969467157687644658645 := by
  unfold tailWord_7423784
  simp only [CollatzResearch.WordTrace]
  refine ⟨135383823468452962105559203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180511764624603949474078937 135383823468452962105559203)
  ·
    refine ⟨203075735202679443158338805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135383823468452962105559203 203075735202679443158338805)
    ·
      refine ⟨19038350175251197796094263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 203075735202679443158338805 19038350175251197796094263)
      ·
        refine ⟨28557525262876796694141395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19038350175251197796094263 28557525262876796694141395)
        ·
          refine ⟨42836287894315195041212093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28557525262876796694141395 42836287894315195041212093)
          ·
            refine ⟨16063607960368198140454535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42836287894315195041212093 16063607960368198140454535)
            ·
              refine ⟨24095411940552297210681803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16063607960368198140454535 24095411940552297210681803)
              ·
                refine ⟨36143117910828445816022705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24095411940552297210681803 36143117910828445816022705)
                ·
                  refine ⟨27107338433121334362017029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36143117910828445816022705 27107338433121334362017029)
                  ·
                    refine ⟨5082625956210250192878193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27107338433121334362017029 5082625956210250192878193)
                    ·
                      refine ⟨3811969467157687644658645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5082625956210250192878193 3811969467157687644658645)
                      ·
                        rfl

theorem cell23_7423784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 1, 2, 4, 2].length) (baseStart_7423784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7423784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7423784 prefixEnd_7423784 := by exact prefixLift 7423784
  have htrace : WordTrace (prefixWord ++ tailWord_7423784) baseStart_7423784 baseEnd_7423784 := by
    simpa [prefixWord, tailWord_7423784, baseEnd_7423784] using wordTrace_append hprefix tailTrace_7423784
  have hstable : (prefixWord ++ tailWord_7423784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7423784).length < 2 ^ (prefixWord ++ tailWord_7423784).sum := by decide
  have hdescent : baseEnd_7423784 < baseStart_7423784 := by decide
  rcases family_descends (prefixWord ++ tailWord_7423784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7423801 : List Nat := [1, 2, 1, 7, 1, 2, 1, 1, 2, 1, 4]
def baseStart_7423801 : Nat := 118140960795 + 7423801 * 2 ^ 59
def prefixEnd_7423801 : Nat := 4983230072969 + 3 ^ 40 * 7423801 * 2
def baseEnd_7423801 : Nat := 3811978196328814078146067

theorem tailTrace_7423801 : CollatzResearch.WordTrace tailWord_7423801 prefixEnd_7423801 3811978196328814078146067 := by
  unfold tailWord_7423801
  simp only [CollatzResearch.WordTrace]
  refine ⟨270768266977844336114487257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180512177985229557409658171 270768266977844336114487257)
  ·
    refine ⟨203076200233383252085865443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270768266977844336114487257 203076200233383252085865443)
    ·
      refine ⟨304614300350074878128798165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203076200233383252085865443 304614300350074878128798165)
      ·
        refine ⟨7139397664454879956143707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 304614300350074878128798165 7139397664454879956143707)
        ·
          refine ⟨10709096496682319934215561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7139397664454879956143707 10709096496682319934215561)
          ·
            refine ⟨8031822372511739950661671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10709096496682319934215561 8031822372511739950661671)
            ·
              refine ⟨12047733558767609925992507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8031822372511739950661671 12047733558767609925992507)
              ·
                refine ⟨18071600338151414888988761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12047733558767609925992507 18071600338151414888988761)
                ·
                  refine ⟨13553700253613561166741571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18071600338151414888988761 13553700253613561166741571)
                  ·
                    refine ⟨20330550380420341750112357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13553700253613561166741571 20330550380420341750112357)
                    ·
                      refine ⟨3811978196328814078146067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20330550380420341750112357 3811978196328814078146067)
                      ·
                        rfl

theorem cell23_7423801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_7423801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7423801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7423801 prefixEnd_7423801 := by exact prefixLift 7423801
  have htrace : WordTrace (prefixWord ++ tailWord_7423801) baseStart_7423801 baseEnd_7423801 := by
    simpa [prefixWord, tailWord_7423801, baseEnd_7423801] using wordTrace_append hprefix tailTrace_7423801
  have hstable : (prefixWord ++ tailWord_7423801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7423801).length < 2 ^ (prefixWord ++ tailWord_7423801).sum := by decide
  have hdescent : baseEnd_7423801 < baseStart_7423801 := by decide
  rcases family_descends (prefixWord ++ tailWord_7423801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7423814 : List Nat := [6, 1, 1, 2, 1, 1, 1, 1, 2, 1, 6]
def baseStart_7423814 : Nat := 118140960795 + 7423814 * 2 ^ 59
def prefixEnd_7423814 : Nat := 4983230072969 + 3 ^ 40 * 7423814 * 2
def baseEnd_7423814 : Nat := 3811984871577322527283507

theorem tailTrace_7423814 : CollatzResearch.WordTrace tailWord_7423814 prefixEnd_7423814 3811984871577322527283507 := by
  unfold tailWord_7423814
  simp only [CollatzResearch.WordTrace]
  refine ⟨8461523160212413729209703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 180512494084531492889806997 8461523160212413729209703)
  ·
    refine ⟨12692284740318620593814555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8461523160212413729209703 12692284740318620593814555)
    ·
      refine ⟨19038427110477930890721833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12692284740318620593814555 19038427110477930890721833)
      ·
        refine ⟨14278820332858448168041375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19038427110477930890721833 14278820332858448168041375)
        ·
          refine ⟨21418230499287672252062063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14278820332858448168041375 21418230499287672252062063)
          ·
            refine ⟨32127345748931508378093095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21418230499287672252062063 32127345748931508378093095)
            ·
              refine ⟨48191018623397262567139643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32127345748931508378093095 48191018623397262567139643)
              ·
                refine ⟨72286527935095893850709465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48191018623397262567139643 72286527935095893850709465)
                ·
                  refine ⟨54214895951321920388032099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72286527935095893850709465 54214895951321920388032099)
                  ·
                    refine ⟨81322343926982880582048149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54214895951321920388032099 81322343926982880582048149)
                    ·
                      refine ⟨3811984871577322527283507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81322343926982880582048149 3811984871577322527283507)
                      ·
                        rfl

theorem cell23_7423814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_7423814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7423814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7423814 prefixEnd_7423814 := by exact prefixLift 7423814
  have htrace : WordTrace (prefixWord ++ tailWord_7423814) baseStart_7423814 baseEnd_7423814 := by
    simpa [prefixWord, tailWord_7423814, baseEnd_7423814] using wordTrace_append hprefix tailTrace_7423814
  have hstable : (prefixWord ++ tailWord_7423814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7423814).length < 2 ^ (prefixWord ++ tailWord_7423814).sum := by decide
  have hdescent : baseEnd_7423814 < baseStart_7423814 := by decide
  rcases family_descends (prefixWord ++ tailWord_7423814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7423817 : List Nat := [1, 2, 1, 1, 2, 4, 1, 2, 5, 1, 3]
def baseStart_7423817 : Nat := 118140960795 + 7423817 * 2 ^ 59
def prefixEnd_7423817 : Nat := 4983230072969 + 3 ^ 40 * 7423817 * 2
def baseEnd_7423817 : Nat := 3811986412019286015545993

theorem tailTrace_7423817 : CollatzResearch.WordTrace tailWord_7423817 prefixEnd_7423817 3811986412019286015545993 := by
  unfold tailWord_7423817
  simp only [CollatzResearch.WordTrace]
  refine ⟨270768850545786370847069705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180512567030524247231379803 270768850545786370847069705)
  ·
    refine ⟨203076637909339778135302279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270768850545786370847069705 203076637909339778135302279)
    ·
      refine ⟨304614956864009667202953419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203076637909339778135302279 304614956864009667202953419)
      ·
        refine ⟨456922435296014500804430129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304614956864009667202953419 456922435296014500804430129)
        ·
          refine ⟨342691826472010875603322597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 456922435296014500804430129 342691826472010875603322597)
          ·
            refine ⟨64254717463502039175622987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 342691826472010875603322597 64254717463502039175622987)
            ·
              refine ⟨96382076195253058763434481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64254717463502039175622987 96382076195253058763434481)
              ·
                refine ⟨72286557146439794072575861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96382076195253058763434481 72286557146439794072575861)
                ·
                  refine ⟨6776864732478730694303987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 72286557146439794072575861 6776864732478730694303987)
                  ·
                    refine ⟨10165297098718096041455981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6776864732478730694303987 10165297098718096041455981)
                    ·
                      refine ⟨3811986412019286015545993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10165297098718096041455981 3811986412019286015545993)
                      ·
                        rfl

theorem cell23_7423817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 2, 5, 1, 3].length) (baseStart_7423817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7423817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7423817 prefixEnd_7423817 := by exact prefixLift 7423817
  have htrace : WordTrace (prefixWord ++ tailWord_7423817) baseStart_7423817 baseEnd_7423817 := by
    simpa [prefixWord, tailWord_7423817, baseEnd_7423817] using wordTrace_append hprefix tailTrace_7423817
  have hstable : (prefixWord ++ tailWord_7423817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7423817).length < 2 ^ (prefixWord ++ tailWord_7423817).sum := by decide
  have hdescent : baseEnd_7423817 < baseStart_7423817 := by decide
  rcases family_descends (prefixWord ++ tailWord_7423817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7423834 : List Nat := [3, 1, 1, 2, 1, 3, 4, 1, 3, 1, 3]
def baseStart_7423834 : Nat := 118140960795 + 7423834 * 2 ^ 59
def prefixEnd_7423834 : Nat := 4983230072969 + 3 ^ 40 * 7423834 * 2
def baseEnd_7423834 : Nat := 3811995141190412449033415

theorem tailTrace_7423834 : CollatzResearch.WordTrace tailWord_7423834 prefixEnd_7423834 3811995141190412449033415 := by
  unfold tailWord_7423834
  simp only [CollatzResearch.WordTrace]
  refine ⟨67692367646681195687609639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180512980391149855166959037 67692367646681195687609639)
  ·
    refine ⟨101538551470021793531414459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67692367646681195687609639 101538551470021793531414459)
    ·
      refine ⟨152307827205032690297121689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101538551470021793531414459 152307827205032690297121689)
      ·
        refine ⟨114230870403774517722841267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152307827205032690297121689 114230870403774517722841267)
        ·
          refine ⟨171346305605661776584261901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114230870403774517722841267 171346305605661776584261901)
          ·
            refine ⟨64254864602123166219098213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 171346305605661776584261901 64254864602123166219098213)
            ·
              refine ⟨12047787112898093666080915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64254864602123166219098213 12047787112898093666080915)
              ·
                refine ⟨18071680669347140499121373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12047787112898093666080915 18071680669347140499121373)
                ·
                  refine ⟨6776880251005177687170515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18071680669347140499121373 6776880251005177687170515)
                  ·
                    refine ⟨10165320376507766530755773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6776880251005177687170515 10165320376507766530755773)
                    ·
                      refine ⟨3811995141190412449033415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10165320376507766530755773 3811995141190412449033415)
                      ·
                        rfl

theorem cell23_7423834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 4, 1, 3, 1, 3].length) (baseStart_7423834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7423834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7423834 prefixEnd_7423834 := by exact prefixLift 7423834
  have htrace : WordTrace (prefixWord ++ tailWord_7423834) baseStart_7423834 baseEnd_7423834 := by
    simpa [prefixWord, tailWord_7423834, baseEnd_7423834] using wordTrace_append hprefix tailTrace_7423834
  have hstable : (prefixWord ++ tailWord_7423834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7423834).length < 2 ^ (prefixWord ++ tailWord_7423834).sum := by decide
  have hdescent : baseEnd_7423834 < baseStart_7423834 := by decide
  rcases family_descends (prefixWord ++ tailWord_7423834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7423854 : List Nat := [4, 1, 2, 3, 1, 1, 1, 4, 1, 5]
def baseStart_7423854 : Nat := 118140960795 + 7423854 * 2 ^ 59
def prefixEnd_7423854 : Nat := 4983230072969 + 3 ^ 40 * 7423854 * 2
def baseEnd_7423854 : Nat := 1270668470267834123594441

theorem tailTrace_7423854 : CollatzResearch.WordTrace tailWord_7423854 prefixEnd_7423854 1270668470267834123594441 := by
  unfold tailWord_7423854
  simp only [CollatzResearch.WordTrace]
  refine ⟨33846275005831540770770827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180513466697768217444111077 33846275005831540770770827)
  ·
    refine ⟨50769412508747311156156241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33846275005831540770770827 50769412508747311156156241)
    ·
      refine ⟨38077059381560483367117181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50769412508747311156156241 38077059381560483367117181)
      ·
        refine ⟨14278897268085181262668943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38077059381560483367117181 14278897268085181262668943)
        ·
          refine ⟨21418345902127771894003415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14278897268085181262668943 21418345902127771894003415)
          ·
            refine ⟨32127518853191657841005123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21418345902127771894003415 32127518853191657841005123)
            ·
              refine ⟨48191278279787486761507685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32127518853191657841005123 48191278279787486761507685)
              ·
                refine ⟨9035864677460153767782691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48191278279787486761507685 9035864677460153767782691)
                ·
                  refine ⟨13553797016190230651674037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9035864677460153767782691 13553797016190230651674037)
                  ·
                    refine ⟨1270668470267834123594441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13553797016190230651674037 1270668470267834123594441)
                    ·
                      rfl

theorem cell23_7423854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 4, 1, 5].length) (baseStart_7423854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7423854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7423854 prefixEnd_7423854 := by exact prefixLift 7423854
  have htrace : WordTrace (prefixWord ++ tailWord_7423854) baseStart_7423854 baseEnd_7423854 := by
    simpa [prefixWord, tailWord_7423854, baseEnd_7423854] using wordTrace_append hprefix tailTrace_7423854
  have hstable : (prefixWord ++ tailWord_7423854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7423854).length < 2 ^ (prefixWord ++ tailWord_7423854).sum := by decide
  have hdescent : baseEnd_7423854 < baseStart_7423854 := by decide
  rcases family_descends (prefixWord ++ tailWord_7423854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7423857 : List Nat := [1, 2, 2, 2, 1, 3, 1, 1, 2, 6, 2]
def baseStart_7423857 : Nat := 118140960795 + 7423857 * 2 ^ 59
def prefixEnd_7423857 : Nat := 4983230072969 + 3 ^ 40 * 7423857 * 2
def baseEnd_7423857 : Nat := 3812006951245465859045809

theorem tailTrace_7423857 : CollatzResearch.WordTrace tailWord_7423857 prefixEnd_7423857 3812006951245465859045809 := by
  unfold tailWord_7423857
  simp only [CollatzResearch.WordTrace]
  refine ⟨270770309465641457678525825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180513539643760971785683883 270770309465641457678525825)
  ·
    refine ⟨203077732099231093258894369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270770309465641457678525825 203077732099231093258894369)
    ·
      refine ⟨152308299074423319944170777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203077732099231093258894369 152308299074423319944170777)
      ·
        refine ⟨114231224305817489958128083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152308299074423319944170777 114231224305817489958128083)
        ·
          refine ⟨171346836458726234937192125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114231224305817489958128083 171346836458726234937192125)
          ·
            refine ⟨64255063672022338101447047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 171346836458726234937192125 64255063672022338101447047)
            ·
              refine ⟨96382595508033507152170571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64255063672022338101447047 96382595508033507152170571)
              ·
                refine ⟨144573893262050260728255857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96382595508033507152170571 144573893262050260728255857)
                ·
                  refine ⟨108430419946537695546191893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 144573893262050260728255857 108430419946537695546191893)
                  ·
                    refine ⟨5082675934993954478727745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 108430419946537695546191893 5082675934993954478727745)
                    ·
                      refine ⟨3812006951245465859045809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5082675934993954478727745 3812006951245465859045809)
                      ·
                        rfl

theorem cell23_7423857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 2, 6, 2].length) (baseStart_7423857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7423857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7423857 prefixEnd_7423857 := by exact prefixLift 7423857
  have htrace : WordTrace (prefixWord ++ tailWord_7423857) baseStart_7423857 baseEnd_7423857 := by
    simpa [prefixWord, tailWord_7423857, baseEnd_7423857] using wordTrace_append hprefix tailTrace_7423857
  have hstable : (prefixWord ++ tailWord_7423857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7423857).length < 2 ^ (prefixWord ++ tailWord_7423857).sum := by decide
  have hdescent : baseEnd_7423857 < baseStart_7423857 := by decide
  rcases family_descends (prefixWord ++ tailWord_7423857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7423877 : List Nat := [1, 3, 1, 1, 3, 2, 4, 1, 1, 1, 5]
def baseStart_7423877 : Nat := 118140960795 + 7423877 * 2 ^ 59
def prefixEnd_7423877 : Nat := 4983230072969 + 3 ^ 40 * 7423877 * 2
def baseEnd_7423877 : Nat := 3812017220858555780795717

theorem tailTrace_7423877 : CollatzResearch.WordTrace tailWord_7423877 prefixEnd_7423877 3812017220858555780795717 := by
  unfold tailWord_7423877
  simp only [CollatzResearch.WordTrace]
  refine ⟨270771038925569001094253885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180514025950379334062835923 270771038925569001094253885)
  ·
    refine ⟨101539139597088375410345207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 270771038925569001094253885 101539139597088375410345207)
    ·
      refine ⟨152308709395632563115517811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101539139597088375410345207 152308709395632563115517811)
      ·
        refine ⟨228463064093448844673276717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152308709395632563115517811 228463064093448844673276717)
        ·
          refine ⟨85673649035043316752478769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 228463064093448844673276717 85673649035043316752478769)
          ·
            refine ⟨64255236776282487564359077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85673649035043316752478769 64255236776282487564359077)
            ·
              refine ⟨12047856895552966418317327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64255236776282487564359077 12047856895552966418317327)
              ·
                refine ⟨18071785343329449627475991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12047856895552966418317327 18071785343329449627475991)
                ·
                  refine ⟨27107678014994174441213987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18071785343329449627475991 27107678014994174441213987)
                  ·
                    refine ⟨40661517022491261661820981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27107678014994174441213987 40661517022491261661820981)
                    ·
                      refine ⟨3812017220858555780795717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40661517022491261661820981 3812017220858555780795717)
                      ·
                        rfl

theorem cell23_7423877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 4, 1, 1, 1, 5].length) (baseStart_7423877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7423877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7423877 prefixEnd_7423877 := by exact prefixLift 7423877
  have htrace : WordTrace (prefixWord ++ tailWord_7423877) baseStart_7423877 baseEnd_7423877 := by
    simpa [prefixWord, tailWord_7423877, baseEnd_7423877] using wordTrace_append hprefix tailTrace_7423877
  have hstable : (prefixWord ++ tailWord_7423877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7423877).length < 2 ^ (prefixWord ++ tailWord_7423877).sum := by decide
  have hdescent : baseEnd_7423877 < baseStart_7423877 := by decide
  rcases family_descends (prefixWord ++ tailWord_7423877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7423901 : List Nat := [1, 4, 2, 1, 2, 2, 4, 1, 2, 4]
def baseStart_7423901 : Nat := 118140960795 + 7423901 * 2 ^ 59
def prefixEnd_7423901 : Nat := 4983230072969 + 3 ^ 40 * 7423901 * 2
def baseEnd_7423901 : Nat := 1270676514798087895631869

theorem tailTrace_7423901 : CollatzResearch.WordTrace tailWord_7423901 prefixEnd_7423901 1270676514798087895631869 := by
  unfold tailWord_7423901
  simp only [CollatzResearch.WordTrace]
  refine ⟨270771914277482053193127557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180514609518321368795418371 270771914277482053193127557)
  ·
    refine ⟨50769733927027884973711417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 270771914277482053193127557 50769733927027884973711417)
    ·
      refine ⟨38077300445270913730283563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50769733927027884973711417 38077300445270913730283563)
      ·
        refine ⟨57115950667906370595425345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38077300445270913730283563 57115950667906370595425345)
        ·
          refine ⟨42836963000929777946569009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57115950667906370595425345 42836963000929777946569009)
          ·
            refine ⟨32127722250697333459926757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42836963000929777946569009 32127722250697333459926757)
            ·
              refine ⟨6023947922005750023736267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32127722250697333459926757 6023947922005750023736267)
              ·
                refine ⟨9035921883008625035604401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6023947922005750023736267 9035921883008625035604401)
                ·
                  refine ⟨6776941412256468776703301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9035921883008625035604401 6776941412256468776703301)
                  ·
                    refine ⟨1270676514798087895631869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6776941412256468776703301 1270676514798087895631869)
                    ·
                      rfl

theorem cell23_7423901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 4, 1, 2, 4].length) (baseStart_7423901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7423901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7423901 prefixEnd_7423901 := by exact prefixLift 7423901
  have htrace : WordTrace (prefixWord ++ tailWord_7423901) baseStart_7423901 baseEnd_7423901 := by
    simpa [prefixWord, tailWord_7423901, baseEnd_7423901] using wordTrace_append hprefix tailTrace_7423901
  have hstable : (prefixWord ++ tailWord_7423901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7423901).length < 2 ^ (prefixWord ++ tailWord_7423901).sum := by decide
  have hdescent : baseEnd_7423901 < baseStart_7423901 := by decide
  rcases family_descends (prefixWord ++ tailWord_7423901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7423907 : List Nat := [1, 1, 1, 4, 1, 2, 1, 5, 1, 3, 3]
def baseStart_7423907 : Nat := 118140960795 + 7423907 * 2 ^ 59
def prefixEnd_7423907 : Nat := 4983230072969 + 3 ^ 40 * 7423907 * 2
def baseEnd_7423907 : Nat := 3812032625278190663420579

theorem tailTrace_7423907 : CollatzResearch.WordTrace tailWord_7423907 prefixEnd_7423907 3812032625278190663420579 := by
  unfold tailWord_7423907
  simp only [CollatzResearch.WordTrace]
  refine ⟨270772133115460316217845975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180514755410306877478563983 270772133115460316217845975)
  ·
    refine ⟨406158199673190474326768963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270772133115460316217845975 406158199673190474326768963)
    ·
      refine ⟨609237299509785711490153445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 406158199673190474326768963 609237299509785711490153445)
      ·
        refine ⟨114231993658084820904403771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 609237299509785711490153445 114231993658084820904403771)
        ·
          refine ⟨171347990487127231356605657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114231993658084820904403771 171347990487127231356605657)
          ·
            refine ⟨128510992865345423517454243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171347990487127231356605657 128510992865345423517454243)
            ·
              refine ⟨192766489298018135276181365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128510992865345423517454243 192766489298018135276181365)
              ·
                refine ⟨18071858371689200182142003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 192766489298018135276181365 18071858371689200182142003)
                ·
                  refine ⟨27107787557533800273213005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18071858371689200182142003 27107787557533800273213005)
                  ·
                    refine ⟨10165420334075175102454877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27107787557533800273213005 10165420334075175102454877)
                    ·
                      refine ⟨3812032625278190663420579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10165420334075175102454877 3812032625278190663420579)
                      ·
                        rfl

theorem cell23_7423907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 5, 1, 3, 3].length) (baseStart_7423907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7423907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7423907 prefixEnd_7423907 := by exact prefixLift 7423907
  have htrace : WordTrace (prefixWord ++ tailWord_7423907) baseStart_7423907 baseEnd_7423907 := by
    simpa [prefixWord, tailWord_7423907, baseEnd_7423907] using wordTrace_append hprefix tailTrace_7423907
  have hstable : (prefixWord ++ tailWord_7423907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7423907).length < 2 ^ (prefixWord ++ tailWord_7423907).sum := by decide
  have hdescent : baseEnd_7423907 < baseStart_7423907 := by decide
  rcases family_descends (prefixWord ++ tailWord_7423907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7423911 : List Nat := [1, 1, 6, 1, 2, 1, 3, 2, 1, 2, 3]
def baseStart_7423911 : Nat := 118140960795 + 7423911 * 2 ^ 59
def prefixEnd_7423911 : Nat := 4983230072969 + 3 ^ 40 * 7423911 * 2
def baseEnd_7423911 : Nat := 3812034679200808647770561

theorem tailTrace_7423911 : CollatzResearch.WordTrace tailWord_7423911 prefixEnd_7423911 3812034679200808647770561 := by
  unfold tailWord_7423911
  simp only [CollatzResearch.WordTrace]
  refine ⟨270772279007445824900991587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180514852671630549933994391 270772279007445824900991587)
  ·
    refine ⟨406158418511168737351487381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270772279007445824900991587 406158418511168737351487381)
    ·
      refine ⟨19038675867711034563350971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 406158418511168737351487381 19038675867711034563350971)
      ·
        refine ⟨28558013801566551845026457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19038675867711034563350971 28558013801566551845026457)
        ·
          refine ⟨21418510351174913883769843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28558013801566551845026457 21418510351174913883769843)
          ·
            refine ⟨32127765526762370825654765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21418510351174913883769843 32127765526762370825654765)
            ·
              refine ⟨12047912072535889059620537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32127765526762370825654765 12047912072535889059620537)
              ·
                refine ⟨9035934054401916794715403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12047912072535889059620537 9035934054401916794715403)
                ·
                  refine ⟨13553901081602875192073105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9035934054401916794715403 13553901081602875192073105)
                  ·
                    refine ⟨10165425811202156394054829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13553901081602875192073105 10165425811202156394054829)
                    ·
                      refine ⟨3812034679200808647770561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10165425811202156394054829 3812034679200808647770561)
                      ·
                        rfl

theorem cell23_7423911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 3, 2, 1, 2, 3].length) (baseStart_7423911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7423911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7423911 prefixEnd_7423911 := by exact prefixLift 7423911
  have htrace : WordTrace (prefixWord ++ tailWord_7423911) baseStart_7423911 baseEnd_7423911 := by
    simpa [prefixWord, tailWord_7423911, baseEnd_7423911] using wordTrace_append hprefix tailTrace_7423911
  have hstable : (prefixWord ++ tailWord_7423911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7423911).length < 2 ^ (prefixWord ++ tailWord_7423911).sum := by decide
  have hdescent : baseEnd_7423911 < baseStart_7423911 := by decide
  rcases family_descends (prefixWord ++ tailWord_7423911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7423918 : List Nat := [4, 1, 5, 1, 1, 1, 1, 2, 1, 6]
def baseStart_7423918 : Nat := 118140960795 + 7423918 * 2 ^ 59
def prefixEnd_7423918 : Nat := 4983230072969 + 3 ^ 40 * 7423918 * 2
def baseEnd_7423918 : Nat := 1270679424521796706794343

theorem tailTrace_7423918 : CollatzResearch.WordTrace tailWord_7423918 prefixEnd_7423918 1270679424521796706794343 := by
  unfold tailWord_7423918
  simp only [CollatzResearch.WordTrace]
  refine ⟨33846566789802558137062051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180515022878946976730997605 33846566789802558137062051)
  ·
    refine ⟨50769850184703837205593077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33846566789802558137062051 50769850184703837205593077)
    ·
      refine ⟨4759673454815984738024351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 50769850184703837205593077 4759673454815984738024351)
      ·
        refine ⟨7139510182223977107036527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4759673454815984738024351 7139510182223977107036527)
        ·
          refine ⟨10709265273335965660554791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7139510182223977107036527 10709265273335965660554791)
          ·
            refine ⟨16063897910003948490832187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10709265273335965660554791 16063897910003948490832187)
            ·
              refine ⟨24095846865005922736248281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16063897910003948490832187 24095846865005922736248281)
              ·
                refine ⟨18071885148754442052186211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24095846865005922736248281 18071885148754442052186211)
                ·
                  refine ⟨27107827723131663078279317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18071885148754442052186211 27107827723131663078279317)
                  ·
                    refine ⟨1270679424521796706794343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27107827723131663078279317 1270679424521796706794343)
                    ·
                      rfl

theorem cell23_7423918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_7423918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7423918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7423918 prefixEnd_7423918 := by exact prefixLift 7423918
  have htrace : WordTrace (prefixWord ++ tailWord_7423918) baseStart_7423918 baseEnd_7423918 := by
    simpa [prefixWord, tailWord_7423918, baseEnd_7423918] using wordTrace_append hprefix tailTrace_7423918
  have hstable : (prefixWord ++ tailWord_7423918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7423918).length < 2 ^ (prefixWord ++ tailWord_7423918).sum := by decide
  have hdescent : baseEnd_7423918 < baseStart_7423918 := by decide
  rcases family_descends (prefixWord ++ tailWord_7423918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7423957 : List Nat := [1, 3, 2, 3, 2, 1, 1, 1, 1, 8]
def baseStart_7423957 : Nat := 118140960795 + 7423957 * 2 ^ 59
def prefixEnd_7423957 : Nat := 4983230072969 + 3 ^ 40 * 7423957 * 2
def baseEnd_7423957 : Nat := 1270686099770305155931783

theorem tailTrace_7423957 : CollatzResearch.WordTrace tailWord_7423957 prefixEnd_7423957 1270686099770305155931783 := by
  unfold tailWord_7423957
  simp only [CollatzResearch.WordTrace]
  refine ⟨270773956765279174757166125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180515971176852783171444083 270773956765279174757166125)
  ·
    refine ⟨101540233786979690533937297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 270773956765279174757166125 101540233786979690533937297)
    ·
      refine ⟨76155175340234767900452973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101540233786979690533937297 76155175340234767900452973)
      ·
        refine ⟨28558190752588037962669865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76155175340234767900452973 28558190752588037962669865)
        ·
          refine ⟨21418643064441028472002399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28558190752588037962669865 21418643064441028472002399)
          ·
            refine ⟨32127964596661542708003599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21418643064441028472002399 32127964596661542708003599)
            ·
              refine ⟨48191946894992314062005399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32127964596661542708003599 48191946894992314062005399)
              ·
                refine ⟨72287920342488471093008099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48191946894992314062005399 72287920342488471093008099)
                ·
                  refine ⟨108431880513732706639512149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72287920342488471093008099 108431880513732706639512149)
                  ·
                    refine ⟨1270686099770305155931783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 108431880513732706639512149 1270686099770305155931783)
                    ·
                      rfl

theorem cell23_7423957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 1, 1, 8].length) (baseStart_7423957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7423957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7423957 prefixEnd_7423957 := by exact prefixLift 7423957
  have htrace : WordTrace (prefixWord ++ tailWord_7423957) baseStart_7423957 baseEnd_7423957 := by
    simpa [prefixWord, tailWord_7423957, baseEnd_7423957] using wordTrace_append hprefix tailTrace_7423957
  have hstable : (prefixWord ++ tailWord_7423957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7423957).length < 2 ^ (prefixWord ++ tailWord_7423957).sum := by decide
  have hdescent : baseEnd_7423957 < baseStart_7423957 := by decide
  rcases family_descends (prefixWord ++ tailWord_7423957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7423958 : List Nat := [5, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3]
def baseStart_7423958 : Nat := 118140960795 + 7423958 * 2 ^ 59
def prefixEnd_7423958 : Nat := 4983230072969 + 3 ^ 40 * 7423958 * 2
def baseEnd_7423958 : Nat := 3812058812791569963882845

theorem tailTrace_7423958 : CollatzResearch.WordTrace tailWord_7423958 prefixEnd_7423958 3812058812791569963882845 := by
  unfold tailWord_7423958
  simp only [CollatzResearch.WordTrace]
  refine ⟨16923374577392221995497033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 180515995492183701285301685 16923374577392221995497033)
  ·
    refine ⟨12692530933044166496622775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16923374577392221995497033 12692530933044166496622775)
    ·
      refine ⟨19038796399566249744934163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12692530933044166496622775 19038796399566249744934163)
      ·
        refine ⟨28558194599349374617401245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19038796399566249744934163 28558194599349374617401245)
        ·
          refine ⟨10709322974756015481525467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28558194599349374617401245 10709322974756015481525467)
          ·
            refine ⟨16063984462134023222288201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10709322974756015481525467 16063984462134023222288201)
            ·
              refine ⟨12047988346600517416716151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16063984462134023222288201 12047988346600517416716151)
              ·
                refine ⟨18071982519900776125074227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12047988346600517416716151 18071982519900776125074227)
                ·
                  refine ⟨27107973779851164187611341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18071982519900776125074227 27107973779851164187611341)
                  ·
                    refine ⟨10165490167444186570354253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27107973779851164187611341 10165490167444186570354253)
                    ·
                      refine ⟨3812058812791569963882845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10165490167444186570354253 3812058812791569963882845)
                      ·
                        rfl

theorem cell23_7423958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3].length) (baseStart_7423958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7423958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7423958 prefixEnd_7423958 := by exact prefixLift 7423958
  have htrace : WordTrace (prefixWord ++ tailWord_7423958) baseStart_7423958 baseEnd_7423958 := by
    simpa [prefixWord, tailWord_7423958, baseEnd_7423958] using wordTrace_append hprefix tailTrace_7423958
  have hstable : (prefixWord ++ tailWord_7423958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7423958).length < 2 ^ (prefixWord ++ tailWord_7423958).sum := by decide
  have hdescent : baseEnd_7423958 < baseStart_7423958 := by decide
  rcases family_descends (prefixWord ++ tailWord_7423958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7423985 : List Nat := [1, 2, 2, 2, 5, 2, 2, 1, 1, 3, 2]
def baseStart_7423985 : Nat := 118140960795 + 7423985 * 2 ^ 59
def prefixEnd_7423985 : Nat := 4983230072969 + 3 ^ 40 * 7423985 * 2
def baseEnd_7423985 : Nat := 3812072676769241358245221

theorem tailTrace_7423985 : CollatzResearch.WordTrace tailWord_7423985 prefixEnd_7423985 3812072676769241358245221 := by
  unfold tailWord_7423985
  simp only [CollatzResearch.WordTrace]
  refine ⟨270774978009177735539185409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180516652006118490359456939 270774978009177735539185409)
  ·
    refine ⟨203081233506883301654389057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270774978009177735539185409 203081233506883301654389057)
    ·
      refine ⟨152310925130162476240791793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203081233506883301654389057 152310925130162476240791793)
      ·
        refine ⟨114233193847621857180593845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152310925130162476240791793 114233193847621857180593845)
        ·
          refine ⟨10709361923214549110680673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 114233193847621857180593845 10709361923214549110680673)
          ·
            refine ⟨8032021442410911833010505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10709361923214549110680673 8032021442410911833010505)
            ·
              refine ⟨6024016081808183874757879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8032021442410911833010505 6024016081808183874757879)
              ·
                refine ⟨9036024122712275812136819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6024016081808183874757879 9036024122712275812136819)
                ·
                  refine ⟨13554036184068413718205229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9036024122712275812136819 13554036184068413718205229)
                  ·
                    refine ⟨5082763569025655144326961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13554036184068413718205229 5082763569025655144326961)
                    ·
                      refine ⟨3812072676769241358245221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5082763569025655144326961 3812072676769241358245221)
                      ·
                        rfl

theorem cell23_7423985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 2, 2, 1, 1, 3, 2].length) (baseStart_7423985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7423985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7423985 prefixEnd_7423985 := by exact prefixLift 7423985
  have htrace : WordTrace (prefixWord ++ tailWord_7423985) baseStart_7423985 baseEnd_7423985 := by
    simpa [prefixWord, tailWord_7423985, baseEnd_7423985] using wordTrace_append hprefix tailTrace_7423985
  have hstable : (prefixWord ++ tailWord_7423985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7423985).length < 2 ^ (prefixWord ++ tailWord_7423985).sum := by decide
  have hdescent : baseEnd_7423985 < baseStart_7423985 := by decide
  rcases family_descends (prefixWord ++ tailWord_7423985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7424014 : List Nat := [4, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3]
def baseStart_7424014 : Nat := 118140960795 + 7424014 * 2 ^ 59
def prefixEnd_7424014 : Nat := 4983230072969 + 3 ^ 40 * 7424014 * 2
def baseEnd_7424014 : Nat := 3812087567708221744782587

theorem tailTrace_7424014 : CollatzResearch.WordTrace tailWord_7424014 prefixEnd_7424014 3812087567708221744782587 := by
  unfold tailWord_7424014
  simp only [CollatzResearch.WordTrace]
  refine ⟨33847004465759084186498887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180517357150715115661327397 33847004465759084186498887)
  ·
    refine ⟨50770506698638626279748331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33847004465759084186498887 50770506698638626279748331)
    ·
      refine ⟨76155760047957939419622497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50770506698638626279748331 76155760047957939419622497)
      ·
        refine ⟨57116820035968454564716873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76155760047957939419622497 57116820035968454564716873)
        ·
          refine ⟨42837615026976340923537655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57116820035968454564716873 42837615026976340923537655)
          ·
            refine ⟨64256422540464511385306483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42837615026976340923537655 64256422540464511385306483)
            ·
              refine ⟨96384633810696767077959725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64256422540464511385306483 96384633810696767077959725)
              ·
                refine ⟨36144237679011287654234897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96384633810696767077959725 36144237679011287654234897)
                ·
                  refine ⟨27108178259258465740676173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36144237679011287654234897 27108178259258465740676173)
                  ·
                    refine ⟨10165566847221924652753565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27108178259258465740676173 10165566847221924652753565)
                    ·
                      refine ⟨3812087567708221744782587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10165566847221924652753565 3812087567708221744782587)
                      ·
                        rfl

theorem cell23_7424014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3].length) (baseStart_7424014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7424014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7424014 prefixEnd_7424014 := by exact prefixLift 7424014
  have htrace : WordTrace (prefixWord ++ tailWord_7424014) baseStart_7424014 baseEnd_7424014 := by
    simpa [prefixWord, tailWord_7424014, baseEnd_7424014] using wordTrace_append hprefix tailTrace_7424014
  have hstable : (prefixWord ++ tailWord_7424014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7424014).length < 2 ^ (prefixWord ++ tailWord_7424014).sum := by decide
  have hdescent : baseEnd_7424014 < baseStart_7424014 := by decide
  rcases family_descends (prefixWord ++ tailWord_7424014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7424034 : List Nat := [3, 3, 1, 1, 1, 2, 2, 3, 2, 5]
def baseStart_7424034 : Nat := 118140960795 + 7424034 * 2 ^ 59
def prefixEnd_7424034 : Nat := 4983230072969 + 3 ^ 40 * 7424034 * 2
def baseEnd_7424034 : Nat := 1270699279107103888844165

theorem tailTrace_7424034 : CollatzResearch.WordTrace tailWord_7424034 prefixEnd_7424034 1270699279107103888844165 := by
  unfold tailWord_7424034
  simp only [CollatzResearch.WordTrace]
  refine ⟨67694191296500054226929789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180517843457333477938479437 67694191296500054226929789)
  ·
    refine ⟨25385321736187520335098671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67694191296500054226929789 25385321736187520335098671)
    ·
      refine ⟨38077982604281280502648007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25385321736187520335098671 38077982604281280502648007)
      ·
        refine ⟨57116973906421920753972011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38077982604281280502648007 57116973906421920753972011)
        ·
          refine ⟨85675460859632881130958017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57116973906421920753972011 85675460859632881130958017)
          ·
            refine ⟨64256595644724660848218513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85675460859632881130958017 64256595644724660848218513)
            ·
              refine ⟨48192446733543495636163885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64256595644724660848218513 48192446733543495636163885)
              ·
                refine ⟨18072167525078810863561457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48192446733543495636163885 18072167525078810863561457)
                ·
                  refine ⟨13554125643809108147671093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18072167525078810863561457 13554125643809108147671093)
                  ·
                    refine ⟨1270699279107103888844165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13554125643809108147671093 1270699279107103888844165)
                    ·
                      rfl

theorem cell23_7424034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 3, 2, 5].length) (baseStart_7424034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7424034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7424034 prefixEnd_7424034 := by exact prefixLift 7424034
  have htrace : WordTrace (prefixWord ++ tailWord_7424034) baseStart_7424034 baseEnd_7424034 := by
    simpa [prefixWord, tailWord_7424034, baseEnd_7424034] using wordTrace_append hprefix tailTrace_7424034
  have hstable : (prefixWord ++ tailWord_7424034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7424034).length < 2 ^ (prefixWord ++ tailWord_7424034).sum := by decide
  have hdescent : baseEnd_7424034 < baseStart_7424034 := by decide
  rcases family_descends (prefixWord ++ tailWord_7424034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7424067 : List Nat := [1, 1, 1, 3, 1, 2, 2, 2, 2, 4, 4]
def baseStart_7424067 : Nat := 118140960795 + 7424067 * 2 ^ 59
def prefixEnd_7424067 : Nat := 4983230072969 + 3 ^ 40 * 7424067 * 2
def baseEnd_7424067 : Nat := 3812114782182910037419843

theorem tailTrace_7424067 : CollatzResearch.WordTrace tailWord_7424067 prefixEnd_7424067 3812114782182910037419843 := by
  unfold tailWord_7424067
  simp only [CollatzResearch.WordTrace]
  refine ⟨270777968794880663543670455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180518645863253775695780303 270777968794880663543670455)
  ·
    refine ⟨406166953192320995315505683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270777968794880663543670455 406166953192320995315505683)
    ·
      refine ⟨609250429788481492973258525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 406166953192320995315505683 609250429788481492973258525)
      ·
        refine ⟨228468911170680559864971947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 609250429788481492973258525 228468911170680559864971947)
        ·
          refine ⟨342703366756020839797457921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228468911170680559864971947 342703366756020839797457921)
          ·
            refine ⟨257027525067015629848093441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 342703366756020839797457921 257027525067015629848093441)
            ·
              refine ⟨192770643800261722386070081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 257027525067015629848093441 192770643800261722386070081)
              ·
                refine ⟨144577982850196291789552561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 192770643800261722386070081 144577982850196291789552561)
                ·
                  refine ⟨108433487137647218842164421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 144577982850196291789552561 108433487137647218842164421)
                  ·
                    refine ⟨20331278838308853532905829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 108433487137647218842164421 20331278838308853532905829)
                    ·
                      refine ⟨3812114782182910037419843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20331278838308853532905829 3812114782182910037419843)
                      ·
                        rfl

theorem cell23_7424067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 2, 4, 4].length) (baseStart_7424067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7424067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7424067 prefixEnd_7424067 := by exact prefixLift 7424067
  have htrace : WordTrace (prefixWord ++ tailWord_7424067) baseStart_7424067 baseEnd_7424067 := by
    simpa [prefixWord, tailWord_7424067, baseEnd_7424067] using wordTrace_append hprefix tailTrace_7424067
  have hstable : (prefixWord ++ tailWord_7424067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7424067).length < 2 ^ (prefixWord ++ tailWord_7424067).sum := by decide
  have hdescent : baseEnd_7424067 < baseStart_7424067 := by decide
  rcases family_descends (prefixWord ++ tailWord_7424067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7424074 : List Nat := [3, 1, 2, 1, 1, 2, 1, 1, 6, 2, 3]
def baseStart_7424074 : Nat := 118140960795 + 7424074 * 2 ^ 59
def prefixEnd_7424074 : Nat := 4983230072969 + 3 ^ 40 * 7424074 * 2
def baseEnd_7424074 : Nat := 3812118376547491510032311

theorem tailTrace_7424074 : CollatzResearch.WordTrace tailWord_7424074 prefixEnd_7424074 3812118376547491510032311 := by
  unfold tailWord_7424074
  simp only [CollatzResearch.WordTrace]
  refine ⟨67694556026463825934793819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180518816070570202492783517 67694556026463825934793819)
  ·
    refine ⟨101541834039695738902190729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67694556026463825934793819 101541834039695738902190729)
    ·
      refine ⟨76156375529771804176643047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101541834039695738902190729 76156375529771804176643047)
      ·
        refine ⟨114234563294657706264964571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76156375529771804176643047 114234563294657706264964571)
        ·
          refine ⟨171351844941986559397446857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114234563294657706264964571 171351844941986559397446857)
          ·
            refine ⟨128513883706489919548085143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171351844941986559397446857 128513883706489919548085143)
            ·
              refine ⟨192770825559734879322127715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128513883706489919548085143 192770825559734879322127715)
              ·
                refine ⟨289156238339602318983191573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 192770825559734879322127715 289156238339602318983191573)
                ·
                  refine ⟨13554198672168858702337105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 289156238339602318983191573 13554198672168858702337105)
                  ·
                    refine ⟨10165649004126644026752829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13554198672168858702337105 10165649004126644026752829)
                    ·
                      refine ⟨3812118376547491510032311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10165649004126644026752829 3812118376547491510032311)
                      ·
                        rfl

theorem cell23_7424074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 6, 2, 3].length) (baseStart_7424074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7424074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7424074 prefixEnd_7424074 := by exact prefixLift 7424074
  have htrace : WordTrace (prefixWord ++ tailWord_7424074) baseStart_7424074 baseEnd_7424074 := by
    simpa [prefixWord, tailWord_7424074, baseEnd_7424074] using wordTrace_append hprefix tailTrace_7424074
  have hstable : (prefixWord ++ tailWord_7424074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7424074).length < 2 ^ (prefixWord ++ tailWord_7424074).sum := by decide
  have hdescent : baseEnd_7424074 < baseStart_7424074 := by decide
  rcases family_descends (prefixWord ++ tailWord_7424074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7424097 : List Nat := [1, 2, 3, 1, 1, 2, 1, 2, 1, 1, 8]
def baseStart_7424097 : Nat := 118140960795 + 7424097 * 2 ^ 59
def prefixEnd_7424097 : Nat := 4983230072969 + 3 ^ 40 * 7424097 * 2
def baseEnd_7424097 : Nat := 3812130186602544920044705

theorem tailTrace_7424097 : CollatzResearch.WordTrace tailWord_7424097 prefixEnd_7424097 3812130186602544920044705 := by
  unfold tailWord_7424097
  simp only [CollatzResearch.WordTrace]
  refine ⟨270779062984771978667262545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180519375323181319111508363 270779062984771978667262545)
  ·
    refine ⟨203084297238578984000446909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270779062984771978667262545 203084297238578984000446909)
    ·
      refine ⟨76156611464467119000167591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 203084297238578984000446909 76156611464467119000167591)
      ·
        refine ⟨114234917196700678500251387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76156611464467119000167591 114234917196700678500251387)
        ·
          refine ⟨171352375795051017750377081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114234917196700678500251387 171352375795051017750377081)
          ·
            refine ⟨128514281846288263312782811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171352375795051017750377081 128514281846288263312782811)
            ·
              refine ⟨192771422769432394969174217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128514281846288263312782811 192771422769432394969174217)
              ·
                refine ⟨144578567077074296226880663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 192771422769432394969174217 144578567077074296226880663)
                ·
                  refine ⟨216867850615611444340320995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 144578567077074296226880663 216867850615611444340320995)
                  ·
                    refine ⟨325301775923417166510481493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 216867850615611444340320995 325301775923417166510481493)
                    ·
                      refine ⟨3812130186602544920044705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 325301775923417166510481493 3812130186602544920044705)
                      ·
                        rfl

theorem cell23_7424097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 1, 8].length) (baseStart_7424097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7424097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7424097 prefixEnd_7424097 := by exact prefixLift 7424097
  have htrace : WordTrace (prefixWord ++ tailWord_7424097) baseStart_7424097 baseEnd_7424097 := by
    simpa [prefixWord, tailWord_7424097, baseEnd_7424097] using wordTrace_append hprefix tailTrace_7424097
  have hstable : (prefixWord ++ tailWord_7424097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7424097).length < 2 ^ (prefixWord ++ tailWord_7424097).sum := by decide
  have hdescent : baseEnd_7424097 < baseStart_7424097 := by decide
  rcases family_descends (prefixWord ++ tailWord_7424097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7424124 : List Nat := [2, 2, 2, 1, 1, 4, 1, 2, 3, 5]
def baseStart_7424124 : Nat := 118140960795 + 7424124 * 2 ^ 59
def prefixEnd_7424124 : Nat := 4983230072969 + 3 ^ 40 * 7424124 * 2
def baseEnd_7424124 : Nat := 1270714683526738771469027

theorem tailTrace_7424124 : CollatzResearch.WordTrace tailWord_7424124 prefixEnd_7424124 1270714683526738771469027 := by
  unfold tailWord_7424124
  simp only [CollatzResearch.WordTrace]
  refine ⟨135390023877837081139247713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180520031837116108185663617 135390023877837081139247713)
  ·
    refine ⟨101542517908377810854435785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135390023877837081139247713 101542517908377810854435785)
    ·
      refine ⟨76156888431283358140826839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101542517908377810854435785 76156888431283358140826839)
      ·
        refine ⟨114235332646925037211240259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76156888431283358140826839 114235332646925037211240259)
        ·
          refine ⟨171352998970387555816860389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114235332646925037211240259 171352998970387555816860389)
          ·
            refine ⟨32128687306947666715661323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 171352998970387555816860389 32128687306947666715661323)
            ·
              refine ⟨48193030960421500073491985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32128687306947666715661323 48193030960421500073491985)
              ·
                refine ⟨36144773220316125055118989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48193030960421500073491985 36144773220316125055118989)
                ·
                  refine ⟨13554289957618546895669621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36144773220316125055118989 13554289957618546895669621)
                  ·
                    refine ⟨1270714683526738771469027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13554289957618546895669621 1270714683526738771469027)
                    ·
                      rfl

theorem cell23_7424124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 2, 3, 5].length) (baseStart_7424124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7424124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7424124 prefixEnd_7424124 := by exact prefixLift 7424124
  have htrace : WordTrace (prefixWord ++ tailWord_7424124) baseStart_7424124 baseEnd_7424124 := by
    simpa [prefixWord, tailWord_7424124, baseEnd_7424124] using wordTrace_append hprefix tailTrace_7424124
  have hstable : (prefixWord ++ tailWord_7424124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7424124).length < 2 ^ (prefixWord ++ tailWord_7424124).sum := by decide
  have hdescent : baseEnd_7424124 < baseStart_7424124 := by decide
  rcases family_descends (prefixWord ++ tailWord_7424124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7424138 : List Nat := [3, 1, 2, 3, 1, 3, 1, 2, 3, 1, 3]
def baseStart_7424138 : Nat := 118140960795 + 7424138 * 2 ^ 59
def prefixEnd_7424138 : Nat := 4983230072969 + 3 ^ 40 * 7424138 * 2
def baseEnd_7424138 : Nat := 3812151239309379259632017

theorem tailTrace_7424138 : CollatzResearch.WordTrace tailWord_7424138 prefixEnd_7424138 3812151239309379259632017 := by
  unfold tailWord_7424138
  simp only [CollatzResearch.WordTrace]
  refine ⟨67695139594405860667376267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180520372251748961779670045 67695139594405860667376267)
  ·
    refine ⟨101542709391608791001064401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67695139594405860667376267 101542709391608791001064401)
    ·
      refine ⟨76157032043706593250798301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101542709391608791001064401 76157032043706593250798301)
      ·
        refine ⟨28558887016389972469049363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76157032043706593250798301 28558887016389972469049363)
        ·
          refine ⟨42838330524584958703574045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28558887016389972469049363 42838330524584958703574045)
          ·
            refine ⟨16064373946719359513840267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42838330524584958703574045 16064373946719359513840267)
            ·
              refine ⟨24096560920079039270760401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16064373946719359513840267 24096560920079039270760401)
              ·
                refine ⟨18072420690059279453070301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24096560920079039270760401 18072420690059279453070301)
                ·
                  refine ⟨6777157758772229794901363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18072420690059279453070301 6777157758772229794901363)
                  ·
                    refine ⟨10165736638158344692352045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6777157758772229794901363 10165736638158344692352045)
                    ·
                      refine ⟨3812151239309379259632017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10165736638158344692352045 3812151239309379259632017)
                      ·
                        rfl

theorem cell23_7424138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 1, 2, 3, 1, 3].length) (baseStart_7424138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7424138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7424138 prefixEnd_7424138 := by exact prefixLift 7424138
  have htrace : WordTrace (prefixWord ++ tailWord_7424138) baseStart_7424138 baseEnd_7424138 := by
    simpa [prefixWord, tailWord_7424138, baseEnd_7424138] using wordTrace_append hprefix tailTrace_7424138
  have hstable : (prefixWord ++ tailWord_7424138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7424138).length < 2 ^ (prefixWord ++ tailWord_7424138).sum := by decide
  have hdescent : baseEnd_7424138 < baseStart_7424138 := by decide
  rcases family_descends (prefixWord ++ tailWord_7424138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7424144 : List Nat := [2, 1, 1, 1, 1, 1, 5, 3, 3, 1, 4]
def baseStart_7424144 : Nat := 118140960795 + 7424144 * 2 ^ 59
def prefixEnd_7424144 : Nat := 4983230072969 + 3 ^ 40 * 7424144 * 2
def baseEnd_7424144 : Nat := 3812154320193306236156989

theorem tailTrace_7424144 : CollatzResearch.WordTrace tailWord_7424144 prefixEnd_7424144 3812154320193306236156989 := by
  unfold tailWord_7424144
  simp only [CollatzResearch.WordTrace]
  refine ⟨135390388607800852847111743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180520518143734470462815657 135390388607800852847111743)
  ·
    refine ⟨203085582911701279270667615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135390388607800852847111743 203085582911701279270667615)
    ·
      refine ⟨304628374367551918906001423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203085582911701279270667615 304628374367551918906001423)
      ·
        refine ⟨456942561551327878359002135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304628374367551918906001423 456942561551327878359002135)
        ·
          refine ⟨685413842326991817538503203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 456942561551327878359002135 685413842326991817538503203)
          ·
            refine ⟨1028120763490487726307754805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 685413842326991817538503203 1028120763490487726307754805)
            ·
              refine ⟨96386321577233224341352013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1028120763490487726307754805 96386321577233224341352013)
              ·
                refine ⟨36144870591462459128007005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96386321577233224341352013 36144870591462459128007005)
                ·
                  refine ⟨13554326471798422173002627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36144870591462459128007005 13554326471798422173002627)
                  ·
                    refine ⟨20331489707697633259503941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13554326471798422173002627 20331489707697633259503941)
                    ·
                      refine ⟨3812154320193306236156989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20331489707697633259503941 3812154320193306236156989)
                      ·
                        rfl

theorem cell23_7424144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 3, 3, 1, 4].length) (baseStart_7424144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7424144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7424144 prefixEnd_7424144 := by exact prefixLift 7424144
  have htrace : WordTrace (prefixWord ++ tailWord_7424144) baseStart_7424144 baseEnd_7424144 := by
    simpa [prefixWord, tailWord_7424144, baseEnd_7424144] using wordTrace_append hprefix tailTrace_7424144
  have hstable : (prefixWord ++ tailWord_7424144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7424144).length < 2 ^ (prefixWord ++ tailWord_7424144).sum := by decide
  have hdescent : baseEnd_7424144 < baseStart_7424144 := by decide
  rcases family_descends (prefixWord ++ tailWord_7424144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7424188 : List Nat := [2, 2, 2, 3, 3, 2, 1, 1, 1, 6]
def baseStart_7424188 : Nat := 118140960795 + 7424188 * 2 ^ 59
def prefixEnd_7424188 : Nat := 4983230072969 + 3 ^ 40 * 7424188 * 2
def baseEnd_7424188 : Nat := 1270725637780701354668929

theorem tailTrace_7424188 : CollatzResearch.WordTrace tailWord_7424188 prefixEnd_7424188 1270725637780701354668929 := by
  unfold tailWord_7424188
  simp only [CollatzResearch.WordTrace]
  refine ⟨135391191013721150604412609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180521588018294867472550145 135391191013721150604412609)
  ·
    refine ⟨101543393260290862953309457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135391191013721150604412609 101543393260290862953309457)
    ·
      refine ⟨76157544945218147214982093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101543393260290862953309457 76157544945218147214982093)
      ·
        refine ⟨28559079354456805205618285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76157544945218147214982093 28559079354456805205618285)
        ·
          refine ⟨10709654757921301952106857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28559079354456805205618285 10709654757921301952106857)
          ·
            refine ⟨8032241068440976464080143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10709654757921301952106857 8032241068440976464080143)
            ·
              refine ⟨12048361602661464696120215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8032241068440976464080143 12048361602661464696120215)
              ·
                refine ⟨18072542403992197044180323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12048361602661464696120215 18072542403992197044180323)
                ·
                  refine ⟨27108813605988295566270485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18072542403992197044180323 27108813605988295566270485)
                  ·
                    refine ⟨1270725637780701354668929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27108813605988295566270485 1270725637780701354668929)
                    ·
                      rfl

theorem cell23_7424188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 1, 1, 1, 6].length) (baseStart_7424188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7424188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7424188 prefixEnd_7424188 := by exact prefixLift 7424188
  have htrace : WordTrace (prefixWord ++ tailWord_7424188) baseStart_7424188 baseEnd_7424188 := by
    simpa [prefixWord, tailWord_7424188, baseEnd_7424188] using wordTrace_append hprefix tailTrace_7424188
  have hstable : (prefixWord ++ tailWord_7424188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7424188).length < 2 ^ (prefixWord ++ tailWord_7424188).sum := by decide
  have hdescent : baseEnd_7424188 < baseStart_7424188 := by decide
  rcases family_descends (prefixWord ++ tailWord_7424188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7424224 : List Nat := [2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 5]
def baseStart_7424224 : Nat := 118140960795 + 7424224 * 2 ^ 59
def prefixEnd_7424224 : Nat := 4983230072969 + 3 ^ 40 * 7424224 * 2
def baseEnd_7424224 : Nat := 3812195398645665923156621

theorem tailTrace_7424224 : CollatzResearch.WordTrace tailWord_7424224 prefixEnd_7424224 3812195398645665923156621 := by
  unfold tailWord_7424224
  simp only [CollatzResearch.WordTrace]
  refine ⟨135391847527655939678567863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180522463370207919571423817 135391847527655939678567863)
  ·
    refine ⟨203087771291483909517851795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135391847527655939678567863 203087771291483909517851795)
    ·
      refine ⟨304631656937225864276777693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203087771291483909517851795 304631656937225864276777693)
      ·
        refine ⟨114236871351459699103791635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 304631656937225864276777693 114236871351459699103791635)
        ·
          refine ⟨171355307027189548655687453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114236871351459699103791635 171355307027189548655687453)
          ·
            refine ⟨64258240135196080745882795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 171355307027189548655687453 64258240135196080745882795)
            ·
              refine ⟨96387360202794121118824193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64258240135196080745882795 96387360202794121118824193)
              ·
                refine ⟨72290520152095590839118145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96387360202794121118824193 72290520152095590839118145)
                ·
                  refine ⟨54217890114071693129338609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72290520152095590839118145 54217890114071693129338609)
                  ·
                    refine ⟨40663417585553769847003957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54217890114071693129338609 40663417585553769847003957)
                    ·
                      refine ⟨3812195398645665923156621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40663417585553769847003957 3812195398645665923156621)
                      ·
                        rfl

theorem cell23_7424224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 5].length) (baseStart_7424224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7424224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7424224 prefixEnd_7424224 := by exact prefixLift 7424224
  have htrace : WordTrace (prefixWord ++ tailWord_7424224) baseStart_7424224 baseEnd_7424224 := by
    simpa [prefixWord, tailWord_7424224, baseEnd_7424224] using wordTrace_append hprefix tailTrace_7424224
  have hstable : (prefixWord ++ tailWord_7424224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7424224).length < 2 ^ (prefixWord ++ tailWord_7424224).sum := by decide
  have hdescent : baseEnd_7424224 < baseStart_7424224 := by decide
  rcases family_descends (prefixWord ++ tailWord_7424224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7424228 : List Nat := [2, 3, 1, 1, 1, 2, 1, 6, 2, 1, 3]
def baseStart_7424228 : Nat := 118140960795 + 7424228 * 2 ^ 59
def prefixEnd_7424228 : Nat := 4983230072969 + 3 ^ 40 * 7424228 * 2
def baseEnd_7424228 : Nat := 3812197452568283907506603

theorem tailTrace_7424228 : CollatzResearch.WordTrace tailWord_7424228 prefixEnd_7424228 3812197452568283907506603 := by
  unfold tailWord_7424228
  simp only [CollatzResearch.WordTrace]
  refine ⟨135391920473648694020140669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180522560631531592026854225 135391920473648694020140669)
  ·
    refine ⟨50771970177618260257552751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135391920473648694020140669 50771970177618260257552751)
    ·
      refine ⟨76157955266427390386329127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50771970177618260257552751 76157955266427390386329127)
      ·
        refine ⟨114236932899641085579493691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76157955266427390386329127 114236932899641085579493691)
        ·
          refine ⟨171355399349461628369240537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114236932899641085579493691 171355399349461628369240537)
          ·
            refine ⟨128516549512096221276930403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171355399349461628369240537 128516549512096221276930403)
            ·
              refine ⟨192774824268144331915395605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128516549512096221276930403 192774824268144331915395605)
              ·
                refine ⟨9036319887569265558534169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 192774824268144331915395605 9036319887569265558534169)
                ·
                  refine ⟨6777239915676949168900627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9036319887569265558534169 6777239915676949168900627)
                  ·
                    refine ⟨10165859873515423753350941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6777239915676949168900627 10165859873515423753350941)
                    ·
                      refine ⟨3812197452568283907506603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10165859873515423753350941 3812197452568283907506603)
                      ·
                        rfl

theorem cell23_7424228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 6, 2, 1, 3].length) (baseStart_7424228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7424228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7424228 prefixEnd_7424228 := by exact prefixLift 7424228
  have htrace : WordTrace (prefixWord ++ tailWord_7424228) baseStart_7424228 baseEnd_7424228 := by
    simpa [prefixWord, tailWord_7424228, baseEnd_7424228] using wordTrace_append hprefix tailTrace_7424228
  have hstable : (prefixWord ++ tailWord_7424228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7424228).length < 2 ^ (prefixWord ++ tailWord_7424228).sum := by decide
  have hdescent : baseEnd_7424228 < baseStart_7424228 := by decide
  rcases family_descends (prefixWord ++ tailWord_7424228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7424229 : List Nat := [1, 3, 1, 4, 2, 2, 3, 2, 1, 2, 2]
def baseStart_7424229 : Nat := 118140960795 + 7424229 * 2 ^ 59
def prefixEnd_7424229 : Nat := 4983230072969 + 3 ^ 40 * 7424229 * 2
def baseEnd_7424229 : Nat := 3812197966048938403594099

theorem tailTrace_7424229 : CollatzResearch.WordTrace tailWord_7424229 prefixEnd_7424229 3812197966048938403594099 := by
  unfold tailWord_7424229
  simp only [CollatzResearch.WordTrace]
  refine ⟨270783877420293765211067741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180522584946862510140711827 270783877420293765211067741)
  ·
    refine ⟨101543954032610161954150403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 270783877420293765211067741 101543954032610161954150403)
    ·
      refine ⟨152315931048915242931225605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101543954032610161954150403 152315931048915242931225605)
      ·
        refine ⟨28559237071671608049604801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 152315931048915242931225605 28559237071671608049604801)
        ·
          refine ⟨21419427803753706037203601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28559237071671608049604801 21419427803753706037203601)
          ·
            refine ⟨16064570852815279527902701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21419427803753706037203601 16064570852815279527902701)
            ·
              refine ⟨6024214069805729822963513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16064570852815279527902701 6024214069805729822963513)
              ·
                refine ⟨4518160552354297367222635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6024214069805729822963513 4518160552354297367222635)
                ·
                  refine ⟨6777240828531446050833953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4518160552354297367222635 6777240828531446050833953)
                  ·
                    refine ⟨5082930621398584538125465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6777240828531446050833953 5082930621398584538125465)
                    ·
                      refine ⟨3812197966048938403594099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5082930621398584538125465 3812197966048938403594099)
                      ·
                        rfl

theorem cell23_7424229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 3, 2, 1, 2, 2].length) (baseStart_7424229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7424229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7424229 prefixEnd_7424229 := by exact prefixLift 7424229
  have htrace : WordTrace (prefixWord ++ tailWord_7424229) baseStart_7424229 baseEnd_7424229 := by
    simpa [prefixWord, tailWord_7424229, baseEnd_7424229] using wordTrace_append hprefix tailTrace_7424229
  have hstable : (prefixWord ++ tailWord_7424229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7424229).length < 2 ^ (prefixWord ++ tailWord_7424229).sum := by decide
  have hdescent : baseEnd_7424229 < baseStart_7424229 := by decide
  rcases family_descends (prefixWord ++ tailWord_7424229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7424238 : List Nat := [4, 1, 2, 1, 1, 1, 1, 4, 3, 3, 2]
def baseStart_7424238 : Nat := 118140960795 + 7424238 * 2 ^ 59
def prefixEnd_7424238 : Nat := 4983230072969 + 3 ^ 40 * 7424238 * 2
def baseEnd_7424238 : Nat := 3812202587374828868381557

theorem tailTrace_7424238 : CollatzResearch.WordTrace tailWord_7424238 prefixEnd_7424238 3812202587374828868381557 := by
  unfold tailWord_7424238
  simp only [CollatzResearch.WordTrace]
  refine ⟨33848025709657644968518171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180522803784840773165430245 33848025709657644968518171)
  ·
    refine ⟨50772038564486467452777257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33848025709657644968518171 50772038564486467452777257)
    ·
      refine ⟨38079028923364850589582943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50772038564486467452777257 38079028923364850589582943)
      ·
        refine ⟨57118543385047275884374415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38079028923364850589582943 57118543385047275884374415)
        ·
          refine ⟨85677815077570913826561623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57118543385047275884374415 85677815077570913826561623)
          ·
            refine ⟨128516722616356370739842435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85677815077570913826561623 128516722616356370739842435)
            ·
              refine ⟨192775083924534556109763653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128516722616356370739842435 192775083924534556109763653)
              ·
                refine ⟨36145328235850229270580685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 192775083924534556109763653 36145328235850229270580685)
                ·
                  refine ⟨13554498088443835976467757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36145328235850229270580685 13554498088443835976467757)
                  ·
                    refine ⟨5082936783166438491175409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13554498088443835976467757 5082936783166438491175409)
                    ·
                      refine ⟨3812202587374828868381557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5082936783166438491175409 3812202587374828868381557)
                      ·
                        rfl

theorem cell23_7424238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 4, 3, 3, 2].length) (baseStart_7424238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7424238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7424238 prefixEnd_7424238 := by exact prefixLift 7424238
  have htrace : WordTrace (prefixWord ++ tailWord_7424238) baseStart_7424238 baseEnd_7424238 := by
    simpa [prefixWord, tailWord_7424238, baseEnd_7424238] using wordTrace_append hprefix tailTrace_7424238
  have hstable : (prefixWord ++ tailWord_7424238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7424238).length < 2 ^ (prefixWord ++ tailWord_7424238).sum := by decide
  have hdescent : baseEnd_7424238 < baseStart_7424238 := by decide
  rcases family_descends (prefixWord ++ tailWord_7424238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7424251 : List Nat := [1, 1, 1, 1, 1, 3, 1, 1, 7, 4, 2]
def baseStart_7424251 : Nat := 118140960795 + 7424251 * 2 ^ 59
def prefixEnd_7424251 : Nat := 4983230072969 + 3 ^ 40 * 7424251 * 2
def baseEnd_7424251 : Nat := 3812209262623337317518997

theorem tailTrace_7424251 : CollatzResearch.WordTrace tailWord_7424251 prefixEnd_7424251 3812209262623337317518997 := by
  unfold tailWord_7424251
  simp only [CollatzResearch.WordTrace]
  refine ⟨270784679826214062968368607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180523119884142708645579071 270784679826214062968368607)
  ·
    refine ⟨406177019739321094452552911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270784679826214062968368607 406177019739321094452552911)
    ·
      refine ⟨609265529608981641678829367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 406177019739321094452552911 609265529608981641678829367)
      ·
        refine ⟨913898294413472462518244051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 609265529608981641678829367 913898294413472462518244051)
        ·
          refine ⟨1370847441620208693777366077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 913898294413472462518244051 1370847441620208693777366077)
          ·
            refine ⟨514067790607578260166512279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1370847441620208693777366077 514067790607578260166512279)
            ·
              refine ⟨771101685911367390249768419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 514067790607578260166512279 771101685911367390249768419)
              ·
                refine ⟨1156652528867051085374652629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 771101685911367390249768419 1156652528867051085374652629)
                ·
                  refine ⟨27109043645321509813468421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1156652528867051085374652629 27109043645321509813468421)
                  ·
                    refine ⟨5082945683497783090025329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27109043645321509813468421 5082945683497783090025329)
                    ·
                      refine ⟨3812209262623337317518997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5082945683497783090025329 3812209262623337317518997)
                      ·
                        rfl

theorem cell23_7424251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 7, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 7, 4, 2].length) (baseStart_7424251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7424251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7424251 prefixEnd_7424251 := by exact prefixLift 7424251
  have htrace : WordTrace (prefixWord ++ tailWord_7424251) baseStart_7424251 baseEnd_7424251 := by
    simpa [prefixWord, tailWord_7424251, baseEnd_7424251] using wordTrace_append hprefix tailTrace_7424251
  have hstable : (prefixWord ++ tailWord_7424251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7424251).length < 2 ^ (prefixWord ++ tailWord_7424251).sum := by decide
  have hdescent : baseEnd_7424251 < baseStart_7424251 := by decide
  rcases family_descends (prefixWord ++ tailWord_7424251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7424268 : List Nat := [2, 2, 1, 2, 2, 2, 3, 2, 1, 4, 2]
def baseStart_7424268 : Nat := 118140960795 + 7424268 * 2 ^ 59
def prefixEnd_7424268 : Nat := 4983230072969 + 3 ^ 40 * 7424268 * 2
def baseEnd_7424268 : Nat := 3812217991794463751006419

theorem tailTrace_7424268 : CollatzResearch.WordTrace tailWord_7424268 prefixEnd_7424268 3812217991794463751006419 := by
  unfold tailWord_7424268
  simp only [CollatzResearch.WordTrace]
  refine ⟨135392649933576237435868729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180523533244768316581158305 135392649933576237435868729)
  ·
    refine ⟨101544487450182178076901547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135392649933576237435868729 101544487450182178076901547)
    ·
      refine ⟨152316731175273267115352321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101544487450182178076901547 152316731175273267115352321)
      ·
        refine ⟨114237548381454950336514241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152316731175273267115352321 114237548381454950336514241)
        ·
          refine ⟨85678161286091212752385681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114237548381454950336514241 85678161286091212752385681)
          ·
            refine ⟨64258620964568409564289261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85678161286091212752385681 64258620964568409564289261)
            ·
              refine ⟨24096982861713153586608473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64258620964568409564289261 24096982861713153586608473)
              ·
                refine ⟨18072737146284865189956355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24096982861713153586608473 18072737146284865189956355)
                ·
                  refine ⟨27109105719427297784934533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18072737146284865189956355 27109105719427297784934533)
                  ·
                    refine ⟨5082957322392618334675225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27109105719427297784934533 5082957322392618334675225)
                    ·
                      refine ⟨3812217991794463751006419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5082957322392618334675225 3812217991794463751006419)
                      ·
                        rfl

theorem cell23_7424268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 2, 1, 4, 2].length) (baseStart_7424268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7424268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7424268 prefixEnd_7424268 := by exact prefixLift 7424268
  have htrace : WordTrace (prefixWord ++ tailWord_7424268) baseStart_7424268 baseEnd_7424268 := by
    simpa [prefixWord, tailWord_7424268, baseEnd_7424268] using wordTrace_append hprefix tailTrace_7424268
  have hstable : (prefixWord ++ tailWord_7424268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7424268).length < 2 ^ (prefixWord ++ tailWord_7424268).sum := by decide
  have hdescent : baseEnd_7424268 < baseStart_7424268 := by decide
  rcases family_descends (prefixWord ++ tailWord_7424268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7424308 : List Nat := [2, 5, 1, 1, 1, 3, 1, 2, 7]
def baseStart_7424308 : Nat := 118140960795 + 7424308 * 2 ^ 59
def prefixEnd_7424308 : Nat := 4983230072969 + 3 ^ 40 * 7424308 * 2
def baseEnd_7424308 : Nat := 423582059002293732722915

theorem tailTrace_7424308 : CollatzResearch.WordTrace tailWord_7424308 prefixEnd_7424308 423582059002293732722915 := by
  unfold tailWord_7424308
  simp only [CollatzResearch.WordTrace]
  refine ⟨135393379393503780851596789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180524505858005041135462385 135393379393503780851596789)
  ·
    refine ⟨12693129318140979454837199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 135393379393503780851596789 12693129318140979454837199)
    ·
      refine ⟨19039693977211469182255799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12693129318140979454837199 19039693977211469182255799)
      ·
        refine ⟨28559540965817203773383699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19039693977211469182255799 28559540965817203773383699)
        ·
          refine ⟨42839311448725805660075549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28559540965817203773383699 42839311448725805660075549)
          ·
            refine ⟨16064741793272177122528331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42839311448725805660075549 16064741793272177122528331)
            ·
              refine ⟨24097112689908265683792497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16064741793272177122528331 24097112689908265683792497)
              ·
                refine ⟨18072834517431199262844373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24097112689908265683792497 18072834517431199262844373)
                ·
                  refine ⟨423582059002293732722915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18072834517431199262844373 423582059002293732722915)
                  ·
                    rfl

theorem cell23_7424308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 2, 7].length) (baseStart_7424308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7424308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7424308 prefixEnd_7424308 := by exact prefixLift 7424308
  have htrace : WordTrace (prefixWord ++ tailWord_7424308) baseStart_7424308 baseEnd_7424308 := by
    simpa [prefixWord, tailWord_7424308, baseEnd_7424308] using wordTrace_append hprefix tailTrace_7424308
  have hstable : (prefixWord ++ tailWord_7424308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7424308).length < 2 ^ (prefixWord ++ tailWord_7424308).sum := by decide
  have hdescent : baseEnd_7424308 < baseStart_7424308 := by decide
  rcases family_descends (prefixWord ++ tailWord_7424308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7424361 : List Nat := [1, 2, 1, 1, 1, 3, 3, 1, 3, 4, 3]
def baseStart_7424361 : Nat := 118140960795 + 7424361 * 2 ^ 59
def prefixEnd_7424361 : Nat := 4983230072969 + 3 ^ 40 * 7424361 * 2
def baseEnd_7424361 : Nat := 3812265745495331887143491

theorem tailTrace_7424361 : CollatzResearch.WordTrace tailWord_7424361 prefixEnd_7424361 3812265745495331887143491 := by
  unfold tailWord_7424361
  simp only [CollatzResearch.WordTrace]
  refine ⟨270788691855815551754872937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180525794570543701169915291 270788691855815551754872937)
  ·
    refine ⟨203091518891861663816154703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270788691855815551754872937 203091518891861663816154703)
    ·
      refine ⟨304637278337792495724232055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203091518891861663816154703 304637278337792495724232055)
      ·
        refine ⟨456955917506688743586348083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304637278337792495724232055 456955917506688743586348083)
        ·
          refine ⟨685433876260033115379522125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 456955917506688743586348083 685433876260033115379522125)
          ·
            refine ⟨257037703597512418267320797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 685433876260033115379522125 257037703597512418267320797)
            ·
              refine ⟨96389138849067156850245299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 257037703597512418267320797 96389138849067156850245299)
              ·
                refine ⟨144583708273600735275367949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96389138849067156850245299 144583708273600735275367949)
                ·
                  refine ⟨54218890602600275728262981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 144583708273600735275367949 54218890602600275728262981)
                  ·
                    refine ⟨10166041987987551699049309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54218890602600275728262981 10166041987987551699049309)
                    ·
                      refine ⟨3812265745495331887143491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10166041987987551699049309 3812265745495331887143491)
                      ·
                        rfl

theorem cell23_7424361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 1, 3, 4, 3].length) (baseStart_7424361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7424361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7424361 prefixEnd_7424361 := by exact prefixLift 7424361
  have htrace : WordTrace (prefixWord ++ tailWord_7424361) baseStart_7424361 baseEnd_7424361 := by
    simpa [prefixWord, tailWord_7424361, baseEnd_7424361] using wordTrace_append hprefix tailTrace_7424361
  have hstable : (prefixWord ++ tailWord_7424361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7424361).length < 2 ^ (prefixWord ++ tailWord_7424361).sum := by decide
  have hdescent : baseEnd_7424361 < baseStart_7424361 := by decide
  rcases family_descends (prefixWord ++ tailWord_7424361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7424368 : List Nat := [2, 1, 1, 1, 4, 3, 2, 2, 3, 4]
def baseStart_7424368 : Nat := 118140960795 + 7424368 * 2 ^ 59
def prefixEnd_7424368 : Nat := 4983230072969 + 3 ^ 40 * 7424368 * 2
def baseEnd_7424368 : Nat := 1270756446619971119918653

theorem tailTrace_7424368 : CollatzResearch.WordTrace tailWord_7424368 prefixEnd_7424368 1270756446619971119918653 := by
  unfold tailWord_7424368
  simp only [CollatzResearch.WordTrace]
  refine ⟨135394473583395095975188879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180525964777860127966918505 135394473583395095975188879)
  ·
    refine ⟨203091710375092643962783319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135394473583395095975188879 203091710375092643962783319)
    ·
      refine ⟨304637565562638965944174979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203091710375092643962783319 304637565562638965944174979)
      ·
        refine ⟨456956348343958448916262469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304637565562638965944174979 456956348343958448916262469)
        ·
          refine ⟨85679315314492209171799213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 456956348343958448916262469 85679315314492209171799213)
          ·
            refine ⟨32129743242934578439424705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85679315314492209171799213 32129743242934578439424705)
            ·
              refine ⟨24097307432200933829568529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32129743242934578439424705 24097307432200933829568529)
              ·
                refine ⟨18072980574150700372176397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24097307432200933829568529 18072980574150700372176397)
                ·
                  refine ⟨6777367715306512639566149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18072980574150700372176397 6777367715306512639566149)
                  ·
                    refine ⟨1270756446619971119918653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6777367715306512639566149 1270756446619971119918653)
                    ·
                      rfl

theorem cell23_7424368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 2, 3, 4].length) (baseStart_7424368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7424368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7424368 prefixEnd_7424368 := by exact prefixLift 7424368
  have htrace : WordTrace (prefixWord ++ tailWord_7424368) baseStart_7424368 baseEnd_7424368 := by
    simpa [prefixWord, tailWord_7424368, baseEnd_7424368] using wordTrace_append hprefix tailTrace_7424368
  have hstable : (prefixWord ++ tailWord_7424368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7424368).length < 2 ^ (prefixWord ++ tailWord_7424368).sum := by decide
  have hdescent : baseEnd_7424368 < baseStart_7424368 := by decide
  rcases family_descends (prefixWord ++ tailWord_7424368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7424381 : List Nat := [1, 4, 1, 1, 2, 3, 1, 2, 8]
def baseStart_7424381 : Nat := 118140960795 + 7424381 * 2 ^ 59
def prefixEnd_7424381 : Nat := 4983230072969 + 3 ^ 40 * 7424381 * 2
def baseEnd_7424381 : Nat := 423586223900935756543711

theorem tailTrace_7424381 : CollatzResearch.WordTrace tailWord_7424381 prefixEnd_7424381 423586223900935756543711 := by
  unfold tailWord_7424381
  simp only [CollatzResearch.WordTrace]
  refine ⟨270789421315743095170600997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180526280877162063447067331 270789421315743095170600997)
  ·
    refine ⟨50773016496701830344487687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 270789421315743095170600997 50773016496701830344487687)
    ·
      refine ⟨76159524745052745516731531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50773016496701830344487687 76159524745052745516731531)
      ·
        refine ⟨114239287117579118275097297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76159524745052745516731531 114239287117579118275097297)
        ·
          refine ⟨85679465338184338706322973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114239287117579118275097297 85679465338184338706322973)
          ·
            refine ⟨32129799501819127014871115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85679465338184338706322973 32129799501819127014871115)
            ·
              refine ⟨48194699252728690522306673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32129799501819127014871115 48194699252728690522306673)
              ·
                refine ⟨36146024439546517891730005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48194699252728690522306673 36146024439546517891730005)
                ·
                  refine ⟨423586223900935756543711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36146024439546517891730005 423586223900935756543711)
                  ·
                    rfl

theorem cell23_7424381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 2, 8].length) (baseStart_7424381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7424381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7424381 prefixEnd_7424381 := by exact prefixLift 7424381
  have htrace : WordTrace (prefixWord ++ tailWord_7424381) baseStart_7424381 baseEnd_7424381 := by
    simpa [prefixWord, tailWord_7424381, baseEnd_7424381] using wordTrace_append hprefix tailTrace_7424381
  have hstable : (prefixWord ++ tailWord_7424381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7424381).length < 2 ^ (prefixWord ++ tailWord_7424381).sum := by decide
  have hdescent : baseEnd_7424381 < baseStart_7424381 := by decide
  rcases family_descends (prefixWord ++ tailWord_7424381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7424398 : List Nat := [4, 1, 1, 4, 1, 1, 2, 1, 8]
def baseStart_7424398 : Nat := 118140960795 + 7424398 * 2 ^ 59
def prefixEnd_7424398 : Nat := 4983230072969 + 3 ^ 40 * 7424398 * 2
def baseEnd_7424398 : Nat := 423587193808838693597869

theorem tailTrace_7424398 : CollatzResearch.WordTrace tailWord_7424398 prefixEnd_7424398 423587193808838693597869 := by
  unfold tailWord_7424398
  simp only [CollatzResearch.WordTrace]
  refine ⟨33848755169585188384246231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180526694237787671382646565 33848755169585188384246231)
  ·
    refine ⟨50773132754377782576369347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33848755169585188384246231 50773132754377782576369347)
    ·
      refine ⟨76159699131566673864554021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50773132754377782576369347 76159699131566673864554021)
      ·
        refine ⟨14279943587168751349603879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76159699131566673864554021 14279943587168751349603879)
        ·
          refine ⟨21419915380753127024405819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14279943587168751349603879 21419915380753127024405819)
          ·
            refine ⟨32129873071129690536608729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21419915380753127024405819 32129873071129690536608729)
            ·
              refine ⟨24097404803347267902456547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32129873071129690536608729 24097404803347267902456547)
              ·
                refine ⟨36146107205020901853684821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24097404803347267902456547 36146107205020901853684821)
                ·
                  refine ⟨423587193808838693597869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36146107205020901853684821 423587193808838693597869)
                  ·
                    rfl

theorem cell23_7424398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 1, 8].length) (baseStart_7424398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7424398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7424398 prefixEnd_7424398 := by exact prefixLift 7424398
  have htrace : WordTrace (prefixWord ++ tailWord_7424398) baseStart_7424398 baseEnd_7424398 := by
    simpa [prefixWord, tailWord_7424398, baseEnd_7424398] using wordTrace_append hprefix tailTrace_7424398
  have hstable : (prefixWord ++ tailWord_7424398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7424398).length < 2 ^ (prefixWord ++ tailWord_7424398).sum := by decide
  have hdescent : baseEnd_7424398 < baseStart_7424398 := by decide
  rcases family_descends (prefixWord ++ tailWord_7424398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7424449 : List Nat := [1, 2, 7, 1, 1, 1, 2, 2, 6]
def baseStart_7424449 : Nat := 118140960795 + 7424449 * 2 ^ 59
def prefixEnd_7424449 : Nat := 4983230072969 + 3 ^ 40 * 7424449 * 2
def baseEnd_7424449 : Nat := 423590103532547504760343

theorem tailTrace_7424449 : CollatzResearch.WordTrace tailWord_7424449 prefixEnd_7424449 423590103532547504760343 := by
  unfold tailWord_7424449
  simp only [CollatzResearch.WordTrace]
  refine ⟨270791901479496742784076401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180527934319664495189384267 270791901479496742784076401)
  ·
    refine ⟨203093926109622557088057301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270791901479496742784076401 203093926109622557088057301)
    ·
      refine ⟨4760013893194278681751343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 203093926109622557088057301 4760013893194278681751343)
      ·
        refine ⟨7140020839791418022627015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4760013893194278681751343 7140020839791418022627015)
        ·
          refine ⟨10710031259687127033940523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7140020839791418022627015 10710031259687127033940523)
          ·
            refine ⟨16065046889530690550910785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10710031259687127033940523 16065046889530690550910785)
            ·
              refine ⟨12048785167148017913183089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16065046889530690550910785 12048785167148017913183089)
              ·
                refine ⟨9036588875361013434887317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12048785167148017913183089 9036588875361013434887317)
                ·
                  refine ⟨423590103532547504760343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9036588875361013434887317 423590103532547504760343)
                  ·
                    rfl

theorem cell23_7424449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 2, 2, 6].length) (baseStart_7424449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7424449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7424449 prefixEnd_7424449 := by exact prefixLift 7424449
  have htrace : WordTrace (prefixWord ++ tailWord_7424449) baseStart_7424449 baseEnd_7424449 := by
    simpa [prefixWord, tailWord_7424449, baseEnd_7424449] using wordTrace_append hprefix tailTrace_7424449
  have hstable : (prefixWord ++ tailWord_7424449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7424449).length < 2 ^ (prefixWord ++ tailWord_7424449).sum := by decide
  have hdescent : baseEnd_7424449 < baseStart_7424449 := by decide
  rcases family_descends (prefixWord ++ tailWord_7424449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7424465 : List Nat := [1, 2, 2, 1, 2, 1, 1, 2, 7, 2, 2]
def baseStart_7424465 : Nat := 118140960795 + 7424465 * 2 ^ 59
def prefixEnd_7424465 : Nat := 4983230072969 + 3 ^ 40 * 7424465 * 2
def baseEnd_7424465 : Nat := 3812319147483399480243013

theorem tailTrace_7424465 : CollatzResearch.WordTrace tailWord_7424465 prefixEnd_7424465 3812319147483399480243013 := by
  unfold tailWord_7424465
  simp only [CollatzResearch.WordTrace]
  refine ⟨270792485047438777516658849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180528323364959185011105899 270792485047438777516658849)
  ·
    refine ⟨203094363785579083137494137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270792485047438777516658849 203094363785579083137494137)
    ·
      refine ⟨152320772839184312353120603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203094363785579083137494137 152320772839184312353120603)
      ·
        refine ⟨228481159258776468529680905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152320772839184312353120603 228481159258776468529680905)
        ·
          refine ⟨171360869444082351397260679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228481159258776468529680905 171360869444082351397260679)
          ·
            refine ⟨257041304166123527095891019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171360869444082351397260679 257041304166123527095891019)
            ·
              refine ⟨385561956249185290643836529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 257041304166123527095891019 385561956249185290643836529)
              ·
                refine ⟨289171467186888967982877397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 385561956249185290643836529 289171467186888967982877397)
                ·
                  refine ⟨6777456262192710187098689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 289171467186888967982877397 6777456262192710187098689)
                  ·
                    refine ⟨5083092196644532640324017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6777456262192710187098689 5083092196644532640324017)
                    ·
                      refine ⟨3812319147483399480243013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5083092196644532640324017 3812319147483399480243013)
                      ·
                        rfl

theorem cell23_7424465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 7, 2, 2].length) (baseStart_7424465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7424465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7424465 prefixEnd_7424465 := by exact prefixLift 7424465
  have htrace : WordTrace (prefixWord ++ tailWord_7424465) baseStart_7424465 baseEnd_7424465 := by
    simpa [prefixWord, tailWord_7424465, baseEnd_7424465] using wordTrace_append hprefix tailTrace_7424465
  have hstable : (prefixWord ++ tailWord_7424465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7424465).length < 2 ^ (prefixWord ++ tailWord_7424465).sum := by decide
  have hdescent : baseEnd_7424465 < baseStart_7424465 := by decide
  rcases family_descends (prefixWord ++ tailWord_7424465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7424499 : List Nat := [1, 1, 1, 2, 2, 2, 6, 3, 1, 2, 2]
def baseStart_7424499 : Nat := 118140960795 + 7424499 * 2 ^ 59
def prefixEnd_7424499 : Nat := 4983230072969 + 3 ^ 40 * 7424499 * 2
def baseEnd_7424499 : Nat := 3812336605825652347217857

theorem tailTrace_7424499 : CollatzResearch.WordTrace tailWord_7424499 prefixEnd_7424499 3812336605825652347217857 := by
  unfold tailWord_7424499
  simp only [CollatzResearch.WordTrace]
  refine ⟨270793725129315601323396551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180529150086210400882264367 270793725129315601323396551)
  ·
    refine ⟨406190587693973401985094827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270793725129315601323396551 406190587693973401985094827)
    ·
      refine ⟨609285881540960102977642241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 406190587693973401985094827 609285881540960102977642241)
      ·
        refine ⟨456964411155720077233231681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 609285881540960102977642241 456964411155720077233231681)
        ·
          refine ⟨342723308366790057924923761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 456964411155720077233231681 342723308366790057924923761)
          ·
            refine ⟨257042481275092543443692821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 342723308366790057924923761 257042481275092543443692821)
            ·
              refine ⟨12048866309769962973923101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 257042481275092543443692821 12048866309769962973923101)
              ·
                refine ⟨4518324866163736115221163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12048866309769962973923101 4518324866163736115221163)
                ·
                  refine ⟨6777487299245604172831745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4518324866163736115221163 6777487299245604172831745)
                  ·
                    refine ⟨5083115474434203129623809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6777487299245604172831745 5083115474434203129623809)
                    ·
                      refine ⟨3812336605825652347217857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5083115474434203129623809 3812336605825652347217857)
                      ·
                        rfl

theorem cell23_7424499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 6, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 6, 3, 1, 2, 2].length) (baseStart_7424499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7424499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7424499 prefixEnd_7424499 := by exact prefixLift 7424499
  have htrace : WordTrace (prefixWord ++ tailWord_7424499) baseStart_7424499 baseEnd_7424499 := by
    simpa [prefixWord, tailWord_7424499, baseEnd_7424499] using wordTrace_append hprefix tailTrace_7424499
  have hstable : (prefixWord ++ tailWord_7424499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7424499).length < 2 ^ (prefixWord ++ tailWord_7424499).sum := by decide
  have hdescent : baseEnd_7424499 < baseStart_7424499 := by decide
  rcases family_descends (prefixWord ++ tailWord_7424499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7424502 : List Nat := [5, 1, 1, 1, 2, 1, 3, 3, 1, 2, 3]
def baseStart_7424502 : Nat := 118140960795 + 7424502 * 2 ^ 59
def prefixEnd_7424502 : Nat := 4983230072969 + 3 ^ 40 * 7424502 * 2
def baseEnd_7424502 : Nat := 3812338146267615835480343

theorem tailTrace_7424502 : CollatzResearch.WordTrace tailWord_7424502 prefixEnd_7424502 3812338146267615835480343 := by
  unfold tailWord_7424502
  simp only [CollatzResearch.WordTrace]
  refine ⟨16924614659269045802234735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 180529223032203155223837173 16924614659269045802234735)
  ·
    refine ⟨25386921988903568703352103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16924614659269045802234735 25386921988903568703352103)
    ·
      refine ⟨38080382983355353055028155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25386921988903568703352103 38080382983355353055028155)
      ·
        refine ⟨57120574475033029582542233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38080382983355353055028155 57120574475033029582542233)
        ·
          refine ⟨42840430856274772186906675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57120574475033029582542233 42840430856274772186906675)
          ·
            refine ⟨64260646284412158280360013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42840430856274772186906675 64260646284412158280360013)
            ·
              refine ⟨24097742356654559355135005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64260646284412158280360013 24097742356654559355135005)
              ·
                refine ⟨9036653383745459758175627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24097742356654559355135005 9036653383745459758175627)
                ·
                  refine ⟨13554980075618189637263441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9036653383745459758175627 13554980075618189637263441)
                  ·
                    refine ⟨10166235056713642227947581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13554980075618189637263441 10166235056713642227947581)
                    ·
                      refine ⟨3812338146267615835480343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10166235056713642227947581 3812338146267615835480343)
                      ·
                        rfl

theorem cell23_7424502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 3, 3, 1, 2, 3].length) (baseStart_7424502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7424502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7424502 prefixEnd_7424502 := by exact prefixLift 7424502
  have htrace : WordTrace (prefixWord ++ tailWord_7424502) baseStart_7424502 baseEnd_7424502 := by
    simpa [prefixWord, tailWord_7424502, baseEnd_7424502] using wordTrace_append hprefix tailTrace_7424502
  have hstable : (prefixWord ++ tailWord_7424502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7424502).length < 2 ^ (prefixWord ++ tailWord_7424502).sum := by decide
  have hdescent : baseEnd_7424502 < baseStart_7424502 := by decide
  rcases family_descends (prefixWord ++ tailWord_7424502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7424515 : List Nat := [1, 1, 1, 3, 2, 1, 5, 1, 4, 1, 3]
def baseStart_7424515 : Nat := 118140960795 + 7424515 * 2 ^ 59
def prefixEnd_7424515 : Nat := 4983230072969 + 3 ^ 40 * 7424515 * 2
def baseEnd_7424515 : Nat := 3812344821516124284617783

theorem tailTrace_7424515 : CollatzResearch.WordTrace tailWord_7424515 prefixEnd_7424515 3812344821516124284617783 := by
  unfold tailWord_7424515
  simp only [CollatzResearch.WordTrace]
  refine ⟨270794308697257636055978999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180529539131505090703985999 270794308697257636055978999)
  ·
    refine ⟨406191463045886454083968499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270794308697257636055978999 406191463045886454083968499)
    ·
      refine ⟨609287194568829681125952749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 406191463045886454083968499 609287194568829681125952749)
      ·
        refine ⟨228482697963311130422232281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 609287194568829681125952749 228482697963311130422232281)
        ·
          refine ⟨171362023472483347816674211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228482697963311130422232281 171362023472483347816674211)
          ·
            refine ⟨257043035208725021725011317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171362023472483347816674211 257043035208725021725011317)
            ·
              refine ⟨24097784550817970786719811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 257043035208725021725011317 24097784550817970786719811)
              ·
                refine ⟨36146676826226956180079717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24097784550817970786719811 36146676826226956180079717)
                ·
                  refine ⟨6777501904917554283764947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36146676826226956180079717 6777501904917554283764947)
                  ·
                    refine ⟨10166252857376331425647421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6777501904917554283764947 10166252857376331425647421)
                    ·
                      refine ⟨3812344821516124284617783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10166252857376331425647421 3812344821516124284617783)
                      ·
                        rfl

theorem cell23_7424515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 1, 4, 1, 3].length) (baseStart_7424515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7424515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7424515 prefixEnd_7424515 := by exact prefixLift 7424515
  have htrace : WordTrace (prefixWord ++ tailWord_7424515) baseStart_7424515 baseEnd_7424515 := by
    simpa [prefixWord, tailWord_7424515, baseEnd_7424515] using wordTrace_append hprefix tailTrace_7424515
  have hstable : (prefixWord ++ tailWord_7424515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7424515).length < 2 ^ (prefixWord ++ tailWord_7424515).sum := by decide
  have hdescent : baseEnd_7424515 < baseStart_7424515 := by decide
  rcases family_descends (prefixWord ++ tailWord_7424515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7424516 : List Nat := [2, 3, 2, 3, 1, 1, 2, 4, 1, 2, 2]
def baseStart_7424516 : Nat := 118140960795 + 7424516 * 2 ^ 59
def prefixEnd_7424516 : Nat := 4983230072969 + 3 ^ 40 * 7424516 * 2
def baseEnd_7424516 : Nat := 3812345334996778780705279

theorem tailTrace_7424516 : CollatzResearch.WordTrace tailWord_7424516 prefixEnd_7424516 3812345334996778780705279 := by
  unfold tailWord_7424516
  simp only [CollatzResearch.WordTrace]
  refine ⟨135397172585127006613382701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180529563446836008817843601 135397172585127006613382701)
  ·
    refine ⟨50773939719422627480018513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135397172585127006613382701 50773939719422627480018513)
    ·
      refine ⟨38080454789566970610013885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50773939719422627480018513 38080454789566970610013885)
      ·
        refine ⟨14280170546087613978755207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38080454789566970610013885 14280170546087613978755207)
        ·
          refine ⟨21420255819131420968132811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14280170546087613978755207 21420255819131420968132811)
          ·
            refine ⟨32130383728697131452199217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21420255819131420968132811 32130383728697131452199217)
            ·
              refine ⟨24097787796522848589149413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32130383728697131452199217 24097787796522848589149413)
              ·
                refine ⟨4518335211848034110465515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24097787796522848589149413 4518335211848034110465515)
                ·
                  refine ⟨6777502817772051165698273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4518335211848034110465515 6777502817772051165698273)
                  ·
                    refine ⟨5083127113329038374273705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6777502817772051165698273 5083127113329038374273705)
                    ·
                      refine ⟨3812345334996778780705279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5083127113329038374273705 3812345334996778780705279)
                      ·
                        rfl

theorem cell23_7424516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 4, 1, 2, 2].length) (baseStart_7424516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7424516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7424516 prefixEnd_7424516 := by exact prefixLift 7424516
  have htrace : WordTrace (prefixWord ++ tailWord_7424516) baseStart_7424516 baseEnd_7424516 := by
    simpa [prefixWord, tailWord_7424516, baseEnd_7424516] using wordTrace_append hprefix tailTrace_7424516
  have hstable : (prefixWord ++ tailWord_7424516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7424516).length < 2 ^ (prefixWord ++ tailWord_7424516).sum := by decide
  have hdescent : baseEnd_7424516 < baseStart_7424516 := by decide
  rcases family_descends (prefixWord ++ tailWord_7424516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7424538 : List Nat := [3, 1, 1, 3, 1, 1, 2, 2, 2, 3, 4]
def baseStart_7424538 : Nat := 118140960795 + 7424538 * 2 ^ 59
def prefixEnd_7424538 : Nat := 4983230072969 + 3 ^ 40 * 7424538 * 2
def baseEnd_7424538 : Nat := 3812356631571177694630177

theorem tailTrace_7424538 : CollatzResearch.WordTrace tailWord_7424538 prefixEnd_7424538 3812356631571177694630177 := by
  unfold tailWord_7424538
  simp only [CollatzResearch.WordTrace]
  refine ⟨67698786894043577746016567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180530098384116207322710845 67698786894043577746016567)
  ·
    refine ⟨101548180341065366619024851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67698786894043577746016567 101548180341065366619024851)
    ·
      refine ⟨152322270511598049928537277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101548180341065366619024851 152322270511598049928537277)
      ·
        refine ⟨57120851441849268723201479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152322270511598049928537277 57120851441849268723201479)
        ·
          refine ⟨85681277162773903084802219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57120851441849268723201479 85681277162773903084802219)
          ·
            refine ⟨128521915744160854627203329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85681277162773903084802219 128521915744160854627203329)
            ·
              refine ⟨96391436808120640970402497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128521915744160854627203329 96391436808120640970402497)
              ·
                refine ⟨72293577606090480727801873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96391436808120640970402497 72293577606090480727801873)
                ·
                  refine ⟨54220183204567860545851405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72293577606090480727801873 54220183204567860545851405)
                  ·
                    refine ⟨20332568701712947704694277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54220183204567860545851405 20332568701712947704694277)
                    ·
                      refine ⟨3812356631571177694630177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20332568701712947704694277 3812356631571177694630177)
                      ·
                        rfl

theorem cell23_7424538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 2, 2, 3, 4].length) (baseStart_7424538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7424538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7424538 prefixEnd_7424538 := by exact prefixLift 7424538
  have htrace : WordTrace (prefixWord ++ tailWord_7424538) baseStart_7424538 baseEnd_7424538 := by
    simpa [prefixWord, tailWord_7424538, baseEnd_7424538] using wordTrace_append hprefix tailTrace_7424538
  have hstable : (prefixWord ++ tailWord_7424538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7424538).length < 2 ^ (prefixWord ++ tailWord_7424538).sum := by decide
  have hdescent : baseEnd_7424538 < baseStart_7424538 := by decide
  rcases family_descends (prefixWord ++ tailWord_7424538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7424555 : List Nat := [1, 1, 1, 1, 2, 1, 3, 6, 1, 4, 2]
def baseStart_7424555 : Nat := 118140960795 + 7424555 * 2 ^ 59
def prefixEnd_7424555 : Nat := 4983230072969 + 3 ^ 40 * 7424555 * 2
def baseEnd_7424555 : Nat := 3812365360742304128117599

theorem tailTrace_7424555 : CollatzResearch.WordTrace tailWord_7424555 prefixEnd_7424555 3812365360742304128117599 := by
  unfold tailWord_7424555
  simp only [CollatzResearch.WordTrace]
  refine ⟨270795767617112722887435119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180530511744741815258290079 270795767617112722887435119)
  ·
    refine ⟨406193651425669084331152679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270795767617112722887435119 406193651425669084331152679)
    ·
      refine ⟨609290477138503626496729019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 406193651425669084331152679 609290477138503626496729019)
      ·
        refine ⟨913935715707755439745093529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 609290477138503626496729019 913935715707755439745093529)
        ·
          refine ⟨685451786780816579808820147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 913935715707755439745093529 685451786780816579808820147)
          ·
            refine ⟨1028177680171224869713230221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 685451786780816579808820147 1028177680171224869713230221)
            ·
              refine ⟨385566630064209326142461333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1028177680171224869713230221 385566630064209326142461333)
              ·
                refine ⟨18073435784259812162927875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 385566630064209326142461333 18073435784259812162927875)
                ·
                  refine ⟨27110153676389718244391813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18073435784259812162927875 27110153676389718244391813)
                  ·
                    refine ⟨5083153814323072170823465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27110153676389718244391813 5083153814323072170823465)
                    ·
                      refine ⟨3812365360742304128117599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5083153814323072170823465 3812365360742304128117599)
                      ·
                        rfl

theorem cell23_7424555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 6, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 6, 1, 4, 2].length) (baseStart_7424555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7424555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7424555 prefixEnd_7424555 := by exact prefixLift 7424555
  have htrace : WordTrace (prefixWord ++ tailWord_7424555) baseStart_7424555 baseEnd_7424555 := by
    simpa [prefixWord, tailWord_7424555, baseEnd_7424555] using wordTrace_append hprefix tailTrace_7424555
  have hstable : (prefixWord ++ tailWord_7424555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7424555).length < 2 ^ (prefixWord ++ tailWord_7424555).sum := by decide
  have hdescent : baseEnd_7424555 < baseStart_7424555 := by decide
  rcases family_descends (prefixWord ++ tailWord_7424555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7424608 : List Nat := [2, 1, 1, 3, 2, 1, 2, 3, 1, 7]
def baseStart_7424608 : Nat := 118140960795 + 7424608 * 2 ^ 59
def prefixEnd_7424608 : Nat := 4983230072969 + 3 ^ 40 * 7424608 * 2
def baseEnd_7424608 : Nat := 1270797525072330806918285

theorem tailTrace_7424608 : CollatzResearch.WordTrace tailWord_7424608 prefixEnd_7424608 1270797525072330806918285 := by
  unfold tailWord_7424608
  simp only [CollatzResearch.WordTrace]
  refine ⟨135398850342960356469557239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180531800457280475292742985 135398850342960356469557239)
  ·
    refine ⟨203098275514440534704335859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135398850342960356469557239 203098275514440534704335859)
    ·
      refine ⟨304647413271660802056503789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203098275514440534704335859 304647413271660802056503789)
      ·
        refine ⟨114242779976872800771188921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 304647413271660802056503789 114242779976872800771188921)
        ·
          refine ⟨85682084982654600578391691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114242779976872800771188921 85682084982654600578391691)
          ·
            refine ⟨128523127473981900867587537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85682084982654600578391691 128523127473981900867587537)
            ·
              refine ⟨96392345605486425650690653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128523127473981900867587537 96392345605486425650690653)
              ·
                refine ⟨36147129602057409619008995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96392345605486425650690653 36147129602057409619008995)
                ·
                  refine ⟨54220694403086114428513493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36147129602057409619008995 54220694403086114428513493)
                  ·
                    refine ⟨1270797525072330806918285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54220694403086114428513493 1270797525072330806918285)
                    ·
                      rfl

theorem cell23_7424608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 3, 1, 7].length) (baseStart_7424608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7424608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7424608 prefixEnd_7424608 := by exact prefixLift 7424608
  have htrace : WordTrace (prefixWord ++ tailWord_7424608) baseStart_7424608 baseEnd_7424608 := by
    simpa [prefixWord, tailWord_7424608, baseEnd_7424608] using wordTrace_append hprefix tailTrace_7424608
  have hstable : (prefixWord ++ tailWord_7424608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7424608).length < 2 ^ (prefixWord ++ tailWord_7424608).sum := by decide
  have hdescent : baseEnd_7424608 < baseStart_7424608 := by decide
  rcases family_descends (prefixWord ++ tailWord_7424608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7424629 : List Nat := [1, 3, 4, 2, 2, 1, 1, 4, 5]
def baseStart_7424629 : Nat := 118140960795 + 7424629 * 2 ^ 59
def prefixEnd_7424629 : Nat := 4983230072969 + 3 ^ 40 * 7424629 * 2
def baseEnd_7424629 : Nat := 423600373145637426510251

theorem tailTrace_7424629 : CollatzResearch.WordTrace tailWord_7424629 prefixEnd_7424629 423600373145637426510251 := by
  unfold tailWord_7424629
  simp only [CollatzResearch.WordTrace]
  refine ⟨270798466618844633525628941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180532311079229755683752627 270798466618844633525628941)
  ·
    refine ⟨101549424982066737572110853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 270798466618844633525628941 101549424982066737572110853)
    ·
      refine ⟨19040517184137513294770785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101549424982066737572110853 19040517184137513294770785)
      ·
        refine ⟨14280387888103134971078089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19040517184137513294770785 14280387888103134971078089)
        ·
          refine ⟨10710290916077351228308567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14280387888103134971078089 10710290916077351228308567)
          ·
            refine ⟨16065436374116026842462851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10710290916077351228308567 16065436374116026842462851)
            ·
              refine ⟨24098154561174040263694277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16065436374116026842462851 24098154561174040263694277)
              ·
                refine ⟨4518403980220132549442677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24098154561174040263694277 4518403980220132549442677)
                ·
                  refine ⟨423600373145637426510251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4518403980220132549442677 423600373145637426510251)
                  ·
                    rfl

theorem cell23_7424629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 4, 5].length) (baseStart_7424629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7424629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7424629 prefixEnd_7424629 := by exact prefixLift 7424629
  have htrace : WordTrace (prefixWord ++ tailWord_7424629) baseStart_7424629 baseEnd_7424629 := by
    simpa [prefixWord, tailWord_7424629, baseEnd_7424629] using wordTrace_append hprefix tailTrace_7424629
  have hstable : (prefixWord ++ tailWord_7424629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7424629).length < 2 ^ (prefixWord ++ tailWord_7424629).sum := by decide
  have hdescent : baseEnd_7424629 < baseStart_7424629 := by decide
  rcases family_descends (prefixWord ++ tailWord_7424629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7424655 : List Nat := [1, 1, 2, 1, 1, 1, 1, 8, 3, 4]
def baseStart_7424655 : Nat := 118140960795 + 7424655 * 2 ^ 59
def prefixEnd_7424655 : Nat := 4983230072969 + 3 ^ 40 * 7424655 * 2
def baseEnd_7424655 : Nat := 1270805569602584578955713

theorem tailTrace_7424655 : CollatzResearch.WordTrace tailWord_7424655 prefixEnd_7424655 1270805569602584578955713 := by
  unfold tailWord_7424655
  simp only [CollatzResearch.WordTrace]
  refine ⟨270799414916750439966075419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180532943277833626644050279 270799414916750439966075419)
  ·
    refine ⟨406199122375125659949113129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270799414916750439966075419 406199122375125659949113129)
    ·
      refine ⟨304649341781344244961834847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 406199122375125659949113129 304649341781344244961834847)
      ·
        refine ⟨456974012672016367442752271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304649341781344244961834847 456974012672016367442752271)
        ·
          refine ⟨685461019008024551164128407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 456974012672016367442752271 685461019008024551164128407)
          ·
            refine ⟨1028191528512036826746192611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 685461019008024551164128407 1028191528512036826746192611)
            ·
              refine ⟨1542287292768055240119288917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1028191528512036826746192611 1542287292768055240119288917)
              ·
                refine ⟨18073679212125647345147917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1542287292768055240119288917 18073679212125647345147917)
                ·
                  refine ⟨6777629704547117754430469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18073679212125647345147917 6777629704547117754430469)
                  ·
                    refine ⟨1270805569602584578955713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6777629704547117754430469 1270805569602584578955713)
                    ·
                      rfl

theorem cell23_7424655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 8, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 8, 3, 4].length) (baseStart_7424655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7424655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7424655 prefixEnd_7424655 := by exact prefixLift 7424655
  have htrace : WordTrace (prefixWord ++ tailWord_7424655) baseStart_7424655 baseEnd_7424655 := by
    simpa [prefixWord, tailWord_7424655, baseEnd_7424655] using wordTrace_append hprefix tailTrace_7424655
  have hstable : (prefixWord ++ tailWord_7424655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7424655).length < 2 ^ (prefixWord ++ tailWord_7424655).sum := by decide
  have hdescent : baseEnd_7424655 < baseStart_7424655 := by decide
  rcases family_descends (prefixWord ++ tailWord_7424655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7424665 : List Nat := [1, 2, 1, 2, 1, 2, 5, 1, 1, 4, 3]
def baseStart_7424665 : Nat := 118140960795 + 7424665 * 2 ^ 59
def prefixEnd_7424665 : Nat := 4983230072969 + 3 ^ 40 * 7424665 * 2
def baseEnd_7424665 : Nat := 3812421843614298697742093

theorem tailTrace_7424665 : CollatzResearch.WordTrace tailWord_7424665 prefixEnd_7424665 3812421843614298697742093 := by
  unfold tailWord_7424665
  simp only [CollatzResearch.WordTrace]
  refine ⟨270799779646714211673939449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180533186431142807782626299 270799779646714211673939449)
  ·
    refine ⟨203099834735035658755454587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270799779646714211673939449 203099834735035658755454587)
    ·
      refine ⟨304649752102553488133181881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203099834735035658755454587 304649752102553488133181881)
      ·
        refine ⟨228487314076915116099886411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 304649752102553488133181881 228487314076915116099886411)
        ·
          refine ⟨342730971115372674149829617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228487314076915116099886411 342730971115372674149829617)
          ·
            refine ⟨257048228336529505612372213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 342730971115372674149829617 257048228336529505612372213)
            ·
              refine ⟨24098271406549641151159895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 257048228336529505612372213 24098271406549641151159895)
              ·
                refine ⟨36147407109824461726739843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24098271406549641151159895 36147407109824461726739843)
                ·
                  refine ⟨54221110664736692590109765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36147407109824461726739843 54221110664736692590109765)
                  ·
                    refine ⟨10166458249638129860645581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54221110664736692590109765 10166458249638129860645581)
                    ·
                      refine ⟨3812421843614298697742093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10166458249638129860645581 3812421843614298697742093)
                      ·
                        rfl

theorem cell23_7424665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 1, 1, 4, 3].length) (baseStart_7424665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7424665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7424665 prefixEnd_7424665 := by exact prefixLift 7424665
  have htrace : WordTrace (prefixWord ++ tailWord_7424665) baseStart_7424665 baseEnd_7424665 := by
    simpa [prefixWord, tailWord_7424665, baseEnd_7424665] using wordTrace_append hprefix tailTrace_7424665
  have hstable : (prefixWord ++ tailWord_7424665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7424665).length < 2 ^ (prefixWord ++ tailWord_7424665).sum := by decide
  have hdescent : baseEnd_7424665 < baseStart_7424665 := by decide
  rcases family_descends (prefixWord ++ tailWord_7424665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7424739 : List Nat := [1, 1, 1, 7, 1, 1, 1, 1, 4, 3, 2]
def baseStart_7424739 : Nat := 118140960795 + 7424739 * 2 ^ 59
def prefixEnd_7424739 : Nat := 4983230072969 + 3 ^ 40 * 7424739 * 2
def baseEnd_7424739 : Nat := 3812459841182731408216753

theorem tailTrace_7424739 : CollatzResearch.WordTrace tailWord_7424739 prefixEnd_7424739 3812459841182731408216753 := by
  unfold tailWord_7424739
  simp only [CollatzResearch.WordTrace]
  refine ⟨270802478648446122312133271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180534985765630748208088847 270802478648446122312133271)
  ·
    refine ⟨406203717972669183468199907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270802478648446122312133271 406203717972669183468199907)
    ·
      refine ⟨609305576959003775202299861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 406203717972669183468199907 609305576959003775202299861)
      ·
        refine ⟨14280599459976650981303903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 609305576959003775202299861 14280599459976650981303903)
        ·
          refine ⟨21420899189964976471955855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14280599459976650981303903 21420899189964976471955855)
          ·
            refine ⟨32131348784947464707933783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21420899189964976471955855 32131348784947464707933783)
            ·
              refine ⟨48197023177421197061900675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32131348784947464707933783 48197023177421197061900675)
              ·
                refine ⟨72295534766131795592851013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48197023177421197061900675 72295534766131795592851013)
                ·
                  refine ⟨13555412768649711673659565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72295534766131795592851013 13555412768649711673659565)
                  ·
                    refine ⟨5083279788243641877622337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13555412768649711673659565 5083279788243641877622337)
                    ·
                      refine ⟨3812459841182731408216753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5083279788243641877622337 3812459841182731408216753)
                      ·
                        rfl

theorem cell23_7424739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 1, 4, 3, 2].length) (baseStart_7424739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7424739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7424739 prefixEnd_7424739 := by exact prefixLift 7424739
  have htrace : WordTrace (prefixWord ++ tailWord_7424739) baseStart_7424739 baseEnd_7424739 := by
    simpa [prefixWord, tailWord_7424739, baseEnd_7424739] using wordTrace_append hprefix tailTrace_7424739
  have hstable : (prefixWord ++ tailWord_7424739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7424739).length < 2 ^ (prefixWord ++ tailWord_7424739).sum := by decide
  have hdescent : baseEnd_7424739 < baseStart_7424739 := by decide
  rcases family_descends (prefixWord ++ tailWord_7424739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7424755 : List Nat := [1, 1, 1, 2, 2, 3, 1, 1, 2, 6, 3]
def baseStart_7424755 : Nat := 118140960795 + 7424755 * 2 ^ 59
def prefixEnd_7424755 : Nat := 4983230072969 + 3 ^ 40 * 7424755 * 2
def baseEnd_7424755 : Nat := 3812468056873203345616679

theorem tailTrace_7424755 : CollatzResearch.WordTrace tailWord_7424755 prefixEnd_7424755 3812468056873203345616679 := by
  unfold tailWord_7424755
  simp only [CollatzResearch.WordTrace]
  refine ⟨270803062216388157044715719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180535374810925438029810479 270803062216388157044715719)
  ·
    refine ⟨406204593324582235567073579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270803062216388157044715719 406204593324582235567073579)
    ·
      refine ⟨609306889986873353350610369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 406204593324582235567073579 609306889986873353350610369)
      ·
        refine ⟨456980167490155015012957777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 609306889986873353350610369 456980167490155015012957777)
        ·
          refine ⟨342735125617616261259718333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 456980167490155015012957777 342735125617616261259718333)
          ·
            refine ⟨128525672106606097972394375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 342735125617616261259718333 128525672106606097972394375)
            ·
              refine ⟨192788508159909146958591563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128525672106606097972394375 192788508159909146958591563)
              ·
                refine ⟨289182762239863720437887345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 192788508159909146958591563 289182762239863720437887345)
                ·
                  refine ⟨216887071679897790328415509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 289182762239863720437887345 216887071679897790328415509)
                  ·
                    refine ⟨10166581484995208921644477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 216887071679897790328415509 10166581484995208921644477)
                    ·
                      refine ⟨3812468056873203345616679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10166581484995208921644477 3812468056873203345616679)
                      ·
                        rfl

theorem cell23_7424755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 6, 3].length) (baseStart_7424755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7424755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7424755 prefixEnd_7424755 := by exact prefixLift 7424755
  have htrace : WordTrace (prefixWord ++ tailWord_7424755) baseStart_7424755 baseEnd_7424755 := by
    simpa [prefixWord, tailWord_7424755, baseEnd_7424755] using wordTrace_append hprefix tailTrace_7424755
  have hstable : (prefixWord ++ tailWord_7424755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7424755).length < 2 ^ (prefixWord ++ tailWord_7424755).sum := by decide
  have hdescent : baseEnd_7424755 < baseStart_7424755 := by decide
  rcases family_descends (prefixWord ++ tailWord_7424755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7424765 : List Nat := [1, 4, 1, 1, 1, 1, 3, 3, 1, 1, 6]
def baseStart_7424765 : Nat := 118140960795 + 7424765 * 2 ^ 59
def prefixEnd_7424765 : Nat := 4983230072969 + 3 ^ 40 * 7424765 * 2
def baseEnd_7424765 : Nat := 3812473191679748306491633

theorem tailTrace_7424765 : CollatzResearch.WordTrace tailWord_7424765 prefixEnd_7424765 3812473191679748306491633 := by
  unfold tailWord_7424765
  simp only [CollatzResearch.WordTrace]
  refine ⟨270803426946351928752579749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180535617964234619168386499 270803426946351928752579749)
  ·
    refine ⟨50775642552440986641108703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 270803426946351928752579749 50775642552440986641108703)
    ·
      refine ⟨76163463828661479961663055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50775642552440986641108703 76163463828661479961663055)
      ·
        refine ⟨114245195742992219942494583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76163463828661479961663055 114245195742992219942494583)
        ·
          refine ⟨171367793614488329913741875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114245195742992219942494583 171367793614488329913741875)
          ·
            refine ⟨257051690421732494870612813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171367793614488329913741875 257051690421732494870612813)
            ·
              refine ⟨96394383908149685576479805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 257051690421732494870612813 96394383908149685576479805)
              ·
                refine ⟨36147893965556132091179927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96394383908149685576479805 36147893965556132091179927)
                ·
                  refine ⟨54221840948334198136769891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36147893965556132091179927 54221840948334198136769891)
                  ·
                    refine ⟨81332761422501297205154837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54221840948334198136769891 81332761422501297205154837)
                    ·
                      refine ⟨3812473191679748306491633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81332761422501297205154837 3812473191679748306491633)
                      ·
                        rfl

theorem cell23_7424765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 3, 1, 1, 6].length) (baseStart_7424765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7424765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7424765 prefixEnd_7424765 := by exact prefixLift 7424765
  have htrace : WordTrace (prefixWord ++ tailWord_7424765) baseStart_7424765 baseEnd_7424765 := by
    simpa [prefixWord, tailWord_7424765, baseEnd_7424765] using wordTrace_append hprefix tailTrace_7424765
  have hstable : (prefixWord ++ tailWord_7424765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7424765).length < 2 ^ (prefixWord ++ tailWord_7424765).sum := by decide
  have hdescent : baseEnd_7424765 < baseStart_7424765 := by decide
  rcases family_descends (prefixWord ++ tailWord_7424765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7424766 : List Nat := [4, 2, 2, 1, 2, 3, 1, 2, 1, 5]
def baseStart_7424766 : Nat := 118140960795 + 7424766 * 2 ^ 59
def prefixEnd_7424766 : Nat := 4983230072969 + 3 ^ 40 * 7424766 * 2
def baseEnd_7424766 : Nat := 1270824568386800934193043

theorem tailTrace_7424766 : CollatzResearch.WordTrace tailWord_7424766 prefixEnd_7424766 1270824568386800934193043 := by
  unfold tailWord_7424766
  simp only [CollatzResearch.WordTrace]
  refine ⟨33850432927418538240420769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180535642279565537282244101 33850432927418538240420769)
  ·
    refine ⟨25387824695563903680315577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33850432927418538240420769 25387824695563903680315577)
    ·
      refine ⟨19040868521672927760236683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25387824695563903680315577 19040868521672927760236683)
      ·
        refine ⟨28561302782509391640355025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19040868521672927760236683 28561302782509391640355025)
        ·
          refine ⟨21420977086882043730266269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28561302782509391640355025 21420977086882043730266269)
          ·
            refine ⟨8032866407580766398849851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21420977086882043730266269 8032866407580766398849851)
            ·
              refine ⟨12049299611371149598274777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8032866407580766398849851 12049299611371149598274777)
              ·
                refine ⟨9036974708528362198706083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12049299611371149598274777 9036974708528362198706083)
                ·
                  refine ⟨13555462062792543298059125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9036974708528362198706083 13555462062792543298059125)
                  ·
                    refine ⟨1270824568386800934193043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13555462062792543298059125 1270824568386800934193043)
                    ·
                      rfl

theorem cell23_7424766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 1, 2, 1, 5].length) (baseStart_7424766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7424766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7424766 prefixEnd_7424766 := by exact prefixLift 7424766
  have htrace : WordTrace (prefixWord ++ tailWord_7424766) baseStart_7424766 baseEnd_7424766 := by
    simpa [prefixWord, tailWord_7424766, baseEnd_7424766] using wordTrace_append hprefix tailTrace_7424766
  have hstable : (prefixWord ++ tailWord_7424766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7424766).length < 2 ^ (prefixWord ++ tailWord_7424766).sum := by decide
  have hdescent : baseEnd_7424766 < baseStart_7424766 := by decide
  rcases family_descends (prefixWord ++ tailWord_7424766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7424769 : List Nat := [1, 2, 4, 1, 1, 1, 1, 3, 5, 2, 2]
def baseStart_7424769 : Nat := 118140960795 + 7424769 * 2 ^ 59
def prefixEnd_7424769 : Nat := 4983230072969 + 3 ^ 40 * 7424769 * 2
def baseEnd_7424769 : Nat := 3812475245602366290841615

theorem tailTrace_7424769 : CollatzResearch.WordTrace tailWord_7424769 prefixEnd_7424769 3812475245602366290841615 := by
  unfold tailWord_7424769
  simp only [CollatzResearch.WordTrace]
  refine ⟨270803572838337437435725361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180535715225558291623816907 270803572838337437435725361)
  ·
    refine ⟨203102679628753078076794021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270803572838337437435725361 203102679628753078076794021)
    ·
      refine ⟨38081752430391202139398879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 203102679628753078076794021 38081752430391202139398879)
      ·
        refine ⟨57122628645586803209098319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38081752430391202139398879 57122628645586803209098319)
        ·
          refine ⟨85683942968380204813647479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57122628645586803209098319 85683942968380204813647479)
          ·
            refine ⟨128525914452570307220471219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85683942968380204813647479 128525914452570307220471219)
            ·
              refine ⟨192788871678855460830706829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128525914452570307220471219 192788871678855460830706829)
              ·
                refine ⟨72295826879570797811515061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 192788871678855460830706829 72295826879570797811515061)
                ·
                  refine ⟨6777733769959762294829537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 72295826879570797811515061 6777733769959762294829537)
                  ·
                    refine ⟨5083300327469821721122153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6777733769959762294829537 5083300327469821721122153)
                    ·
                      refine ⟨3812475245602366290841615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5083300327469821721122153 3812475245602366290841615)
                      ·
                        rfl

theorem cell23_7424769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 3, 5, 2, 2].length) (baseStart_7424769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7424769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7424769 prefixEnd_7424769 := by exact prefixLift 7424769
  have htrace : WordTrace (prefixWord ++ tailWord_7424769) baseStart_7424769 baseEnd_7424769 := by
    simpa [prefixWord, tailWord_7424769, baseEnd_7424769] using wordTrace_append hprefix tailTrace_7424769
  have hstable : (prefixWord ++ tailWord_7424769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7424769).length < 2 ^ (prefixWord ++ tailWord_7424769).sum := by decide
  have hdescent : baseEnd_7424769 < baseStart_7424769 := by decide
  rcases family_descends (prefixWord ++ tailWord_7424769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7424797 : List Nat := [1, 4, 2, 4, 1, 2, 2, 2, 1, 1, 3]
def baseStart_7424797 : Nat := 118140960795 + 7424797 * 2 ^ 59
def prefixEnd_7424797 : Nat := 4983230072969 + 3 ^ 40 * 7424797 * 2
def baseEnd_7424797 : Nat := 3812489623060692181291487

theorem tailTrace_7424797 : CollatzResearch.WordTrace tailWord_7424797 prefixEnd_7424797 3812489623060692181291487 := by
  unfold tailWord_7424797
  simp only [CollatzResearch.WordTrace]
  refine ⟨270804594082235998217744645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180536396054823998811829763 270804594082235998217744645)
  ·
    refine ⟨50775861390419249665827121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 270804594082235998217744645 50775861390419249665827121)
    ·
      refine ⟨38081896042814437249370341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50775861390419249665827121 38081896042814437249370341)
      ·
        refine ⟨7140355508027706984256939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38081896042814437249370341 7140355508027706984256939)
        ·
          refine ⟨10710533262041560476385409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7140355508027706984256939 10710533262041560476385409)
          ·
            refine ⟨8032899946531170357289057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10710533262041560476385409 8032899946531170357289057)
            ·
              refine ⟨6024674959898377767966793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8032899946531170357289057 6024674959898377767966793)
              ·
                refine ⟨4518506219923783325975095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6024674959898377767966793 4518506219923783325975095)
                ·
                  refine ⟨6777759329885674988962643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4518506219923783325975095 6777759329885674988962643)
                  ·
                    refine ⟨10166638994828512483443965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6777759329885674988962643 10166638994828512483443965)
                    ·
                      refine ⟨3812489623060692181291487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10166638994828512483443965 3812489623060692181291487)
                      ·
                        rfl

theorem cell23_7424797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_7424797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7424797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7424797 prefixEnd_7424797 := by exact prefixLift 7424797
  have htrace : WordTrace (prefixWord ++ tailWord_7424797) baseStart_7424797 baseEnd_7424797 := by
    simpa [prefixWord, tailWord_7424797, baseEnd_7424797] using wordTrace_append hprefix tailTrace_7424797
  have hstable : (prefixWord ++ tailWord_7424797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7424797).length < 2 ^ (prefixWord ++ tailWord_7424797).sum := by decide
  have hdescent : baseEnd_7424797 < baseStart_7424797 := by decide
  rcases family_descends (prefixWord ++ tailWord_7424797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7424805 : List Nat := [1, 3, 1, 2, 3, 1, 1, 1, 1, 9]
def baseStart_7424805 : Nat := 118140960795 + 7424805 * 2 ^ 59
def prefixEnd_7424805 : Nat := 4983230072969 + 3 ^ 40 * 7424805 * 2
def baseEnd_7424805 : Nat := 1270831243635309383330483

theorem tailTrace_7424805 : CollatzResearch.WordTrace tailWord_7424805 prefixEnd_7424805 1270831243635309383330483 := by
  unfold tailWord_7424805
  simp only [CollatzResearch.WordTrace]
  refine ⟨270804885866207015584035869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180536590577471343722690579 270804885866207015584035869)
  ·
    refine ⟨101551832199827630844013451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 270804885866207015584035869 101551832199827630844013451)
    ·
      refine ⟨152327748299741446266020177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101551832199827630844013451 152327748299741446266020177)
      ·
        refine ⟨114245811224806084699515133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152327748299741446266020177 114245811224806084699515133)
        ·
          refine ⟨42842179209302281762318175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114245811224806084699515133 42842179209302281762318175)
          ·
            refine ⟨64263268813953422643477263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42842179209302281762318175 64263268813953422643477263)
            ·
              refine ⟨96394903220930133965215895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64263268813953422643477263 96394903220930133965215895)
              ·
                refine ⟨144592354831395200947823843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96394903220930133965215895 144592354831395200947823843)
                ·
                  refine ⟨216888532247092801421735765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 144592354831395200947823843 216888532247092801421735765)
                  ·
                    refine ⟨1270831243635309383330483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 216888532247092801421735765 1270831243635309383330483)
                    ·
                      rfl

theorem cell23_7424805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 9].length) (baseStart_7424805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7424805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7424805 prefixEnd_7424805 := by exact prefixLift 7424805
  have htrace : WordTrace (prefixWord ++ tailWord_7424805) baseStart_7424805 baseEnd_7424805 := by
    simpa [prefixWord, tailWord_7424805, baseEnd_7424805] using wordTrace_append hprefix tailTrace_7424805
  have hstable : (prefixWord ++ tailWord_7424805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7424805).length < 2 ^ (prefixWord ++ tailWord_7424805).sum := by decide
  have hdescent : baseEnd_7424805 < baseStart_7424805 := by decide
  rcases family_descends (prefixWord ++ tailWord_7424805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7424819 : List Nat := [1, 1, 1, 2, 6, 2, 2, 1, 1, 3, 3]
def baseStart_7424819 : Nat := 118140960795 + 7424819 * 2 ^ 59
def prefixEnd_7424819 : Nat := 4983230072969 + 3 ^ 40 * 7424819 * 2
def baseEnd_7424819 : Nat := 3812500919635091095216385

theorem tailTrace_7424819 : CollatzResearch.WordTrace tailWord_7424819 prefixEnd_7424819 3812500919635091095216385 := by
  unfold tailWord_7424819
  simp only [CollatzResearch.WordTrace]
  refine ⟨270805396488156295975045511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180536930992104197316697007 270805396488156295975045511)
  ·
    refine ⟨406208094732234443962568267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270805396488156295975045511 406208094732234443962568267)
    ·
      refine ⟨609312142098351665943852401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 406208094732234443962568267 609312142098351665943852401)
      ·
        refine ⟨456984106573763749457889301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 609312142098351665943852401 456984106573763749457889301)
        ·
          refine ⟨21421129995645175755838561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 456984106573763749457889301 21421129995645175755838561)
          ·
            refine ⟨16065847496733881816878921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21421129995645175755838561 16065847496733881816878921)
            ·
              refine ⟨12049385622550411362659191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16065847496733881816878921 12049385622550411362659191)
              ·
                refine ⟨18074078433825617043988787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12049385622550411362659191 18074078433825617043988787)
                ·
                  refine ⟨27111117650738425565983181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18074078433825617043988787 27111117650738425565983181)
                  ·
                    refine ⟨10166669119026909587243693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27111117650738425565983181 10166669119026909587243693)
                    ·
                      refine ⟨3812500919635091095216385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10166669119026909587243693 3812500919635091095216385)
                      ·
                        rfl

theorem cell23_7424819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 2, 1, 1, 3, 3].length) (baseStart_7424819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7424819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7424819 prefixEnd_7424819 := by exact prefixLift 7424819
  have htrace : WordTrace (prefixWord ++ tailWord_7424819) baseStart_7424819 baseEnd_7424819 := by
    simpa [prefixWord, tailWord_7424819, baseEnd_7424819] using wordTrace_append hprefix tailTrace_7424819
  have hstable : (prefixWord ++ tailWord_7424819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7424819).length < 2 ^ (prefixWord ++ tailWord_7424819).sum := by decide
  have hdescent : baseEnd_7424819 < baseStart_7424819 := by decide
  rcases family_descends (prefixWord ++ tailWord_7424819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7424835 : List Nat := [1, 1, 1, 3, 1, 4, 1, 2, 1, 8]
def baseStart_7424835 : Nat := 118140960795 + 7424835 * 2 ^ 59
def prefixEnd_7424835 : Nat := 4983230072969 + 3 ^ 40 * 7424835 * 2
def baseEnd_7424835 : Nat := 1270836378441854344205437

theorem tailTrace_7424835 : CollatzResearch.WordTrace tailWord_7424835 prefixEnd_7424835 1270836378441854344205437 := by
  unfold tailWord_7424835
  simp only [CollatzResearch.WordTrace]
  refine ⟨270805980056098330707627959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180537320037398887138418639 270805980056098330707627959)
  ·
    refine ⟨406208970084147496061441939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270805980056098330707627959 406208970084147496061441939)
    ·
      refine ⟨609313455126221244092162909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 406208970084147496061441939 609313455126221244092162909)
      ·
        refine ⟨228492545672332966534561091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 609313455126221244092162909 228492545672332966534561091)
        ·
          refine ⟨342738818508499449801841637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228492545672332966534561091 342738818508499449801841637)
          ·
            refine ⟨64263528470343646837845307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 342738818508499449801841637 64263528470343646837845307)
            ·
              refine ⟨96395292705515470256767961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64263528470343646837845307 96395292705515470256767961)
              ·
                refine ⟨72296469529136602692575971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96395292705515470256767961 72296469529136602692575971)
                ·
                  refine ⟨108444704293704904038863957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72296469529136602692575971 108444704293704904038863957)
                  ·
                    refine ⟨1270836378441854344205437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 108444704293704904038863957 1270836378441854344205437)
                    ·
                      rfl

theorem cell23_7424835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 2, 1, 8].length) (baseStart_7424835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7424835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7424835 prefixEnd_7424835 := by exact prefixLift 7424835
  have htrace : WordTrace (prefixWord ++ tailWord_7424835) baseStart_7424835 baseEnd_7424835 := by
    simpa [prefixWord, tailWord_7424835, baseEnd_7424835] using wordTrace_append hprefix tailTrace_7424835
  have hstable : (prefixWord ++ tailWord_7424835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7424835).length < 2 ^ (prefixWord ++ tailWord_7424835).sum := by decide
  have hdescent : baseEnd_7424835 < baseStart_7424835 := by decide
  rcases family_descends (prefixWord ++ tailWord_7424835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7424882 : List Nat := [3, 2, 1, 2, 1, 1, 4, 2, 7]
def baseStart_7424882 : Nat := 118140960795 + 7424882 * 2 ^ 59
def prefixEnd_7424882 : Nat := 4983230072969 + 3 ^ 40 * 7424882 * 2
def baseEnd_7424882 : Nat := 423614807657369372080955

theorem tailTrace_7424882 : CollatzResearch.WordTrace tailWord_7424882 prefixEnd_7424882 423614807657369372080955 := by
  unfold tailWord_7424882
  simp only [CollatzResearch.WordTrace]
  refine ⟨67701923571732014433647225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180538462857952038489725933 67701923571732014433647225)
  ·
    refine ⟨50776442678799010825235419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67701923571732014433647225 50776442678799010825235419)
    ·
      refine ⟨76164664018198516237853129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50776442678799010825235419 76164664018198516237853129)
      ·
        refine ⟨57123498013648887178389847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76164664018198516237853129 57123498013648887178389847)
        ·
          refine ⟨85685247020473330767584771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57123498013648887178389847 85685247020473330767584771)
          ·
            refine ⟨128527870530709996151377157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85685247020473330767584771 128527870530709996151377157)
            ·
              refine ⟨24098975724508124278383217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 128527870530709996151377157 24098975724508124278383217)
              ·
                refine ⟨18074231793381093208787413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24098975724508124278383217 18074231793381093208787413)
                ·
                  refine ⟨423614807657369372080955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18074231793381093208787413 423614807657369372080955)
                  ·
                    rfl

theorem cell23_7424882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 2, 7].length) (baseStart_7424882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7424882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7424882 prefixEnd_7424882 := by exact prefixLift 7424882
  have htrace : WordTrace (prefixWord ++ tailWord_7424882) baseStart_7424882 baseEnd_7424882 := by
    simpa [prefixWord, tailWord_7424882, baseEnd_7424882] using wordTrace_append hprefix tailTrace_7424882
  have hstable : (prefixWord ++ tailWord_7424882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7424882).length < 2 ^ (prefixWord ++ tailWord_7424882).sum := by decide
  have hdescent : baseEnd_7424882 < baseStart_7424882 := by decide
  rcases family_descends (prefixWord ++ tailWord_7424882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7424892 : List Nat := [2, 2, 2, 1, 1, 1, 1, 4, 1, 5, 3]
def baseStart_7424892 : Nat := 118140960795 + 7424892 * 2 ^ 59
def prefixEnd_7424892 : Nat := 4983230072969 + 3 ^ 40 * 7424892 * 2
def baseEnd_7424892 : Nat := 3812538403722869309603549

theorem tailTrace_7424892 : CollatzResearch.WordTrace tailWord_7424892 prefixEnd_7424892 3812538403722869309603549 := by
  unfold tailWord_7424892
  simp only [CollatzResearch.WordTrace]
  refine ⟨135404029508445914721226465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180538706011261219628301953 135404029508445914721226465)
  ·
    refine ⟨101553022131334436040919849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135404029508445914721226465 101553022131334436040919849)
    ·
      refine ⟨76164766598500827030689887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101553022131334436040919849 76164766598500827030689887)
      ·
        refine ⟨114247149897751240546034831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76164766598500827030689887 114247149897751240546034831)
        ·
          refine ⟨171370724846626860819052247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114247149897751240546034831 171370724846626860819052247)
          ·
            refine ⟨257056087269940291228578371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171370724846626860819052247 257056087269940291228578371)
            ·
              refine ⟨385584130904910436842867557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 257056087269940291228578371 385584130904910436842867557)
              ·
                refine ⟨72297024544670706908037667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 385584130904910436842867557 72297024544670706908037667)
                ·
                  refine ⟨108445536817006060362056501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72297024544670706908037667 108445536817006060362056501)
                  ·
                    refine ⟨10166769076594318158942797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 108445536817006060362056501 10166769076594318158942797)
                    ·
                      refine ⟨3812538403722869309603549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10166769076594318158942797 3812538403722869309603549)
                      ·
                        rfl

theorem cell23_7424892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 4, 1, 5, 3].length) (baseStart_7424892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7424892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7424892 prefixEnd_7424892 := by exact prefixLift 7424892
  have htrace : WordTrace (prefixWord ++ tailWord_7424892) baseStart_7424892 baseEnd_7424892 := by
    simpa [prefixWord, tailWord_7424892, baseEnd_7424892] using wordTrace_append hprefix tailTrace_7424892
  have hstable : (prefixWord ++ tailWord_7424892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7424892).length < 2 ^ (prefixWord ++ tailWord_7424892).sum := by decide
  have hdescent : baseEnd_7424892 < baseStart_7424892 := by decide
  rcases family_descends (prefixWord ++ tailWord_7424892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7424919 : List Nat := [1, 1, 3, 3, 1, 2, 2, 1, 2, 5, 2]
def baseStart_7424919 : Nat := 118140960795 + 7424919 * 2 ^ 59
def prefixEnd_7424919 : Nat := 4983230072969 + 3 ^ 40 * 7424919 * 2
def baseEnd_7424919 : Nat := 3812552267700540703965925

theorem tailTrace_7424919 : CollatzResearch.WordTrace tailWord_7424919 prefixEnd_7424919 3812552267700540703965925 := by
  unfold tailWord_7424919
  simp only [CollatzResearch.WordTrace]
  refine ⟨270809043787794013053685811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180539362525196008702457207 270809043787794013053685811)
  ·
    refine ⟨406213565681691019580528717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270809043787794013053685811 406213565681691019580528717)
    ·
      refine ⟨152330087130634132342698269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 406213565681691019580528717 152330087130634132342698269)
      ·
        refine ⟨57123782673987799628511851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152330087130634132342698269 57123782673987799628511851)
        ·
          refine ⟨85685674010981699442767777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57123782673987799628511851 85685674010981699442767777)
          ·
            refine ⟨64264255508236274582075833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85685674010981699442767777 64264255508236274582075833)
            ·
              refine ⟨48198191631177205936556875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64264255508236274582075833 48198191631177205936556875)
              ·
                refine ⟨72297287446765808904835313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48198191631177205936556875 72297287446765808904835313)
                ·
                  refine ⟨54222965585074356678626485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72297287446765808904835313 54222965585074356678626485)
                  ·
                    refine ⟨5083403023600720938621233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54222965585074356678626485 5083403023600720938621233)
                    ·
                      refine ⟨3812552267700540703965925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5083403023600720938621233 3812552267700540703965925)
                      ·
                        rfl

theorem cell23_7424919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 1, 2, 5, 2].length) (baseStart_7424919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7424919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7424919 prefixEnd_7424919 := by exact prefixLift 7424919
  have htrace : WordTrace (prefixWord ++ tailWord_7424919) baseStart_7424919 baseEnd_7424919 := by
    simpa [prefixWord, tailWord_7424919, baseEnd_7424919] using wordTrace_append hprefix tailTrace_7424919
  have hstable : (prefixWord ++ tailWord_7424919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7424919).length < 2 ^ (prefixWord ++ tailWord_7424919).sum := by decide
  have hdescent : baseEnd_7424919 < baseStart_7424919 := by decide
  rcases family_descends (prefixWord ++ tailWord_7424919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7425049 : List Nat := [1, 2, 1, 2, 1, 1, 7, 1, 1, 6]
def baseStart_7425049 : Nat := 118140960795 + 7425049 * 2 ^ 59
def prefixEnd_7425049 : Nat := 4983230072969 + 3 ^ 40 * 7425049 * 2
def baseEnd_7425049 : Nat := 1270873006728541731780109

theorem tailTrace_7425049 : CollatzResearch.WordTrace tailWord_7425049 prefixEnd_7425049 1270873006728541731780109 := by
  unfold tailWord_7425049
  simp only [CollatzResearch.WordTrace]
  refine ⟨270813785277323045255918201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180542523518215363503945467 270813785277323045255918201)
  ·
    refine ⟨203110338957992283941938651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270813785277323045255918201 203110338957992283941938651)
    ·
      refine ⟨304665508436988425912907977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203110338957992283941938651 304665508436988425912907977)
      ·
        refine ⟨228499131327741319434680983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 304665508436988425912907977 228499131327741319434680983)
        ·
          refine ⟨342748696991611979152021475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228499131327741319434680983 342748696991611979152021475)
          ·
            refine ⟨514123045487417968728032213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 342748696991611979152021475 514123045487417968728032213)
            ·
              refine ⟨12049758878611358642063255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 514123045487417968728032213 12049758878611358642063255)
              ·
                refine ⟨18074638317917037963094883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12049758878611358642063255 18074638317917037963094883)
                ·
                  refine ⟨27111957476875556944642325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18074638317917037963094883 27111957476875556944642325)
                  ·
                    refine ⟨1270873006728541731780109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27111957476875556944642325 1270873006728541731780109)
                    ·
                      rfl

theorem cell23_7425049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 7, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 7, 1, 1, 6].length) (baseStart_7425049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7425049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7425049 prefixEnd_7425049 := by exact prefixLift 7425049
  have htrace : WordTrace (prefixWord ++ tailWord_7425049) baseStart_7425049 baseEnd_7425049 := by
    simpa [prefixWord, tailWord_7425049, baseEnd_7425049] using wordTrace_append hprefix tailTrace_7425049
  have hstable : (prefixWord ++ tailWord_7425049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7425049).length < 2 ^ (prefixWord ++ tailWord_7425049).sum := by decide
  have hdescent : baseEnd_7425049 < baseStart_7425049 := by decide
  rcases family_descends (prefixWord ++ tailWord_7425049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7425053 : List Nat := [1, 4, 2, 2, 3, 1, 2, 2, 1, 5]
def baseStart_7425053 : Nat := 118140960795 + 7425053 * 2 ^ 59
def prefixEnd_7425053 : Nat := 4983230072969 + 3 ^ 40 * 7425053 * 2
def baseEnd_7425053 : Nat := 1270873691369414393230103

theorem tailTrace_7425053 : CollatzResearch.WordTrace tailWord_7425053 prefixEnd_7425053 1270873691369414393230103 := by
  unfold tailWord_7425053
  simp only [CollatzResearch.WordTrace]
  refine ⟨270813931169308553939063813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180542620779539035959375875 270813931169308553939063813)
  ·
    refine ⟨50777612094245353863574465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 270813931169308553939063813 50777612094245353863574465)
    ·
      refine ⟨38083209070684015397680849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50777612094245353863574465 38083209070684015397680849)
      ·
        refine ⟨28562406803013011548260637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38083209070684015397680849 28562406803013011548260637)
        ·
          refine ⟨10710902551129879330597739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28562406803013011548260637 10710902551129879330597739)
          ·
            refine ⟨16066353826694818995896609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10710902551129879330597739 16066353826694818995896609)
            ·
              refine ⟨12049765370021114246922457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16066353826694818995896609 12049765370021114246922457)
              ·
                refine ⟨9037324027515835685191843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12049765370021114246922457 9037324027515835685191843)
                ·
                  refine ⟨13555986041273753527787765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9037324027515835685191843 13555986041273753527787765)
                  ·
                    refine ⟨1270873691369414393230103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13555986041273753527787765 1270873691369414393230103)
                    ·
                      rfl

theorem cell23_7425053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 2, 2, 1, 5].length) (baseStart_7425053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7425053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7425053 prefixEnd_7425053 := by exact prefixLift 7425053
  have htrace : WordTrace (prefixWord ++ tailWord_7425053) baseStart_7425053 baseEnd_7425053 := by
    simpa [prefixWord, tailWord_7425053, baseEnd_7425053] using wordTrace_append hprefix tailTrace_7425053
  have hstable : (prefixWord ++ tailWord_7425053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7425053).length < 2 ^ (prefixWord ++ tailWord_7425053).sum := by decide
  have hdescent : baseEnd_7425053 < baseStart_7425053 := by decide
  rcases family_descends (prefixWord ++ tailWord_7425053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7425086 : List Nat := [4, 2, 1, 3, 1, 1, 1, 2, 1, 1, 6]
def baseStart_7425086 : Nat := 118140960795 + 7425086 * 2 ^ 59
def prefixEnd_7425086 : Nat := 4983230072969 + 3 ^ 40 * 7425086 * 2
def baseEnd_7425086 : Nat := 3812638018969841550577657

theorem tailTrace_7425086 : CollatzResearch.WordTrace tailWord_7425086 prefixEnd_7425086 3812638018969841550577657 := by
  unfold tailWord_7425086
  simp only [CollatzResearch.WordTrace]
  refine ⟨33851891847273625071876889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180543423185459333716676741 33851891847273625071876889)
  ·
    refine ⟨25388918885455218803907667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33851891847273625071876889 25388918885455218803907667)
    ·
      refine ⟨38083378328182828205861501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25388918885455218803907667 38083378328182828205861501)
      ·
        refine ⟨14281266873068560577198063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38083378328182828205861501 14281266873068560577198063)
        ·
          refine ⟨21421900309602840865797095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14281266873068560577198063 21421900309602840865797095)
          ·
            refine ⟨32132850464404261298695643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21421900309602840865797095 32132850464404261298695643)
            ·
              refine ⟨48199275696606391948043465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32132850464404261298695643 48199275696606391948043465)
              ·
                refine ⟨36149456772454793961032599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48199275696606391948043465 36149456772454793961032599)
                ·
                  refine ⟨54224185158682190941548899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36149456772454793961032599 54224185158682190941548899)
                  ·
                    refine ⟨81336277738023286412323349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54224185158682190941548899 81336277738023286412323349)
                    ·
                      refine ⟨3812638018969841550577657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81336277738023286412323349 3812638018969841550577657)
                      ·
                        rfl

theorem cell23_7425086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_7425086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7425086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7425086 prefixEnd_7425086 := by exact prefixLift 7425086
  have htrace : WordTrace (prefixWord ++ tailWord_7425086) baseStart_7425086 baseEnd_7425086 := by
    simpa [prefixWord, tailWord_7425086, baseEnd_7425086] using wordTrace_append hprefix tailTrace_7425086
  have hstable : (prefixWord ++ tailWord_7425086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7425086).length < 2 ^ (prefixWord ++ tailWord_7425086).sum := by decide
  have hdescent : baseEnd_7425086 < baseStart_7425086 := by decide
  rcases family_descends (prefixWord ++ tailWord_7425086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7425156 : List Nat := [2, 3, 2, 1, 2, 3, 1, 1, 2, 6]
def baseStart_7425156 : Nat := 118140960795 + 7425156 * 2 ^ 59
def prefixEnd_7425156 : Nat := 4983230072969 + 3 ^ 40 * 7425156 * 2
def baseEnd_7425156 : Nat := 1270891320871885425567445

theorem tailTrace_7425156 : CollatzResearch.WordTrace tailWord_7425156 prefixEnd_7425156 1270891320871885425567445 := by
  unfold tailWord_7425156
  simp only [CollatzResearch.WordTrace]
  refine ⟨135408843943967701265031661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180545125258623601686708881 135408843943967701265031661)
  ·
    refine ⟨50778316478987887974386873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135408843943967701265031661 50778316478987887974386873)
    ·
      refine ⟨38083737359240915980790155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50778316478987887974386873 38083737359240915980790155)
      ·
        refine ⟨57125606038861373971185233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38083737359240915980790155 57125606038861373971185233)
        ·
          refine ⟨42844204529146030478388925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57125606038861373971185233 42844204529146030478388925)
          ·
            refine ⟨16066576698429761429395847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42844204529146030478388925 16066576698429761429395847)
            ·
              refine ⟨24099865047644642144093771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16066576698429761429395847 24099865047644642144093771)
              ·
                refine ⟨36149797571466963216140657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24099865047644642144093771 36149797571466963216140657)
                ·
                  refine ⟨27112348178600222412105493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36149797571466963216140657 27112348178600222412105493)
                  ·
                    refine ⟨1270891320871885425567445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27112348178600222412105493 1270891320871885425567445)
                    ·
                      rfl

theorem cell23_7425156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 1, 2, 6].length) (baseStart_7425156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7425156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7425156 prefixEnd_7425156 := by exact prefixLift 7425156
  have htrace : WordTrace (prefixWord ++ tailWord_7425156) baseStart_7425156 baseEnd_7425156 := by
    simpa [prefixWord, tailWord_7425156, baseEnd_7425156] using wordTrace_append hprefix tailTrace_7425156
  have hstable : (prefixWord ++ tailWord_7425156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7425156).length < 2 ^ (prefixWord ++ tailWord_7425156).sum := by decide
  have hdescent : baseEnd_7425156 < baseStart_7425156 := by decide
  rcases family_descends (prefixWord ++ tailWord_7425156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7425197 : List Nat := [1, 5, 2, 1, 3, 1, 1, 1, 4, 2, 2]
def baseStart_7425197 : Nat := 118140960795 + 7425197 * 2 ^ 59
def prefixEnd_7425197 : Nat := 4983230072969 + 3 ^ 40 * 7425197 * 2
def baseEnd_7425197 : Nat := 3812695015322490616289647

theorem tailTrace_7425197 : CollatzResearch.WordTrace tailWord_7425197 prefixEnd_7425197 3812695015322490616289647 := by
  unfold tailWord_7425197
  simp only [CollatzResearch.WordTrace]
  refine ⟨270819183280786866532305845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180546122187191244354870563 270819183280786866532305845)
  ·
    refine ⟨25389298432573768737403673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 270819183280786866532305845 25389298432573768737403673)
    ·
      refine ⟨19041973824430326553052755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25389298432573768737403673 19041973824430326553052755)
      ·
        refine ⟨28562960736645489829579133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19041973824430326553052755 28562960736645489829579133)
        ·
          refine ⟨10711110276242058686092175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28562960736645489829579133 10711110276242058686092175)
          ·
            refine ⟨16066665414363088029138263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10711110276242058686092175 16066665414363088029138263)
            ·
              refine ⟨24099998121544632043707395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16066665414363088029138263 24099998121544632043707395)
              ·
                refine ⟨36149997182316948065561093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24099998121544632043707395 36149997182316948065561093)
                ·
                  refine ⟨6778124471684427762292705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36149997182316948065561093 6778124471684427762292705)
                  ·
                    refine ⟨5083593353763320821719529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6778124471684427762292705 5083593353763320821719529)
                    ·
                      refine ⟨3812695015322490616289647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5083593353763320821719529 3812695015322490616289647)
                      ·
                        rfl

theorem cell23_7425197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 1, 4, 2, 2].length) (baseStart_7425197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7425197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7425197 prefixEnd_7425197 := by exact prefixLift 7425197
  have htrace : WordTrace (prefixWord ++ tailWord_7425197) baseStart_7425197 baseEnd_7425197 := by
    simpa [prefixWord, tailWord_7425197, baseEnd_7425197] using wordTrace_append hprefix tailTrace_7425197
  have hstable : (prefixWord ++ tailWord_7425197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7425197).length < 2 ^ (prefixWord ++ tailWord_7425197).sum := by decide
  have hdescent : baseEnd_7425197 < baseStart_7425197 := by decide
  rcases family_descends (prefixWord ++ tailWord_7425197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7425214 : List Nat := [4, 2, 1, 1, 3, 2, 3, 1, 2, 2, 2]
def baseStart_7425214 : Nat := 118140960795 + 7425214 * 2 ^ 59
def prefixEnd_7425214 : Nat := 4983230072969 + 3 ^ 40 * 7425214 * 2
def baseEnd_7425214 : Nat := 3812703744493617049777069

theorem tailTrace_7425214 : CollatzResearch.WordTrace tailWord_7425214 prefixEnd_7425214 3812703744493617049777069 := by
  unfold tailWord_7425214
  simp only [CollatzResearch.WordTrace]
  refine ⟨33852475415215659804459337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180546535547816852290449797 33852475415215659804459337)
  ·
    refine ⟨25389356561411744853344503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33852475415215659804459337 25389356561411744853344503)
    ·
      refine ⟨38084034842117617280016755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25389356561411744853344503 38084034842117617280016755)
      ·
        refine ⟨57126052263176425920025133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38084034842117617280016755 57126052263176425920025133)
        ·
          refine ⟨21422269598691159720009425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57126052263176425920025133 21422269598691159720009425)
          ·
            refine ⟨16066702199018369790007069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21422269598691159720009425 16066702199018369790007069)
            ·
              refine ⟨6025013324631888671252651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16066702199018369790007069 6025013324631888671252651)
              ·
                refine ⟨9037519986947833006878977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6025013324631888671252651 9037519986947833006878977)
                ·
                  refine ⟨6778139990210874755159233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9037519986947833006878977 6778139990210874755159233)
                  ·
                    refine ⟨5083604992658156066369425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6778139990210874755159233 5083604992658156066369425)
                    ·
                      refine ⟨3812703744493617049777069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5083604992658156066369425 3812703744493617049777069)
                      ·
                        rfl

theorem cell23_7425214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 3, 1, 2, 2, 2].length) (baseStart_7425214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7425214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7425214 prefixEnd_7425214 := by exact prefixLift 7425214
  have htrace : WordTrace (prefixWord ++ tailWord_7425214) baseStart_7425214 baseEnd_7425214 := by
    simpa [prefixWord, tailWord_7425214, baseEnd_7425214] using wordTrace_append hprefix tailTrace_7425214
  have hstable : (prefixWord ++ tailWord_7425214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7425214).length < 2 ^ (prefixWord ++ tailWord_7425214).sum := by decide
  have hdescent : baseEnd_7425214 < baseStart_7425214 := by decide
  rcases family_descends (prefixWord ++ tailWord_7425214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7425313 : List Nat := [1, 2, 3, 2, 1, 1, 1, 2, 3, 5, 2]
def baseStart_7425313 : Nat := 118140960795 + 7425313 * 2 ^ 59
def prefixEnd_7425313 : Nat := 4983230072969 + 3 ^ 40 * 7425313 * 2
def baseEnd_7425313 : Nat := 3812754579078412162439113

theorem tailTrace_7425313 : CollatzResearch.WordTrace tailWord_7425313 prefixEnd_7425313 3812754579078412162439113 := by
  unfold tailWord_7425313
  simp only [CollatzResearch.WordTrace]
  refine ⟨270823414148366618343528593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180548942765577745562352395 270823414148366618343528593)
  ·
    refine ⟨203117560611274963757646445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270823414148366618343528593 203117560611274963757646445)
    ·
      refine ⟨76169085229228111409117417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 203117560611274963757646445 76169085229228111409117417)
      ·
        refine ⟨57126813921921083556838063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76169085229228111409117417 57126813921921083556838063)
        ·
          refine ⟨85690220882881625335257095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57126813921921083556838063 85690220882881625335257095)
          ·
            refine ⟨128535331324322438002885643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85690220882881625335257095 128535331324322438002885643)
            ·
              refine ⟨192802996986483657004328465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128535331324322438002885643 192802996986483657004328465)
              ·
                refine ⟨144602247739862742753246349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 192802996986483657004328465 144602247739862742753246349)
                ·
                  refine ⟨54225842902448528532467381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 144602247739862742753246349 54225842902448528532467381)
                  ·
                    refine ⟨5083672772104549549918817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54225842902448528532467381 5083672772104549549918817)
                    ·
                      refine ⟨3812754579078412162439113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5083672772104549549918817 3812754579078412162439113)
                      ·
                        rfl

theorem cell23_7425313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 3, 5, 2].length) (baseStart_7425313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7425313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7425313 prefixEnd_7425313 := by exact prefixLift 7425313
  have htrace : WordTrace (prefixWord ++ tailWord_7425313) baseStart_7425313 baseEnd_7425313 := by
    simpa [prefixWord, tailWord_7425313, baseEnd_7425313] using wordTrace_append hprefix tailTrace_7425313
  have hstable : (prefixWord ++ tailWord_7425313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7425313).length < 2 ^ (prefixWord ++ tailWord_7425313).sum := by decide
  have hdescent : baseEnd_7425313 < baseStart_7425313 := by decide
  rcases family_descends (prefixWord ++ tailWord_7425313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7425337 : List Nat := [1, 2, 1, 6, 2, 1, 1, 2, 3, 1, 3]
def baseStart_7425337 : Nat := 118140960795 + 7425337 * 2 ^ 59
def prefixEnd_7425337 : Nat := 4983230072969 + 3 ^ 40 * 7425337 * 2
def baseEnd_7425337 : Nat := 3812766902614120068539003

theorem tailTrace_7425337 : CollatzResearch.WordTrace tailWord_7425337 prefixEnd_7425337 3812766902614120068539003 := by
  unfold tailWord_7425337
  simp only [CollatzResearch.WordTrace]
  refine ⟨270824289500279670442402265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180549526333519780294934843 270824289500279670442402265)
  ·
    refine ⟨203118217125209752831801699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270824289500279670442402265 203118217125209752831801699)
    ·
      refine ⟨304677325687814629247702549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203118217125209752831801699 304677325687814629247702549)
      ·
        refine ⟨14281749641616310745986057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 304677325687814629247702549 14281749641616310745986057)
        ·
          refine ⟨10711312231212233059489543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14281749641616310745986057 10711312231212233059489543)
          ·
            refine ⟨16066968346818349589234315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10711312231212233059489543 16066968346818349589234315)
            ·
              refine ⟨24100452520227524383851473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16066968346818349589234315 24100452520227524383851473)
              ·
                refine ⟨18075339390170643287888605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24100452520227524383851473 18075339390170643287888605)
                ·
                  refine ⟨6778252271313991232958227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18075339390170643287888605 6778252271313991232958227)
                  ·
                    refine ⟨10167378406970986849437341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6778252271313991232958227 10167378406970986849437341)
                    ·
                      refine ⟨3812766902614120068539003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10167378406970986849437341 3812766902614120068539003)
                      ·
                        rfl

theorem cell23_7425337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_7425337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7425337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7425337 prefixEnd_7425337 := by exact prefixLift 7425337
  have htrace : WordTrace (prefixWord ++ tailWord_7425337) baseStart_7425337 baseEnd_7425337 := by
    simpa [prefixWord, tailWord_7425337, baseEnd_7425337] using wordTrace_append hprefix tailTrace_7425337
  have hstable : (prefixWord ++ tailWord_7425337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7425337).length < 2 ^ (prefixWord ++ tailWord_7425337).sum := by decide
  have hdescent : baseEnd_7425337 < baseStart_7425337 := by decide
  rcases family_descends (prefixWord ++ tailWord_7425337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7425343 : List Nat := [1, 1, 2, 2, 4, 2, 2, 1, 3, 1, 4]
def baseStart_7425343 : Nat := 118140960795 + 7425343 * 2 ^ 59
def prefixEnd_7425343 : Nat := 4983230072969 + 3 ^ 40 * 7425343 * 2
def baseEnd_7425343 : Nat := 3812769983498047045063975

theorem tailTrace_7425343 : CollatzResearch.WordTrace tailWord_7425343 prefixEnd_7425343 3812769983498047045063975 := by
  unfold tailWord_7425343
  simp only [CollatzResearch.WordTrace]
  refine ⟨270824508338257933467120683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180549672225505288978080455 270824508338257933467120683)
  ·
    refine ⟨406236762507386900200681025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270824508338257933467120683 406236762507386900200681025)
    ·
      refine ⟨304677571880540175150510769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 406236762507386900200681025 304677571880540175150510769)
      ·
        refine ⟨228508178910405131362883077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 304677571880540175150510769 228508178910405131362883077)
        ·
          refine ⟨42845283545700962130540577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 228508178910405131362883077 42845283545700962130540577)
          ·
            refine ⟨32133962659275721597905433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42845283545700962130540577 32133962659275721597905433)
            ·
              refine ⟨24100471994456791198429075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32133962659275721597905433 24100471994456791198429075)
              ·
                refine ⟨36150707991685186797643613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24100471994456791198429075 36150707991685186797643613)
                ·
                  refine ⟨13556515496881945049116355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36150707991685186797643613 13556515496881945049116355)
                  ·
                    refine ⟨20334773245322917573674533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13556515496881945049116355 20334773245322917573674533)
                    ·
                      refine ⟨3812769983498047045063975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20334773245322917573674533 3812769983498047045063975)
                      ·
                        rfl

theorem cell23_7425343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 1, 3, 1, 4].length) (baseStart_7425343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7425343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7425343 prefixEnd_7425343 := by exact prefixLift 7425343
  have htrace : WordTrace (prefixWord ++ tailWord_7425343) baseStart_7425343 baseEnd_7425343 := by
    simpa [prefixWord, tailWord_7425343, baseEnd_7425343] using wordTrace_append hprefix tailTrace_7425343
  have hstable : (prefixWord ++ tailWord_7425343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7425343).length < 2 ^ (prefixWord ++ tailWord_7425343).sum := by decide
  have hdescent : baseEnd_7425343 < baseStart_7425343 := by decide
  rcases family_descends (prefixWord ++ tailWord_7425343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7425360 : List Nat := [2, 1, 1, 1, 1, 5, 1, 2, 5, 2, 2]
def baseStart_7425360 : Nat := 118140960795 + 7425360 * 2 ^ 59
def prefixEnd_7425360 : Nat := 4983230072969 + 3 ^ 40 * 7425360 * 2
def baseEnd_7425360 : Nat := 3812778712669173478551397

theorem tailTrace_7425360 : CollatzResearch.WordTrace tailWord_7425360 prefixEnd_7425360 3812778712669173478551397 := by
  unfold tailWord_7425360
  simp only [CollatzResearch.WordTrace]
  refine ⟨135412564189598172685244767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180550085586130896913659689 135412564189598172685244767)
  ·
    refine ⟨203118846284397259027867151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135412564189598172685244767 203118846284397259027867151)
    ·
      refine ⟨304678269426595888541800727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203118846284397259027867151 304678269426595888541800727)
      ·
        refine ⟨457017404139893832812701091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304678269426595888541800727 457017404139893832812701091)
        ·
          refine ⟨685526106209840749219051637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 457017404139893832812701091 685526106209840749219051637)
          ·
            refine ⟨64268072457172570239286091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 685526106209840749219051637 64268072457172570239286091)
            ·
              refine ⟨96402108685758855358929137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64268072457172570239286091 96402108685758855358929137)
              ·
                refine ⟨72301581514319141519196853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96402108685758855358929137 72301581514319141519196853)
                ·
                  refine ⟨6778273266967419517424705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 72301581514319141519196853 6778273266967419517424705)
                  ·
                    refine ⟨5083704950225564638068529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6778273266967419517424705 5083704950225564638068529)
                    ·
                      refine ⟨3812778712669173478551397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5083704950225564638068529 3812778712669173478551397)
                      ·
                        rfl

theorem cell23_7425360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 2, 5, 2, 2].length) (baseStart_7425360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7425360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7425360 prefixEnd_7425360 := by exact prefixLift 7425360
  have htrace : WordTrace (prefixWord ++ tailWord_7425360) baseStart_7425360 baseEnd_7425360 := by
    simpa [prefixWord, tailWord_7425360, baseEnd_7425360] using wordTrace_append hprefix tailTrace_7425360
  have hstable : (prefixWord ++ tailWord_7425360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7425360).length < 2 ^ (prefixWord ++ tailWord_7425360).sum := by decide
  have hdescent : baseEnd_7425360 < baseStart_7425360 := by decide
  rcases family_descends (prefixWord ++ tailWord_7425360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7425370 : List Nat := [3, 1, 1, 2, 1, 2, 5, 2, 2, 4]
def baseStart_7425370 : Nat := 118140960795 + 7425370 * 2 ^ 59
def prefixEnd_7425370 : Nat := 4983230072969 + 3 ^ 40 * 7425370 * 2
def baseEnd_7425370 : Nat := 1270927949158572813142117

theorem tailTrace_7425370 : CollatzResearch.WordTrace tailWord_7425370 prefixEnd_7425370 1270927949158572813142117 := by
  unfold tailWord_7425370
  simp only [CollatzResearch.WordTrace]
  refine ⟨67706373277290029269588391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180550328739440078052235709 67706373277290029269588391)
  ·
    refine ⟨101559559915935043904382587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67706373277290029269588391 101559559915935043904382587)
    ·
      refine ⟨152339339873902565856573881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101559559915935043904382587 152339339873902565856573881)
      ·
        refine ⟨114254504905426924392430411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152339339873902565856573881 114254504905426924392430411)
        ·
          refine ⟨171381757358140386588645617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114254504905426924392430411 171381757358140386588645617)
          ·
            refine ⟨128536318018605289941484213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171381757358140386588645617 128536318018605289941484213)
            ·
              refine ⟨12050279814244245932014145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 128536318018605289941484213 12050279814244245932014145)
              ·
                refine ⟨9037709860683184449010609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12050279814244245932014145 9037709860683184449010609)
                ·
                  refine ⟨6778282395512388336757957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9037709860683184449010609 6778282395512388336757957)
                  ·
                    refine ⟨1270927949158572813142117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6778282395512388336757957 1270927949158572813142117)
                    ·
                      rfl

theorem cell23_7425370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 5, 2, 2, 4].length) (baseStart_7425370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7425370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7425370 prefixEnd_7425370 := by exact prefixLift 7425370
  have htrace : WordTrace (prefixWord ++ tailWord_7425370) baseStart_7425370 baseEnd_7425370 := by
    simpa [prefixWord, tailWord_7425370, baseEnd_7425370] using wordTrace_append hprefix tailTrace_7425370
  have hstable : (prefixWord ++ tailWord_7425370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7425370).length < 2 ^ (prefixWord ++ tailWord_7425370).sum := by decide
  have hdescent : baseEnd_7425370 < baseStart_7425370 := by decide
  rcases family_descends (prefixWord ++ tailWord_7425370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7425411 : List Nat := [1, 1, 1, 3, 5, 3, 1, 3, 1, 2, 2]
def baseStart_7425411 : Nat := 118140960795 + 7425411 * 2 ^ 59
def prefixEnd_7425411 : Nat := 4983230072969 + 3 ^ 40 * 7425411 * 2
def baseEnd_7425411 : Nat := 3812804900182552779013663

theorem tailTrace_7425411 : CollatzResearch.WordTrace tailWord_7425411 prefixEnd_7425411 3812804900182552779013663 := by
  unfold tailWord_7425411
  simp only [CollatzResearch.WordTrace]
  refine ⟨270826988502011581080596087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180551325668007720720397391 270826988502011581080596087)
  ·
    refine ⟨406240482753017371620894131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270826988502011581080596087 406240482753017371620894131)
    ·
      refine ⟨609360724129526057431341197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 406240482753017371620894131 609360724129526057431341197)
      ·
        refine ⟨228510271548572271536752949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 609360724129526057431341197 228510271548572271536752949)
        ·
          refine ⟨21422837957678650456570589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 228510271548572271536752949 21422837957678650456570589)
          ·
            refine ⟨8033564234129493921213971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21422837957678650456570589 8033564234129493921213971)
            ·
              refine ⟨12050346351194240881820957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8033564234129493921213971 12050346351194240881820957)
              ·
                refine ⟨4518879881697840330682859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12050346351194240881820957 4518879881697840330682859)
                ·
                  refine ⟨6778319822546760496024289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4518879881697840330682859 6778319822546760496024289)
                  ·
                    refine ⟨5083739866910070372018217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6778319822546760496024289 5083739866910070372018217)
                    ·
                      refine ⟨3812804900182552779013663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5083739866910070372018217 3812804900182552779013663)
                      ·
                        rfl

theorem cell23_7425411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 1, 3, 1, 2, 2].length) (baseStart_7425411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7425411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7425411 prefixEnd_7425411 := by exact prefixLift 7425411
  have htrace : WordTrace (prefixWord ++ tailWord_7425411) baseStart_7425411 baseEnd_7425411 := by
    simpa [prefixWord, tailWord_7425411, baseEnd_7425411] using wordTrace_append hprefix tailTrace_7425411
  have hstable : (prefixWord ++ tailWord_7425411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7425411).length < 2 ^ (prefixWord ++ tailWord_7425411).sum := by decide
  have hdescent : baseEnd_7425411 < baseStart_7425411 := by decide
  rcases family_descends (prefixWord ++ tailWord_7425411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7425428 : List Nat := [2, 4, 2, 1, 2, 2, 3, 2, 1, 2, 2]
def baseStart_7425428 : Nat := 118140960795 + 7425428 * 2 ^ 59
def prefixEnd_7425428 : Nat := 4983230072969 + 3 ^ 40 * 7425428 * 2
def baseEnd_7425428 : Nat := 3812813629353679212501085

theorem tailTrace_7425428 : CollatzResearch.WordTrace tailWord_7425428 prefixEnd_7425428 3812813629353679212501085 := by
  unfold tailWord_7425428
  simp only [CollatzResearch.WordTrace]
  refine ⟨135413804271474996491982469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180551739028633328655976625 135413804271474996491982469)
  ·
    refine ⟨25390088300901561842246713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135413804271474996491982469 25390088300901561842246713)
    ·
      refine ⟨19042566225676171381685035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25390088300901561842246713 19042566225676171381685035)
      ·
        refine ⟨28563849338514257072527553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19042566225676171381685035 28563849338514257072527553)
        ·
          refine ⟨21422887003885692804395665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28563849338514257072527553 21422887003885692804395665)
          ·
            refine ⟨16067165252914269603296749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21422887003885692804395665 16067165252914269603296749)
            ·
              refine ⟨6025186969842851101236281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16067165252914269603296749 6025186969842851101236281)
              ·
                refine ⟨4518890227382138325927211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6025186969842851101236281 4518890227382138325927211)
                ·
                  refine ⟨6778335341073207488890817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4518890227382138325927211 6778335341073207488890817)
                  ·
                    refine ⟨5083751505804905616668113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6778335341073207488890817 5083751505804905616668113)
                    ·
                      refine ⟨3812813629353679212501085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5083751505804905616668113 3812813629353679212501085)
                      ·
                        rfl

theorem cell23_7425428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 3, 2, 1, 2, 2].length) (baseStart_7425428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7425428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7425428 prefixEnd_7425428 := by exact prefixLift 7425428
  have htrace : WordTrace (prefixWord ++ tailWord_7425428) baseStart_7425428 baseEnd_7425428 := by
    simpa [prefixWord, tailWord_7425428, baseEnd_7425428] using wordTrace_append hprefix tailTrace_7425428
  have hstable : (prefixWord ++ tailWord_7425428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7425428).length < 2 ^ (prefixWord ++ tailWord_7425428).sum := by decide
  have hdescent : baseEnd_7425428 < baseStart_7425428 := by decide
  rcases family_descends (prefixWord ++ tailWord_7425428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7425438 : List Nat := [4, 3, 1, 2, 3, 1, 2, 1, 2, 4]
def baseStart_7425438 : Nat := 118140960795 + 7425438 * 2 ^ 59
def prefixEnd_7425438 : Nat := 4983230072969 + 3 ^ 40 * 7425438 * 2
def baseEnd_7425438 : Nat := 1270939588053408057792013

theorem tailTrace_7425438 : CollatzResearch.WordTrace tailWord_7425438 prefixEnd_7425438 1270939588053408057792013 := by
  unfold tailWord_7425438
  simp only [CollatzResearch.WordTrace]
  refine ⟨33853496659114220586478621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180551982181942509794552645 33853496659114220586478621)
  ·
    refine ⟨12695061247167832719929483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33853496659114220586478621 12695061247167832719929483)
    ·
      refine ⟨19042591870751749079894225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12695061247167832719929483 19042591870751749079894225)
      ·
        refine ⟨14281943903063811809920669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19042591870751749079894225 14281943903063811809920669)
        ·
          refine ⟨5355728963648929428720251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14281943903063811809920669 5355728963648929428720251)
          ·
            refine ⟨8033593445473394143080377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5355728963648929428720251 8033593445473394143080377)
            ·
              refine ⟨6025195084105045607310283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8033593445473394143080377 6025195084105045607310283)
              ·
                refine ⟨9037792626157568410965425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6025195084105045607310283 9037792626157568410965425)
                ·
                  refine ⟨6778344469618176308224069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9037792626157568410965425 6778344469618176308224069)
                  ·
                    refine ⟨1270939588053408057792013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6778344469618176308224069 1270939588053408057792013)
                    ·
                      rfl

theorem cell23_7425438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 2, 1, 2, 4].length) (baseStart_7425438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7425438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7425438 prefixEnd_7425438 := by exact prefixLift 7425438
  have htrace : WordTrace (prefixWord ++ tailWord_7425438) baseStart_7425438 baseEnd_7425438 := by
    simpa [prefixWord, tailWord_7425438, baseEnd_7425438] using wordTrace_append hprefix tailTrace_7425438
  have hstable : (prefixWord ++ tailWord_7425438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7425438).length < 2 ^ (prefixWord ++ tailWord_7425438).sum := by decide
  have hdescent : baseEnd_7425438 < baseStart_7425438 := by decide
  rcases family_descends (prefixWord ++ tailWord_7425438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7425484 : List Nat := [2, 2, 1, 4, 2, 1, 1, 4, 2, 2, 2]
def baseStart_7425484 : Nat := 118140960795 + 7425484 * 2 ^ 59
def prefixEnd_7425484 : Nat := 4983230072969 + 3 ^ 40 * 7425484 * 2
def baseEnd_7425484 : Nat := 3812842384270330993400827

theorem tailTrace_7425484 : CollatzResearch.WordTrace tailWord_7425484 prefixEnd_7425484 3812842384270330993400827 := by
  unfold tailWord_7425484
  simp only [CollatzResearch.WordTrace]
  refine ⟨135414825515373557274001753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180553100687164743032002337 135414825515373557274001753)
  ·
    refine ⟨101561119136530167955501315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135414825515373557274001753 101561119136530167955501315)
    ·
      refine ⟨152341678704795251933251973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101561119136530167955501315 152341678704795251933251973)
      ·
        refine ⟨28564064757149109737484745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 152341678704795251933251973 28564064757149109737484745)
        ·
          refine ⟨21423048567861832303113559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28564064757149109737484745 21423048567861832303113559)
          ·
            refine ⟨32134572851792748454670339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21423048567861832303113559 32134572851792748454670339)
            ·
              refine ⟨48201859277689122682005509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32134572851792748454670339 48201859277689122682005509)
              ·
                refine ⟨9037848614566710502876033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48201859277689122682005509 9037848614566710502876033)
                ·
                  refine ⟨6778386460925032877157025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9037848614566710502876033 6778386460925032877157025)
                  ·
                    refine ⟨5083789845693774657867769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6778386460925032877157025 5083789845693774657867769)
                    ·
                      refine ⟨3812842384270330993400827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5083789845693774657867769 3812842384270330993400827)
                      ·
                        rfl

theorem cell23_7425484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 4, 2, 2, 2].length) (baseStart_7425484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7425484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7425484 prefixEnd_7425484 := by exact prefixLift 7425484
  have htrace : WordTrace (prefixWord ++ tailWord_7425484) baseStart_7425484 baseEnd_7425484 := by
    simpa [prefixWord, tailWord_7425484, baseEnd_7425484] using wordTrace_append hprefix tailTrace_7425484
  have hstable : (prefixWord ++ tailWord_7425484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7425484).length < 2 ^ (prefixWord ++ tailWord_7425484).sum := by decide
  have hdescent : baseEnd_7425484 < baseStart_7425484 := by decide
  rcases family_descends (prefixWord ++ tailWord_7425484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7425503 : List Nat := [1, 1, 2, 3, 3, 1, 2, 2, 1, 7]
def baseStart_7425503 : Nat := 118140960795 + 7425503 * 2 ^ 59
def prefixEnd_7425503 : Nat := 4983230072969 + 3 ^ 40 * 7425503 * 2
def baseEnd_7425503 : Nat := 1270950713467588806354413

theorem tailTrace_7425503 : CollatzResearch.WordTrace tailWord_7425503 prefixEnd_7425503 1270950713467588806354413 := by
  unfold tailWord_7425503
  simp only [CollatzResearch.WordTrace]
  refine ⟨270830344017678280792945163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180553562678452187195296775 270830344017678280792945163)
  ·
    refine ⟨406245516026517421189417745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270830344017678280792945163 406245516026517421189417745)
    ·
      refine ⟨304684137019888065892063309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 406245516026517421189417745 304684137019888065892063309)
      ·
        refine ⟨114256551382458024709523741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 304684137019888065892063309 114256551382458024709523741)
        ·
          refine ⟨42846206768421759266071403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114256551382458024709523741 42846206768421759266071403)
          ·
            refine ⟨64269310152632638899107105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42846206768421759266071403 64269310152632638899107105)
            ·
              refine ⟨48201982614474479174330329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64269310152632638899107105 48201982614474479174330329)
              ·
                refine ⟨36151486960855859380747747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48201982614474479174330329 36151486960855859380747747)
                ·
                  refine ⟨54227230441283789071121621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36151486960855859380747747 54227230441283789071121621)
                  ·
                    refine ⟨1270950713467588806354413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54227230441283789071121621 1270950713467588806354413)
                    ·
                      rfl

theorem cell23_7425503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 2, 1, 7].length) (baseStart_7425503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7425503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7425503 prefixEnd_7425503 := by exact prefixLift 7425503
  have htrace : WordTrace (prefixWord ++ tailWord_7425503) baseStart_7425503 baseEnd_7425503 := by
    simpa [prefixWord, tailWord_7425503, baseEnd_7425503] using wordTrace_append hprefix tailTrace_7425503
  have hstable : (prefixWord ++ tailWord_7425503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7425503).length < 2 ^ (prefixWord ++ tailWord_7425503).sum := by decide
  have hdescent : baseEnd_7425503 < baseStart_7425503 := by decide
  rcases family_descends (prefixWord ++ tailWord_7425503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7425520 : List Nat := [2, 1, 1, 1, 3, 4, 3, 1, 2, 5]
def baseStart_7425520 : Nat := 118140960795 + 7425520 * 2 ^ 59
def prefixEnd_7425520 : Nat := 4983230072969 + 3 ^ 40 * 7425520 * 2
def baseEnd_7425520 : Nat := 1270953623191297617516887

theorem tailTrace_7425520 : CollatzResearch.WordTrace tailWord_7425520 prefixEnd_7425520 1270953623191297617516887 := by
  unfold tailWord_7425520
  simp only [CollatzResearch.WordTrace]
  refine ⟨135415482029308346348157007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180553976039077795130876009 135415482029308346348157007)
  ·
    refine ⟨203123223043962519522235511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135415482029308346348157007 203123223043962519522235511)
    ·
      refine ⟨304684834565943779283353267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203123223043962519522235511 304684834565943779283353267)
      ·
        refine ⟨457027251848915668925029901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304684834565943779283353267 457027251848915668925029901)
        ·
          refine ⟨171385219443343375846886213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 457027251848915668925029901 171385219443343375846886213)
          ·
            refine ⟨32134728645626882971291165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 171385219443343375846886213 32134728645626882971291165)
            ·
              refine ⟨12050523242110081114234187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32134728645626882971291165 12050523242110081114234187)
              ·
                refine ⟨18075784863165121671351281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12050523242110081114234187 18075784863165121671351281)
                ·
                  refine ⟨13556838647373841253513461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18075784863165121671351281 13556838647373841253513461)
                  ·
                    refine ⟨1270953623191297617516887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13556838647373841253513461 1270953623191297617516887)
                    ·
                      rfl

theorem cell23_7425520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 3, 1, 2, 5].length) (baseStart_7425520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7425520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7425520 prefixEnd_7425520 := by exact prefixLift 7425520
  have htrace : WordTrace (prefixWord ++ tailWord_7425520) baseStart_7425520 baseEnd_7425520 := by
    simpa [prefixWord, tailWord_7425520, baseEnd_7425520] using wordTrace_append hprefix tailTrace_7425520
  have hstable : (prefixWord ++ tailWord_7425520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7425520).length < 2 ^ (prefixWord ++ tailWord_7425520).sum := by decide
  have hdescent : baseEnd_7425520 < baseStart_7425520 := by decide
  rcases family_descends (prefixWord ++ tailWord_7425520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7425553 : List Nat := [1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 6]
def baseStart_7425553 : Nat := 118140960795 + 7425553 * 2 ^ 59
def prefixEnd_7425553 : Nat := 4983230072969 + 3 ^ 40 * 7425553 * 2
def baseEnd_7425553 : Nat := 3812877814435491223438009

theorem tailTrace_7425553 : CollatzResearch.WordTrace tailWord_7425553 prefixEnd_7425553 3812877814435491223438009 := by
  unfold tailWord_7425553
  simp only [CollatzResearch.WordTrace]
  refine ⟨270832167667497139332265313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180554778444998092888176875 270832167667497139332265313)
  ·
    refine ⟨203124125750622854499198985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270832167667497139332265313 203124125750622854499198985)
    ·
      refine ⟨152343094312967140874399239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203124125750622854499198985 152343094312967140874399239)
      ·
        refine ⟨228514641469450711311598859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152343094312967140874399239 228514641469450711311598859)
        ·
          refine ⟨342771962204176066967398289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228514641469450711311598859 342771962204176066967398289)
          ·
            refine ⟨257078971653132050225548717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 342771962204176066967398289 257078971653132050225548717)
            ·
              refine ⟨96404614369924518834580769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 257078971653132050225548717 96404614369924518834580769)
              ·
                refine ⟨72303460777443389125935577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96404614369924518834580769 72303460777443389125935577)
                ·
                  refine ⟨54227595583082541844451683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72303460777443389125935577 54227595583082541844451683)
                  ·
                    refine ⟨81341393374623812766677525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54227595583082541844451683 81341393374623812766677525)
                    ·
                      refine ⟨3812877814435491223438009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81341393374623812766677525 3812877814435491223438009)
                      ·
                        rfl

theorem cell23_7425553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 6].length) (baseStart_7425553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7425553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7425553 prefixEnd_7425553 := by exact prefixLift 7425553
  have htrace : WordTrace (prefixWord ++ tailWord_7425553) baseStart_7425553 baseEnd_7425553 := by
    simpa [prefixWord, tailWord_7425553, baseEnd_7425553] using wordTrace_append hprefix tailTrace_7425553
  have hstable : (prefixWord ++ tailWord_7425553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7425553).length < 2 ^ (prefixWord ++ tailWord_7425553).sum := by decide
  have hdescent : baseEnd_7425553 < baseStart_7425553 := by decide
  rcases family_descends (prefixWord ++ tailWord_7425553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7425557 : List Nat := [1, 3, 2, 1, 3, 2, 2, 1, 2, 4, 2]
def baseStart_7425557 : Nat := 118140960795 + 7425557 * 2 ^ 59
def prefixEnd_7425557 : Nat := 4983230072969 + 3 ^ 40 * 7425557 * 2
def baseEnd_7425557 : Nat := 3812879868358109207787991

theorem tailTrace_7425557 : CollatzResearch.WordTrace tailWord_7425557 prefixEnd_7425557 3812879868358109207787991 := by
  unfold tailWord_7425557
  simp only [CollatzResearch.WordTrace]
  refine ⟨270832313559482648015410925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180554875706321765343607283 270832313559482648015410925)
  ·
    refine ⟨101562117584805993005779097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 270832313559482648015410925 101562117584805993005779097)
    ·
      refine ⟨76171588188604494754334323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101562117584805993005779097 76171588188604494754334323)
      ·
        refine ⟨114257382282906742131501485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76171588188604494754334323 114257382282906742131501485)
        ·
          refine ⟨42846518356090028299313057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114257382282906742131501485 42846518356090028299313057)
          ·
            refine ⟨32134888767067521224484793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42846518356090028299313057 32134888767067521224484793)
            ·
              refine ⟨24101166575300640918363595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32134888767067521224484793 24101166575300640918363595)
              ·
                refine ⟨36151749862950961377545393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24101166575300640918363595 36151749862950961377545393)
                ·
                  refine ⟨27113812397213221033159045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36151749862950961377545393 27113812397213221033159045)
                  ·
                    refine ⟨5083839824477478943717321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27113812397213221033159045 5083839824477478943717321)
                    ·
                      refine ⟨3812879868358109207787991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5083839824477478943717321 3812879868358109207787991)
                      ·
                        rfl

theorem cell23_7425557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 1, 2, 4, 2].length) (baseStart_7425557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7425557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7425557 prefixEnd_7425557 := by exact prefixLift 7425557
  have htrace : WordTrace (prefixWord ++ tailWord_7425557) baseStart_7425557 baseEnd_7425557 := by
    simpa [prefixWord, tailWord_7425557, baseEnd_7425557] using wordTrace_append hprefix tailTrace_7425557
  have hstable : (prefixWord ++ tailWord_7425557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7425557).length < 2 ^ (prefixWord ++ tailWord_7425557).sum := by decide
  have hdescent : baseEnd_7425557 < baseStart_7425557 := by decide
  rcases family_descends (prefixWord ++ tailWord_7425557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7425601 : List Nat := [1, 2, 5, 1, 1, 1, 5, 2, 1, 4]
def baseStart_7425601 : Nat := 118140960795 + 7425601 * 2 ^ 59
def prefixEnd_7425601 : Nat := 4983230072969 + 3 ^ 40 * 7425601 * 2
def baseEnd_7425601 : Nat := 1270967487168969011879263

theorem tailTrace_7425601 : CollatzResearch.WordTrace tailWord_7425601 prefixEnd_7425601 1270967487168969011879263 := by
  unfold tailWord_7425601
  simp only [CollatzResearch.WordTrace]
  refine ⟨270833918371323243530012657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180555945580882162353341771 270833918371323243530012657)
  ·
    refine ⟨203125438778492432647509493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270833918371323243530012657 203125438778492432647509493)
    ·
      refine ⟨19043009885483665560704015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 203125438778492432647509493 19043009885483665560704015)
      ·
        refine ⟨28564514828225498341056023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19043009885483665560704015 28564514828225498341056023)
        ·
          refine ⟨42846772242338247511584035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28564514828225498341056023 42846772242338247511584035)
          ·
            refine ⟨64270158363507371267376053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42846772242338247511584035 64270158363507371267376053)
            ·
              refine ⟨6025327346578816056316505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64270158363507371267376053 6025327346578816056316505)
              ·
                refine ⟨4518995509934112042237379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6025327346578816056316505 4518995509934112042237379)
                ·
                  refine ⟨6778493264901168063356069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4518995509934112042237379 6778493264901168063356069)
                  ·
                    refine ⟨1270967487168969011879263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6778493264901168063356069 1270967487168969011879263)
                    ·
                      rfl

theorem cell23_7425601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 5, 2, 1, 4].length) (baseStart_7425601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7425601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7425601 prefixEnd_7425601 := by exact prefixLift 7425601
  have htrace : WordTrace (prefixWord ++ tailWord_7425601) baseStart_7425601 baseEnd_7425601 := by
    simpa [prefixWord, tailWord_7425601, baseEnd_7425601] using wordTrace_append hprefix tailTrace_7425601
  have hstable : (prefixWord ++ tailWord_7425601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7425601).length < 2 ^ (prefixWord ++ tailWord_7425601).sum := by decide
  have hdescent : baseEnd_7425601 < baseStart_7425601 := by decide
  rcases family_descends (prefixWord ++ tailWord_7425601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7425603 : List Nat := [1, 1, 1, 3, 1, 2, 1, 1, 4, 1, 7]
def baseStart_7425603 : Nat := 118140960795 + 7425603 * 2 ^ 59
def prefixEnd_7425603 : Nat := 4983230072969 + 3 ^ 40 * 7425603 * 2
def baseEnd_7425603 : Nat := 3812903488468216027812779

theorem tailTrace_7425603 : CollatzResearch.WordTrace tailWord_7425603 prefixEnd_7425603 3812903488468216027812779 := by
  unfold tailWord_7425603
  simp only [CollatzResearch.WordTrace]
  refine ⟨270833991317315997871585463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180555994211543998581056975 270833991317315997871585463)
  ·
    refine ⟨406250986975973996807378195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270833991317315997871585463 406250986975973996807378195)
    ·
      refine ⟨609376480463960995211067293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 406250986975973996807378195 609376480463960995211067293)
      ·
        refine ⟨228516180173985373204150235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 609376480463960995211067293 228516180173985373204150235)
        ·
          refine ⟨342774270260978059806225353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228516180173985373204150235 342774270260978059806225353)
          ·
            refine ⟨257080702695733544854669015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 342774270260978059806225353 257080702695733544854669015)
            ·
              refine ⟨385621054043600317282003523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 257080702695733544854669015 385621054043600317282003523)
              ·
                refine ⟨578431581065400475923005285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 385621054043600317282003523 578431581065400475923005285)
                ·
                  refine ⟨108455921449762589235563491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 578431581065400475923005285 108455921449762589235563491)
                  ·
                    refine ⟨162683882174643883853345237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 108455921449762589235563491 162683882174643883853345237)
                    ·
                      refine ⟨3812903488468216027812779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 162683882174643883853345237 3812903488468216027812779)
                      ·
                        rfl

theorem cell23_7425603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 4, 1, 7].length) (baseStart_7425603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7425603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7425603 prefixEnd_7425603 := by exact prefixLift 7425603
  have htrace : WordTrace (prefixWord ++ tailWord_7425603) baseStart_7425603 baseEnd_7425603 := by
    simpa [prefixWord, tailWord_7425603, baseEnd_7425603] using wordTrace_append hprefix tailTrace_7425603
  have hstable : (prefixWord ++ tailWord_7425603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7425603).length < 2 ^ (prefixWord ++ tailWord_7425603).sum := by decide
  have hdescent : baseEnd_7425603 < baseStart_7425603 := by decide
  rcases family_descends (prefixWord ++ tailWord_7425603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7425610 : List Nat := [3, 1, 2, 1, 1, 3, 2, 2, 3, 5]
def baseStart_7425610 : Nat := 118140960795 + 7425610 * 2 ^ 59
def prefixEnd_7425610 : Nat := 4983230072969 + 3 ^ 40 * 7425610 * 2
def baseEnd_7425610 : Nat := 1270969027610932500141749

theorem tailTrace_7425610 : CollatzResearch.WordTrace tailWord_7425610 prefixEnd_7425610 1270969027610932500141749 := by
  unfold tailWord_7425610
  simp only [CollatzResearch.WordTrace]
  refine ⟨67708561657072659516772571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180556164418860425378060189 67708561657072659516772571)
  ·
    refine ⟨101562842485608989275158857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67708561657072659516772571 101562842485608989275158857)
    ·
      refine ⟨76172131864206741956369143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101562842485608989275158857 76172131864206741956369143)
      ·
        refine ⟨114258197796310112934553715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76172131864206741956369143 114258197796310112934553715)
        ·
          refine ⟨171387296694465169401830573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114258197796310112934553715 171387296694465169401830573)
          ·
            refine ⟨64270236260424438525686465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 171387296694465169401830573 64270236260424438525686465)
            ·
              refine ⟨48202677195318328894264849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64270236260424438525686465 48202677195318328894264849)
              ·
                refine ⟨36152007896488746670698637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48202677195318328894264849 36152007896488746670698637)
                ·
                  refine ⟨13557002961183280001511989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36152007896488746670698637 13557002961183280001511989)
                  ·
                    refine ⟨1270969027610932500141749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13557002961183280001511989 1270969027610932500141749)
                    ·
                      rfl

theorem cell23_7425610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 2, 3, 5].length) (baseStart_7425610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7425610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7425610 prefixEnd_7425610 := by exact prefixLift 7425610
  have htrace : WordTrace (prefixWord ++ tailWord_7425610) baseStart_7425610 baseEnd_7425610 := by
    simpa [prefixWord, tailWord_7425610, baseEnd_7425610] using wordTrace_append hprefix tailTrace_7425610
  have hstable : (prefixWord ++ tailWord_7425610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7425610).length < 2 ^ (prefixWord ++ tailWord_7425610).sum := by decide
  have hdescent : baseEnd_7425610 < baseStart_7425610 := by decide
  rcases family_descends (prefixWord ++ tailWord_7425610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7425617 : List Nat := [1, 2, 2, 1, 3, 2, 1, 2, 4, 3, 2]
def baseStart_7425617 : Nat := 118140960795 + 7425617 * 2 ^ 59
def prefixEnd_7425617 : Nat := 4983230072969 + 3 ^ 40 * 7425617 * 2
def baseEnd_7425617 : Nat := 3812910677197378973037715

theorem tailTrace_7425617 : CollatzResearch.WordTrace tailWord_7425617 prefixEnd_7425617 3812910677197378973037715 := by
  unfold tailWord_7425617
  simp only [CollatzResearch.WordTrace]
  refine ⟨270834501939265278262595105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180556334626176852175063403 270834501939265278262595105)
  ·
    refine ⟨203125876454448958696946329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270834501939265278262595105 203125876454448958696946329)
    ·
      refine ⟨152344407340836719022709747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203125876454448958696946329 152344407340836719022709747)
      ·
        refine ⟨228516611011255078534064621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152344407340836719022709747 228516611011255078534064621)
        ·
          refine ⟨85693729129220654450274233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 228516611011255078534064621 85693729129220654450274233)
          ·
            refine ⟨64270296846915490837705675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85693729129220654450274233 64270296846915490837705675)
            ·
              refine ⟨96405445270373236256558513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64270296846915490837705675 96405445270373236256558513)
              ·
                refine ⟨72304083952779927192418885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96405445270373236256558513 72304083952779927192418885)
                ·
                  refine ⟨13557015741146236348578541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72304083952779927192418885 13557015741146236348578541)
                  ·
                    refine ⟨5083880902929838630716953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13557015741146236348578541 5083880902929838630716953)
                    ·
                      refine ⟨3812910677197378973037715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5083880902929838630716953 3812910677197378973037715)
                      ·
                        rfl

theorem cell23_7425617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 2, 4, 3, 2].length) (baseStart_7425617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7425617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7425617 prefixEnd_7425617 := by exact prefixLift 7425617
  have htrace : WordTrace (prefixWord ++ tailWord_7425617) baseStart_7425617 baseEnd_7425617 := by
    simpa [prefixWord, tailWord_7425617, baseEnd_7425617] using wordTrace_append hprefix tailTrace_7425617
  have hstable : (prefixWord ++ tailWord_7425617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7425617).length < 2 ^ (prefixWord ++ tailWord_7425617).sum := by decide
  have hdescent : baseEnd_7425617 < baseStart_7425617 := by decide
  rcases family_descends (prefixWord ++ tailWord_7425617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7425660 : List Nat := [2, 2, 2, 1, 1, 2, 1, 1, 5, 2, 4]
def baseStart_7425660 : Nat := 118140960795 + 7425660 * 2 ^ 59
def prefixEnd_7425660 : Nat := 4983230072969 + 3 ^ 40 * 7425660 * 2
def baseEnd_7425660 : Nat := 3812932756865522304800017

theorem tailTrace_7425660 : CollatzResearch.WordTrace tailWord_7425660 prefixEnd_7425660 3812932756865522304800017 := by
  unfold tailWord_7425660
  simp only [CollatzResearch.WordTrace]
  refine ⟨135418035139054748303205217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180557380185406331070940289 135418035139054748303205217)
  ·
    refine ⟨101563526354291061227403913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135418035139054748303205217 101563526354291061227403913)
    ·
      refine ⟨76172644765718295920552935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101563526354291061227403913 76172644765718295920552935)
      ·
        refine ⟨114258967148577443880829403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76172644765718295920552935 114258967148577443880829403)
        ·
          refine ⟨171388450722866165821244105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114258967148577443880829403 171388450722866165821244105)
          ·
            refine ⟨128541338042149624365933079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171388450722866165821244105 128541338042149624365933079)
            ·
              refine ⟨192812007063224436548899619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128541338042149624365933079 192812007063224436548899619)
              ·
                refine ⟨289218010594836654823349429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 192812007063224436548899619 289218010594836654823349429)
                ·
                  refine ⟨27114188493265936389689009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 289218010594836654823349429 27114188493265936389689009)
                  ·
                    refine ⟨20335641369949452292266757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27114188493265936389689009 20335641369949452292266757)
                    ·
                      refine ⟨3812932756865522304800017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20335641369949452292266757 3812932756865522304800017)
                      ·
                        rfl

theorem cell23_7425660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 5, 2, 4].length) (baseStart_7425660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7425660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7425660 prefixEnd_7425660 := by exact prefixLift 7425660
  have htrace : WordTrace (prefixWord ++ tailWord_7425660) baseStart_7425660 baseEnd_7425660 := by
    simpa [prefixWord, tailWord_7425660, baseEnd_7425660] using wordTrace_append hprefix tailTrace_7425660
  have hstable : (prefixWord ++ tailWord_7425660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7425660).length < 2 ^ (prefixWord ++ tailWord_7425660).sum := by decide
  have hdescent : baseEnd_7425660 < baseStart_7425660 := by decide
  rcases family_descends (prefixWord ++ tailWord_7425660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7425664 : List Nat := [2, 1, 1, 2, 1, 4, 2, 3, 3, 2, 2]
def baseStart_7425664 : Nat := 118140960795 + 7425664 * 2 ^ 59
def prefixEnd_7425664 : Nat := 4983230072969 + 3 ^ 40 * 7425664 * 2
def baseEnd_7425664 : Nat := 3812934810788140289149999

theorem tailTrace_7425664 : CollatzResearch.WordTrace tailWord_7425664 prefixEnd_7425664 3812934810788140289149999 := by
  unfold tailWord_7425664
  simp only [CollatzResearch.WordTrace]
  refine ⟨135418108085047502644778023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180557477446730003526370697 135418108085047502644778023)
  ·
    refine ⟨203127162127571253967167035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135418108085047502644778023 203127162127571253967167035)
    ·
      refine ⟨304690743191356880950750553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203127162127571253967167035 304690743191356880950750553)
      ·
        refine ⟨228518057393517660713062915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 304690743191356880950750553 228518057393517660713062915)
        ·
          refine ⟨342777086090276491069594373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228518057393517660713062915 342777086090276491069594373)
          ·
            refine ⟨64270703641926842075548945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 342777086090276491069594373 64270703641926842075548945)
            ·
              refine ⟨48203027731445131556661709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64270703641926842075548945 48203027731445131556661709)
              ·
                refine ⟨18076135399291924333748141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48203027731445131556661709 18076135399291924333748141)
                ·
                  refine ⟨6778550774734471625155553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18076135399291924333748141 6778550774734471625155553)
                  ·
                    refine ⟨5083913081050853718866665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6778550774734471625155553 5083913081050853718866665)
                    ·
                      refine ⟨3812934810788140289149999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5083913081050853718866665 3812934810788140289149999)
                      ·
                        rfl

theorem cell23_7425664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 3, 3, 2, 2].length) (baseStart_7425664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7425664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7425664 prefixEnd_7425664 := by exact prefixLift 7425664
  have htrace : WordTrace (prefixWord ++ tailWord_7425664) baseStart_7425664 baseEnd_7425664 := by
    simpa [prefixWord, tailWord_7425664, baseEnd_7425664] using wordTrace_append hprefix tailTrace_7425664
  have hstable : (prefixWord ++ tailWord_7425664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7425664).length < 2 ^ (prefixWord ++ tailWord_7425664).sum := by decide
  have hdescent : baseEnd_7425664 < baseStart_7425664 := by decide
  rcases family_descends (prefixWord ++ tailWord_7425664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7425674 : List Nat := [3, 1, 2, 3, 2, 1, 2, 3, 2, 4]
def baseStart_7425674 : Nat := 118140960795 + 7425674 * 2 ^ 59
def prefixEnd_7425674 : Nat := 4983230072969 + 3 ^ 40 * 7425674 * 2
def baseEnd_7425674 : Nat := 1270979981864895083341651

theorem tailTrace_7425674 : CollatzResearch.WordTrace tailWord_7425674 prefixEnd_7425674 1270979981864895083341651 := by
  unfold tailWord_7425674
  simp only [CollatzResearch.WordTrace]
  refine ⟨67709145225014694249355019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180557720600039184664946717 67709145225014694249355019)
  ·
    refine ⟨101563717837522041374032529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67709145225014694249355019 101563717837522041374032529)
    ·
      refine ⟨76172788378141531030524397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101563717837522041374032529 76172788378141531030524397)
      ·
        refine ⟨28564795641803074136446649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76172788378141531030524397 28564795641803074136446649)
        ·
          refine ⟨21423596731352305602334987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28564795641803074136446649 21423596731352305602334987)
          ·
            refine ⟨32135395097028458403502481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21423596731352305602334987 32135395097028458403502481)
            ·
              refine ⟨24101546322771343802626861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32135395097028458403502481 24101546322771343802626861)
              ·
                refine ⟨9038079871039253925985073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24101546322771343802626861 9038079871039253925985073)
                ·
                  refine ⟨6778559903279440444488805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9038079871039253925985073 6778559903279440444488805)
                  ·
                    refine ⟨1270979981864895083341651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6778559903279440444488805 1270979981864895083341651)
                    ·
                      rfl

theorem cell23_7425674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 3, 2, 4].length) (baseStart_7425674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7425674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7425674 prefixEnd_7425674 := by exact prefixLift 7425674
  have htrace : WordTrace (prefixWord ++ tailWord_7425674) baseStart_7425674 baseEnd_7425674 := by
    simpa [prefixWord, tailWord_7425674, baseEnd_7425674] using wordTrace_append hprefix tailTrace_7425674
  have hstable : (prefixWord ++ tailWord_7425674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7425674).length < 2 ^ (prefixWord ++ tailWord_7425674).sum := by decide
  have hdescent : baseEnd_7425674 < baseStart_7425674 := by decide
  rcases family_descends (prefixWord ++ tailWord_7425674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7425687 : List Nat := [1, 1, 3, 3, 2, 3, 3, 7]
def baseStart_7425687 : Nat := 118140960795 + 7425687 * 2 ^ 59
def prefixEnd_7425687 : Nat := 4983230072969 + 3 ^ 40 * 7425687 * 2
def baseEnd_7425687 : Nat := 141220245216414581450459

theorem tailTrace_7425687 : CollatzResearch.WordTrace tailWord_7425687 prefixEnd_7425687 141220245216414581450459 := by
  unfold tailWord_7425687
  simp only [CollatzResearch.WordTrace]
  refine ⟨270837055049011680217643315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180558036699341120145095543 270837055049011680217643315)
  ·
    refine ⟨406255582573517520326464973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270837055049011680217643315 406255582573517520326464973)
    ·
      refine ⟨152345843465069070122424365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 406255582573517520326464973 152345843465069070122424365)
      ·
        refine ⟨57129691299400901295909137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152345843465069070122424365 57129691299400901295909137)
        ·
          refine ⟨42847268474550675971931853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57129691299400901295909137 42847268474550675971931853)
          ·
            refine ⟨16067725677956503489474445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42847268474550675971931853 16067725677956503489474445)
            ·
              refine ⟨6025397129233688808552917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16067725677956503489474445 6025397129233688808552917)
              ·
                refine ⟨141220245216414581450459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6025397129233688808552917 141220245216414581450459)
                ·
                  rfl

theorem cell23_7425687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 3, 7].length) (baseStart_7425687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7425687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7425687 prefixEnd_7425687 := by exact prefixLift 7425687
  have htrace : WordTrace (prefixWord ++ tailWord_7425687) baseStart_7425687 baseEnd_7425687 := by
    simpa [prefixWord, tailWord_7425687, baseEnd_7425687] using wordTrace_append hprefix tailTrace_7425687
  have hstable : (prefixWord ++ tailWord_7425687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7425687).length < 2 ^ (prefixWord ++ tailWord_7425687).sum := by decide
  have hdescent : baseEnd_7425687 < baseStart_7425687 := by decide
  rcases family_descends (prefixWord ++ tailWord_7425687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7425694 : List Nat := [4, 3, 1, 1, 1, 2, 2, 2, 1, 2, 4]
def baseStart_7425694 : Nat := 118140960795 + 7425694 * 2 ^ 59
def prefixEnd_7425694 : Nat := 4983230072969 + 3 ^ 40 * 7425694 * 2
def baseEnd_7425694 : Nat := 3812950215207775171774861

theorem tailTrace_7425694 : CollatzResearch.WordTrace tailWord_7425694 prefixEnd_7425694 3812950215207775171774861 := by
  unfold tailWord_7425694
  simp only [CollatzResearch.WordTrace]
  refine ⟨33854663794998290051643517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180558206906657546942098757 33854663794998290051643517)
  ·
    refine ⟨12695498923124358769366319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33854663794998290051643517 12695498923124358769366319)
    ·
      refine ⟨19043248384686538154049479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12695498923124358769366319 19043248384686538154049479)
      ·
        refine ⟨28564872577029807231074219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19043248384686538154049479 28564872577029807231074219)
        ·
          refine ⟨42847308865544710846611329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28564872577029807231074219 42847308865544710846611329)
          ·
            refine ⟨32135481649158533134958497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42847308865544710846611329 32135481649158533134958497)
            ·
              refine ⟨24101611236868899851218873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32135481649158533134958497 24101611236868899851218873)
              ·
                refine ⟨18076208427651674888414155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24101611236868899851218873 18076208427651674888414155)
                ·
                  refine ⟨27114312641477512332621233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18076208427651674888414155 27114312641477512332621233)
                  ·
                    refine ⟨20335734481108134249465925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27114312641477512332621233 20335734481108134249465925)
                    ·
                      refine ⟨3812950215207775171774861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20335734481108134249465925 3812950215207775171774861)
                      ·
                        rfl

theorem cell23_7425694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_7425694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7425694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7425694 prefixEnd_7425694 := by exact prefixLift 7425694
  have htrace : WordTrace (prefixWord ++ tailWord_7425694) baseStart_7425694 baseEnd_7425694 := by
    simpa [prefixWord, tailWord_7425694, baseEnd_7425694] using wordTrace_append hprefix tailTrace_7425694
  have hstable : (prefixWord ++ tailWord_7425694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7425694).length < 2 ^ (prefixWord ++ tailWord_7425694).sum := by decide
  have hdescent : baseEnd_7425694 < baseStart_7425694 := by decide
  rcases family_descends (prefixWord ++ tailWord_7425694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7425720 : List Nat := [2, 1, 2, 1, 2, 1, 1, 3, 1, 5, 4]
def baseStart_7425720 : Nat := 118140960795 + 7425720 * 2 ^ 59
def prefixEnd_7425720 : Nat := 4983230072969 + 3 ^ 40 * 7425720 * 2
def baseEnd_7425720 : Nat := 3812963565704792070049741

theorem tailTrace_7425720 : CollatzResearch.WordTrace tailWord_7425720 prefixEnd_7425720 3812963565704792070049741 := by
  unfold tailWord_7425720
  simp only [CollatzResearch.WordTrace]
  refine ⟨135419129328946063426797307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180558839105261417902396409 135419129328946063426797307)
  ·
    refine ⟨203128693993419095140195961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135419129328946063426797307 203128693993419095140195961)
    ·
      refine ⟨152346520495064321355146971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203128693993419095140195961 152346520495064321355146971)
      ·
        refine ⟨228519780742596482032720457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152346520495064321355146971 228519780742596482032720457)
        ·
          refine ⟨171389835556947361524540343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228519780742596482032720457 171389835556947361524540343)
          ·
            refine ⟨257084753335421042286810515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171389835556947361524540343 257084753335421042286810515)
            ·
              refine ⟨385627130003131563430215773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 257084753335421042286810515 385627130003131563430215773)
              ·
                refine ⟨144610173751174336286330915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 385627130003131563430215773 144610173751174336286330915)
                ·
                  refine ⟨216915260626761504429496373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 144610173751174336286330915 216915260626761504429496373)
                  ·
                    refine ⟨20335805683758891040265285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 216915260626761504429496373 20335805683758891040265285)
                    ·
                      refine ⟨3812963565704792070049741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20335805683758891040265285 3812963565704792070049741)
                      ·
                        rfl

theorem cell23_7425720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 1, 5, 4].length) (baseStart_7425720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7425720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7425720 prefixEnd_7425720 := by exact prefixLift 7425720
  have htrace : WordTrace (prefixWord ++ tailWord_7425720) baseStart_7425720 baseEnd_7425720 := by
    simpa [prefixWord, tailWord_7425720, baseEnd_7425720] using wordTrace_append hprefix tailTrace_7425720
  have hstable : (prefixWord ++ tailWord_7425720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7425720).length < 2 ^ (prefixWord ++ tailWord_7425720).sum := by decide
  have hdescent : baseEnd_7425720 < baseStart_7425720 := by decide
  rcases family_descends (prefixWord ++ tailWord_7425720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7425760 : List Nat := [2, 1, 1, 3, 1, 2, 2, 2, 9]
def baseStart_7425760 : Nat := 118140960795 + 7425760 * 2 ^ 59
def prefixEnd_7425760 : Nat := 4983230072969 + 3 ^ 40 * 7425760 * 2
def baseEnd_7425760 : Nat := 423664900547885768172173

theorem tailTrace_7425760 : CollatzResearch.WordTrace tailWord_7425760 prefixEnd_7425760 423664900547885768172173 := by
  unfold tailWord_7425760
  simp only [CollatzResearch.WordTrace]
  refine ⟨135419858788873606842525367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180559811718498142456700489 135419858788873606842525367)
  ·
    refine ⟨203129788183310410263788051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135419858788873606842525367 203129788183310410263788051)
    ·
      refine ⟨304694682274965615395682077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203129788183310410263788051 304694682274965615395682077)
      ·
        refine ⟨114260505853112105773380779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 304694682274965615395682077 114260505853112105773380779)
        ·
          refine ⟨171390758779668158660071169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114260505853112105773380779 171390758779668158660071169)
          ·
            refine ⟨128543069084751118995053377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171390758779668158660071169 128543069084751118995053377)
            ·
              refine ⟨96407301813563339246290033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128543069084751118995053377 96407301813563339246290033)
              ·
                refine ⟨72305476360172504434717525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96407301813563339246290033 72305476360172504434717525)
                ·
                  refine ⟨423664900547885768172173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 72305476360172504434717525 423664900547885768172173)
                  ·
                    rfl

theorem cell23_7425760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 2, 9].length) (baseStart_7425760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7425760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7425760 prefixEnd_7425760 := by exact prefixLift 7425760
  have htrace : WordTrace (prefixWord ++ tailWord_7425760) baseStart_7425760 baseEnd_7425760 := by
    simpa [prefixWord, tailWord_7425760, baseEnd_7425760] using wordTrace_append hprefix tailTrace_7425760
  have hstable : (prefixWord ++ tailWord_7425760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7425760).length < 2 ^ (prefixWord ++ tailWord_7425760).sum := by decide
  have hdescent : baseEnd_7425760 < baseStart_7425760 := by decide
  rcases family_descends (prefixWord ++ tailWord_7425760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7425777 : List Nat := [1, 2, 2, 2, 2, 3, 3, 1, 7]
def baseStart_7425777 : Nat := 118140960795 + 7425777 * 2 ^ 59
def prefixEnd_7425777 : Nat := 4983230072969 + 3 ^ 40 * 7425777 * 2
def baseEnd_7425777 : Nat := 423665870455788705226331

theorem tailTrace_7425777 : CollatzResearch.WordTrace tailWord_7425777 prefixEnd_7425777 423665870455788705226331 := by
  unfold tailWord_7425777
  simp only [CollatzResearch.WordTrace]
  refine ⟨270840337618685625588419585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180560225079123750392279723 270840337618685625588419585)
  ·
    refine ⟨203130253214014219191314689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270840337618685625588419585 203130253214014219191314689)
    ·
      refine ⟨152347689910510664393486017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203130253214014219191314689 152347689910510664393486017)
      ·
        refine ⟨114260767432882998295114513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152347689910510664393486017 114260767432882998295114513)
        ·
          refine ⟨85695575574662248721335885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114260767432882998295114513 85695575574662248721335885)
          ·
            refine ⟨32135840840498343270500957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85695575574662248721335885 32135840840498343270500957)
            ·
              refine ⟨12050940315186878726437859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32135840840498343270500957 12050940315186878726437859)
              ·
                refine ⟨18076410472780318089656789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12050940315186878726437859 18076410472780318089656789)
                ·
                  refine ⟨423665870455788705226331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18076410472780318089656789 423665870455788705226331)
                  ·
                    rfl

theorem cell23_7425777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 3, 1, 7].length) (baseStart_7425777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7425777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7425777 prefixEnd_7425777 := by exact prefixLift 7425777
  have htrace : WordTrace (prefixWord ++ tailWord_7425777) baseStart_7425777 baseEnd_7425777 := by
    simpa [prefixWord, tailWord_7425777, baseEnd_7425777] using wordTrace_append hprefix tailTrace_7425777
  have hstable : (prefixWord ++ tailWord_7425777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7425777).length < 2 ^ (prefixWord ++ tailWord_7425777).sum := by decide
  have hdescent : baseEnd_7425777 < baseStart_7425777 := by decide
  rcases family_descends (prefixWord ++ tailWord_7425777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7425828 : List Nat := [2, 3, 1, 3, 2, 3, 2, 2, 5]
def baseStart_7425828 : Nat := 118140960795 + 7425828 * 2 ^ 59
def prefixEnd_7425828 : Nat := 4983230072969 + 3 ^ 40 * 7425828 * 2
def baseEnd_7425828 : Nat := 423668780179497516388805

theorem tailTrace_7425828 : CollatzResearch.WordTrace tailWord_7425828 prefixEnd_7425828 423668780179497516388805 := by
  unfold tailWord_7425828
  simp only [CollatzResearch.WordTrace]
  refine ⟨135421098870750430649263069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180561465161000574199017425 135421098870750430649263069)
  ·
    refine ⟨50782912076531411493473651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135421098870750430649263069 50782912076531411493473651)
    ·
      refine ⟨76174368114797117240210477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50782912076531411493473651 76174368114797117240210477)
      ·
        refine ⟨28565388043048918965078929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76174368114797117240210477 28565388043048918965078929)
        ·
          refine ⟨21424041032286689223809197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28565388043048918965078929 21424041032286689223809197)
          ·
            refine ⟨8034015387107508458928449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21424041032286689223809197 8034015387107508458928449)
            ·
              refine ⟨6025511540330631344196337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8034015387107508458928449 6025511540330631344196337)
              ·
                refine ⟨4519133655247973508147253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6025511540330631344196337 4519133655247973508147253)
                ·
                  refine ⟨423668780179497516388805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4519133655247973508147253 423668780179497516388805)
                  ·
                    rfl

theorem cell23_7425828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 2, 2, 5].length) (baseStart_7425828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7425828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7425828 prefixEnd_7425828 := by exact prefixLift 7425828
  have htrace : WordTrace (prefixWord ++ tailWord_7425828) baseStart_7425828 baseEnd_7425828 := by
    simpa [prefixWord, tailWord_7425828, baseEnd_7425828] using wordTrace_append hprefix tailTrace_7425828
  have hstable : (prefixWord ++ tailWord_7425828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7425828).length < 2 ^ (prefixWord ++ tailWord_7425828).sum := by decide
  have hdescent : baseEnd_7425828 < baseStart_7425828 := by decide
  rcases family_descends (prefixWord ++ tailWord_7425828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7425864 : List Nat := [2, 1, 3, 1, 1, 5, 1, 1, 1, 4, 3]
def baseStart_7425864 : Nat := 118140960795 + 7425864 * 2 ^ 59
def prefixEnd_7425864 : Nat := 4983230072969 + 3 ^ 40 * 7425864 * 2
def baseEnd_7425864 : Nat := 3813037506919039506649079

theorem tailTrace_7425864 : CollatzResearch.WordTrace tailWord_7425864 prefixEnd_7425864 3813037506919039506649079 := by
  unfold tailWord_7425864
  simp only [CollatzResearch.WordTrace]
  refine ⟨135421755384685219723418323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180562340512913626297891097 135421755384685219723418323)
  ·
    refine ⟨203132633077027829585127485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135421755384685219723418323 203132633077027829585127485)
    ·
      refine ⟨76174737403885436094422807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 203132633077027829585127485 76174737403885436094422807)
      ·
        refine ⟨114262106105828154141634211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76174737403885436094422807 114262106105828154141634211)
        ·
          refine ⟨171393159158742231212451317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114262106105828154141634211 171393159158742231212451317)
          ·
            refine ⟨16068108671132084176167311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 171393159158742231212451317 16068108671132084176167311)
            ·
              refine ⟨24102163006698126264250967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16068108671132084176167311 24102163006698126264250967)
              ·
                refine ⟨36153244510047189396376451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24102163006698126264250967 36153244510047189396376451)
                ·
                  refine ⟨54229866765070784094564677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36153244510047189396376451 54229866765070784094564677)
                  ·
                    refine ⟨10168100018450772017730877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54229866765070784094564677 10168100018450772017730877)
                    ·
                      refine ⟨3813037506919039506649079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10168100018450772017730877 3813037506919039506649079)
                      ·
                        rfl

theorem cell23_7425864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 1, 1, 4, 3].length) (baseStart_7425864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7425864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7425864 prefixEnd_7425864 := by exact prefixLift 7425864
  have htrace : WordTrace (prefixWord ++ tailWord_7425864) baseStart_7425864 baseEnd_7425864 := by
    simpa [prefixWord, tailWord_7425864, baseEnd_7425864] using wordTrace_append hprefix tailTrace_7425864
  have hstable : (prefixWord ++ tailWord_7425864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7425864).length < 2 ^ (prefixWord ++ tailWord_7425864).sum := by decide
  have hdescent : baseEnd_7425864 < baseStart_7425864 := by decide
  rcases family_descends (prefixWord ++ tailWord_7425864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7425887 : List Nat := [1, 1, 2, 3, 1, 4, 1, 1, 1, 2, 6]
def baseStart_7425887 : Nat := 118140960795 + 7425887 * 2 ^ 59
def prefixEnd_7425887 : Nat := 4983230072969 + 3 ^ 40 * 7425887 * 2
def baseEnd_7425887 : Nat := 3813049316974092916661473

theorem tailTrace_7425887 : CollatzResearch.WordTrace tailWord_7425887 prefixEnd_7425887 3813049316974092916661473 := by
  unfold tailWord_7425887
  simp only [CollatzResearch.WordTrace]
  refine ⟨270844349648287114374923915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180562899765524742916615943 270844349648287114374923915)
  ·
    refine ⟨406266524472430671562385873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270844349648287114374923915 406266524472430671562385873)
    ·
      refine ⟨304699893354323003671789405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 406266524472430671562385873 304699893354323003671789405)
      ·
        refine ⟨114262460007871126376921027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 304699893354323003671789405 114262460007871126376921027)
        ·
          refine ⟨171393690011806689565381541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114262460007871126376921027 171393690011806689565381541)
          ·
            refine ⟨32136316877213754293509039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 171393690011806689565381541 32136316877213754293509039)
            ·
              refine ⟨48204475315820631440263559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32136316877213754293509039 48204475315820631440263559)
              ·
                refine ⟨72306712973730947160395339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48204475315820631440263559 72306712973730947160395339)
                ·
                  refine ⟨108460069460596420740593009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72306712973730947160395339 108460069460596420740593009)
                  ·
                    refine ⟨81345052095447315555444757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 108460069460596420740593009 81345052095447315555444757)
                    ·
                      refine ⟨3813049316974092916661473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81345052095447315555444757 3813049316974092916661473)
                      ·
                        rfl

theorem cell23_7425887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 1, 1, 2, 6].length) (baseStart_7425887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7425887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7425887 prefixEnd_7425887 := by exact prefixLift 7425887
  have htrace : WordTrace (prefixWord ++ tailWord_7425887) baseStart_7425887 baseEnd_7425887 := by
    simpa [prefixWord, tailWord_7425887, baseEnd_7425887] using wordTrace_append hprefix tailTrace_7425887
  have hstable : (prefixWord ++ tailWord_7425887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7425887).length < 2 ^ (prefixWord ++ tailWord_7425887).sum := by decide
  have hdescent : baseEnd_7425887 < baseStart_7425887 := by decide
  rcases family_descends (prefixWord ++ tailWord_7425887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7425897 : List Nat := [1, 2, 1, 1, 1, 3, 1, 3, 5, 5]
def baseStart_7425897 : Nat := 118140960795 + 7425897 * 2 ^ 59
def prefixEnd_7425897 : Nat := 4983230072969 + 3 ^ 40 * 7425897 * 2
def baseEnd_7425897 : Nat := 1271018150593545959178809

theorem tailTrace_7425897 : CollatzResearch.WordTrace tailWord_7425897 prefixEnd_7425897 1271018150593545959178809 := by
  unfold tailWord_7425897
  simp only [CollatzResearch.WordTrace]
  refine ⟨270844714378250886082787945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180563142918833924055191963 270844714378250886082787945)
  ·
    refine ⟨203133535783688164562090959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270844714378250886082787945 203133535783688164562090959)
    ·
      refine ⟨304700303675532246843136439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203133535783688164562090959 304700303675532246843136439)
      ·
        refine ⟨457050455513298370264704659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304700303675532246843136439 457050455513298370264704659)
        ·
          refine ⟨685575683269947555397056989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 457050455513298370264704659 685575683269947555397056989)
          ·
            refine ⟨257090881226230333273896371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 685575683269947555397056989 257090881226230333273896371)
            ·
              refine ⟨385636321839345499910844557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 257090881226230333273896371 385636321839345499910844557)
              ·
                refine ⟨144613620689754562466566709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 385636321839345499910844557 144613620689754562466566709)
                ·
                  refine ⟨13557526939664490231240629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 144613620689754562466566709 13557526939664490231240629)
                  ·
                    refine ⟨1271018150593545959178809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13557526939664490231240629 1271018150593545959178809)
                    ·
                      rfl

theorem cell23_7425897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 5, 5].length) (baseStart_7425897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7425897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7425897 prefixEnd_7425897 := by exact prefixLift 7425897
  have htrace : WordTrace (prefixWord ++ tailWord_7425897) baseStart_7425897 baseEnd_7425897 := by
    simpa [prefixWord, tailWord_7425897, baseEnd_7425897] using wordTrace_append hprefix tailTrace_7425897
  have hstable : (prefixWord ++ tailWord_7425897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7425897).length < 2 ^ (prefixWord ++ tailWord_7425897).sum := by decide
  have hdescent : baseEnd_7425897 < baseStart_7425897 := by decide
  rcases family_descends (prefixWord ++ tailWord_7425897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7425914 : List Nat := [3, 1, 1, 1, 1, 1, 5, 4, 1, 5]
def baseStart_7425914 : Nat := 118140960795 + 7425914 * 2 ^ 59
def prefixEnd_7425914 : Nat := 4983230072969 + 3 ^ 40 * 7425914 * 2
def baseEnd_7425914 : Nat := 1271021060317254770341283

theorem tailTrace_7425914 : CollatzResearch.WordTrace tailWord_7425914 prefixEnd_7425914 1271021060317254770341283 := by
  unfold tailWord_7425914
  simp only [CollatzResearch.WordTrace]
  refine ⟨67711333604797324496539199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180563556279459531990771197 67711333604797324496539199)
  ·
    refine ⟨101567000407195986744808799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67711333604797324496539199 101567000407195986744808799)
    ·
      refine ⟨152350500610793980117213199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101567000407195986744808799 152350500610793980117213199)
      ·
        refine ⟨228525750916190970175819799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152350500610793980117213199 228525750916190970175819799)
        ·
          refine ⟨342788626374286455263729699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228525750916190970175819799 342788626374286455263729699)
          ·
            refine ⟨514182939561429682895594549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 342788626374286455263729699 514182939561429682895594549)
            ·
              refine ⟨48204650583884032771461989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 514182939561429682895594549 48204650583884032771461989)
              ·
                refine ⟨9038371984478256144649123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48204650583884032771461989 9038371984478256144649123)
                ·
                  refine ⟨13557557976717384216973685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9038371984478256144649123 13557557976717384216973685)
                  ·
                    refine ⟨1271021060317254770341283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13557557976717384216973685 1271021060317254770341283)
                    ·
                      rfl

theorem cell23_7425914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 4, 1, 5].length) (baseStart_7425914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7425914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7425914 prefixEnd_7425914 := by exact prefixLift 7425914
  have htrace : WordTrace (prefixWord ++ tailWord_7425914) baseStart_7425914 baseEnd_7425914 := by
    simpa [prefixWord, tailWord_7425914, baseEnd_7425914] using wordTrace_append hprefix tailTrace_7425914
  have hstable : (prefixWord ++ tailWord_7425914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7425914).length < 2 ^ (prefixWord ++ tailWord_7425914).sum := by decide
  have hdescent : baseEnd_7425914 < baseStart_7425914 := by decide
  rcases family_descends (prefixWord ++ tailWord_7425914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7425938 : List Nat := [3, 2, 3, 2, 1, 1, 1, 1, 4, 3, 2]
def baseStart_7425938 : Nat := 118140960795 + 7425938 * 2 ^ 59
def prefixEnd_7425938 : Nat := 4983230072969 + 3 ^ 40 * 7425938 * 2
def baseEnd_7425938 : Nat := 3813075504487472217123739

theorem tailTrace_7425938 : CollatzResearch.WordTrace tailWord_7425938 prefixEnd_7425938 3813075504487472217123739 := by
  unfold tailWord_7425938
  simp only [CollatzResearch.WordTrace]
  refine ⟨67711552442775587521257617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180564139847401566723353645 67711552442775587521257617)
  ·
    refine ⟨50783664332081690640943213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67711552442775587521257617 50783664332081690640943213)
    ·
      refine ⟨19043874124530633990353705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50783664332081690640943213 19043874124530633990353705)
      ·
        refine ⟨14282905593397975492765279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19043874124530633990353705 14282905593397975492765279)
        ·
          refine ⟨21424358390096963239147919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14282905593397975492765279 21424358390096963239147919)
          ·
            refine ⟨32136537585145444858721879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21424358390096963239147919 32136537585145444858721879)
            ·
              refine ⟨48204806377718167288082819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32136537585145444858721879 48204806377718167288082819)
              ·
                refine ⟨72307209566577250932124229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48204806377718167288082819 72307209566577250932124229)
                ·
                  refine ⟨13557601793733234549773293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72307209566577250932124229 13557601793733234549773293)
                  ·
                    refine ⟨5084100672649962956164985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13557601793733234549773293 5084100672649962956164985)
                    ·
                      refine ⟨3813075504487472217123739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5084100672649962956164985 3813075504487472217123739)
                      ·
                        rfl

theorem cell23_7425938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 1, 4, 3, 2].length) (baseStart_7425938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7425938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7425938 prefixEnd_7425938 := by exact prefixLift 7425938
  have htrace : WordTrace (prefixWord ++ tailWord_7425938) baseStart_7425938 baseEnd_7425938 := by
    simpa [prefixWord, tailWord_7425938, baseEnd_7425938] using wordTrace_append hprefix tailTrace_7425938
  have hstable : (prefixWord ++ tailWord_7425938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7425938).length < 2 ^ (prefixWord ++ tailWord_7425938).sum := by decide
  have hdescent : baseEnd_7425938 < baseStart_7425938 := by decide
  rcases family_descends (prefixWord ++ tailWord_7425938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7425972 : List Nat := [2, 5, 2, 1, 2, 1, 2, 1, 2, 3, 2]
def baseStart_7425972 : Nat := 118140960795 + 7425972 * 2 ^ 59
def prefixEnd_7425972 : Nat := 4983230072969 + 3 ^ 40 * 7425972 * 2
def baseEnd_7425972 : Nat := 3813092962829725084098583

theorem tailTrace_7425972 : CollatzResearch.WordTrace tailWord_7425972 prefixEnd_7425972 3813092962829725084098583 := by
  unfold tailWord_7425972
  simp only [CollatzResearch.WordTrace]
  refine ⟨135423724926489586945884085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180564966568652782594512113 135423724926489586945884085)
  ·
    refine ⟨12695974211858398776176633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 135423724926489586945884085 12695974211858398776176633)
    ·
      refine ⟨9521980658893799082132475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12695974211858398776176633 9521980658893799082132475)
      ·
        refine ⟨14282970988340698623198713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9521980658893799082132475 14282970988340698623198713)
        ·
          refine ⟨10712228241255523967399035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14282970988340698623198713 10712228241255523967399035)
          ·
            refine ⟨16068342361883285951098553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10712228241255523967399035 16068342361883285951098553)
            ·
              refine ⟨12051256771412464463323915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16068342361883285951098553 12051256771412464463323915)
              ·
                refine ⟨18076885157118696694985873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12051256771412464463323915 18076885157118696694985873)
                ·
                  refine ⟨13557663867839022521239405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18076885157118696694985873 13557663867839022521239405)
                  ·
                    refine ⟨5084123950439633445464777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13557663867839022521239405 5084123950439633445464777)
                    ·
                      refine ⟨3813092962829725084098583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5084123950439633445464777 3813092962829725084098583)
                      ·
                        rfl

theorem cell23_7425972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 2, 1, 2, 3, 2].length) (baseStart_7425972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7425972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7425972 prefixEnd_7425972 := by exact prefixLift 7425972
  have htrace : WordTrace (prefixWord ++ tailWord_7425972) baseStart_7425972 baseEnd_7425972 := by
    simpa [prefixWord, tailWord_7425972, baseEnd_7425972] using wordTrace_append hprefix tailTrace_7425972
  have hstable : (prefixWord ++ tailWord_7425972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7425972).length < 2 ^ (prefixWord ++ tailWord_7425972).sum := by decide
  have hdescent : baseEnd_7425972 < baseStart_7425972 := by decide
  rcases family_descends (prefixWord ++ tailWord_7425972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7425981 : List Nat := [1, 4, 1, 2, 3, 2, 1, 2, 1, 2, 4]
def baseStart_7425981 : Nat := 118140960795 + 7425981 * 2 ^ 59
def prefixEnd_7425981 : Nat := 4983230072969 + 3 ^ 40 * 7425981 * 2
def baseEnd_7425981 : Nat := 3813097584155615548886041

theorem tailTrace_7425981 : CollatzResearch.WordTrace tailWord_7425981 prefixEnd_7425981 3813097584155615548886041 := by
  unfold tailWord_7425981
  simp only [CollatzResearch.WordTrace]
  refine ⟨270847778109946568428845797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180565185406631045619230531 270847778109946568428845797)
  ·
    refine ⟨50783958395614981580408587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 270847778109946568428845797 50783958395614981580408587)
    ·
      refine ⟨76175937593422472370612881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50783958395614981580408587 76175937593422472370612881)
      ·
        refine ⟨57131953195066854277959661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76175937593422472370612881 57131953195066854277959661)
        ·
          refine ⟨21424482448150070354234873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57131953195066854277959661 21424482448150070354234873)
          ·
            refine ⟨16068361836112552765676155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21424482448150070354234873 16068361836112552765676155)
            ·
              refine ⟨24102542754168829148514233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16068361836112552765676155 24102542754168829148514233)
              ·
                refine ⟨18076907065626621861385675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24102542754168829148514233 18076907065626621861385675)
                ·
                  refine ⟨27115360598439932792078513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18076907065626621861385675 27115360598439932792078513)
                  ·
                    refine ⟨20336520448829949594058885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27115360598439932792078513 20336520448829949594058885)
                    ·
                      refine ⟨3813097584155615548886041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20336520448829949594058885 3813097584155615548886041)
                      ·
                        rfl

theorem cell23_7425981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 2, 1, 2, 4].length) (baseStart_7425981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7425981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7425981 prefixEnd_7425981 := by exact prefixLift 7425981
  have htrace : WordTrace (prefixWord ++ tailWord_7425981) baseStart_7425981 baseEnd_7425981 := by
    simpa [prefixWord, tailWord_7425981, baseEnd_7425981] using wordTrace_append hprefix tailTrace_7425981
  have hstable : (prefixWord ++ tailWord_7425981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7425981).length < 2 ^ (prefixWord ++ tailWord_7425981).sum := by decide
  have hdescent : baseEnd_7425981 < baseStart_7425981 := by decide
  rcases family_descends (prefixWord ++ tailWord_7425981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7425987 : List Nat := [1, 1, 1, 3, 1, 1, 2, 1, 3, 9]
def baseStart_7425987 : Nat := 118140960795 + 7425987 * 2 ^ 59
def prefixEnd_7425987 : Nat := 4983230072969 + 3 ^ 40 * 7425987 * 2
def baseEnd_7425987 : Nat := 1271033555013180841803671

theorem tailTrace_7425987 : CollatzResearch.WordTrace tailWord_7425987 prefixEnd_7425987 1271033555013180841803671 := by
  unfold tailWord_7425987
  simp only [CollatzResearch.WordTrace]
  refine ⟨270847996947924831453564215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180565331298616554302376143 270847996947924831453564215)
  ·
    refine ⟨406271995421887247180346323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270847996947924831453564215 406271995421887247180346323)
    ·
      refine ⟨609407993132830870770519485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 406271995421887247180346323 609407993132830870770519485)
      ·
        refine ⟨228527997424811576538944807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 609407993132830870770519485 228527997424811576538944807)
        ·
          refine ⟨342791996137217364808417211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228527997424811576538944807 342791996137217364808417211)
          ·
            refine ⟨514187994205826047212625817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 342791996137217364808417211 514187994205826047212625817)
            ·
              refine ⟨385640995654369535409469363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 514187994205826047212625817 385640995654369535409469363)
              ·
                refine ⟨578461493481554303114204045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 385640995654369535409469363 578461493481554303114204045)
                ·
                  refine ⟨216923060055582863667826517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 578461493481554303114204045 216923060055582863667826517)
                  ·
                    refine ⟨1271033555013180841803671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 216923060055582863667826517 1271033555013180841803671)
                    ·
                      rfl

theorem cell23_7425987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 9].length) (baseStart_7425987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7425987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7425987 prefixEnd_7425987 := by exact prefixLift 7425987
  have htrace : WordTrace (prefixWord ++ tailWord_7425987) baseStart_7425987 baseEnd_7425987 := by
    simpa [prefixWord, tailWord_7425987, baseEnd_7425987] using wordTrace_append hprefix tailTrace_7425987
  have hstable : (prefixWord ++ tailWord_7425987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7425987).length < 2 ^ (prefixWord ++ tailWord_7425987).sum := by decide
  have hdescent : baseEnd_7425987 < baseStart_7425987 := by decide
  rcases family_descends (prefixWord ++ tailWord_7425987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7426004 : List Nat := [2, 4, 1, 2, 1, 1, 1, 1, 1, 9]
def baseStart_7426004 : Nat := 118140960795 + 7426004 * 2 ^ 59
def prefixEnd_7426004 : Nat := 4983230072969 + 3 ^ 40 * 7426004 * 2
def baseEnd_7426004 : Nat := 1271036464736889652966145

theorem tailTrace_7426004 : CollatzResearch.WordTrace tailWord_7426004 prefixEnd_7426004 1271036464736889652966145 := by
  unfold tailWord_7426004
  simp only [CollatzResearch.WordTrace]
  refine ⟨135424308494431621678466533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180565744659242162237955377 135424308494431621678466533)
  ·
    refine ⟨25392057842705929064712475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135424308494431621678466533 25392057842705929064712475)
    ·
      refine ⟨38088086764058893597068713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25392057842705929064712475 38088086764058893597068713)
      ·
        refine ⟨28566065073044170197801535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38088086764058893597068713 28566065073044170197801535)
        ·
          refine ⟨42849097609566255296702303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28566065073044170197801535 42849097609566255296702303)
          ·
            refine ⟨64273646414349382945053455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42849097609566255296702303 64273646414349382945053455)
            ·
              refine ⟨96410469621524074417580183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64273646414349382945053455 96410469621524074417580183)
              ·
                refine ⟨144615704432286111626370275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96410469621524074417580183 144615704432286111626370275)
                ·
                  refine ⟨216923556648429167439555413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 144615704432286111626370275 216923556648429167439555413)
                  ·
                    refine ⟨1271036464736889652966145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 216923556648429167439555413 1271036464736889652966145)
                    ·
                      rfl

theorem cell23_7426004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 1, 9].length) (baseStart_7426004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7426004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7426004 prefixEnd_7426004 := by exact prefixLift 7426004
  have htrace : WordTrace (prefixWord ++ tailWord_7426004) baseStart_7426004 baseEnd_7426004 := by
    simpa [prefixWord, tailWord_7426004, baseEnd_7426004] using wordTrace_append hprefix tailTrace_7426004
  have hstable : (prefixWord ++ tailWord_7426004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7426004).length < 2 ^ (prefixWord ++ tailWord_7426004).sum := by decide
  have hdescent : baseEnd_7426004 < baseStart_7426004 := by decide
  rcases family_descends (prefixWord ++ tailWord_7426004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7426024 : List Nat := [2, 1, 4, 1, 1, 1, 1, 1, 4, 3, 4]
def baseStart_7426024 : Nat := 118140960795 + 7426024 * 2 ^ 59
def prefixEnd_7426024 : Nat := 4983230072969 + 3 ^ 40 * 7426024 * 2
def baseEnd_7426024 : Nat := 3813119663823758880648343

theorem tailTrace_7426024 : CollatzResearch.WordTrace tailWord_7426024 prefixEnd_7426024 3813119663823758880648343 := by
  unfold tailWord_7426024
  simp only [CollatzResearch.WordTrace]
  refine ⟨135424673224395393386330563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180566230965860524515107417 135424673224395393386330563)
  ·
    refine ⟨203137009836593090079495845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135424673224395393386330563 203137009836593090079495845)
    ·
      refine ⟨38088189344361204389905471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 203137009836593090079495845 38088189344361204389905471)
      ·
        refine ⟨57132284016541806584858207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38088189344361204389905471 57132284016541806584858207)
        ·
          refine ⟨85698426024812709877287311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57132284016541806584858207 85698426024812709877287311)
          ·
            refine ⟨128547639037219064815930967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85698426024812709877287311 128547639037219064815930967)
            ·
              refine ⟨192821458555828597223896451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128547639037219064815930967 192821458555828597223896451)
              ·
                refine ⟨289232187833742895835844677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 192821458555828597223896451 289232187833742895835844677)
                ·
                  refine ⟨54231035218826792969220877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 289232187833742895835844677 54231035218826792969220877)
                  ·
                    refine ⟨20336638207060047363457829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54231035218826792969220877 20336638207060047363457829)
                    ·
                      refine ⟨3813119663823758880648343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20336638207060047363457829 3813119663823758880648343)
                      ·
                        rfl

theorem cell23_7426024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 4, 3, 4].length) (baseStart_7426024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7426024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7426024 prefixEnd_7426024 := by exact prefixLift 7426024
  have htrace : WordTrace (prefixWord ++ tailWord_7426024) baseStart_7426024 baseEnd_7426024 := by
    simpa [prefixWord, tailWord_7426024, baseEnd_7426024] using wordTrace_append hprefix tailTrace_7426024
  have hstable : (prefixWord ++ tailWord_7426024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7426024).length < 2 ^ (prefixWord ++ tailWord_7426024).sum := by decide
  have hdescent : baseEnd_7426024 < baseStart_7426024 := by decide
  rcases family_descends (prefixWord ++ tailWord_7426024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7426044 : List Nat := [2, 2, 2, 1, 2, 2, 2, 1, 1, 3, 5]
def baseStart_7426044 : Nat := 118140960795 + 7426044 * 2 ^ 59
def prefixEnd_7426044 : Nat := 4983230072969 + 3 ^ 40 * 7426044 * 2
def baseEnd_7426044 : Nat := 3813129933436848802398251

theorem tailTrace_7426044 : CollatzResearch.WordTrace tailWord_7426044 prefixEnd_7426044 3813129933436848802398251 := by
  unfold tailWord_7426044
  simp only [CollatzResearch.WordTrace]
  refine ⟨135425037954359165094194593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180566717272478886792259457 135425037954359165094194593)
  ·
    refine ⟨101568778465769373820645945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135425037954359165094194593 101568778465769373820645945)
    ·
      refine ⟨76176583849327030365484459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101568778465769373820645945 76176583849327030365484459)
      ·
        refine ⟨114264875773990545548226689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76176583849327030365484459 114264875773990545548226689)
        ·
          refine ⟨85698656830492909161170017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114264875773990545548226689 85698656830492909161170017)
          ·
            refine ⟨64273992622869681870877513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85698656830492909161170017 64273992622869681870877513)
            ·
              refine ⟨48205494467152261403158135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64273992622869681870877513 48205494467152261403158135)
              ·
                refine ⟨72308241700728392104737203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48205494467152261403158135 72308241700728392104737203)
                ·
                  refine ⟨108462362551092588157105805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72308241700728392104737203 108462362551092588157105805)
                  ·
                    refine ⟨40673385956659720558914677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 108462362551092588157105805 40673385956659720558914677)
                    ·
                      refine ⟨3813129933436848802398251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40673385956659720558914677 3813129933436848802398251)
                      ·
                        rfl

theorem cell23_7426044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 1, 1, 3, 5].length) (baseStart_7426044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7426044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7426044 prefixEnd_7426044 := by exact prefixLift 7426044
  have htrace : WordTrace (prefixWord ++ tailWord_7426044) baseStart_7426044 baseEnd_7426044 := by
    simpa [prefixWord, tailWord_7426044, baseEnd_7426044] using wordTrace_append hprefix tailTrace_7426044
  have hstable : (prefixWord ++ tailWord_7426044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7426044).length < 2 ^ (prefixWord ++ tailWord_7426044).sum := by decide
  have hdescent : baseEnd_7426044 < baseStart_7426044 := by decide
  rcases family_descends (prefixWord ++ tailWord_7426044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7426045 : List Nat := [1, 4, 1, 1, 1, 2, 6, 1, 1, 3, 2]
def baseStart_7426045 : Nat := 118140960795 + 7426045 * 2 ^ 59
def prefixEnd_7426045 : Nat := 4983230072969 + 3 ^ 40 * 7426045 * 2
def baseEnd_7426045 : Nat := 3813130446917503298485747

theorem tailTrace_7426045 : CollatzResearch.WordTrace tailWord_7426045 prefixEnd_7426045 3813130446917503298485747 := by
  unfold tailWord_7426045
  simp only [CollatzResearch.WordTrace]
  refine ⟨270850112381714707359175589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180566741587809804906117059 270850112381714707359175589)
  ·
    refine ⟨50784396071571507629845423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 270850112381714707359175589 50784396071571507629845423)
    ·
      refine ⟨76176594107357261444768135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50784396071571507629845423 76176594107357261444768135)
      ·
        refine ⟨114264891161035892167152203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76176594107357261444768135 114264891161035892167152203)
        ·
          refine ⟨171397336741553838250728305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114264891161035892167152203 171397336741553838250728305)
          ·
            refine ⟨128548002556165378688046229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171397336741553838250728305 128548002556165378688046229)
            ·
              refine ⟨6025687619820252126002167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 128548002556165378688046229 6025687619820252126002167)
              ·
                refine ⟨9038531429730378189003251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6025687619820252126002167 9038531429730378189003251)
                ·
                  refine ⟨13557797144595567283504877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9038531429730378189003251 13557797144595567283504877)
                  ·
                    refine ⟨5084173929223337731314329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13557797144595567283504877 5084173929223337731314329)
                    ·
                      refine ⟨3813130446917503298485747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5084173929223337731314329 3813130446917503298485747)
                      ·
                        rfl

theorem cell23_7426045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 6, 1, 1, 3, 2].length) (baseStart_7426045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7426045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7426045 prefixEnd_7426045 := by exact prefixLift 7426045
  have htrace : WordTrace (prefixWord ++ tailWord_7426045) baseStart_7426045 baseEnd_7426045 := by
    simpa [prefixWord, tailWord_7426045, baseEnd_7426045] using wordTrace_append hprefix tailTrace_7426045
  have hstable : (prefixWord ++ tailWord_7426045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7426045).length < 2 ^ (prefixWord ++ tailWord_7426045).sum := by decide
  have hdescent : baseEnd_7426045 < baseStart_7426045 := by decide
  rcases family_descends (prefixWord ++ tailWord_7426045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7426098 : List Nat := [3, 2, 1, 1, 2, 3, 3, 3, 5]
def baseStart_7426098 : Nat := 118140960795 + 7426098 * 2 ^ 59
def prefixEnd_7426098 : Nat := 4983230072969 + 3 ^ 40 * 7426098 * 2
def baseEnd_7426098 : Nat := 423684184599132399013667

theorem tailTrace_7426098 : CollatzResearch.WordTrace tailWord_7426098 prefixEnd_7426098 423684184599132399013667 := by
  unfold tailWord_7426098
  simp only [CollatzResearch.WordTrace]
  refine ⟨67713011362630674352713737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180568030300348464940569965 67713011362630674352713737)
  ·
    refine ⟨50784758521973005764535303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67713011362630674352713737 50784758521973005764535303)
    ·
      refine ⟨76177137782959508646802955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50784758521973005764535303 76177137782959508646802955)
      ·
        refine ⟨114265706674439262970204433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76177137782959508646802955 114265706674439262970204433)
        ·
          refine ⟨85699280005829447227653325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114265706674439262970204433 85699280005829447227653325)
          ·
            refine ⟨32137230002186042710369997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85699280005829447227653325 32137230002186042710369997)
            ·
              refine ⟨12051461250819766016388749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32137230002186042710369997 12051461250819766016388749)
              ·
                refine ⟨4519297969057412256145781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12051461250819766016388749 4519297969057412256145781)
                ·
                  refine ⟨423684184599132399013667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4519297969057412256145781 423684184599132399013667)
                  ·
                    rfl

theorem cell23_7426098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 3, 3, 5].length) (baseStart_7426098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7426098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7426098 prefixEnd_7426098 := by exact prefixLift 7426098
  have htrace : WordTrace (prefixWord ++ tailWord_7426098) baseStart_7426098 baseEnd_7426098 := by
    simpa [prefixWord, tailWord_7426098, baseEnd_7426098] using wordTrace_append hprefix tailTrace_7426098
  have hstable : (prefixWord ++ tailWord_7426098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7426098).length < 2 ^ (prefixWord ++ tailWord_7426098).sum := by decide
  have hdescent : baseEnd_7426098 < baseStart_7426098 := by decide
  rcases family_descends (prefixWord ++ tailWord_7426098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7426202 : List Nat := [3, 1, 1, 5, 2, 2, 1, 1, 2, 2, 3]
def baseStart_7426202 : Nat := 118140960795 + 7426202 * 2 ^ 59
def prefixEnd_7426202 : Nat := 4983230072969 + 3 ^ 40 * 7426202 * 2
def baseEnd_7426202 : Nat := 3813211063380259184222525

theorem tailTrace_7426202 : CollatzResearch.WordTrace tailWord_7426202 prefixEnd_7426202 3813211063380259184222525 := by
  unfold tailWord_7426202
  simp only [CollatzResearch.WordTrace]
  refine ⟨67713959660536480793160215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180570559094763948781760573 67713959660536480793160215)
  ·
    refine ⟨101570939490804721189740323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67713959660536480793160215 101570939490804721189740323)
    ·
      refine ⟨152356409236207081784610485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101570939490804721189740323 152356409236207081784610485)
      ·
        refine ⟨14283413365894413917307233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 152356409236207081784610485 14283413365894413917307233)
        ·
          refine ⟨10712560024420810437980425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14283413365894413917307233 10712560024420810437980425)
          ·
            refine ⟨8034420018315607828485319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10712560024420810437980425 8034420018315607828485319)
            ·
              refine ⟨12051630027473411742727979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8034420018315607828485319 12051630027473411742727979)
              ·
                refine ⟨18077445041210117614091969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12051630027473411742727979 18077445041210117614091969)
                ·
                  refine ⟨13558083780907588210568977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18077445041210117614091969 13558083780907588210568977)
                  ·
                    refine ⟨10168562835680691157926733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13558083780907588210568977 10168562835680691157926733)
                    ·
                      refine ⟨3813211063380259184222525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10168562835680691157926733 3813211063380259184222525)
                      ·
                        rfl

theorem cell23_7426202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_7426202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7426202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7426202 prefixEnd_7426202 := by exact prefixLift 7426202
  have htrace : WordTrace (prefixWord ++ tailWord_7426202) baseStart_7426202 baseEnd_7426202 := by
    simpa [prefixWord, tailWord_7426202, baseEnd_7426202] using wordTrace_append hprefix tailTrace_7426202
  have hstable : (prefixWord ++ tailWord_7426202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7426202).length < 2 ^ (prefixWord ++ tailWord_7426202).sum := by decide
  have hdescent : baseEnd_7426202 < baseStart_7426202 := by decide
  rcases family_descends (prefixWord ++ tailWord_7426202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7426251 : List Nat := [1, 1, 1, 1, 3, 2, 5, 1, 1, 1, 6]
def baseStart_7426251 : Nat := 118140960795 + 7426251 * 2 ^ 59
def prefixEnd_7426251 : Nat := 4983230072969 + 3 ^ 40 * 7426251 * 2
def baseEnd_7426251 : Nat := 3813236223932329492509799

theorem tailTrace_7426251 : CollatzResearch.WordTrace tailWord_7426251 prefixEnd_7426251 3813236223932329492509799 := by
  unfold tailWord_7426251
  simp only [CollatzResearch.WordTrace]
  refine ⟨270857625818968404541174607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180571750545978936360783071 270857625818968404541174607)
  ·
    refine ⟨406286438728452606811761911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270857625818968404541174607 406286438728452606811761911)
    ·
      refine ⟨609429658092678910217642867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 406286438728452606811761911 609429658092678910217642867)
      ·
        refine ⟨914144487139018365326464301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 609429658092678910217642867 914144487139018365326464301)
        ·
          refine ⟨342804182677131886997424113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 914144487139018365326464301 342804182677131886997424113)
          ·
            refine ⟨257103137007848915248068085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 342804182677131886997424113 257103137007848915248068085)
            ·
              refine ⟨24103419094485835804506383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 257103137007848915248068085 24103419094485835804506383)
              ·
                refine ⟨36155128641728753706759575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24103419094485835804506383 36155128641728753706759575)
                ·
                  refine ⟨54232692962593130560139363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36155128641728753706759575 54232692962593130560139363)
                  ·
                    refine ⟨81349039443889695840209045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54232692962593130560139363 81349039443889695840209045)
                    ·
                      refine ⟨3813236223932329492509799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81349039443889695840209045 3813236223932329492509799)
                      ·
                        rfl

theorem cell23_7426251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 1, 1, 1, 6].length) (baseStart_7426251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7426251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7426251 prefixEnd_7426251 := by exact prefixLift 7426251
  have htrace : WordTrace (prefixWord ++ tailWord_7426251) baseStart_7426251 baseEnd_7426251 := by
    simpa [prefixWord, tailWord_7426251, baseEnd_7426251] using wordTrace_append hprefix tailTrace_7426251
  have hstable : (prefixWord ++ tailWord_7426251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7426251).length < 2 ^ (prefixWord ++ tailWord_7426251).sum := by decide
  have hdescent : baseEnd_7426251 < baseStart_7426251 := by decide
  rcases family_descends (prefixWord ++ tailWord_7426251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7426252 : List Nat := [2, 2, 1, 6, 1, 1, 2, 2, 1, 5]
def baseStart_7426252 : Nat := 118140960795 + 7426252 * 2 ^ 59
def prefixEnd_7426252 : Nat := 4983230072969 + 3 ^ 40 * 7426252 * 2
def baseEnd_7426252 : Nat := 1271078912470994662865765

theorem tailTrace_7426252 : CollatzResearch.WordTrace tailWord_7426252 prefixEnd_7426252 1271078912470994662865765 := by
  unfold tailWord_7426252
  simp only [CollatzResearch.WordTrace]
  refine ⟨135428831145982390855980505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180571774861309854474640673 135428831145982390855980505)
  ·
    refine ⟨101571623359486793141985379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135428831145982390855980505 101571623359486793141985379)
    ·
      refine ⟨152357435039230189712978069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101571623359486793141985379 152357435039230189712978069)
      ·
        refine ⟨7141754767463915142795847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 152357435039230189712978069 7141754767463915142795847)
        ·
          refine ⟨10712632151195872714193771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7141754767463915142795847 10712632151195872714193771)
          ·
            refine ⟨16068948226793809071290657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10712632151195872714193771 16068948226793809071290657)
            ·
              refine ⟨12051711170095356803467993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16068948226793809071290657 12051711170095356803467993)
              ·
                refine ⟨9038783377571517602600995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12051711170095356803467993 9038783377571517602600995)
                ·
                  refine ⟨13558175066357276403901493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9038783377571517602600995 13558175066357276403901493)
                  ·
                    refine ⟨1271078912470994662865765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13558175066357276403901493 1271078912470994662865765)
                    ·
                      rfl

theorem cell23_7426252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 2, 2, 1, 5].length) (baseStart_7426252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7426252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7426252 prefixEnd_7426252 := by exact prefixLift 7426252
  have htrace : WordTrace (prefixWord ++ tailWord_7426252) baseStart_7426252 baseEnd_7426252 := by
    simpa [prefixWord, tailWord_7426252, baseEnd_7426252] using wordTrace_append hprefix tailTrace_7426252
  have hstable : (prefixWord ++ tailWord_7426252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7426252).length < 2 ^ (prefixWord ++ tailWord_7426252).sum := by decide
  have hdescent : baseEnd_7426252 < baseStart_7426252 := by decide
  rcases family_descends (prefixWord ++ tailWord_7426252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7426255 : List Nat := [1, 1, 2, 1, 1, 3, 3, 4, 3, 2, 2]
def baseStart_7426255 : Nat := 118140960795 + 7426255 * 2 ^ 59
def prefixEnd_7426255 : Nat := 4983230072969 + 3 ^ 40 * 7426255 * 2
def baseEnd_7426255 : Nat := 3813238277854947476859781

theorem tailTrace_7426255 : CollatzResearch.WordTrace tailWord_7426255 prefixEnd_7426255 3813238277854947476859781 := by
  unfold tailWord_7426255
  simp only [CollatzResearch.WordTrace]
  refine ⟨270857771710953913224320219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180571847807302608816213479 270857771710953913224320219)
  ·
    refine ⟨406286657566430869836480329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270857771710953913224320219 406286657566430869836480329)
    ·
      refine ⟨304714993174823152377360247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 406286657566430869836480329 304714993174823152377360247)
      ·
        refine ⟨457072489762234728566040371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304714993174823152377360247 457072489762234728566040371)
        ·
          refine ⟨685608734643352092849060557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 457072489762234728566040371 685608734643352092849060557)
          ·
            refine ⟨257103275491257034818397709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 685608734643352092849060557 257103275491257034818397709)
            ·
              refine ⟨96413728309221388056899141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 257103275491257034818397709 96413728309221388056899141)
              ·
                refine ⟨18077574057979010260668589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 96413728309221388056899141 18077574057979010260668589)
                ·
                  refine ⟨6779090271742128847750721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18077574057979010260668589 6779090271742128847750721)
                  ·
                    refine ⟨5084317703806596635813041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6779090271742128847750721 5084317703806596635813041)
                    ·
                      refine ⟨3813238277854947476859781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5084317703806596635813041 3813238277854947476859781)
                      ·
                        rfl

theorem cell23_7426255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 4, 3, 2, 2].length) (baseStart_7426255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7426255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7426255 prefixEnd_7426255 := by exact prefixLift 7426255
  have htrace : WordTrace (prefixWord ++ tailWord_7426255) baseStart_7426255 baseEnd_7426255 := by
    simpa [prefixWord, tailWord_7426255, baseEnd_7426255] using wordTrace_append hprefix tailTrace_7426255
  have hstable : (prefixWord ++ tailWord_7426255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7426255).length < 2 ^ (prefixWord ++ tailWord_7426255).sum := by decide
  have hdescent : baseEnd_7426255 < baseStart_7426255 := by decide
  rcases family_descends (prefixWord ++ tailWord_7426255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7426291 : List Nat := [1, 1, 1, 2, 2, 4, 2, 1, 2, 7]
def baseStart_7426291 : Nat := 118140960795 + 7426291 * 2 ^ 59
def prefixEnd_7426291 : Nat := 4983230072969 + 3 ^ 40 * 7426291 * 2
def baseEnd_7426291 : Nat := 1271085587719503112003205

theorem tailTrace_7426291 : CollatzResearch.WordTrace tailWord_7426291 prefixEnd_7426291 1271085587719503112003205 := by
  unfold tailWord_7426291
  simp only [CollatzResearch.WordTrace]
  refine ⟨270859084738823491372630727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180572723159215660915087151 270859084738823491372630727)
  ·
    refine ⟨406288627108235237058946091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270859084738823491372630727 406288627108235237058946091)
    ·
      refine ⟨609432940662352855588419137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 406288627108235237058946091 609432940662352855588419137)
      ·
        refine ⟨457074705496764641691314353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 609432940662352855588419137 457074705496764641691314353)
        ·
          refine ⟨342806029122573481268485765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 457074705496764641691314353 342806029122573481268485765)
          ·
            refine ⟨64276130460482527737841081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 342806029122573481268485765 64276130460482527737841081)
            ·
              refine ⟨48207097845361895803380811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64276130460482527737841081 48207097845361895803380811)
              ·
                refine ⟨72310646768042843705071217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48207097845361895803380811 72310646768042843705071217)
                ·
                  refine ⟨54232985076032132778803413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72310646768042843705071217 54232985076032132778803413)
                  ·
                    refine ⟨1271085587719503112003205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54232985076032132778803413 1271085587719503112003205)
                    ·
                      rfl

theorem cell23_7426291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 1, 2, 7].length) (baseStart_7426291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7426291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7426291 prefixEnd_7426291 := by exact prefixLift 7426291
  have htrace : WordTrace (prefixWord ++ tailWord_7426291) baseStart_7426291 baseEnd_7426291 := by
    simpa [prefixWord, tailWord_7426291, baseEnd_7426291] using wordTrace_append hprefix tailTrace_7426291
  have hstable : (prefixWord ++ tailWord_7426291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7426291).length < 2 ^ (prefixWord ++ tailWord_7426291).sum := by decide
  have hdescent : baseEnd_7426291 < baseStart_7426291 := by decide
  rcases family_descends (prefixWord ++ tailWord_7426291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7426315 : List Nat := [1, 1, 1, 1, 5, 2, 3, 1, 3, 3, 2]
def baseStart_7426315 : Nat := 118140960795 + 7426315 * 2 ^ 59
def prefixEnd_7426315 : Nat := 4983230072969 + 3 ^ 40 * 7426315 * 2
def baseEnd_7426315 : Nat := 3813269086694217242109505

theorem tailTrace_7426315 : CollatzResearch.WordTrace tailWord_7426315 prefixEnd_7426315 3813269086694217242109505 := by
  unfold tailWord_7426315
  simp only [CollatzResearch.WordTrace]
  refine ⟨270859960090736543471504399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180573306727157695647669599 270859960090736543471504399)
  ·
    refine ⟨406289940136104815207256599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270859960090736543471504399 406289940136104815207256599)
    ·
      refine ⟨609434910204157222810884899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 406289940136104815207256599 609434910204157222810884899)
      ·
        refine ⟨914152365306235834216327349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 609434910204157222810884899 914152365306235834216327349)
        ·
          refine ⟨85701784247459609457780689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 914152365306235834216327349 85701784247459609457780689)
          ·
            refine ⟨64276338185594707093335517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85701784247459609457780689 64276338185594707093335517)
            ·
              refine ⟨24103626819598015160000819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64276338185594707093335517 24103626819598015160000819)
              ·
                refine ⟨36155440229397022740001229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24103626819598015160000819 36155440229397022740001229)
                ·
                  refine ⟨13558290086023883527500461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36155440229397022740001229 13558290086023883527500461)
                  ·
                    refine ⟨5084358782258956322812673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13558290086023883527500461 5084358782258956322812673)
                    ·
                      refine ⟨3813269086694217242109505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5084358782258956322812673 3813269086694217242109505)
                      ·
                        rfl

theorem cell23_7426315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 1, 3, 3, 2].length) (baseStart_7426315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7426315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7426315 prefixEnd_7426315 := by exact prefixLift 7426315
  have htrace : WordTrace (prefixWord ++ tailWord_7426315) baseStart_7426315 baseEnd_7426315 := by
    simpa [prefixWord, tailWord_7426315, baseEnd_7426315] using wordTrace_append hprefix tailTrace_7426315
  have hstable : (prefixWord ++ tailWord_7426315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7426315).length < 2 ^ (prefixWord ++ tailWord_7426315).sum := by decide
  have hdescent : baseEnd_7426315 < baseStart_7426315 := by decide
  rcases family_descends (prefixWord ++ tailWord_7426315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7426348 : List Nat := [2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 3]
def baseStart_7426348 : Nat := 118140960795 + 7426348 * 2 ^ 59
def prefixEnd_7426348 : Nat := 4983230072969 + 3 ^ 40 * 7426348 * 2
def baseEnd_7426348 : Nat := 3813286031555815612996853

theorem tailTrace_7426348 : CollatzResearch.WordTrace tailWord_7426348 prefixEnd_7426348 3813286031555815612996853 := by
  unfold tailWord_7426348
  simp only [CollatzResearch.WordTrace]
  refine ⟨135430581849808495053727849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180574109133077993404970465 135430581849808495053727849)
  ·
    refine ⟨101572936387356371290295887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135430581849808495053727849 101572936387356371290295887)
    ·
      refine ⟨152359404581034556935443831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101572936387356371290295887 152359404581034556935443831)
      ·
        refine ⟨228539106871551835403165747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152359404581034556935443831 228539106871551835403165747)
        ·
          refine ⟨342808660307327753104748621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228539106871551835403165747 342808660307327753104748621)
          ·
            refine ⟨128553247615247907414280733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 342808660307327753104748621 128553247615247907414280733)
            ·
              refine ⟨48207467855717965280355275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128553247615247907414280733 48207467855717965280355275)
              ·
                refine ⟨72311201783576947920532913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48207467855717965280355275 72311201783576947920532913)
                ·
                  refine ⟨54233401337682710940399685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72311201783576947920532913 54233401337682710940399685)
                  ·
                    refine ⟨10168762750815508301324941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54233401337682710940399685 10168762750815508301324941)
                    ·
                      refine ⟨3813286031555815612996853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10168762750815508301324941 3813286031555815612996853)
                      ·
                        rfl

theorem cell23_7426348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 3].length) (baseStart_7426348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7426348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7426348 prefixEnd_7426348 := by exact prefixLift 7426348
  have htrace : WordTrace (prefixWord ++ tailWord_7426348) baseStart_7426348 baseEnd_7426348 := by
    simpa [prefixWord, tailWord_7426348, baseEnd_7426348] using wordTrace_append hprefix tailTrace_7426348
  have hstable : (prefixWord ++ tailWord_7426348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7426348).length < 2 ^ (prefixWord ++ tailWord_7426348).sum := by decide
  have hdescent : baseEnd_7426348 < baseStart_7426348 := by decide
  rcases family_descends (prefixWord ++ tailWord_7426348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7426362 : List Nat := [3, 1, 1, 1, 4, 3, 2, 1, 1, 4, 2]
def baseStart_7426362 : Nat := 118140960795 + 7426362 * 2 ^ 59
def prefixEnd_7426362 : Nat := 4983230072969 + 3 ^ 40 * 7426362 * 2
def baseEnd_7426362 : Nat := 3813293220284978558221789

theorem tailTrace_7426362 : CollatzResearch.WordTrace tailWord_7426362 prefixEnd_7426362 3813293220284978558221789 := by
  unfold tailWord_7426362
  simp only [CollatzResearch.WordTrace]
  refine ⟨67715418580391567624616335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180574449547710846998976893 67715418580391567624616335)
  ·
    refine ⟨101573127870587351436924503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67715418580391567624616335 101573127870587351436924503)
    ·
      refine ⟨152359691805881027155386755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101573127870587351436924503 152359691805881027155386755)
      ·
        refine ⟨228539537708821540733080133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152359691805881027155386755 228539537708821540733080133)
        ·
          refine ⟨42851163320404038887452525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 228539537708821540733080133 42851163320404038887452525)
          ·
            refine ⟨16069186245151514582794697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42851163320404038887452525 16069186245151514582794697)
            ·
              refine ⟨12051889683863635937096023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16069186245151514582794697 12051889683863635937096023)
              ·
                refine ⟨18077834525795453905644035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12051889683863635937096023 18077834525795453905644035)
                ·
                  refine ⟨27116751788693180858466053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18077834525795453905644035 27116751788693180858466053)
                  ·
                    refine ⟨5084390960379971410962385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27116751788693180858466053 5084390960379971410962385)
                    ·
                      refine ⟨3813293220284978558221789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5084390960379971410962385 3813293220284978558221789)
                      ·
                        rfl

theorem cell23_7426362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 2, 1, 1, 4, 2].length) (baseStart_7426362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7426362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7426362 prefixEnd_7426362 := by exact prefixLift 7426362
  have htrace : WordTrace (prefixWord ++ tailWord_7426362) baseStart_7426362 baseEnd_7426362 := by
    simpa [prefixWord, tailWord_7426362, baseEnd_7426362] using wordTrace_append hprefix tailTrace_7426362
  have hstable : (prefixWord ++ tailWord_7426362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7426362).length < 2 ^ (prefixWord ++ tailWord_7426362).sum := by decide
  have hdescent : baseEnd_7426362 < baseStart_7426362 := by decide
  rcases family_descends (prefixWord ++ tailWord_7426362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7426385 : List Nat := [1, 2, 2, 1, 4, 2, 1, 5, 5]
def baseStart_7426385 : Nat := 118140960795 + 7426385 * 2 ^ 59
def prefixEnd_7426385 : Nat := 4983230072969 + 3 ^ 40 * 7426385 * 2
def baseEnd_7426385 : Nat := 423700558926670218692687

theorem tailTrace_7426385 : CollatzResearch.WordTrace tailWord_7426385 prefixEnd_7426385 423700558926670218692687 := by
  unfold tailWord_7426385
  simp only [CollatzResearch.WordTrace]
  refine ⟨270862513200482945426552609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180575008800321963617701739 270862513200482945426552609)
  ·
    refine ⟨203146884900362209069914457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270862513200482945426552609 203146884900362209069914457)
    ·
      refine ⟨152360163675271656802435843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203146884900362209069914457 152360163675271656802435843)
      ·
        refine ⟨228540245512907485203653765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152360163675271656802435843 228540245512907485203653765)
        ·
          refine ⟨42851296033670153475685081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 228540245512907485203653765 42851296033670153475685081)
          ·
            refine ⟨32138472025252615106763811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42851296033670153475685081 32138472025252615106763811)
            ·
              refine ⟨48207708037878922660145717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32138472025252615106763811 48207708037878922660145717)
              ·
                refine ⟨4519472628551148999388661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48207708037878922660145717 4519472628551148999388661)
                ·
                  refine ⟨423700558926670218692687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4519472628551148999388661 423700558926670218692687)
                  ·
                    rfl

theorem cell23_7426385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 5, 5].length) (baseStart_7426385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7426385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7426385 prefixEnd_7426385 := by exact prefixLift 7426385
  have htrace : WordTrace (prefixWord ++ tailWord_7426385) baseStart_7426385 baseEnd_7426385 := by
    simpa [prefixWord, tailWord_7426385, baseEnd_7426385] using wordTrace_append hprefix tailTrace_7426385
  have hstable : (prefixWord ++ tailWord_7426385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7426385).length < 2 ^ (prefixWord ++ tailWord_7426385).sum := by decide
  have hdescent : baseEnd_7426385 < baseStart_7426385 := by decide
  rcases family_descends (prefixWord ++ tailWord_7426385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7426396 : List Nat := [2, 2, 4, 3, 1, 1, 1, 1, 4, 2, 2]
def baseStart_7426396 : Nat := 118140960795 + 7426396 * 2 ^ 59
def prefixEnd_7426396 : Nat := 4983230072969 + 3 ^ 40 * 7426396 * 2
def baseEnd_7426396 : Nat := 3813310678627231425196633

theorem tailTrace_7426396 : CollatzResearch.WordTrace tailWord_7426396 prefixEnd_7426396 3813310678627231425196633 := by
  unfold tailWord_7426396
  simp only [CollatzResearch.WordTrace]
  refine ⟨135431457201721547152601521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180575276268962062870135361 135431457201721547152601521)
  ·
    refine ⟨101573592901291160364451141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135431457201721547152601521 101573592901291160364451141)
    ·
      refine ⟨19045048668992092568334589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 101573592901291160364451141 19045048668992092568334589)
      ·
        refine ⟨7141893250872034713125471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19045048668992092568334589 7141893250872034713125471)
        ·
          refine ⟨10712839876308052069688207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7141893250872034713125471 10712839876308052069688207)
          ·
            refine ⟨16069259814462078104532311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10712839876308052069688207 16069259814462078104532311)
            ·
              refine ⟨24103889721693117156798467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16069259814462078104532311 24103889721693117156798467)
              ·
                refine ⟨36155834582539675735197701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24103889721693117156798467 36155834582539675735197701)
                ·
                  refine ⟨6779218984226189200349569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36155834582539675735197701 6779218984226189200349569)
                  ·
                    refine ⟨5084414238169641900262177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6779218984226189200349569 5084414238169641900262177)
                    ·
                      refine ⟨3813310678627231425196633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5084414238169641900262177 3813310678627231425196633)
                      ·
                        rfl

theorem cell23_7426396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_7426396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7426396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7426396 prefixEnd_7426396 := by exact prefixLift 7426396
  have htrace : WordTrace (prefixWord ++ tailWord_7426396) baseStart_7426396 baseEnd_7426396 := by
    simpa [prefixWord, tailWord_7426396, baseEnd_7426396] using wordTrace_append hprefix tailTrace_7426396
  have hstable : (prefixWord ++ tailWord_7426396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7426396).length < 2 ^ (prefixWord ++ tailWord_7426396).sum := by decide
  have hdescent : baseEnd_7426396 < baseStart_7426396 := by decide
  rcases family_descends (prefixWord ++ tailWord_7426396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7426402 : List Nat := [3, 3, 2, 1, 1, 2, 2, 4, 5]
def baseStart_7426402 : Nat := 118140960795 + 7426402 * 2 ^ 59
def prefixEnd_7426402 : Nat := 4983230072969 + 3 ^ 40 * 7426402 * 2
def baseEnd_7426402 : Nat := 423701528834573155746845

theorem tailTrace_7426402 : CollatzResearch.WordTrace tailWord_7426402 prefixEnd_7426402 423701528834573155746845 := by
  unfold tailWord_7426402
  simp only [CollatzResearch.WordTrace]
  refine ⟨67715783310355339332480365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180575422160947571553280973 67715783310355339332480365)
  ·
    refine ⟨25393418741383252249680137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 67715783310355339332480365 25393418741383252249680137)
    ·
      refine ⟨19045064056037439187260103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25393418741383252249680137 19045064056037439187260103)
      ·
        refine ⟨28567596084056158780890155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19045064056037439187260103 28567596084056158780890155)
        ·
          refine ⟨42851394126084238171335233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28567596084056158780890155 42851394126084238171335233)
          ·
            refine ⟨32138545594563178628501425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42851394126084238171335233 32138545594563178628501425)
            ·
              refine ⟨24103909195922383971376069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32138545594563178628501425 24103909195922383971376069)
              ·
                refine ⟨4519482974235446994633013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24103909195922383971376069 4519482974235446994633013)
                ·
                  refine ⟨423701528834573155746845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4519482974235446994633013 423701528834573155746845)
                  ·
                    rfl

theorem cell23_7426402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 4, 5].length) (baseStart_7426402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7426402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7426402 prefixEnd_7426402 := by exact prefixLift 7426402
  have htrace : WordTrace (prefixWord ++ tailWord_7426402) baseStart_7426402 baseEnd_7426402 := by
    simpa [prefixWord, tailWord_7426402, baseEnd_7426402] using wordTrace_append hprefix tailTrace_7426402
  have hstable : (prefixWord ++ tailWord_7426402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7426402).length < 2 ^ (prefixWord ++ tailWord_7426402).sum := by decide
  have hdescent : baseEnd_7426402 < baseStart_7426402 := by decide
  rcases family_descends (prefixWord ++ tailWord_7426402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7426455 : List Nat := [1, 1, 3, 3, 1, 1, 3, 1, 4, 2, 3]
def baseStart_7426455 : Nat := 118140960795 + 7426455 * 2 ^ 59
def prefixEnd_7426455 : Nat := 4983230072969 + 3 ^ 40 * 7426455 * 2
def baseEnd_7426455 : Nat := 3813340973985846694358861

theorem tailTrace_7426455 : CollatzResearch.WordTrace tailWord_7426455 prefixEnd_7426455 3813340973985846694358861 := by
  unfold tailWord_7426455
  simp only [CollatzResearch.WordTrace]
  refine ⟨270865066310229347381600819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180576710873486231587733879 270865066310229347381600819)
  ·
    refine ⟨406297599465344021072401229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270865066310229347381600819 406297599465344021072401229)
    ·
      refine ⟨152361599799504007902150461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 406297599465344021072401229 152361599799504007902150461)
      ·
        refine ⟨57135599924814002963306423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152361599799504007902150461 57135599924814002963306423)
        ·
          refine ⟨85703399887221004444959635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57135599924814002963306423 85703399887221004444959635)
          ·
            refine ⟨128555099830831506667439453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85703399887221004444959635 128555099830831506667439453)
            ·
              refine ⟨48208162436561815000289795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128555099830831506667439453 48208162436561815000289795)
              ·
                refine ⟨72312243654842722500434693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48208162436561815000289795 72312243654842722500434693)
                ·
                  refine ⟨13558545685283010468831505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72312243654842722500434693 13558545685283010468831505)
                  ·
                    refine ⟨10168909263962257851623629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13558545685283010468831505 10168909263962257851623629)
                    ·
                      refine ⟨3813340973985846694358861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10168909263962257851623629 3813340973985846694358861)
                      ·
                        rfl

theorem cell23_7426455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 1, 4, 2, 3].length) (baseStart_7426455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7426455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7426455 prefixEnd_7426455 := by exact prefixLift 7426455
  have htrace : WordTrace (prefixWord ++ tailWord_7426455) baseStart_7426455 baseEnd_7426455 := by
    simpa [prefixWord, tailWord_7426455, baseEnd_7426455] using wordTrace_append hprefix tailTrace_7426455
  have hstable : (prefixWord ++ tailWord_7426455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7426455).length < 2 ^ (prefixWord ++ tailWord_7426455).sum := by decide
  have hdescent : baseEnd_7426455 < baseStart_7426455 := by decide
  rcases family_descends (prefixWord ++ tailWord_7426455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7426505 : List Nat := [1, 2, 1, 1, 2, 1, 4, 5, 1, 5]
def baseStart_7426505 : Nat := 118140960795 + 7426505 * 2 ^ 59
def prefixEnd_7426505 : Nat := 4983230072969 + 3 ^ 40 * 7426505 * 2
def baseEnd_7426505 : Nat := 1271122216006190499577877

theorem tailTrace_7426505 : CollatzResearch.WordTrace tailWord_7426505 prefixEnd_7426505 1271122216006190499577877 := by
  unfold tailWord_7426505
  simp only [CollatzResearch.WordTrace]
  refine ⟨270866889960048205920920969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180577926640032137280613979 270866889960048205920920969)
  ·
    refine ⟨203150167470036154440690727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270866889960048205920920969 203150167470036154440690727)
    ·
      refine ⟨304725251205054231661036091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203150167470036154440690727 304725251205054231661036091)
      ·
        refine ⟨457087876807581347491554137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304725251205054231661036091 457087876807581347491554137)
        ·
          refine ⟨342815907605686010618665603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 457087876807581347491554137 342815907605686010618665603)
          ·
            refine ⟨514223861408529015927998405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 342815907605686010618665603 514223861408529015927998405)
            ·
              refine ⟨96416974014099190486499701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 514223861408529015927998405 96416974014099190486499701)
              ·
                refine ⟨9039091313821799108109347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 96416974014099190486499701 9039091313821799108109347)
                ·
                  refine ⟨13558636970732698662164021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9039091313821799108109347 13558636970732698662164021)
                  ·
                    refine ⟨1271122216006190499577877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13558636970732698662164021 1271122216006190499577877)
                    ·
                      rfl

theorem cell23_7426505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 5, 1, 5].length) (baseStart_7426505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7426505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7426505 prefixEnd_7426505 := by exact prefixLift 7426505
  have htrace : WordTrace (prefixWord ++ tailWord_7426505) baseStart_7426505 baseEnd_7426505 := by
    simpa [prefixWord, tailWord_7426505, baseEnd_7426505] using wordTrace_append hprefix tailTrace_7426505
  have hstable : (prefixWord ++ tailWord_7426505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7426505).length < 2 ^ (prefixWord ++ tailWord_7426505).sum := by decide
  have hdescent : baseEnd_7426505 < baseStart_7426505 := by decide
  rcases family_descends (prefixWord ++ tailWord_7426505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7426542 : List Nat := [4, 1, 2, 1, 2, 2, 2, 1, 3, 1, 4]
def baseStart_7426542 : Nat := 118140960795 + 7426542 * 2 ^ 59
def prefixEnd_7426542 : Nat := 4983230072969 + 3 ^ 40 * 7426542 * 2
def baseEnd_7426542 : Nat := 3813385646802787853970961

theorem tailTrace_7426542 : CollatzResearch.WordTrace tailWord_7426542 prefixEnd_7426542 3813385646802787853970961 := by
  unfold tailWord_7426542
  simp only [CollatzResearch.WordTrace]
  refine ⟨33858529932614270155002235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180578826307276107493345253 33858529932614270155002235)
  ·
    refine ⟨50787794898921405232503353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33858529932614270155002235 50787794898921405232503353)
    ·
      refine ⟨38090846174191053924377515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50787794898921405232503353 38090846174191053924377515)
      ·
        refine ⟨57136269261286580886566273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38090846174191053924377515 57136269261286580886566273)
        ·
          refine ⟨42852201945964935664924705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57136269261286580886566273 42852201945964935664924705)
          ·
            refine ⟨32139151459473701748693529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42852201945964935664924705 32139151459473701748693529)
            ·
              refine ⟨24104363594605276311520147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32139151459473701748693529 24104363594605276311520147)
              ·
                refine ⟨36156545391907914467280221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24104363594605276311520147 36156545391907914467280221)
                ·
                  refine ⟨13558704521965467925230083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36156545391907914467280221 13558704521965467925230083)
                  ·
                    refine ⟨20338056782948201887845125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13558704521965467925230083 20338056782948201887845125)
                    ·
                      refine ⟨3813385646802787853970961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20338056782948201887845125 3813385646802787853970961)
                      ·
                        rfl

theorem cell23_7426542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 1, 3, 1, 4].length) (baseStart_7426542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7426542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7426542 prefixEnd_7426542 := by exact prefixLift 7426542
  have htrace : WordTrace (prefixWord ++ tailWord_7426542) baseStart_7426542 baseEnd_7426542 := by
    simpa [prefixWord, tailWord_7426542, baseEnd_7426542] using wordTrace_append hprefix tailTrace_7426542
  have hstable : (prefixWord ++ tailWord_7426542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7426542).length < 2 ^ (prefixWord ++ tailWord_7426542).sum := by decide
  have hdescent : baseEnd_7426542 < baseStart_7426542 := by decide
  rcases family_descends (prefixWord ++ tailWord_7426542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7426575 : List Nat := [1, 1, 2, 1, 1, 1, 2, 3, 5, 3, 3]
def baseStart_7426575 : Nat := 118140960795 + 7426575 * 2 ^ 59
def prefixEnd_7426575 : Nat := 4983230072969 + 3 ^ 40 * 7426575 * 2
def baseEnd_7426575 : Nat := 3813402591664386224858309

theorem tailTrace_7426575 : CollatzResearch.WordTrace tailWord_7426575 prefixEnd_7426575 3813402591664386224858309 := by
  unfold tailWord_7426575
  simp only [CollatzResearch.WordTrace]
  refine ⟨270869443069794607875969179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180579628713196405250646119 270869443069794607875969179)
  ·
    refine ⟨406304164604691911813953769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270869443069794607875969179 406304164604691911813953769)
    ·
      refine ⟨304728123453518933860465327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 406304164604691911813953769 304728123453518933860465327)
      ·
        refine ⟨457092185180278400790697991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304728123453518933860465327 457092185180278400790697991)
        ·
          refine ⟨685638277770417601186046987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 457092185180278400790697991 685638277770417601186046987)
          ·
            refine ⟨1028457416655626401779070481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 685638277770417601186046987 1028457416655626401779070481)
            ·
              refine ⟨771343062491719801334302861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1028457416655626401779070481 771343062491719801334302861)
              ·
                refine ⟨289253648434394925500363573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 771343062491719801334302861 289253648434394925500363573)
                ·
                  refine ⟨27117529540724524265659085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 289253648434394925500363573 27117529540724524265659085)
                  ·
                    refine ⟨10169073577771696599622157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27117529540724524265659085 10169073577771696599622157)
                    ·
                      refine ⟨3813402591664386224858309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10169073577771696599622157 3813402591664386224858309)
                      ·
                        rfl

theorem cell23_7426575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 5, 3, 3].length) (baseStart_7426575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7426575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7426575 prefixEnd_7426575 := by exact prefixLift 7426575
  have htrace : WordTrace (prefixWord ++ tailWord_7426575) baseStart_7426575 baseEnd_7426575 := by
    simpa [prefixWord, tailWord_7426575, baseEnd_7426575] using wordTrace_append hprefix tailTrace_7426575
  have hstable : (prefixWord ++ tailWord_7426575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7426575).length < 2 ^ (prefixWord ++ tailWord_7426575).sum := by decide
  have hdescent : baseEnd_7426575 < baseStart_7426575 := by decide
  rcases family_descends (prefixWord ++ tailWord_7426575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7426589 : List Nat := [1, 4, 2, 2, 1, 4, 1, 1, 1, 2, 4]
def baseStart_7426589 : Nat := 118140960795 + 7426589 * 2 ^ 59
def prefixEnd_7426589 : Nat := 4983230072969 + 3 ^ 40 * 7426589 * 2
def baseEnd_7426589 : Nat := 3813409780393549170083245

theorem tailTrace_7426589 : CollatzResearch.WordTrace tailWord_7426589 prefixEnd_7426589 3813409780393549170083245 := by
  unfold tailWord_7426589
  simp only [CollatzResearch.WordTrace]
  refine ⟨270869953691743888266978821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180579969127829258844652547 270869953691743888266978821)
  ·
    refine ⟨50788116317201979050058529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 270869953691743888266978821 50788116317201979050058529)
    ·
      refine ⟨38091087237901484287543897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50788116317201979050058529 38091087237901484287543897)
      ·
        refine ⟨28568315428426113215657923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38091087237901484287543897 28568315428426113215657923)
        ·
          refine ⟨42852473142639169823486885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28568315428426113215657923 42852473142639169823486885)
          ·
            refine ⟨8034838714244844341903791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42852473142639169823486885 8034838714244844341903791)
            ·
              refine ⟨12052258071367266512855687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8034838714244844341903791 12052258071367266512855687)
              ·
                refine ⟨18078387107050899769283531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12052258071367266512855687 18078387107050899769283531)
                ·
                  refine ⟨27117580660576349653925297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18078387107050899769283531 27117580660576349653925297)
                  ·
                    refine ⟨20338185495432262240443973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27117580660576349653925297 20338185495432262240443973)
                    ·
                      refine ⟨3813409780393549170083245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20338185495432262240443973 3813409780393549170083245)
                      ·
                        rfl

theorem cell23_7426589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 1, 1, 1, 2, 4].length) (baseStart_7426589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7426589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7426589 prefixEnd_7426589 := by exact prefixLift 7426589
  have htrace : WordTrace (prefixWord ++ tailWord_7426589) baseStart_7426589 baseEnd_7426589 := by
    simpa [prefixWord, tailWord_7426589, baseEnd_7426589] using wordTrace_append hprefix tailTrace_7426589
  have hstable : (prefixWord ++ tailWord_7426589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7426589).length < 2 ^ (prefixWord ++ tailWord_7426589).sum := by decide
  have hdescent : baseEnd_7426589 < baseStart_7426589 := by decide
  rcases family_descends (prefixWord ++ tailWord_7426589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7426599 : List Nat := [1, 1, 7, 2, 1, 1, 1, 9]
def baseStart_7426599 : Nat := 118140960795 + 7426599 * 2 ^ 59
def prefixEnd_7426599 : Nat := 4983230072969 + 3 ^ 40 * 7426599 * 2
def baseEnd_7426599 : Nat := 141237589451855338183637

theorem tailTrace_7426599 : CollatzResearch.WordTrace tailWord_7426599 prefixEnd_7426599 141237589451855338183637 := by
  unfold tailWord_7426599
  simp only [CollatzResearch.WordTrace]
  refine ⟨270870318421707659974842851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180580212281138439983228567 270870318421707659974842851)
  ·
    refine ⟨406305477632561489962264277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270870318421707659974842851 406305477632561489962264277)
    ·
      refine ⟨9522784632013159920990569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 406305477632561489962264277 9522784632013159920990569)
      ·
        refine ⟨7142088474009869940742927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9522784632013159920990569 7142088474009869940742927)
        ·
          refine ⟨10713132711014804911114391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7142088474009869940742927 10713132711014804911114391)
          ·
            refine ⟨16069699066522207366671587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10713132711014804911114391 16069699066522207366671587)
            ·
              refine ⟨24104548599783311050007381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16069699066522207366671587 24104548599783311050007381)
              ·
                refine ⟨141237589451855338183637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24104548599783311050007381 141237589451855338183637)
                ·
                  rfl

theorem cell23_7426599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 9].length) (baseStart_7426599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7426599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7426599 prefixEnd_7426599 := by exact prefixLift 7426599
  have htrace : WordTrace (prefixWord ++ tailWord_7426599) baseStart_7426599 baseEnd_7426599 := by
    simpa [prefixWord, tailWord_7426599, baseEnd_7426599] using wordTrace_append hprefix tailTrace_7426599
  have hstable : (prefixWord ++ tailWord_7426599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7426599).length < 2 ^ (prefixWord ++ tailWord_7426599).sum := by decide
  have hdescent : baseEnd_7426599 < baseStart_7426599 := by decide
  rcases family_descends (prefixWord ++ tailWord_7426599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7426655 : List Nat := [1, 1, 2, 3, 1, 1, 1, 6, 7]
def baseStart_7426655 : Nat := 118140960795 + 7426655 * 2 ^ 59
def prefixEnd_7426655 : Nat := 4983230072969 + 3 ^ 40 * 7426655 * 2
def baseEnd_7426655 : Nat := 423715963346305101317549

theorem tailTrace_7426655 : CollatzResearch.WordTrace tailWord_7426655 prefixEnd_7426655 423715963346305101317549 := by
  unfold tailWord_7426655
  simp only [CollatzResearch.WordTrace]
  refine ⟨270872360909504781538881419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180581573939669854359254279 270872360909504781538881419)
  ·
    refine ⟨406308541364257172308322129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270872360909504781538881419 406308541364257172308322129)
    ·
      refine ⟨304731406023192879231241597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 406308541364257172308322129 304731406023192879231241597)
      ·
        refine ⟨114274277258697329711715599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 304731406023192879231241597 114274277258697329711715599)
        ·
          refine ⟨171411415888045994567573399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114274277258697329711715599 171411415888045994567573399)
          ·
            refine ⟨257117123832068991851360099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171411415888045994567573399 257117123832068991851360099)
            ·
              refine ⟨385675685748103487777040149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 257117123832068991851360099 385675685748103487777040149)
              ·
                refine ⟨18078547769442350989548757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 385675685748103487777040149 18078547769442350989548757)
                ·
                  refine ⟨423715963346305101317549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18078547769442350989548757 423715963346305101317549)
                  ·
                    rfl

theorem cell23_7426655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 6, 7].length) (baseStart_7426655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7426655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7426655 prefixEnd_7426655 := by exact prefixLift 7426655
  have htrace : WordTrace (prefixWord ++ tailWord_7426655) baseStart_7426655 baseEnd_7426655 := by
    simpa [prefixWord, tailWord_7426655, baseEnd_7426655] using wordTrace_append hprefix tailTrace_7426655
  have hstable : (prefixWord ++ tailWord_7426655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7426655).length < 2 ^ (prefixWord ++ tailWord_7426655).sum := by decide
  have hdescent : baseEnd_7426655 < baseStart_7426655 := by decide
  rcases family_descends (prefixWord ++ tailWord_7426655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7426689 : List Nat := [1, 2, 4, 2, 1, 1, 3, 4, 5]
def baseStart_7426689 : Nat := 118140960795 + 7426689 * 2 ^ 59
def prefixEnd_7426689 : Nat := 4983230072969 + 3 ^ 40 * 7426689 * 2
def baseEnd_7426689 : Nat := 423717903162110975425865

theorem tailTrace_7426689 : CollatzResearch.WordTrace tailWord_7426689 prefixEnd_7426689 423717903162110975425865 := by
  unfold tailWord_7426689
  simp only [CollatzResearch.WordTrace]
  refine ⟨270873600991381605345619121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180582400660921070230412747 270873600991381605345619121)
  ·
    refine ⟨203155200743536204009214341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270873600991381605345619121 203155200743536204009214341)
    ·
      refine ⟨38091600139413038251727689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 203155200743536204009214341 38091600139413038251727689)
      ·
        refine ⟨28568700104559778688795767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38091600139413038251727689 28568700104559778688795767)
        ·
          refine ⟨42853050156839668033193651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28568700104559778688795767 42853050156839668033193651)
          ·
            refine ⟨64279575235259502049790477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42853050156839668033193651 64279575235259502049790477)
            ·
              refine ⟨24104840713222313268671429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64279575235259502049790477 24104840713222313268671429)
              ·
                refine ⟨4519657633729183737875893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24104840713222313268671429 4519657633729183737875893)
                ·
                  refine ⟨423717903162110975425865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4519657633729183737875893 423717903162110975425865)
                  ·
                    rfl

theorem cell23_7426689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 4, 5].length) (baseStart_7426689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7426689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7426689 prefixEnd_7426689 := by exact prefixLift 7426689
  have htrace : WordTrace (prefixWord ++ tailWord_7426689) baseStart_7426689 baseEnd_7426689 := by
    simpa [prefixWord, tailWord_7426689, baseEnd_7426689] using wordTrace_append hprefix tailTrace_7426689
  have hstable : (prefixWord ++ tailWord_7426689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7426689).length < 2 ^ (prefixWord ++ tailWord_7426689).sum := by decide
  have hdescent : baseEnd_7426689 < baseStart_7426689 := by decide
  rcases family_descends (prefixWord ++ tailWord_7426689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7426702 : List Nat := [4, 1, 1, 3, 1, 1, 2, 2, 1, 7]
def baseStart_7426702 : Nat := 118140960795 + 7426702 * 2 ^ 59
def prefixEnd_7426702 : Nat := 4983230072969 + 3 ^ 40 * 7426702 * 2
def baseEnd_7426702 : Nat := 1271155934569169075990075

theorem tailTrace_7426702 : CollatzResearch.WordTrace tailWord_7426702 prefixEnd_7426702 1271155934569169075990075 := by
  unfold tailWord_7426702
  simp only [CollatzResearch.WordTrace]
  refine ⟨33859259392541813570730295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180582716760223005710561573 33859259392541813570730295)
  ·
    refine ⟨50788889088812720356095443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33859259392541813570730295 50788889088812720356095443)
    ·
      refine ⟨76183333633219080534143165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50788889088812720356095443 76183333633219080534143165)
      ·
        refine ⟨28568750112457155200303687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76183333633219080534143165 28568750112457155200303687)
        ·
          refine ⟨42853125168685732800455531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28568750112457155200303687 42853125168685732800455531)
          ·
            refine ⟨64279687753028599200683297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42853125168685732800455531 64279687753028599200683297)
            ·
              refine ⟨48209765814771449400512473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64279687753028599200683297 48209765814771449400512473)
              ·
                refine ⟨36157324361078587050384355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48209765814771449400512473 36157324361078587050384355)
                ·
                  refine ⟨54235986541617880575576533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36157324361078587050384355 54235986541617880575576533)
                  ·
                    refine ⟨1271155934569169075990075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54235986541617880575576533 1271155934569169075990075)
                    ·
                      rfl

theorem cell23_7426702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 2, 1, 7].length) (baseStart_7426702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7426702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7426702 prefixEnd_7426702 := by exact prefixLift 7426702
  have htrace : WordTrace (prefixWord ++ tailWord_7426702) baseStart_7426702 baseEnd_7426702 := by
    simpa [prefixWord, tailWord_7426702, baseEnd_7426702] using wordTrace_append hprefix tailTrace_7426702
  have hstable : (prefixWord ++ tailWord_7426702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7426702).length < 2 ^ (prefixWord ++ tailWord_7426702).sum := by decide
  have hdescent : baseEnd_7426702 < baseStart_7426702 := by decide
  rcases family_descends (prefixWord ++ tailWord_7426702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7426739 : List Nat := [1, 1, 1, 2, 3, 4, 1, 2, 2, 4, 2]
def baseStart_7426739 : Nat := 118140960795 + 7426739 * 2 ^ 59
def prefixEnd_7426739 : Nat := 4983230072969 + 3 ^ 40 * 7426739 * 2
def baseEnd_7426739 : Nat := 3813486802491723583207555

theorem tailTrace_7426739 : CollatzResearch.WordTrace tailWord_7426739 prefixEnd_7426739 3813486802491723583207555 := by
  unfold tailWord_7426739
  simp only [CollatzResearch.WordTrace]
  refine ⟨270875424641200463884939271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180583616427466975923292847 270875424641200463884939271)
  ·
    refine ⟨406313136961800695827408907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270875424641200463884939271 406313136961800695827408907)
    ·
      refine ⟨609469705442701043741113361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 406313136961800695827408907 609469705442701043741113361)
      ·
        refine ⟨457102279082025782805835021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 609469705442701043741113361 457102279082025782805835021)
        ·
          refine ⟨171413354655759668552188133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 457102279082025782805835021 171413354655759668552188133)
          ·
            refine ⟨32140003997954937853535275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 171413354655759668552188133 32140003997954937853535275)
            ·
              refine ⟨48210005996932406780302913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32140003997954937853535275 48210005996932406780302913)
              ·
                refine ⟨36157504497699305085227185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48210005996932406780302913 36157504497699305085227185)
                ·
                  refine ⟨27118128373274478813920389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36157504497699305085227185 27118128373274478813920389)
                  ·
                    refine ⟨5084649069988964777610073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27118128373274478813920389 5084649069988964777610073)
                    ·
                      refine ⟨3813486802491723583207555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5084649069988964777610073 3813486802491723583207555)
                      ·
                        rfl

theorem cell23_7426739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 2, 2, 4, 2].length) (baseStart_7426739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7426739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7426739 prefixEnd_7426739 := by exact prefixLift 7426739
  have htrace : WordTrace (prefixWord ++ tailWord_7426739) baseStart_7426739 baseEnd_7426739 := by
    simpa [prefixWord, tailWord_7426739, baseEnd_7426739] using wordTrace_append hprefix tailTrace_7426739
  have hstable : (prefixWord ++ tailWord_7426739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7426739).length < 2 ^ (prefixWord ++ tailWord_7426739).sum := by decide
  have hdescent : baseEnd_7426739 < baseStart_7426739 := by decide
  rcases family_descends (prefixWord ++ tailWord_7426739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7426749 : List Nat := [1, 4, 1, 2, 1, 3, 1, 3, 3, 4]
def baseStart_7426749 : Nat := 118140960795 + 7426749 * 2 ^ 59
def prefixEnd_7426749 : Nat := 4983230072969 + 3 ^ 40 * 7426749 * 2
def baseEnd_7426749 : Nat := 1271163979099422848027503

theorem tailTrace_7426749 : CollatzResearch.WordTrace tailWord_7426749 prefixEnd_7426749 1271163979099422848027503 := by
  unfold tailWord_7426749
  simp only [CollatzResearch.WordTrace]
  refine ⟨270875789371164235592803301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180583859580776157061868867 270875789371164235592803301)
  ·
    refine ⟨50789210507093294173650619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 270875789371164235592803301 50789210507093294173650619)
    ·
      refine ⟨76183815760639941260475929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50789210507093294173650619 76183815760639941260475929)
      ·
        refine ⟨57137861820479955945356947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76183815760639941260475929 57137861820479955945356947)
        ·
          refine ⟨85706792730719933918035421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57137861820479955945356947 85706792730719933918035421)
          ·
            refine ⟨32140047274019975219263283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85706792730719933918035421 32140047274019975219263283)
            ·
              refine ⟨48210070911029962828894925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32140047274019975219263283 48210070911029962828894925)
              ·
                refine ⟨18078776591636236060835597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48210070911029962828894925 18078776591636236060835597)
                ·
                  refine ⟨6779541221863588522813349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18078776591636236060835597 6779541221863588522813349)
                  ·
                    refine ⟨1271163979099422848027503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6779541221863588522813349 1271163979099422848027503)
                    ·
                      rfl

theorem cell23_7426749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 3, 3, 4].length) (baseStart_7426749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7426749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7426749 prefixEnd_7426749 := by exact prefixLift 7426749
  have htrace : WordTrace (prefixWord ++ tailWord_7426749) baseStart_7426749 baseEnd_7426749 := by
    simpa [prefixWord, tailWord_7426749, baseEnd_7426749] using wordTrace_append hprefix tailTrace_7426749
  have hstable : (prefixWord ++ tailWord_7426749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7426749).length < 2 ^ (prefixWord ++ tailWord_7426749).sum := by decide
  have hdescent : baseEnd_7426749 < baseStart_7426749 := by decide
  rcases family_descends (prefixWord ++ tailWord_7426749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7426756 : List Nat := [2, 3, 3, 1, 1, 2, 2, 1, 2, 4, 2]
def baseStart_7426756 : Nat := 118140960795 + 7426756 * 2 ^ 59
def prefixEnd_7426756 : Nat := 4983230072969 + 3 ^ 40 * 7426756 * 2
def baseEnd_7426756 : Nat := 3813495531662850016694977

theorem tailTrace_7426756 : CollatzResearch.WordTrace tailWord_7426756 prefixEnd_7426756 3813495531662850016694977 := by
  unfold tailWord_7426756
  simp only [CollatzResearch.WordTrace]
  refine ⟨135438022341069437894154061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180584029788092583858872081 135438022341069437894154061)
  ·
    refine ⟨50789258377901039210307773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135438022341069437894154061 50789258377901039210307773)
    ·
      refine ⟨19045971891712889703865415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50789258377901039210307773 19045971891712889703865415)
      ·
        refine ⟨28568957837569334555798123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19045971891712889703865415 28568957837569334555798123)
        ·
          refine ⟨42853436756354001833697185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28568957837569334555798123 42853436756354001833697185)
          ·
            refine ⟨32140077567265501375272889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42853436756354001833697185 32140077567265501375272889)
            ·
              refine ⟨24105058175449126031454667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32140077567265501375272889 24105058175449126031454667)
              ·
                refine ⟨36157587263173689047182001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24105058175449126031454667 36157587263173689047182001)
                ·
                  refine ⟨27118190447380266785386501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36157587263173689047182001 27118190447380266785386501)
                  ·
                    refine ⟨5084660708883800022259969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27118190447380266785386501 5084660708883800022259969)
                    ·
                      refine ⟨3813495531662850016694977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5084660708883800022259969 3813495531662850016694977)
                      ·
                        rfl

theorem cell23_7426756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 1, 2, 4, 2].length) (baseStart_7426756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7426756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7426756 prefixEnd_7426756 := by exact prefixLift 7426756
  have htrace : WordTrace (prefixWord ++ tailWord_7426756) baseStart_7426756 baseEnd_7426756 := by
    simpa [prefixWord, tailWord_7426756, baseEnd_7426756] using wordTrace_append hprefix tailTrace_7426756
  have hstable : (prefixWord ++ tailWord_7426756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7426756).length < 2 ^ (prefixWord ++ tailWord_7426756).sum := by decide
  have hdescent : baseEnd_7426756 < baseStart_7426756 := by decide
  rcases family_descends (prefixWord ++ tailWord_7426756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7426783 : List Nat := [1, 1, 2, 3, 2, 5, 1, 3, 1, 4]
def baseStart_7426783 : Nat := 118140960795 + 7426783 * 2 ^ 59
def prefixEnd_7426783 : Nat := 4983230072969 + 3 ^ 40 * 7426783 * 2
def baseEnd_7426783 : Nat := 1271169798546840470352451

theorem tailTrace_7426783 : CollatzResearch.WordTrace tailWord_7426783 prefixEnd_7426783 1271169798546840470352451 := by
  unfold tailWord_7426783
  simp only [CollatzResearch.WordTrace]
  refine ⟨270877029453041059399541003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180584686302027372933027335 270877029453041059399541003)
  ·
    refine ⟨406315544179561589099311505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270877029453041059399541003 406315544179561589099311505)
    ·
      refine ⟨304736658134671191824483629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 406315544179561589099311505 304736658134671191824483629)
      ·
        refine ⟨114276246800501696934181361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 304736658134671191824483629 114276246800501696934181361)
        ·
          refine ⟨85707185100376272700636021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114276246800501696934181361 85707185100376272700636021)
          ·
            refine ⟨8035048603160275565684627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 85707185100376272700636021 8035048603160275565684627)
            ·
              refine ⟨12052572904740413348526941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8035048603160275565684627 12052572904740413348526941)
              ·
                refine ⟨4519714839277655005697603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12052572904740413348526941 4519714839277655005697603)
                ·
                  refine ⟨6779572258916482508546405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4519714839277655005697603 6779572258916482508546405)
                  ·
                    refine ⟨1271169798546840470352451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6779572258916482508546405 1271169798546840470352451)
                    ·
                      rfl

theorem cell23_7426783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 1, 3, 1, 4].length) (baseStart_7426783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7426783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7426783 prefixEnd_7426783 := by exact prefixLift 7426783
  have htrace : WordTrace (prefixWord ++ tailWord_7426783) baseStart_7426783 baseEnd_7426783 := by
    simpa [prefixWord, tailWord_7426783, baseEnd_7426783] using wordTrace_append hprefix tailTrace_7426783
  have hstable : (prefixWord ++ tailWord_7426783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7426783).length < 2 ^ (prefixWord ++ tailWord_7426783).sum := by decide
  have hdescent : baseEnd_7426783 < baseStart_7426783 := by decide
  rcases family_descends (prefixWord ++ tailWord_7426783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7426852 : List Nat := [2, 3, 1, 3, 14]
def baseStart_7426852 : Nat := 118140960795 + 7426852 * 2 ^ 59
def prefixEnd_7426852 : Nat := 4983230072969 + 3 ^ 40 * 7426852 * 2
def baseEnd_7426852 : Nat := 5231200035398740248415

theorem tailTrace_7426852 : CollatzResearch.WordTrace tailWord_7426852 prefixEnd_7426852 5231200035398740248415 := by
  unfold tailWord_7426852
  simp only [CollatzResearch.WordTrace]
  refine ⟨135439773044895542091901405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180586364059860722789201873 135439773044895542091901405)
  ·
    refine ⟨50789914891835828284463027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135439773044895542091901405 50789914891835828284463027)
    ·
      refine ⟨76184872337753742426694541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50789914891835828284463027 76184872337753742426694541)
      ·
        refine ⟨28569327126657653410010453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76184872337753742426694541 28569327126657653410010453)
        ·
          refine ⟨5231200035398740248415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 28569327126657653410010453 5231200035398740248415)
          ·
            rfl

theorem cell23_7426852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 14].length) (baseStart_7426852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7426852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7426852 prefixEnd_7426852 := by exact prefixLift 7426852
  have htrace : WordTrace (prefixWord ++ tailWord_7426852) baseStart_7426852 baseEnd_7426852 := by
    simpa [prefixWord, tailWord_7426852, baseEnd_7426852] using wordTrace_append hprefix tailTrace_7426852
  have hstable : (prefixWord ++ tailWord_7426852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7426852).length < 2 ^ (prefixWord ++ tailWord_7426852).sum := by decide
  have hdescent : baseEnd_7426852 < baseStart_7426852 := by decide
  rcases family_descends (prefixWord ++ tailWord_7426852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7426869 : List Nat := [1, 3, 3, 1, 3, 1, 3, 8]
def baseStart_7426869 : Nat := 118140960795 + 7426869 * 2 ^ 59
def prefixEnd_7426869 : Nat := 4983230072969 + 3 ^ 40 * 7426869 * 2
def baseEnd_7426869 : Nat := 141242724258400299058591

theorem tailTrace_7426869 : CollatzResearch.WordTrace tailWord_7426869 prefixEnd_7426869 141242724258400299058591 := by
  unfold tailWord_7426869
  simp only [CollatzResearch.WordTrace]
  refine ⟨270880166130729496087171661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180586777420486330724781107 270880166130729496087171661)
  ·
    refine ⟨101580062299023561032689373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 270880166130729496087171661 101580062299023561032689373)
    ·
      refine ⟨38092523362133835387258515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101580062299023561032689373 38092523362133835387258515)
      ·
        refine ⟨57138785043200753080887773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38092523362133835387258515 57138785043200753080887773)
        ·
          refine ⟨21427044391200282405332915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57138785043200753080887773 21427044391200282405332915)
          ·
            refine ⟨32140566586800423607999373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21427044391200282405332915 32140566586800423607999373)
            ·
              refine ⟨12052712470050158852999765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32140566586800423607999373 12052712470050158852999765)
              ·
                refine ⟨141242724258400299058591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12052712470050158852999765 141242724258400299058591)
                ·
                  rfl

theorem cell23_7426869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 3, 8].length) (baseStart_7426869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7426869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7426869 prefixEnd_7426869 := by exact prefixLift 7426869
  have htrace : WordTrace (prefixWord ++ tailWord_7426869) baseStart_7426869 baseEnd_7426869 := by
    simpa [prefixWord, tailWord_7426869, baseEnd_7426869] using wordTrace_append hprefix tailTrace_7426869
  have hstable : (prefixWord ++ tailWord_7426869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7426869).length < 2 ^ (prefixWord ++ tailWord_7426869).sum := by decide
  have hdescent : baseEnd_7426869 < baseStart_7426869 := by decide
  rcases family_descends (prefixWord ++ tailWord_7426869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7426884 : List Nat := [2, 3, 4, 2, 2, 1, 1, 1, 2, 3, 2]
def baseStart_7426884 : Nat := 118140960795 + 7426884 * 2 ^ 59
def prefixEnd_7426884 : Nat := 4983230072969 + 3 ^ 40 * 7426884 * 2
def baseEnd_7426884 : Nat := 3813561257186625515894389

theorem tailTrace_7426884 : CollatzResearch.WordTrace tailWord_7426884 prefixEnd_7426884 3813561257186625515894389 := by
  unfold tailWord_7426884
  simp only [CollatzResearch.WordTrace]
  refine ⟨135440356612837576824483853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180587142150450102432645137 135440356612837576824483853)
  ·
    refine ⟨50790133729814091309181445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135440356612837576824483853 50790133729814091309181445)
    ·
      refine ⟨9523150074340142120471521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50790133729814091309181445 9523150074340142120471521)
      ·
        refine ⟨7142362555755106590353641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9523150074340142120471521 7142362555755106590353641)
        ·
          refine ⟨5356771916816329942765231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7142362555755106590353641 5356771916816329942765231)
          ·
            refine ⟨8035157875224494914147847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5356771916816329942765231 8035157875224494914147847)
            ·
              refine ⟨12052736812836742371221771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8035157875224494914147847 12052736812836742371221771)
              ·
                refine ⟨18079105219255113556832657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12052736812836742371221771 18079105219255113556832657)
                ·
                  refine ⟨13559328914441335167624493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18079105219255113556832657 13559328914441335167624493)
                  ·
                    refine ⟨5084748342915500687859185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13559328914441335167624493 5084748342915500687859185)
                    ·
                      refine ⟨3813561257186625515894389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5084748342915500687859185 3813561257186625515894389)
                      ·
                        rfl

theorem cell23_7426884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_7426884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7426884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7426884 prefixEnd_7426884 := by exact prefixLift 7426884
  have htrace : WordTrace (prefixWord ++ tailWord_7426884) baseStart_7426884 baseEnd_7426884 := by
    simpa [prefixWord, tailWord_7426884, baseEnd_7426884] using wordTrace_append hprefix tailTrace_7426884
  have hstable : (prefixWord ++ tailWord_7426884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7426884).length < 2 ^ (prefixWord ++ tailWord_7426884).sum := by decide
  have hdescent : baseEnd_7426884 < baseStart_7426884 := by decide
  rcases family_descends (prefixWord ++ tailWord_7426884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7426897 : List Nat := [1, 2, 2, 1, 6, 1, 2, 3, 1, 2, 2]
def baseStart_7426897 : Nat := 118140960795 + 7426897 * 2 ^ 59
def prefixEnd_7426897 : Nat := 4983230072969 + 3 ^ 40 * 7426897 * 2
def baseEnd_7426897 : Nat := 3813567932435133965031829

theorem tailTrace_7426897 : CollatzResearch.WordTrace tailWord_7426897 prefixEnd_7426897 3813567932435133965031829 := by
  unfold tailWord_7426897
  simp only [CollatzResearch.WordTrace]
  refine ⟨270881187374628056869190945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180587458249752037912793963 270881187374628056869190945)
  ·
    refine ⟨203160890530971042651893209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270881187374628056869190945 203160890530971042651893209)
    ·
      refine ⟨152370667898228281988919907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203160890530971042651893209 152370667898228281988919907)
      ·
        refine ⟨228556001847342422983379861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152370667898228281988919907 228556001847342422983379861)
        ·
          refine ⟨10713562586594176077345931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 228556001847342422983379861 10713562586594176077345931)
          ·
            refine ⟨16070343879891264116018897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10713562586594176077345931 16070343879891264116018897)
            ·
              refine ⟨12052757909918448087014173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16070343879891264116018897 12052757909918448087014173)
              ·
                refine ⟨4519784216219418032630315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12052757909918448087014173 4519784216219418032630315)
                ·
                  refine ⟨6779676324329127048945473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4519784216219418032630315 6779676324329127048945473)
                  ·
                    refine ⟨5084757243246845286709105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6779676324329127048945473 5084757243246845286709105)
                    ·
                      refine ⟨3813567932435133965031829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5084757243246845286709105 3813567932435133965031829)
                      ·
                        rfl

theorem cell23_7426897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 2, 3, 1, 2, 2].length) (baseStart_7426897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7426897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7426897 prefixEnd_7426897 := by exact prefixLift 7426897
  have htrace : WordTrace (prefixWord ++ tailWord_7426897) baseStart_7426897 baseEnd_7426897 := by
    simpa [prefixWord, tailWord_7426897, baseEnd_7426897] using wordTrace_append hprefix tailTrace_7426897
  have hstable : (prefixWord ++ tailWord_7426897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7426897).length < 2 ^ (prefixWord ++ tailWord_7426897).sum := by decide
  have hdescent : baseEnd_7426897 < baseStart_7426897 := by decide
  rcases family_descends (prefixWord ++ tailWord_7426897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7426929 : List Nat := [1, 2, 2, 2, 1, 4, 2, 1, 2, 6]
def baseStart_7426929 : Nat := 118140960795 + 7426929 * 2 ^ 59
def prefixEnd_7426929 : Nat := 4983230072969 + 3 ^ 40 * 7426929 * 2
def baseEnd_7426929 : Nat := 1271194787938692613277227

theorem tailTrace_7426929 : CollatzResearch.WordTrace tailWord_7426929 prefixEnd_7426929 1271194787938692613277227 := by
  unfold tailWord_7426929
  simp only [CollatzResearch.WordTrace]
  refine ⟨270882354510512126334355841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180588236340341417556237227 270882354510512126334355841)
  ·
    refine ⟨203161765882884094750766881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270882354510512126334355841 203161765882884094750766881)
    ·
      refine ⟨152371324412163071063075161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203161765882884094750766881 152371324412163071063075161)
      ·
        refine ⟨114278493309122303297306371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152371324412163071063075161 114278493309122303297306371)
        ·
          refine ⟨171417739963683454945959557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114278493309122303297306371 171417739963683454945959557)
          ·
            refine ⟨32140826243190647802367417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 171417739963683454945959557 32140826243190647802367417)
            ·
              refine ⟨24105619682392985851775563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32140826243190647802367417 24105619682392985851775563)
              ·
                refine ⟨36158429523589478777663345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24105619682392985851775563 36158429523589478777663345)
                ·
                  refine ⟨27118822142692109083247509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36158429523589478777663345 27118822142692109083247509)
                  ·
                    refine ⟨1271194787938692613277227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27118822142692109083247509 1271194787938692613277227)
                    ·
                      rfl

theorem cell23_7426929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 1, 2, 6].length) (baseStart_7426929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7426929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7426929 prefixEnd_7426929 := by exact prefixLift 7426929
  have htrace : WordTrace (prefixWord ++ tailWord_7426929) baseStart_7426929 baseEnd_7426929 := by
    simpa [prefixWord, tailWord_7426929, baseEnd_7426929] using wordTrace_append hprefix tailTrace_7426929
  have hstable : (prefixWord ++ tailWord_7426929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7426929).length < 2 ^ (prefixWord ++ tailWord_7426929).sum := by decide
  have hdescent : baseEnd_7426929 < baseStart_7426929 := by decide
  rcases family_descends (prefixWord ++ tailWord_7426929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7426936 : List Nat := [2, 1, 2, 1, 1, 1, 1, 7, 1, 4, 2]
def baseStart_7426936 : Nat := 118140960795 + 7426936 * 2 ^ 59
def prefixEnd_7426936 : Nat := 4983230072969 + 3 ^ 40 * 7426936 * 2
def baseEnd_7426936 : Nat := 3813587958180659312444149

theorem tailTrace_7426936 : CollatzResearch.WordTrace tailWord_7426936 prefixEnd_7426936 3813587958180659312444149 := by
  unfold tailWord_7426936
  simp only [CollatzResearch.WordTrace]
  refine ⟨135441304910743383264930331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180588406547657844353240441 135441304910743383264930331)
  ·
    refine ⟨203161957366115074897395497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135441304910743383264930331 203161957366115074897395497)
    ·
      refine ⟨152371468024586306173046623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203161957366115074897395497 152371468024586306173046623)
      ·
        refine ⟨228557202036879459259569935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152371468024586306173046623 228557202036879459259569935)
        ·
          refine ⟨342835803055319188889354903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228557202036879459259569935 342835803055319188889354903)
          ·
            refine ⟨514253704582978783334032355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 342835803055319188889354903 514253704582978783334032355)
            ·
              refine ⟨771380556874468175001048533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 514253704582978783334032355 771380556874468175001048533)
              ·
                refine ⟨18079231801745347851587075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 771380556874468175001048533 18079231801745347851587075)
                ·
                  refine ⟨27118847702618021777380613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18079231801745347851587075 27118847702618021777380613)
                  ·
                    refine ⟨5084783944240879083258865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27118847702618021777380613 5084783944240879083258865)
                    ·
                      refine ⟨3813587958180659312444149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5084783944240879083258865 3813587958180659312444149)
                      ·
                        rfl

theorem cell23_7426936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 7, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 7, 1, 4, 2].length) (baseStart_7426936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7426936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7426936 prefixEnd_7426936 := by exact prefixLift 7426936
  have htrace : WordTrace (prefixWord ++ tailWord_7426936) baseStart_7426936 baseEnd_7426936 := by
    simpa [prefixWord, tailWord_7426936, baseEnd_7426936] using wordTrace_append hprefix tailTrace_7426936
  have hstable : (prefixWord ++ tailWord_7426936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7426936).length < 2 ^ (prefixWord ++ tailWord_7426936).sum := by decide
  have hdescent : baseEnd_7426936 < baseStart_7426936 := by decide
  rcases family_descends (prefixWord ++ tailWord_7426936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7426939 : List Nat := [1, 1, 1, 1, 1, 5, 2, 2, 2, 4, 3]
def baseStart_7426939 : Nat := 118140960795 + 7426939 * 2 ^ 59
def prefixEnd_7426939 : Nat := 4983230072969 + 3 ^ 40 * 7426939 * 2
def baseEnd_7426939 : Nat := 3813589498622622800706635

theorem tailTrace_7426939 : CollatzResearch.WordTrace tailWord_7426939 prefixEnd_7426939 3813589498622622800706635 := by
  unfold tailWord_7426939
  simp only [CollatzResearch.WordTrace]
  refine ⟨270882719240475898042219871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180588479493650598694813247 270882719240475898042219871)
  ·
    refine ⟨406324078860713847063329807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270882719240475898042219871 406324078860713847063329807)
    ·
      refine ⟨609486118291070770594994711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 406324078860713847063329807 609486118291070770594994711)
      ·
        refine ⟨914229177436606155892492067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 609486118291070770594994711 914229177436606155892492067)
        ·
          refine ⟨1371343766154909233838738101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 914229177436606155892492067 1371343766154909233838738101)
          ·
            refine ⟨128563478077022740672381697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1371343766154909233838738101 128563478077022740672381697)
            ·
              refine ⟨96422608557767055504286273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128563478077022740672381697 96422608557767055504286273)
              ·
                refine ⟨72316956418325291628214705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96422608557767055504286273 72316956418325291628214705)
                ·
                  refine ⟨54237717313743968721161029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72316956418325291628214705 54237717313743968721161029)
                  ·
                    refine ⟨10169571996326994135217693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54237717313743968721161029 10169571996326994135217693)
                    ·
                      refine ⟨3813589498622622800706635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10169571996326994135217693 3813589498622622800706635)
                      ·
                        rfl

theorem cell23_7426939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 2, 2, 4, 3].length) (baseStart_7426939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7426939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7426939 prefixEnd_7426939 := by exact prefixLift 7426939
  have htrace : WordTrace (prefixWord ++ tailWord_7426939) baseStart_7426939 baseEnd_7426939 := by
    simpa [prefixWord, tailWord_7426939, baseEnd_7426939] using wordTrace_append hprefix tailTrace_7426939
  have hstable : (prefixWord ++ tailWord_7426939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7426939).length < 2 ^ (prefixWord ++ tailWord_7426939).sum := by decide
  have hdescent : baseEnd_7426939 < baseStart_7426939 := by decide
  rcases family_descends (prefixWord ++ tailWord_7426939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7426953 : List Nat := [1, 2, 1, 1, 5, 2, 1, 2, 4, 2, 2]
def baseStart_7426953 : Nat := 118140960795 + 7426953 * 2 ^ 59
def prefixEnd_7426953 : Nat := 4983230072969 + 3 ^ 40 * 7426953 * 2
def baseEnd_7426953 : Nat := 3813596687351785745931571

theorem tailTrace_7426953 : CollatzResearch.WordTrace tailWord_7426953 prefixEnd_7426953 3813596687351785745931571 := by
  unfold tailWord_7426953
  simp only [CollatzResearch.WordTrace]
  refine ⟨270883229862425178433229513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180588819908283452288819675 270883229862425178433229513)
  ·
    refine ⟨203162422396818883824922135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270883229862425178433229513 203162422396818883824922135)
    ·
      refine ⟨304743633595228325737383203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203162422396818883824922135 304743633595228325737383203)
      ·
        refine ⟨457115450392842488606074805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304743633595228325737383203 457115450392842488606074805)
        ·
          refine ⟨42854573474328983306819513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 457115450392842488606074805 42854573474328983306819513)
          ·
            refine ⟨32140930105746737480114635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42854573474328983306819513 32140930105746737480114635)
            ·
              refine ⟨48211395158620106220171953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32140930105746737480114635 48211395158620106220171953)
              ·
                refine ⟨36158546368965079665128965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48211395158620106220171953 36158546368965079665128965)
                ·
                  refine ⟨6779727444180952437211681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36158546368965079665128965 6779727444180952437211681)
                  ·
                    refine ⟨5084795583135714327908761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6779727444180952437211681 5084795583135714327908761)
                    ·
                      refine ⟨3813596687351785745931571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5084795583135714327908761 3813596687351785745931571)
                      ·
                        rfl

theorem cell23_7426953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 2, 4, 2, 2].length) (baseStart_7426953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7426953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7426953 prefixEnd_7426953 := by exact prefixLift 7426953
  have htrace : WordTrace (prefixWord ++ tailWord_7426953) baseStart_7426953 baseEnd_7426953 := by
    simpa [prefixWord, tailWord_7426953, baseEnd_7426953] using wordTrace_append hprefix tailTrace_7426953
  have hstable : (prefixWord ++ tailWord_7426953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7426953).length < 2 ^ (prefixWord ++ tailWord_7426953).sum := by decide
  have hdescent : baseEnd_7426953 < baseStart_7426953 := by decide
  rcases family_descends (prefixWord ++ tailWord_7426953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7426976 : List Nat := [2, 1, 1, 4, 1, 1, 2, 6, 5]
def baseStart_7426976 : Nat := 118140960795 + 7426976 * 2 ^ 59
def prefixEnd_7426976 : Nat := 4983230072969 + 3 ^ 40 * 7426976 * 2
def baseEnd_7426976 : Nat := 423734277489648795104885

theorem tailTrace_7426976 : CollatzResearch.WordTrace tailWord_7426976 prefixEnd_7426976 423734277489648795104885 := by
  unfold tailWord_7426976
  simp only [CollatzResearch.WordTrace]
  refine ⟨135442034370670926680658391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180589379160894568907544521 135442034370670926680658391)
  ·
    refine ⟨203163051556006390020987587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135442034370670926680658391 203163051556006390020987587)
    ·
      refine ⟨304744577334009585031481381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203163051556006390020987587 304744577334009585031481381)
      ·
        refine ⟨57139608250126797193402759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 304744577334009585031481381 57139608250126797193402759)
        ·
          refine ⟨85709412375190195790104139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57139608250126797193402759 85709412375190195790104139)
          ·
            refine ⟨128564118562785293685156209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85709412375190195790104139 128564118562785293685156209)
            ·
              refine ⟨96423088922088970263867157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128564118562785293685156209 96423088922088970263867157)
              ·
                refine ⟨4519832293222920481118773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 96423088922088970263867157 4519832293222920481118773)
                ·
                  refine ⟨423734277489648795104885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4519832293222920481118773 423734277489648795104885)
                  ·
                    rfl

theorem cell23_7426976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 6, 5].length) (baseStart_7426976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7426976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7426976 prefixEnd_7426976 := by exact prefixLift 7426976
  have htrace : WordTrace (prefixWord ++ tailWord_7426976) baseStart_7426976 baseEnd_7426976 := by
    simpa [prefixWord, tailWord_7426976, baseEnd_7426976] using wordTrace_append hprefix tailTrace_7426976
  have hstable : (prefixWord ++ tailWord_7426976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7426976).length < 2 ^ (prefixWord ++ tailWord_7426976).sum := by decide
  have hdescent : baseEnd_7426976 < baseStart_7426976 := by decide
  rcases family_descends (prefixWord ++ tailWord_7426976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7427030 : List Nat := [5, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2]
def baseStart_7427030 : Nat := 118140960795 + 7427030 * 2 ^ 59
def prefixEnd_7427030 : Nat := 4983230072969 + 3 ^ 40 * 7427030 * 2
def baseEnd_7427030 : Nat := 3813636225362181944668717

theorem tailTrace_7427030 : CollatzResearch.WordTrace tailWord_7427030 prefixEnd_7427030 3813636225362181944668717 := by
  unfold tailWord_7427030
  simp only [CollatzResearch.WordTrace]
  refine ⟨16930377392696638786486409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 180590692188764147055855029 16930377392696638786486409)
  ·
    refine ⟨12697783044522479089864807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16930377392696638786486409 12697783044522479089864807)
    ·
      refine ⟨19046674566783718634797211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12697783044522479089864807 19046674566783718634797211)
      ·
        refine ⟨28570011850175577952195817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19046674566783718634797211 28570011850175577952195817)
        ·
          refine ⟨21427508887631683464146863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28570011850175577952195817 21427508887631683464146863)
          ·
            refine ⟨32141263331447525196220295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21427508887631683464146863 32141263331447525196220295)
            ·
              refine ⟨48211894997171287794330443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32141263331447525196220295 48211894997171287794330443)
              ·
                refine ⟨72317842495756931691495665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48211894997171287794330443 72317842495756931691495665)
                ·
                  refine ⟨54238381871817698768621749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72317842495756931691495665 54238381871817698768621749)
                  ·
                    refine ⟨5084848300482909259558289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54238381871817698768621749 5084848300482909259558289)
                    ·
                      refine ⟨3813636225362181944668717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5084848300482909259558289 3813636225362181944668717)
                      ·
                        rfl

theorem cell23_7427030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2].length) (baseStart_7427030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7427030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7427030 prefixEnd_7427030 := by exact prefixLift 7427030
  have htrace : WordTrace (prefixWord ++ tailWord_7427030) baseStart_7427030 baseEnd_7427030 := by
    simpa [prefixWord, tailWord_7427030, baseEnd_7427030] using wordTrace_append hprefix tailTrace_7427030
  have hstable : (prefixWord ++ tailWord_7427030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7427030).length < 2 ^ (prefixWord ++ tailWord_7427030).sum := by decide
  have hdescent : baseEnd_7427030 < baseStart_7427030 := by decide
  rcases family_descends (prefixWord ++ tailWord_7427030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7427043 : List Nat := [1, 1, 1, 6, 1, 1, 3, 1, 2, 4, 2]
def baseStart_7427043 : Nat := 118140960795 + 7427043 * 2 ^ 59
def prefixEnd_7427043 : Nat := 4983230072969 + 3 ^ 40 * 7427043 * 2
def baseEnd_7427043 : Nat := 3813642900610690393806157

theorem tailTrace_7427043 : CollatzResearch.WordTrace tailWord_7427043 prefixEnd_7427043 3813642900610690393806157 := by
  unfold tailWord_7427043
  simp only [CollatzResearch.WordTrace]
  refine ⟨270886512432099123804005783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180591008288066082536003855 270886512432099123804005783)
  ·
    refine ⟨406329768648148685706008675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270886512432099123804005783 406329768648148685706008675)
    ·
      refine ⟨609494652972223028559013013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 406329768648148685706008675 609494652972223028559013013)
      ·
        refine ⟨28570061858072954463703735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 609494652972223028559013013 28570061858072954463703735)
        ·
          refine ⟨42855092787109431695555603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28570061858072954463703735 42855092787109431695555603)
          ·
            refine ⟨64282639180664147543333405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42855092787109431695555603 64282639180664147543333405)
            ·
              refine ⟨24105989692749055328750027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64282639180664147543333405 24105989692749055328750027)
              ·
                refine ⟨36158984539123582993125041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24105989692749055328750027 36158984539123582993125041)
                ·
                  refine ⟨27119238404342687244843781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36158984539123582993125041 27119238404342687244843781)
                  ·
                    refine ⟨5084857200814253858408209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 27119238404342687244843781 5084857200814253858408209)
                    ·
                      refine ⟨3813642900610690393806157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5084857200814253858408209 3813642900610690393806157)
                      ·
                        rfl

theorem cell23_7427043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 1, 2, 4, 2].length) (baseStart_7427043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7427043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7427043 prefixEnd_7427043 := by exact prefixLift 7427043
  have htrace : WordTrace (prefixWord ++ tailWord_7427043) baseStart_7427043 baseEnd_7427043 := by
    simpa [prefixWord, tailWord_7427043, baseEnd_7427043] using wordTrace_append hprefix tailTrace_7427043
  have hstable : (prefixWord ++ tailWord_7427043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7427043).length < 2 ^ (prefixWord ++ tailWord_7427043).sum := by decide
  have hdescent : baseEnd_7427043 < baseStart_7427043 := by decide
  rcases family_descends (prefixWord ++ tailWord_7427043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7427083 : List Nat := [1, 1, 1, 1, 6, 4, 1, 2, 6]
def baseStart_7427083 : Nat := 118140960795 + 7427083 * 2 ^ 59
def prefixEnd_7427083 : Nat := 4983230072969 + 3 ^ 40 * 7427083 * 2
def baseEnd_7427083 : Nat := 423740382204096693033997

theorem tailTrace_7427083 : CollatzResearch.WordTrace tailWord_7427083 prefixEnd_7427083 423740382204096693033997 := by
  unfold tailWord_7427083
  simp only [CollatzResearch.WordTrace]
  refine ⟨270887971351954210635461903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180591980901302807090307935 270887971351954210635461903)
  ·
    refine ⟨406331957027931315953192855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270887971351954210635461903 406331957027931315953192855)
    ·
      refine ⟨609497935541896973929789283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 406331957027931315953192855 609497935541896973929789283)
      ·
        refine ⟨914246903312845460894683925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 609497935541896973929789283 914246903312845460894683925)
        ·
          refine ⟨42855323592789630979438309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 914246903312845460894683925 42855323592789630979438309)
          ·
            refine ⟨8035373173648055808644683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42855323592789630979438309 8035373173648055808644683)
            ·
              refine ⟨12053059760472083712967025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8035373173648055808644683 12053059760472083712967025)
              ·
                refine ⟨9039794820354062784725269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12053059760472083712967025 9039794820354062784725269)
                ·
                  refine ⟨423740382204096693033997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9039794820354062784725269 423740382204096693033997)
                  ·
                    rfl

theorem cell23_7427083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 1, 2, 6].length) (baseStart_7427083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7427083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7427083 prefixEnd_7427083 := by exact prefixLift 7427083
  have htrace : WordTrace (prefixWord ++ tailWord_7427083) baseStart_7427083 baseEnd_7427083 := by
    simpa [prefixWord, tailWord_7427083, baseEnd_7427083] using wordTrace_append hprefix tailTrace_7427083
  have hstable : (prefixWord ++ tailWord_7427083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7427083).length < 2 ^ (prefixWord ++ tailWord_7427083).sum := by decide
  have hdescent : baseEnd_7427083 < baseStart_7427083 := by decide
  rcases family_descends (prefixWord ++ tailWord_7427083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7427086 : List Nat := [4, 1, 1, 2, 2, 2, 1, 1, 1, 2, 6]
def baseStart_7427086 : Nat := 118140960795 + 7427086 * 2 ^ 59
def prefixEnd_7427086 : Nat := 4983230072969 + 3 ^ 40 * 7427086 * 2
def baseEnd_7427086 : Nat := 3813664980278833725568459

theorem tailTrace_7427086 : CollatzResearch.WordTrace tailWord_7427086 prefixEnd_7427086 3813664980278833725568459 := by
  unfold tailWord_7427086
  simp only [CollatzResearch.WordTrace]
  refine ⟨33861010096367917768477639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180592053847295561431880741 33861010096367917768477639)
  ·
    refine ⟨50791515144551876652716459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33861010096367917768477639 50791515144551876652716459)
    ·
      refine ⟨76187272716827814979074689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50791515144551876652716459 76187272716827814979074689)
      ·
        refine ⟨57140454537620861234306017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76187272716827814979074689 57140454537620861234306017)
        ·
          refine ⟨42855340903215645925729513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57140454537620861234306017 42855340903215645925729513)
          ·
            refine ⟨32141505677411734444297135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42855340903215645925729513 32141505677411734444297135)
            ·
              refine ⟨48212258516117601666445703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32141505677411734444297135 48212258516117601666445703)
              ·
                refine ⟨72318387774176402499668555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48212258516117601666445703 72318387774176402499668555)
                ·
                  refine ⟨108477581661264603749502833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72318387774176402499668555 108477581661264603749502833)
                  ·
                    refine ⟨81358186245948452812127125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 108477581661264603749502833 81358186245948452812127125)
                    ·
                      refine ⟨3813664980278833725568459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81358186245948452812127125 3813664980278833725568459)
                      ·
                        rfl

theorem cell23_7427086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 1, 1, 2, 6].length) (baseStart_7427086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7427086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7427086 prefixEnd_7427086 := by exact prefixLift 7427086
  have htrace : WordTrace (prefixWord ++ tailWord_7427086) baseStart_7427086 baseEnd_7427086 := by
    simpa [prefixWord, tailWord_7427086, baseEnd_7427086] using wordTrace_append hprefix tailTrace_7427086
  have hstable : (prefixWord ++ tailWord_7427086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7427086).length < 2 ^ (prefixWord ++ tailWord_7427086).sum := by decide
  have hdescent : baseEnd_7427086 < baseStart_7427086 := by decide
  rcases family_descends (prefixWord ++ tailWord_7427086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7427100 : List Nat := [2, 2, 3, 1, 4, 1, 3, 1, 6]
def baseStart_7427100 : Nat := 118140960795 + 7427100 * 2 ^ 59
def prefixEnd_7427100 : Nat := 4983230072969 + 3 ^ 40 * 7427100 * 2
def baseEnd_7427100 : Nat := 423741352111999630088155

theorem tailTrace_7427100 : CollatzResearch.WordTrace tailWord_7427100 prefixEnd_7427100 423741352111999630088155 := by
  unfold tailWord_7427100
  simp only [CollatzResearch.WordTrace]
  refine ⟨135444295696446311269415377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180592394261928415025887169 135444295696446311269415377)
  ·
    refine ⟨101583221772334733452061533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135444295696446311269415377 101583221772334733452061533)
    ·
      refine ⟨38093708164625525044523075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101583221772334733452061533 38093708164625525044523075)
      ·
        refine ⟨57140562246938287566784613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38093708164625525044523075 57140562246938287566784613)
        ·
          refine ⟨10713855421300928918772115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57140562246938287566784613 10713855421300928918772115)
          ·
            refine ⟨16070783131951393378158173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10713855421300928918772115 16070783131951393378158173)
            ·
              refine ⟨6026543674481772516809315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16070783131951393378158173 6026543674481772516809315)
              ·
                refine ⟨9039815511722658775213973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6026543674481772516809315 9039815511722658775213973)
                ·
                  refine ⟨423741352111999630088155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9039815511722658775213973 423741352111999630088155)
                  ·
                    rfl

theorem cell23_7427100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 3, 1, 6].length) (baseStart_7427100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7427100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7427100 prefixEnd_7427100 := by exact prefixLift 7427100
  have htrace : WordTrace (prefixWord ++ tailWord_7427100) baseStart_7427100 baseEnd_7427100 := by
    simpa [prefixWord, tailWord_7427100, baseEnd_7427100] using wordTrace_append hprefix tailTrace_7427100
  have hstable : (prefixWord ++ tailWord_7427100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7427100).length < 2 ^ (prefixWord ++ tailWord_7427100).sum := by decide
  have hdescent : baseEnd_7427100 < baseStart_7427100 := by decide
  rcases family_descends (prefixWord ++ tailWord_7427100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7427103 : List Nat := [1, 1, 2, 4, 1, 3, 1, 2, 1, 5, 2]
def baseStart_7427103 : Nat := 118140960795 + 7427103 * 2 ^ 59
def prefixEnd_7427103 : Nat := 4983230072969 + 3 ^ 40 * 7427103 * 2
def baseEnd_7427103 : Nat := 3813673709449960159055881

theorem tailTrace_7427103 : CollatzResearch.WordTrace tailWord_7427103 prefixEnd_7427103 3813673709449960159055881 := by
  unfold tailWord_7427103
  simp only [CollatzResearch.WordTrace]
  refine ⟨270888700811881754051189963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180592467207921169367459975 270888700811881754051189963)
  ·
    refine ⟨406333051217822631076784945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270888700811881754051189963 406333051217822631076784945)
    ·
      refine ⟨304749788413366973307588709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 406333051217822631076784945 304749788413366973307588709)
      ·
        refine ⟨57140585327506307495172883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 304749788413366973307588709 57140585327506307495172883)
        ·
          refine ⟨85710877991259461242759325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57140585327506307495172883 85710877991259461242759325)
          ·
            refine ⟨32141579246722297966034747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85710877991259461242759325 32141579246722297966034747)
            ·
              refine ⟨48212368870083446949052121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32141579246722297966034747 48212368870083446949052121)
              ·
                refine ⟨36159276652562585211789091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48212368870083446949052121 36159276652562585211789091)
                ·
                  refine ⟨54238914978843877817683637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36159276652562585211789091 54238914978843877817683637)
                  ·
                    refine ⟨5084898279266613545407841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 54238914978843877817683637 5084898279266613545407841)
                    ·
                      refine ⟨3813673709449960159055881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5084898279266613545407841 3813673709449960159055881)
                      ·
                        rfl

theorem cell23_7427103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 2, 1, 5, 2].length) (baseStart_7427103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7427103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7427103 prefixEnd_7427103 := by exact prefixLift 7427103
  have htrace : WordTrace (prefixWord ++ tailWord_7427103) baseStart_7427103 baseEnd_7427103 := by
    simpa [prefixWord, tailWord_7427103, baseEnd_7427103] using wordTrace_append hprefix tailTrace_7427103
  have hstable : (prefixWord ++ tailWord_7427103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7427103).length < 2 ^ (prefixWord ++ tailWord_7427103).sum := by decide
  have hdescent : baseEnd_7427103 < baseStart_7427103 := by decide
  rcases family_descends (prefixWord ++ tailWord_7427103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7427137 : List Nat := [1, 2, 5, 1, 3, 1, 1, 2, 2, 3, 2]
def baseStart_7427137 : Nat := 118140960795 + 7427137 * 2 ^ 59
def prefixEnd_7427137 : Nat := 4983230072969 + 3 ^ 40 * 7427137 * 2
def baseEnd_7427137 : Nat := 3813691167792213026030725

theorem tailTrace_7427137 : CollatzResearch.WordTrace tailWord_7427137 prefixEnd_7427137 3813691167792213026030725 := by
  unfold tailWord_7427137
  simp only [CollatzResearch.WordTrace]
  refine ⟨270889940893758577857927665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180593293929172385238618443 270889940893758577857927665)
  ·
    refine ⟨203167455670318933393445749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270889940893758577857927665 203167455670318933393445749)
    ·
      refine ⟨19046948969092400005635539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 203167455670318933393445749 19046948969092400005635539)
      ·
        refine ⟨28570423453638600008453309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19046948969092400005635539 28570423453638600008453309)
        ·
          refine ⟨10713908795114475003169991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28570423453638600008453309 10713908795114475003169991)
          ·
            refine ⟨16070863192671712504754987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10713908795114475003169991 16070863192671712504754987)
            ·
              refine ⟨24106294789007568757132481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16070863192671712504754987 24106294789007568757132481)
              ·
                refine ⟨18079721091755676567849361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24106294789007568757132481 18079721091755676567849361)
                ·
                  refine ⟨13559790818816757425887021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18079721091755676567849361 13559790818816757425887021)
                  ·
                    refine ⟨5084921557056284034707633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13559790818816757425887021 5084921557056284034707633)
                    ·
                      refine ⟨3813691167792213026030725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5084921557056284034707633 3813691167792213026030725)
                      ·
                        rfl

theorem cell23_7427137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 2, 2, 3, 2].length) (baseStart_7427137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7427137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7427137 prefixEnd_7427137 := by exact prefixLift 7427137
  have htrace : WordTrace (prefixWord ++ tailWord_7427137) baseStart_7427137 baseEnd_7427137 := by
    simpa [prefixWord, tailWord_7427137, baseEnd_7427137] using wordTrace_append hprefix tailTrace_7427137
  have hstable : (prefixWord ++ tailWord_7427137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7427137).length < 2 ^ (prefixWord ++ tailWord_7427137).sum := by decide
  have hdescent : baseEnd_7427137 < baseStart_7427137 := by decide
  rcases family_descends (prefixWord ++ tailWord_7427137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7427143 : List Nat := [1, 1, 4, 1, 3, 2, 2, 1, 4, 4]
def baseStart_7427143 : Nat := 118140960795 + 7427143 * 2 ^ 59
def prefixEnd_7427143 : Nat := 4983230072969 + 3 ^ 40 * 7427143 * 2
def baseEnd_7427143 : Nat := 1271231416225380000851899

theorem tailTrace_7427143 : CollatzResearch.WordTrace tailWord_7427143 prefixEnd_7427143 1271231416225380000851899 := by
  unfold tailWord_7427143
  simp only [CollatzResearch.WordTrace]
  refine ⟨270890159731736840882646083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180593439821157893921764055 270890159731736840882646083)
  ·
    refine ⟨406335239597605261323969125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270890159731736840882646083 406335239597605261323969125)
    ·
      refine ⟨76187857424550986498244211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 406335239597605261323969125 76187857424550986498244211)
      ·
        refine ⟨114281786136826479747366317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76187857424550986498244211 114281786136826479747366317)
        ·
          refine ⟨42855669801309929905262369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114281786136826479747366317 42855669801309929905262369)
          ·
            refine ⟨32141752350982447428946777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42855669801309929905262369 32141752350982447428946777)
            ·
              refine ⟨24106314263236835571710083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32141752350982447428946777 24106314263236835571710083)
              ·
                refine ⟨36159471394855253357565125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24106314263236835571710083 36159471394855253357565125)
                ·
                  refine ⟨6779900886535360004543461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36159471394855253357565125 6779900886535360004543461)
                  ·
                    refine ⟨1271231416225380000851899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6779900886535360004543461 1271231416225380000851899)
                    ·
                      rfl

theorem cell23_7427143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 1, 4, 4].length) (baseStart_7427143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7427143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7427143 prefixEnd_7427143 := by exact prefixLift 7427143
  have htrace : WordTrace (prefixWord ++ tailWord_7427143) baseStart_7427143 baseEnd_7427143 := by
    simpa [prefixWord, tailWord_7427143, baseEnd_7427143] using wordTrace_append hprefix tailTrace_7427143
  have hstable : (prefixWord ++ tailWord_7427143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7427143).length < 2 ^ (prefixWord ++ tailWord_7427143).sum := by decide
  have hdescent : baseEnd_7427143 < baseStart_7427143 := by decide
  rcases family_descends (prefixWord ++ tailWord_7427143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7427146 : List Nat := [3, 1, 2, 1, 1, 2, 3, 2, 1, 1, 6]
def baseStart_7427146 : Nat := 118140960795 + 7427146 * 2 ^ 59
def prefixEnd_7427146 : Nat := 4983230072969 + 3 ^ 40 * 7427146 * 2
def baseEnd_7427146 : Nat := 3813695789118103490818183

theorem tailTrace_7427146 : CollatzResearch.WordTrace tailWord_7427146 prefixEnd_7427146 3813695789118103490818183 := by
  unfold tailWord_7427146
  simp only [CollatzResearch.WordTrace]
  refine ⟨67722567287681493098751323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180593512767150648263336861 67722567287681493098751323)
  ·
    refine ⟨101583850931522239648126985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67722567287681493098751323 101583850931522239648126985)
    ·
      refine ⟨76187888198641679736095239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101583850931522239648126985 76187888198641679736095239)
      ·
        refine ⟨114281832297962519604142859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76187888198641679736095239 114281832297962519604142859)
        ·
          refine ⟨171422748446943779406214289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114281832297962519604142859 171422748446943779406214289)
          ·
            refine ⟨128567061335207834554660717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171422748446943779406214289 128567061335207834554660717)
            ·
              refine ⟨48212648000702937957997769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128567061335207834554660717 48212648000702937957997769)
              ·
                refine ⟨36159486000527203468498327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48212648000702937957997769 36159486000527203468498327)
                ·
                  refine ⟨54239229000790805202747491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36159486000527203468498327 54239229000790805202747491)
                  ·
                    refine ⟨81358843501186207804121237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 54239229000790805202747491 81358843501186207804121237)
                    ·
                      refine ⟨3813695789118103490818183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 81358843501186207804121237 3813695789118103490818183)
                      ·
                        rfl

theorem cell23_7427146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 2, 1, 1, 6].length) (baseStart_7427146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7427146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7427146 prefixEnd_7427146 := by exact prefixLift 7427146
  have htrace : WordTrace (prefixWord ++ tailWord_7427146) baseStart_7427146 baseEnd_7427146 := by
    simpa [prefixWord, tailWord_7427146, baseEnd_7427146] using wordTrace_append hprefix tailTrace_7427146
  have hstable : (prefixWord ++ tailWord_7427146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7427146).length < 2 ^ (prefixWord ++ tailWord_7427146).sum := by decide
  have hdescent : baseEnd_7427146 < baseStart_7427146 := by decide
  rcases family_descends (prefixWord ++ tailWord_7427146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7427156 : List Nat := [2, 4, 1, 1, 1, 1, 3, 10]
def baseStart_7427156 : Nat := 118140960795 + 7427156 * 2 ^ 59
def prefixEnd_7427156 : Nat := 4983230072969 + 3 ^ 40 * 7427156 * 2
def baseEnd_7427156 : Nat := 141248182367579572284931

theorem tailTrace_7427156 : CollatzResearch.WordTrace tailWord_7427156 prefixEnd_7427156 141248182367579572284931 := by
  unfold tailWord_7427156
  simp only [CollatzResearch.WordTrace]
  refine ⟨135445316940344872051434661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180593755920459829401912881 135445316940344872051434661)
  ·
    refine ⟨25395996926314663509643999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 135445316940344872051434661 25395996926314663509643999)
    ·
      refine ⟨38093995389471995264465999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25395996926314663509643999 38093995389471995264465999)
      ·
        refine ⟨57140993084207992896698999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38093995389471995264465999 57140993084207992896698999)
        ·
          refine ⟨85711489626311989345048499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57140993084207992896698999 85711489626311989345048499)
          ·
            refine ⟨128567234439467984017572749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85711489626311989345048499 128567234439467984017572749)
            ·
              refine ⟨48212712914800494006589781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128567234439467984017572749 48212712914800494006589781)
              ·
                refine ⟨141248182367579572284931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 48212712914800494006589781 141248182367579572284931)
                ·
                  rfl

theorem cell23_7427156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 10].length) (baseStart_7427156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7427156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7427156 prefixEnd_7427156 := by exact prefixLift 7427156
  have htrace : WordTrace (prefixWord ++ tailWord_7427156) baseStart_7427156 baseEnd_7427156 := by
    simpa [prefixWord, tailWord_7427156, baseEnd_7427156] using wordTrace_append hprefix tailTrace_7427156
  have hstable : (prefixWord ++ tailWord_7427156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7427156).length < 2 ^ (prefixWord ++ tailWord_7427156).sum := by decide
  have hdescent : baseEnd_7427156 < baseStart_7427156 := by decide
  rcases family_descends (prefixWord ++ tailWord_7427156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7427183 : List Nat := [1, 1, 2, 1, 3, 3, 3, 2, 1, 3, 3]
def baseStart_7427183 : Nat := 118140960795 + 7427183 * 2 ^ 59
def prefixEnd_7427183 : Nat := 4983230072969 + 3 ^ 40 * 7427183 * 2
def baseEnd_7427183 : Nat := 3813714787902319846055513

theorem tailTrace_7427183 : CollatzResearch.WordTrace tailWord_7427183 prefixEnd_7427183 3813714787902319846055513 := by
  unfold tailWord_7427183
  simp only [CollatzResearch.WordTrace]
  refine ⟨270891618651591927714102203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180594412434394618476068135 270891618651591927714102203)
  ·
    refine ⟨406337427977387891571153305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270891618651591927714102203 406337427977387891571153305)
    ·
      refine ⟨304753070983040918678364979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 406337427977387891571153305 304753070983040918678364979)
      ·
        refine ⟨457129606474561378017547469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304753070983040918678364979 457129606474561378017547469)
        ·
          refine ⟨171423602427960516756580301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 457129606474561378017547469 171423602427960516756580301)
          ·
            refine ⟨64283850910485193783717613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 171423602427960516756580301 64283850910485193783717613)
            ·
              refine ⟨24106444091431947668894105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64283850910485193783717613 24106444091431947668894105)
              ·
                refine ⟨18079833068573960751670579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24106444091431947668894105 18079833068573960751670579)
                ·
                  refine ⟨27119749602860941127505869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18079833068573960751670579 27119749602860941127505869)
                  ·
                    refine ⟨10169906101072852922814701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27119749602860941127505869 10169906101072852922814701)
                    ·
                      refine ⟨3813714787902319846055513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10169906101072852922814701 3813714787902319846055513)
                      ·
                        rfl

theorem cell23_7427183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 2, 1, 3, 3].length) (baseStart_7427183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7427183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7427183 prefixEnd_7427183 := by exact prefixLift 7427183
  have htrace : WordTrace (prefixWord ++ tailWord_7427183) baseStart_7427183 baseEnd_7427183 := by
    simpa [prefixWord, tailWord_7427183, baseEnd_7427183] using wordTrace_append hprefix tailTrace_7427183
  have hstable : (prefixWord ++ tailWord_7427183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7427183).length < 2 ^ (prefixWord ++ tailWord_7427183).sum := by decide
  have hdescent : baseEnd_7427183 < baseStart_7427183 := by decide
  rcases family_descends (prefixWord ++ tailWord_7427183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7427200 : List Nat := [2, 1, 1, 2, 1, 3, 3, 4, 2, 1, 3]
def baseStart_7427200 : Nat := 118140960795 + 7427200 * 2 ^ 59
def prefixEnd_7427200 : Nat := 4983230072969 + 3 ^ 40 * 7427200 * 2
def baseEnd_7427200 : Nat := 3813723517073446279542935

theorem tailTrace_7427200 : CollatzResearch.WordTrace tailWord_7427200 prefixEnd_7427200 3813723517073446279542935 := by
  unfold tailWord_7427200
  simp only [CollatzResearch.WordTrace]
  refine ⟨135446119346265169808735527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180594825795020226411647369 135446119346265169808735527)
  ·
    refine ⟨203169179019397754713103291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135446119346265169808735527 203169179019397754713103291)
    ·
      refine ⟨304753768529096632069654937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203169179019397754713103291 304753768529096632069654937)
      ·
        refine ⟨228565326396822474052241203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 304753768529096632069654937 228565326396822474052241203)
        ·
          refine ⟨342847989595233711078361805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228565326396822474052241203 342847989595233711078361805)
          ·
            refine ⟨128567996098212641654385677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 342847989595233711078361805 128567996098212641654385677)
            ·
              refine ⟨48212998536829740620394629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 128567996098212641654385677 48212998536829740620394629)
              ·
                refine ⟨9039937225655576366323993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48212998536829740620394629 9039937225655576366323993)
                ·
                  refine ⟨6779952919241682274742995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9039937225655576366323993 6779952919241682274742995)
                  ·
                    refine ⟨10169929378862523412114493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6779952919241682274742995 10169929378862523412114493)
                    ·
                      refine ⟨3813723517073446279542935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10169929378862523412114493 3813723517073446279542935)
                      ·
                        rfl

theorem cell23_7427200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 4, 2, 1, 3].length) (baseStart_7427200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7427200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7427200 prefixEnd_7427200 := by exact prefixLift 7427200
  have htrace : WordTrace (prefixWord ++ tailWord_7427200) baseStart_7427200 baseEnd_7427200 := by
    simpa [prefixWord, tailWord_7427200, baseEnd_7427200] using wordTrace_append hprefix tailTrace_7427200
  have hstable : (prefixWord ++ tailWord_7427200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7427200).length < 2 ^ (prefixWord ++ tailWord_7427200).sum := by decide
  have hdescent : baseEnd_7427200 < baseStart_7427200 := by decide
  rcases family_descends (prefixWord ++ tailWord_7427200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7427201 : List Nat := [1, 2, 4, 2, 2, 1, 4, 2, 1, 2, 2]
def baseStart_7427201 : Nat := 118140960795 + 7427201 * 2 ^ 59
def prefixEnd_7427201 : Nat := 4983230072969 + 3 ^ 40 * 7427201 * 2
def baseEnd_7427201 : Nat := 3813724030554100775630431

theorem tailTrace_7427201 : CollatzResearch.WordTrace tailWord_7427201 prefixEnd_7427201 3813724030554100775630431 := by
  unfold tailWord_7427201
  simp only [CollatzResearch.WordTrace]
  refine ⟨270892275165526716788257457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180594850110351144525504971 270892275165526716788257457)
  ·
    refine ⟨203169206374145037591193093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270892275165526716788257457 203169206374145037591193093)
    ·
      refine ⟨38094226195152194548348705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 203169206374145037591193093 38094226195152194548348705)
      ·
        refine ⟨28570669646364145911261529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38094226195152194548348705 28570669646364145911261529)
        ·
          refine ⟨21428002234773109433446147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28570669646364145911261529 21428002234773109433446147)
          ·
            refine ⟨32142003352159664150169221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21428002234773109433446147 32142003352159664150169221)
            ·
              refine ⟨6026625628529937028156729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32142003352159664150169221 6026625628529937028156729)
              ·
                refine ⟨4519969221397452771117547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6026625628529937028156729 4519969221397452771117547)
                ·
                  refine ⟨6779953832096179156676321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4519969221397452771117547 6779953832096179156676321)
                  ·
                    refine ⟨5084965374072134367507241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6779953832096179156676321 5084965374072134367507241)
                    ·
                      refine ⟨3813724030554100775630431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5084965374072134367507241 3813724030554100775630431)
                      ·
                        rfl

theorem cell23_7427201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 4, 2, 1, 2, 2].length) (baseStart_7427201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7427201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7427201 prefixEnd_7427201 := by exact prefixLift 7427201
  have htrace : WordTrace (prefixWord ++ tailWord_7427201) baseStart_7427201 baseEnd_7427201 := by
    simpa [prefixWord, tailWord_7427201, baseEnd_7427201] using wordTrace_append hprefix tailTrace_7427201
  have hstable : (prefixWord ++ tailWord_7427201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7427201).length < 2 ^ (prefixWord ++ tailWord_7427201).sum := by decide
  have hdescent : baseEnd_7427201 < baseStart_7427201 := by decide
  rcases family_descends (prefixWord ++ tailWord_7427201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7427210 : List Nat := [3, 1, 2, 3, 1, 1, 1, 1, 5, 3, 2]
def baseStart_7427210 : Nat := 118140960795 + 7427210 * 2 ^ 59
def prefixEnd_7427210 : Nat := 4983230072969 + 3 ^ 40 * 7427210 * 2
def baseEnd_7427210 : Nat := 3813728651879991240417889

theorem tailTrace_7427210 : CollatzResearch.WordTrace tailWord_7427210 prefixEnd_7427210 3813728651879991240417889 := by
  unfold tailWord_7427210
  simp only [CollatzResearch.WordTrace]
  refine ⟨67723150855623527831333771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180595068948329407550223389 67723150855623527831333771)
  ·
    refine ⟨101584726283435291747000657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67723150855623527831333771 101584726283435291747000657)
    ·
      refine ⟨76188544712576468810250493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 101584726283435291747000657 76188544712576468810250493)
      ·
        refine ⟨28570704267216175803843935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76188544712576468810250493 28570704267216175803843935)
        ·
          refine ⟨42856056400824263705765903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28570704267216175803843935 42856056400824263705765903)
          ·
            refine ⟨64284084601236395558648855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42856056400824263705765903 64284084601236395558648855)
            ·
              refine ⟨96426126901854593337973283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64284084601236395558648855 96426126901854593337973283)
              ·
                refine ⟨144639190352781890006959925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 96426126901854593337973283 144639190352781890006959925)
                ·
                  refine ⟨13559924095573302188152493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 144639190352781890006959925 13559924095573302188152493)
                  ·
                    refine ⟨5084971535839988320557185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13559924095573302188152493 5084971535839988320557185)
                    ·
                      refine ⟨3813728651879991240417889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5084971535839988320557185 3813728651879991240417889)
                      ·
                        rfl

theorem cell23_7427210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 5, 3, 2].length) (baseStart_7427210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7427210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7427210 prefixEnd_7427210 := by exact prefixLift 7427210
  have htrace : WordTrace (prefixWord ++ tailWord_7427210) baseStart_7427210 baseEnd_7427210 := by
    simpa [prefixWord, tailWord_7427210, baseEnd_7427210] using wordTrace_append hprefix tailTrace_7427210
  have hstable : (prefixWord ++ tailWord_7427210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7427210).length < 2 ^ (prefixWord ++ tailWord_7427210).sum := by decide
  have hdescent : baseEnd_7427210 < baseStart_7427210 := by decide
  rcases family_descends (prefixWord ++ tailWord_7427210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7427256 : List Nat := [2, 1, 2, 1, 2, 1, 2, 1, 1, 1, 9]
def baseStart_7427256 : Nat := 118140960795 + 7427256 * 2 ^ 59
def prefixEnd_7427256 : Nat := 4983230072969 + 3 ^ 40 * 7427256 * 2
def baseEnd_7427256 : Nat := 3813752271990098060442677

theorem tailTrace_7427256 : CollatzResearch.WordTrace tailWord_7427256 prefixEnd_7427256 3813752271990098060442677 := by
  unfold tailWord_7427256
  simp only [CollatzResearch.WordTrace]
  refine ⟨135447140590163730590754811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180596187453551640787673081 135447140590163730590754811)
  ·
    refine ⟨203170710885245595886132217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135447140590163730590754811 203170710885245595886132217)
    ·
      refine ⟨152378033163934196914599163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203170710885245595886132217 152378033163934196914599163)
      ·
        refine ⟨228567049745901295371898745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152378033163934196914599163 228567049745901295371898745)
        ·
          refine ⟨171425287309425971528924059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228567049745901295371898745 171425287309425971528924059)
          ·
            refine ⟨257137930964138957293386089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171425287309425971528924059 257137930964138957293386089)
            ·
              refine ⟨192853448223104217970039567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 257137930964138957293386089 192853448223104217970039567)
              ·
                refine ⟨289280172334656326955059351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 192853448223104217970039567 289280172334656326955059351)
                ·
                  refine ⟨433920258501984490432589027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 289280172334656326955059351 433920258501984490432589027)
                  ·
                    refine ⟨650880387752976735648883541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 433920258501984490432589027 650880387752976735648883541)
                    ·
                      refine ⟨3813752271990098060442677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 650880387752976735648883541 3813752271990098060442677)
                      ·
                        rfl

theorem cell23_7427256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 1, 1, 9].length) (baseStart_7427256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7427256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7427256 prefixEnd_7427256 := by exact prefixLift 7427256
  have htrace : WordTrace (prefixWord ++ tailWord_7427256) baseStart_7427256 baseEnd_7427256 := by
    simpa [prefixWord, tailWord_7427256, baseEnd_7427256] using wordTrace_append hprefix tailTrace_7427256
  have hstable : (prefixWord ++ tailWord_7427256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7427256).length < 2 ^ (prefixWord ++ tailWord_7427256).sum := by decide
  have hdescent : baseEnd_7427256 < baseStart_7427256 := by decide
  rcases family_descends (prefixWord ++ tailWord_7427256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7427257 : List Nat := [1, 2, 1, 4, 1, 4, 1, 1, 4, 2, 2]
def baseStart_7427257 : Nat := 118140960795 + 7427257 * 2 ^ 59
def prefixEnd_7427257 : Nat := 4983230072969 + 3 ^ 40 * 7427257 * 2
def baseEnd_7427257 : Nat := 3813752785470752556530173

theorem tailTrace_7427257 : CollatzResearch.WordTrace tailWord_7427257 prefixEnd_7427257 3813752785470752556530173 := by
  unfold tailWord_7427257
  simp only [CollatzResearch.WordTrace]
  refine ⟨270894317653323838352296025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180596211768882558901530683 270894317653323838352296025)
  ·
    refine ⟨203170738239992878764222019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270894317653323838352296025 203170738239992878764222019)
    ·
      refine ⟨304756107359989318146333029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203170738239992878764222019 304756107359989318146333029)
      ·
        refine ⟨57141770129997997152437443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 304756107359989318146333029 57141770129997997152437443)
        ·
          refine ⟨85712655194996995728656165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57141770129997997152437443 85712655194996995728656165)
          ·
            refine ⟨16071122849061936699123031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85712655194996995728656165 16071122849061936699123031)
            ·
              refine ⟨24106684273592905048684547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16071122849061936699123031 24106684273592905048684547)
              ·
                refine ⟨36160026410389357573026821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24106684273592905048684547 36160026410389357573026821)
                ·
                  refine ⟨6780004951948004544942529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36160026410389357573026821 6780004951948004544942529)
                  ·
                    refine ⟨5085003713961003408706897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6780004951948004544942529 5085003713961003408706897)
                    ·
                      refine ⟨3813752785470752556530173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5085003713961003408706897 3813752785470752556530173)
                      ·
                        rfl

theorem cell23_7427257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 1, 4, 2, 2].length) (baseStart_7427257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7427257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7427257 prefixEnd_7427257 := by exact prefixLift 7427257
  have htrace : WordTrace (prefixWord ++ tailWord_7427257) baseStart_7427257 baseEnd_7427257 := by
    simpa [prefixWord, tailWord_7427257, baseEnd_7427257] using wordTrace_append hprefix tailTrace_7427257
  have hstable : (prefixWord ++ tailWord_7427257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7427257).length < 2 ^ (prefixWord ++ tailWord_7427257).sum := by decide
  have hdescent : baseEnd_7427257 < baseStart_7427257 := by decide
  rcases family_descends (prefixWord ++ tailWord_7427257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7427297 : List Nat := [1, 2, 3, 1, 3, 4, 1, 3, 5]
def baseStart_7427297 : Nat := 118140960795 + 7427297 * 2 ^ 59
def prefixEnd_7427297 : Nat := 4983230072969 + 3 ^ 40 * 7427297 * 2
def baseEnd_7427297 : Nat := 423752591632992488892221

theorem tailTrace_7427297 : CollatzResearch.WordTrace tailWord_7427297 prefixEnd_7427297 423752591632992488892221 := by
  unfold tailWord_7427297
  simp only [CollatzResearch.WordTrace]
  refine ⟨270895776573178925183752145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180597184382119283455834763 270895776573178925183752145)
  ·
    refine ⟨203171832429884193887814109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270895776573178925183752145 203171832429884193887814109)
    ·
      refine ⟨76189437161206572707930291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 203171832429884193887814109 76189437161206572707930291)
      ·
        refine ⟨114284155741809859061895437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76189437161206572707930291 114284155741809859061895437)
        ·
          refine ⟨42856558403178697148210789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114284155741809859061895437 42856558403178697148210789)
          ·
            refine ⟨8035604700596005715289523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42856558403178697148210789 8035604700596005715289523)
            ·
              refine ⟨12053407050894008572934285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8035604700596005715289523 12053407050894008572934285)
              ·
                refine ⟨4520027644085253214850357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12053407050894008572934285 4520027644085253214850357)
                ·
                  refine ⟨423752591632992488892221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4520027644085253214850357 423752591632992488892221)
                  ·
                    rfl

theorem cell23_7427297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 1, 3, 5].length) (baseStart_7427297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7427297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7427297 prefixEnd_7427297 := by exact prefixLift 7427297
  have htrace : WordTrace (prefixWord ++ tailWord_7427297) baseStart_7427297 baseEnd_7427297 := by
    simpa [prefixWord, tailWord_7427297, baseEnd_7427297] using wordTrace_append hprefix tailTrace_7427297
  have hstable : (prefixWord ++ tailWord_7427297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7427297).length < 2 ^ (prefixWord ++ tailWord_7427297).sum := by decide
  have hdescent : baseEnd_7427297 < baseStart_7427297 := by decide
  rcases family_descends (prefixWord ++ tailWord_7427297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7427314 : List Nat := [3, 2, 1, 3, 3, 1, 3, 2, 5]
def baseStart_7427314 : Nat := 118140960795 + 7427314 * 2 ^ 59
def prefixEnd_7427314 : Nat := 4983230072969 + 3 ^ 40 * 7427314 * 2
def baseEnd_7427314 : Nat := 423753561540895425946379

theorem tailTrace_7427314 : CollatzResearch.WordTrace tailWord_7427314 prefixEnd_7427314 423753561540895425946379 := by
  unfold tailWord_7427314
  simp only [CollatzResearch.WordTrace]
  refine ⟨67724099153529334271780249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180597597742744891391413997 67724099153529334271780249)
  ·
    refine ⟨50793074365147000703835187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 67724099153529334271780249 50793074365147000703835187)
    ·
      refine ⟨76189611547720501055752781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50793074365147000703835187 76189611547720501055752781)
      ·
        refine ⟨28571104330395187895907293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76189611547720501055752781 28571104330395187895907293)
        ·
          refine ⟨10714164123898195460965235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28571104330395187895907293 10714164123898195460965235)
          ·
            refine ⟨16071246185847293191447853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10714164123898195460965235 16071246185847293191447853)
            ·
              refine ⟨6026717319692734946792945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16071246185847293191447853 6026717319692734946792945)
              ·
                refine ⟨4520037989769551210094709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6026717319692734946792945 4520037989769551210094709)
                ·
                  refine ⟨423753561540895425946379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4520037989769551210094709 423753561540895425946379)
                  ·
                    rfl

theorem cell23_7427314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 3, 2, 5].length) (baseStart_7427314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7427314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7427314 prefixEnd_7427314 := by exact prefixLift 7427314
  have htrace : WordTrace (prefixWord ++ tailWord_7427314) baseStart_7427314 baseEnd_7427314 := by
    simpa [prefixWord, tailWord_7427314, baseEnd_7427314] using wordTrace_append hprefix tailTrace_7427314
  have hstable : (prefixWord ++ tailWord_7427314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7427314).length < 2 ^ (prefixWord ++ tailWord_7427314).sum := by decide
  have hdescent : baseEnd_7427314 < baseStart_7427314 := by decide
  rcases family_descends (prefixWord ++ tailWord_7427314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7427398 : List Nat := [6, 1, 1, 3, 1, 2, 1, 1, 2, 1, 4]
def baseStart_7427398 : Nat := 118140960795 + 7427398 * 2 ^ 59
def prefixEnd_7427398 : Nat := 4983230072969 + 3 ^ 40 * 7427398 * 2
def baseEnd_7427398 : Nat := 3813825186243036504867025

theorem tailTrace_7427398 : CollatzResearch.WordTrace tailWord_7427398 prefixEnd_7427398 3813825186243036504867025 := by
  unfold tailWord_7427398
  simp only [CollatzResearch.WordTrace]
  refine ⟨8465608135806656857286839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 180599640230542012955452565 8465608135806656857286839)
  ·
    refine ⟨12698412203709985285930259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8465608135806656857286839 12698412203709985285930259)
    ·
      refine ⟨19047618305564977928895389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12698412203709985285930259 19047618305564977928895389)
      ·
        refine ⟨7142856864586866723335771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19047618305564977928895389 7142856864586866723335771)
        ·
          refine ⟨10714285296880300085003657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7142856864586866723335771 10714285296880300085003657)
          ·
            refine ⟨8035713972660225063752743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10714285296880300085003657 8035713972660225063752743)
            ·
              refine ⟨12053570958990337595629115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8035713972660225063752743 12053570958990337595629115)
              ·
                refine ⟨18080356438485506393443673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12053570958990337595629115 18080356438485506393443673)
                ·
                  refine ⟨13560267328864129795082755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18080356438485506393443673 13560267328864129795082755)
                  ·
                    refine ⟨20340400993296194692624133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13560267328864129795082755 20340400993296194692624133)
                    ·
                      refine ⟨3813825186243036504867025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20340400993296194692624133 3813825186243036504867025)
                      ·
                        rfl

theorem cell23_7427398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_7427398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7427398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7427398 prefixEnd_7427398 := by exact prefixLift 7427398
  have htrace : WordTrace (prefixWord ++ tailWord_7427398) baseStart_7427398 baseEnd_7427398 := by
    simpa [prefixWord, tailWord_7427398, baseEnd_7427398] using wordTrace_append hprefix tailTrace_7427398
  have hstable : (prefixWord ++ tailWord_7427398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7427398).length < 2 ^ (prefixWord ++ tailWord_7427398).sum := by decide
  have hdescent : baseEnd_7427398 < baseStart_7427398 := by decide
  rcases family_descends (prefixWord ++ tailWord_7427398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7427400 : List Nat := [2, 1, 3, 1, 1, 2, 1, 6, 1, 5]
def baseStart_7427400 : Nat := 118140960795 + 7427400 * 2 ^ 59
def prefixEnd_7427400 : Nat := 4983230072969 + 3 ^ 40 * 7427400 * 2
def baseEnd_7427400 : Nat := 1271275404401448499014005

theorem tailTrace_7427400 : CollatzResearch.WordTrace tailWord_7427400 prefixEnd_7427400 1271275404401448499014005 := by
  unfold tailWord_7427400
  simp only [CollatzResearch.WordTrace]
  refine ⟨135449766645902886887375827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180599688861203849183167769 135449766645902886887375827)
  ·
    refine ⟨203174649968854330331063741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135449766645902886887375827 203174649968854330331063741)
    ·
      refine ⟨76190493738320373874148903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 203174649968854330331063741 76190493738320373874148903)
      ·
        refine ⟨114285740607480560811223355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76190493738320373874148903 114285740607480560811223355)
        ·
          refine ⟨171428610911220841216835033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114285740607480560811223355 171428610911220841216835033)
          ·
            refine ⟨128571458183415630912626275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171428610911220841216835033 128571458183415630912626275)
            ·
              refine ⟨192857187275123446368939413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128571458183415630912626275 192857187275123446368939413)
              ·
                refine ⟨9040180653521411548544035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 192857187275123446368939413 9040180653521411548544035)
                ·
                  refine ⟨13560270980282117322816053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9040180653521411548544035 13560270980282117322816053)
                  ·
                    refine ⟨1271275404401448499014005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13560270980282117322816053 1271275404401448499014005)
                    ·
                      rfl

theorem cell23_7427400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 6, 1, 5].length) (baseStart_7427400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7427400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7427400 prefixEnd_7427400 := by exact prefixLift 7427400
  have htrace : WordTrace (prefixWord ++ tailWord_7427400) baseStart_7427400 baseEnd_7427400 := by
    simpa [prefixWord, tailWord_7427400, baseEnd_7427400] using wordTrace_append hprefix tailTrace_7427400
  have hstable : (prefixWord ++ tailWord_7427400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7427400).length < 2 ^ (prefixWord ++ tailWord_7427400).sum := by decide
  have hdescent : baseEnd_7427400 < baseStart_7427400 := by decide
  rcases family_descends (prefixWord ++ tailWord_7427400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7427417 : List Nat := [1, 2, 1, 2, 2, 2, 6, 1, 1, 5]
def baseStart_7427417 : Nat := 118140960795 + 7427417 * 2 ^ 59
def prefixEnd_7427417 : Nat := 4983230072969 + 3 ^ 40 * 7427417 * 2
def baseEnd_7427417 : Nat := 1271278314125157310176479

theorem tailTrace_7427417 : CollatzResearch.WordTrace tailWord_7427417 prefixEnd_7427417 1271278314125157310176479 := by
  unfold tailWord_7427417
  simp only [CollatzResearch.WordTrace]
  refine ⟨270900153332744185678120505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180600102221829457118747003 270900153332744185678120505)
  ·
    refine ⟨203175114999558139258590379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270900153332744185678120505 203175114999558139258590379)
    ·
      refine ⟨304762672499337208887885569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203175114999558139258590379 304762672499337208887885569)
      ·
        refine ⟨228572004374502906665914177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 304762672499337208887885569 228572004374502906665914177)
        ·
          refine ⟨171429003280877179999435633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228572004374502906665914177 171429003280877179999435633)
          ·
            refine ⟨128571752460657884999576725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 171429003280877179999435633 128571752460657884999576725)
            ·
              refine ⟨6026800896593338359355159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 128571752460657884999576725 6026800896593338359355159)
              ·
                refine ⟨9040201344890007539032739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6026800896593338359355159 9040201344890007539032739)
                ·
                  refine ⟨13560302017335011308549109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9040201344890007539032739 13560302017335011308549109)
                  ·
                    refine ⟨1271278314125157310176479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13560302017335011308549109 1271278314125157310176479)
                    ·
                      rfl

theorem cell23_7427417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 6, 1, 1, 5].length) (baseStart_7427417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7427417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7427417 prefixEnd_7427417 := by exact prefixLift 7427417
  have htrace : WordTrace (prefixWord ++ tailWord_7427417) baseStart_7427417 baseEnd_7427417 := by
    simpa [prefixWord, tailWord_7427417, baseEnd_7427417] using wordTrace_append hprefix tailTrace_7427417
  have hstable : (prefixWord ++ tailWord_7427417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7427417).length < 2 ^ (prefixWord ++ tailWord_7427417).sum := by decide
  have hdescent : baseEnd_7427417 < baseStart_7427417 := by decide
  rcases family_descends (prefixWord ++ tailWord_7427417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7427440 : List Nat := [2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 5]
def baseStart_7427440 : Nat := 118140960795 + 7427440 * 2 ^ 59
def prefixEnd_7427440 : Nat := 4983230072969 + 3 ^ 40 * 7427440 * 2
def baseEnd_7427440 : Nat := 3813846752430525340541831

theorem tailTrace_7427440 : CollatzResearch.WordTrace tailWord_7427440 prefixEnd_7427440 3813846752430525340541831 := by
  unfold tailWord_7427440
  simp only [CollatzResearch.WordTrace]
  refine ⟨135450496105830430303103887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180600661474440573737471849 135450496105830430303103887)
  ·
    refine ⟨203175744158745645454655831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135450496105830430303103887 203175744158745645454655831)
    ·
      refine ⟨304763616238118468181983747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203175744158745645454655831 304763616238118468181983747)
      ·
        refine ⟨457145424357177702272975621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304763616238118468181983747 457145424357177702272975621)
        ·
          refine ⟨85714767066970819176182929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 457145424357177702272975621 85714767066970819176182929)
          ·
            refine ⟨64286075300228114382137197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85714767066970819176182929 64286075300228114382137197)
            ·
              refine ⟨24107278237585542893301449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64286075300228114382137197 24107278237585542893301449)
              ·
                refine ⟨18080458678189157169976087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24107278237585542893301449 18080458678189157169976087)
                ·
                  refine ⟨27120688017283735754964131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18080458678189157169976087 27120688017283735754964131)
                  ·
                    refine ⟨40681032025925603632446197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27120688017283735754964131 40681032025925603632446197)
                    ·
                      refine ⟨3813846752430525340541831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40681032025925603632446197 3813846752430525340541831)
                      ·
                        rfl

theorem cell23_7427440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 5].length) (baseStart_7427440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7427440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7427440 prefixEnd_7427440 := by exact prefixLift 7427440
  have htrace : WordTrace (prefixWord ++ tailWord_7427440) baseStart_7427440 baseEnd_7427440 := by
    simpa [prefixWord, tailWord_7427440, baseEnd_7427440] using wordTrace_append hprefix tailTrace_7427440
  have hstable : (prefixWord ++ tailWord_7427440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7427440).length < 2 ^ (prefixWord ++ tailWord_7427440).sum := by decide
  have hdescent : baseEnd_7427440 < baseStart_7427440 := by decide
  rcases family_descends (prefixWord ++ tailWord_7427440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7427460 : List Nat := [2, 3, 2, 1, 1, 4, 1, 9]
def baseStart_7427460 : Nat := 118140960795 + 7427460 * 2 ^ 59
def prefixEnd_7427460 : Nat := 4983230072969 + 3 ^ 40 * 7427460 * 2
def baseEnd_7427460 : Nat := 141253963779393157862657

theorem tailTrace_7427460 : CollatzResearch.WordTrace tailWord_7427460 prefixEnd_7427460 141253963779393157862657 := by
  unfold tailWord_7427460
  simp only [CollatzResearch.WordTrace]
  refine ⟨135450860835794202010967917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180601147781058936014623889 135450860835794202010967917)
  ·
    refine ⟨50794072813422825754112969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 135450860835794202010967917 50794072813422825754112969)
    ·
      refine ⟨38095554610067119315584727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50794072813422825754112969 38095554610067119315584727)
      ·
        refine ⟨57143331915100678973377091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38095554610067119315584727 57143331915100678973377091)
        ·
          refine ⟨85714997872651018460065637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57143331915100678973377091 85714997872651018460065637)
          ·
            refine ⟨16071562101122065961262307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 85714997872651018460065637 16071562101122065961262307)
            ·
              refine ⟨24107343151683098941893461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16071562101122065961262307 24107343151683098941893461)
              ·
                refine ⟨141253963779393157862657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24107343151683098941893461 141253963779393157862657)
                ·
                  rfl

theorem cell23_7427460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 9].length) (baseStart_7427460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7427460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7427460 prefixEnd_7427460 := by exact prefixLift 7427460
  have htrace : WordTrace (prefixWord ++ tailWord_7427460) baseStart_7427460 baseEnd_7427460 := by
    simpa [prefixWord, tailWord_7427460, baseEnd_7427460] using wordTrace_append hprefix tailTrace_7427460
  have hstable : (prefixWord ++ tailWord_7427460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7427460).length < 2 ^ (prefixWord ++ tailWord_7427460).sum := by decide
  have hdescent : baseEnd_7427460 < baseStart_7427460 := by decide
  rcases family_descends (prefixWord ++ tailWord_7427460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7427488 : List Nat := [2, 1, 1, 4, 1, 2, 5, 2, 1, 2, 2]
def baseStart_7427488 : Nat := 118140960795 + 7427488 * 2 ^ 59
def prefixEnd_7427488 : Nat := 4983230072969 + 3 ^ 40 * 7427488 * 2
def baseEnd_7427488 : Nat := 3813871399501941152741611

theorem tailTrace_7427488 : CollatzResearch.WordTrace tailWord_7427488 prefixEnd_7427488 3813871399501941152741611 := by
  unfold tailWord_7427488
  simp only [CollatzResearch.WordTrace]
  refine ⟨135451371457743482401977559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180601828610324643202636745 135451371457743482401977559)
  ·
    refine ⟨203177057186615223602966339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135451371457743482401977559 203177057186615223602966339)
    ·
      refine ⟨304765585779922835404449509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203177057186615223602966339 304765585779922835404449509)
      ·
        refine ⟨57143547333735531638334283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 304765585779922835404449509 57143547333735531638334283)
        ·
          refine ⟨85715321000603297457501425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57143547333735531638334283 85715321000603297457501425)
          ·
            refine ⟨64286490750452473093126069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85715321000603297457501425 64286490750452473093126069)
            ·
              refine ⟨6026858507854919352480569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 64286490750452473093126069 6026858507854919352480569)
              ·
                refine ⟨4520143880891189514360427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6026858507854919352480569 4520143880891189514360427)
                ·
                  refine ⟨6780215821336784271540641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4520143880891189514360427 6780215821336784271540641)
                  ·
                    refine ⟨5085161866002588203655481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6780215821336784271540641 5085161866002588203655481)
                    ·
                      refine ⟨3813871399501941152741611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5085161866002588203655481 3813871399501941152741611)
                      ·
                        rfl

theorem cell23_7427488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 5, 2, 1, 2, 2].length) (baseStart_7427488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7427488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7427488 prefixEnd_7427488 := by exact prefixLift 7427488
  have htrace : WordTrace (prefixWord ++ tailWord_7427488) baseStart_7427488 baseEnd_7427488 := by
    simpa [prefixWord, tailWord_7427488, baseEnd_7427488] using wordTrace_append hprefix tailTrace_7427488
  have hstable : (prefixWord ++ tailWord_7427488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7427488).length < 2 ^ (prefixWord ++ tailWord_7427488).sum := by decide
  have hdescent : baseEnd_7427488 < baseStart_7427488 := by decide
  rcases family_descends (prefixWord ++ tailWord_7427488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7427522 : List Nat := [3, 5, 2, 1, 1, 1, 3, 1, 1, 1, 4]
def baseStart_7427522 : Nat := 118140960795 + 7427522 * 2 ^ 59
def prefixEnd_7427522 : Nat := 4983230072969 + 3 ^ 40 * 7427522 * 2
def baseEnd_7427522 : Nat := 3813888857844194019716455

theorem tailTrace_7427522 : CollatzResearch.WordTrace tailWord_7427522 prefixEnd_7427522 3813888857844194019716455 := by
  unfold tailWord_7427522
  simp only [CollatzResearch.WordTrace]
  refine ⟨67725995749340947152673205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180602655331575859073795213 67725995749340947152673205)
  ·
    refine ⟨6349312101500713795563113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 67725995749340947152673205 6349312101500713795563113)
    ·
      refine ⟨4761984076125535346672335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6349312101500713795563113 4761984076125535346672335)
      ·
        refine ⟨7142976114188303020008503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4761984076125535346672335 7142976114188303020008503)
        ·
          refine ⟨10714464171282454530012755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7142976114188303020008503 10714464171282454530012755)
          ·
            refine ⟨16071696256923681795019133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10714464171282454530012755 16071696256923681795019133)
            ·
              refine ⟨6026886096346380673132175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16071696256923681795019133 6026886096346380673132175)
              ·
                refine ⟨9040329144519571009698263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6026886096346380673132175 9040329144519571009698263)
                ·
                  refine ⟨13560493716779356514547395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9040329144519571009698263 13560493716779356514547395)
                  ·
                    refine ⟨20340740575169034771821093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13560493716779356514547395 20340740575169034771821093)
                    ·
                      refine ⟨3813888857844194019716455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20340740575169034771821093 3813888857844194019716455)
                      ·
                        rfl

theorem cell23_7427522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_7427522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7427522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7427522 prefixEnd_7427522 := by exact prefixLift 7427522
  have htrace : WordTrace (prefixWord ++ tailWord_7427522) baseStart_7427522 baseEnd_7427522 := by
    simpa [prefixWord, tailWord_7427522, baseEnd_7427522] using wordTrace_append hprefix tailTrace_7427522
  have hstable : (prefixWord ++ tailWord_7427522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7427522).length < 2 ^ (prefixWord ++ tailWord_7427522).sum := by decide
  have hdescent : baseEnd_7427522 < baseStart_7427522 := by decide
  rcases family_descends (prefixWord ++ tailWord_7427522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7427544 : List Nat := [2, 1, 2, 2, 2, 1, 2, 3, 4, 2, 2]
def baseStart_7427544 : Nat := 118140960795 + 7427544 * 2 ^ 59
def prefixEnd_7427544 : Nat := 4983230072969 + 3 ^ 40 * 7427544 * 2
def baseEnd_7427544 : Nat := 3813900154418592933641353

theorem tailTrace_7427544 : CollatzResearch.WordTrace tailWord_7427544 prefixEnd_7427544 3813900154418592933641353 := by
  unfold tailWord_7427544
  simp only [CollatzResearch.WordTrace]
  refine ⟨135452392701642043183996843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180603190268856057578662457 135452392701642043183996843)
  ·
    refine ⟨203178589052463064775995265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135452392701642043183996843 203178589052463064775995265)
    ·
      refine ⟨152383941789347298581996449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203178589052463064775995265 152383941789347298581996449)
      ·
        refine ⟨114287956342010473936497337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152383941789347298581996449 114287956342010473936497337)
        ·
          refine ⟨85715967256507855452373003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 114287956342010473936497337 85715967256507855452373003)
          ·
            refine ⟨128573950884761783178559505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85715967256507855452373003 128573950884761783178559505)
            ·
              refine ⟨96430463163571337383919629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128573950884761783178559505 96430463163571337383919629)
              ·
                refine ⟨36161423686339251518969861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 96430463163571337383919629 36161423686339251518969861)
                ·
                  refine ⟨6780266941188609659806849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36161423686339251518969861 6780266941188609659806849)
                  ·
                    refine ⟨5085200205891457244855137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6780266941188609659806849 5085200205891457244855137)
                    ·
                      refine ⟨3813900154418592933641353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5085200205891457244855137 3813900154418592933641353)
                      ·
                        rfl

theorem cell23_7427544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 3, 4, 2, 2].length) (baseStart_7427544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7427544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7427544 prefixEnd_7427544 := by exact prefixLift 7427544
  have htrace : WordTrace (prefixWord ++ tailWord_7427544) baseStart_7427544 baseEnd_7427544 := by
    simpa [prefixWord, tailWord_7427544, baseEnd_7427544] using wordTrace_append hprefix tailTrace_7427544
  have hstable : (prefixWord ++ tailWord_7427544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7427544).length < 2 ^ (prefixWord ++ tailWord_7427544).sum := by decide
  have hdescent : baseEnd_7427544 < baseStart_7427544 := by decide
  rcases family_descends (prefixWord ++ tailWord_7427544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7427557 : List Nat := [1, 3, 1, 5, 1, 1, 1, 1, 1, 4, 4]
def baseStart_7427557 : Nat := 118140960795 + 7427557 * 2 ^ 59
def prefixEnd_7427557 : Nat := 4983230072969 + 3 ^ 40 * 7427557 * 2
def baseEnd_7427557 : Nat := 3813906829667101382778793

theorem tailTrace_7427557 : CollatzResearch.WordTrace tailWord_7427557 prefixEnd_7427557 3813906829667101382778793 := by
  unfold tailWord_7427557
  simp only [CollatzResearch.WordTrace]
  refine ⟨270905259552236989588216925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180603506368157993058811283 270905259552236989588216925)
  ·
    refine ⟨101589472332088871095581347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 270905259552236989588216925 101589472332088871095581347)
    ·
      refine ⟨152384208498133306643372021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101589472332088871095581347 152384208498133306643372021)
      ·
        refine ⟨14286019546699997497816127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 152384208498133306643372021 14286019546699997497816127)
        ·
          refine ⟨21429029320049996246724191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14286019546699997497816127 21429029320049996246724191)
          ·
            refine ⟨32143543980074994370086287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21429029320049996246724191 32143543980074994370086287)
            ·
              refine ⟨48215315970112491555129431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32143543980074994370086287 48215315970112491555129431)
              ·
                refine ⟨72322973955168737332694147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48215315970112491555129431 72322973955168737332694147)
                ·
                  refine ⟨108484460932753105999041221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 72322973955168737332694147 108484460932753105999041221)
                  ·
                    refine ⟨20340836424891207374820229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 108484460932753105999041221 20340836424891207374820229)
                    ·
                      refine ⟨3813906829667101382778793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20340836424891207374820229 3813906829667101382778793)
                      ·
                        rfl

theorem cell23_7427557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_7427557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7427557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7427557 prefixEnd_7427557 := by exact prefixLift 7427557
  have htrace : WordTrace (prefixWord ++ tailWord_7427557) baseStart_7427557 baseEnd_7427557 := by
    simpa [prefixWord, tailWord_7427557, baseEnd_7427557] using wordTrace_append hprefix tailTrace_7427557
  have hstable : (prefixWord ++ tailWord_7427557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7427557).length < 2 ^ (prefixWord ++ tailWord_7427557).sum := by decide
  have hdescent : baseEnd_7427557 < baseStart_7427557 := by decide
  rcases family_descends (prefixWord ++ tailWord_7427557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7427582 : List Nat := [4, 2, 2, 3, 1, 2, 2, 1, 1, 3, 2]
def baseStart_7427582 : Nat := 118140960795 + 7427582 * 2 ^ 59
def prefixEnd_7427582 : Nat := 4983230072969 + 3 ^ 40 * 7427582 * 2
def baseEnd_7427582 : Nat := 3813919666683463784966179

theorem tailTrace_7427582 : CollatzResearch.WordTrace tailWord_7427582 prefixEnd_7427582 3813919666683463784966179 := by
  unfold tailWord_7427582
  simp only [CollatzResearch.WordTrace]
  refine ⟨33863271422143302357234625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180604114251430945905251333 33863271422143302357234625)
  ·
    refine ⟨25397453566607476767925969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33863271422143302357234625 25397453566607476767925969)
    ·
      refine ⟨19048090174955607575944477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25397453566607476767925969 19048090174955607575944477)
      ·
        refine ⟨7143033815608352840979179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19048090174955607575944477 7143033815608352840979179)
        ·
          refine ⟨10714550723412529261468769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7143033815608352840979179 10714550723412529261468769)
          ·
            refine ⟨8035913042559396946101577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10714550723412529261468769 8035913042559396946101577)
            ·
              refine ⟨6026934781919547709576183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8035913042559396946101577 6026934781919547709576183)
              ·
                refine ⟨9040402172879321564364275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6026934781919547709576183 9040402172879321564364275)
                ·
                  refine ⟨13560603259318982346546413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9040402172879321564364275 13560603259318982346546413)
                  ·
                    refine ⟨5085226222244618379954905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13560603259318982346546413 5085226222244618379954905)
                    ·
                      refine ⟨3813919666683463784966179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5085226222244618379954905 3813919666683463784966179)
                      ·
                        rfl

theorem cell23_7427582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_7427582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7427582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7427582 prefixEnd_7427582 := by exact prefixLift 7427582
  have htrace : WordTrace (prefixWord ++ tailWord_7427582) baseStart_7427582 baseEnd_7427582 := by
    simpa [prefixWord, tailWord_7427582, baseEnd_7427582] using wordTrace_append hprefix tailTrace_7427582
  have hstable : (prefixWord ++ tailWord_7427582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7427582).length < 2 ^ (prefixWord ++ tailWord_7427582).sum := by decide
  have hdescent : baseEnd_7427582 < baseStart_7427582 := by decide
  rcases family_descends (prefixWord ++ tailWord_7427582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7427587 : List Nat := [1, 1, 1, 3, 2, 1, 2, 2, 1, 7, 2]
def baseStart_7427587 : Nat := 118140960795 + 7427587 * 2 ^ 59
def prefixEnd_7427587 : Nat := 4983230072969 + 3 ^ 40 * 7427587 * 2
def baseEnd_7427587 : Nat := 3813922234086736265403655

theorem tailTrace_7427587 : CollatzResearch.WordTrace tailWord_7427587 prefixEnd_7427587 3813922234086736265403655 := by
  unfold tailWord_7427587
  simp only [CollatzResearch.WordTrace]
  refine ⟨270906353742128304711809015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180604235828085536474539343 270906353742128304711809015)
  ·
    refine ⟨406359530613192457067713523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270906353742128304711809015 406359530613192457067713523)
    ·
      refine ⟨609539295919788685601570285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 406359530613192457067713523 609539295919788685601570285)
      ·
        refine ⟨228577235969920757100588857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 609539295919788685601570285 228577235969920757100588857)
        ·
          refine ⟨171432926977440567825441643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 228577235969920757100588857 171432926977440567825441643)
          ·
            refine ⟨257149390466160851738162465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171432926977440567825441643 257149390466160851738162465)
            ·
              refine ⟨192862042849620638803621849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 257149390466160851738162465 192862042849620638803621849)
              ·
                refine ⟨144646532137215479102716387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 192862042849620638803621849 144646532137215479102716387)
                ·
                  refine ⟨216969798205823218654074581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 144646532137215479102716387 216969798205823218654074581)
                  ·
                    refine ⟨5085229645448981687204873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 216969798205823218654074581 5085229645448981687204873)
                    ·
                      refine ⟨3813922234086736265403655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5085229645448981687204873 3813922234086736265403655)
                      ·
                        rfl

theorem cell23_7427587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 7, 2].length) (baseStart_7427587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7427587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7427587 prefixEnd_7427587 := by exact prefixLift 7427587
  have htrace : WordTrace (prefixWord ++ tailWord_7427587) baseStart_7427587 baseEnd_7427587 := by
    simpa [prefixWord, tailWord_7427587, baseEnd_7427587] using wordTrace_append hprefix tailTrace_7427587
  have hstable : (prefixWord ++ tailWord_7427587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7427587).length < 2 ^ (prefixWord ++ tailWord_7427587).sum := by decide
  have hdescent : baseEnd_7427587 < baseStart_7427587 := by decide
  rcases family_descends (prefixWord ++ tailWord_7427587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7427595 : List Nat := [1, 1, 1, 1, 9, 1, 1, 2, 2, 2, 2]
def baseStart_7427595 : Nat := 118140960795 + 7427595 * 2 ^ 59
def prefixEnd_7427595 : Nat := 4983230072969 + 3 ^ 40 * 7427595 * 2
def baseEnd_7427595 : Nat := 3813926341931972234103619

theorem tailTrace_7427595 : CollatzResearch.WordTrace tailWord_7427595 prefixEnd_7427595 3813926341931972234103619 := by
  unfold tailWord_7427595
  simp only [CollatzResearch.WordTrace]
  refine ⟨270906645526099322078100239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180604430350732881385400159 270906645526099322078100239)
  ·
    refine ⟨406359968289148983117150359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270906645526099322078100239 406359968289148983117150359)
    ·
      refine ⟨609539952433723474675725539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 406359968289148983117150359 609539952433723474675725539)
      ·
        refine ⟨914309928650585212013588309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 609539952433723474675725539 914309928650585212013588309)
        ·
          refine ⟨5357284738187022726642119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 914309928650585212013588309 5357284738187022726642119)
          ·
            refine ⟨8035927107280534089963179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5357284738187022726642119 8035927107280534089963179)
            ·
              refine ⟨12053890660920801134944769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8035927107280534089963179 12053890660920801134944769)
              ·
                refine ⟨9040417995690600851208577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12053890660920801134944769 9040417995690600851208577)
                ·
                  refine ⟨6780313496767950638406433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9040417995690600851208577 6780313496767950638406433)
                  ·
                    refine ⟨5085235122575962978804825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6780313496767950638406433 5085235122575962978804825)
                    ·
                      refine ⟨3813926341931972234103619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5085235122575962978804825 3813926341931972234103619)
                      ·
                        rfl

theorem cell23_7427595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 1, 2, 2, 2, 2].length) (baseStart_7427595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7427595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7427595 prefixEnd_7427595 := by exact prefixLift 7427595
  have htrace : WordTrace (prefixWord ++ tailWord_7427595) baseStart_7427595 baseEnd_7427595 := by
    simpa [prefixWord, tailWord_7427595, baseEnd_7427595] using wordTrace_append hprefix tailTrace_7427595
  have hstable : (prefixWord ++ tailWord_7427595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7427595).length < 2 ^ (prefixWord ++ tailWord_7427595).sum := by decide
  have hdescent : baseEnd_7427595 < baseStart_7427595 := by decide
  rcases family_descends (prefixWord ++ tailWord_7427595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7427617 : List Nat := [1, 2, 3, 2, 2, 2, 1, 2, 1, 3, 4]
def baseStart_7427617 : Nat := 118140960795 + 7427617 * 2 ^ 59
def prefixEnd_7427617 : Nat := 4983230072969 + 3 ^ 40 * 7427617 * 2
def baseEnd_7427617 : Nat := 3813937638506371148028517

theorem tailTrace_7427617 : CollatzResearch.WordTrace tailWord_7427617 prefixEnd_7427617 3813937638506371148028517 := by
  unfold tailWord_7427617
  simp only [CollatzResearch.WordTrace]
  refine ⟨270907447932019619835401105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180604965288013079890267403 270907447932019619835401105)
  ·
    refine ⟨203180585949014714876550829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270907447932019619835401105 203180585949014714876550829)
    ·
      refine ⟨76192719730880518078706561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 203180585949014714876550829 76192719730880518078706561)
      ·
        refine ⟨57144539798160388559029921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76192719730880518078706561 57144539798160388559029921)
        ·
          refine ⟨42858404848620291419272441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57144539798160388559029921 42858404848620291419272441)
          ·
            refine ⟨32143803636465218564454331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42858404848620291419272441 32143803636465218564454331)
            ·
              refine ⟨48215705454697827846681497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32143803636465218564454331 48215705454697827846681497)
              ·
                refine ⟨36161779091023370885011123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48215705454697827846681497 36161779091023370885011123)
                ·
                  refine ⟨54242668636535056327516685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36161779091023370885011123 54242668636535056327516685)
                  ·
                    refine ⟨20341000738700646122818757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54242668636535056327516685 20341000738700646122818757)
                    ·
                      refine ⟨3813937638506371148028517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20341000738700646122818757 3813937638506371148028517)
                      ·
                        rfl

theorem cell23_7427617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 2, 1, 3, 4].length) (baseStart_7427617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7427617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7427617 prefixEnd_7427617 := by exact prefixLift 7427617
  have htrace : WordTrace (prefixWord ++ tailWord_7427617) baseStart_7427617 baseEnd_7427617 := by
    simpa [prefixWord, tailWord_7427617, baseEnd_7427617] using wordTrace_append hprefix tailTrace_7427617
  have hstable : (prefixWord ++ tailWord_7427617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7427617).length < 2 ^ (prefixWord ++ tailWord_7427617).sum := by decide
  have hdescent : baseEnd_7427617 < baseStart_7427617 := by decide
  rcases family_descends (prefixWord ++ tailWord_7427617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7427717 : List Nat := [1, 3, 1, 1, 4, 1, 1, 2, 3, 6]
def baseStart_7427717 : Nat := 118140960795 + 7427717 * 2 ^ 59
def prefixEnd_7427717 : Nat := 4983230072969 + 3 ^ 40 * 7427717 * 2
def baseEnd_7427717 : Nat := 1271329662190606918926019

theorem tailTrace_7427717 : CollatzResearch.WordTrace tailWord_7427717 prefixEnd_7427717 1271329662190606918926019 := by
  unfold tailWord_7427717
  simp only [CollatzResearch.WordTrace]
  refine ⟨270911095231657336914041405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180607396821104891276027603 270911095231657336914041405)
  ·
    refine ⟨101591660711871501342765527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 270911095231657336914041405 101591660711871501342765527)
    ·
      refine ⟨152387491067807252014148291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101591660711871501342765527 152387491067807252014148291)
      ·
        refine ⟨228581236601710878021222437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152387491067807252014148291 228581236601710878021222437)
        ·
          refine ⟨42858981862820789628979207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 228581236601710878021222437 42858981862820789628979207)
          ·
            refine ⟨64288472794231184443468811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42858981862820789628979207 64288472794231184443468811)
            ·
              refine ⟨96432709191346776665203217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64288472794231184443468811 96432709191346776665203217)
              ·
                refine ⟨72324531893510082498902413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96432709191346776665203217 72324531893510082498902413)
                ·
                  refine ⟨27121699460066280937088405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 72324531893510082498902413 27121699460066280937088405)
                  ·
                    refine ⟨1271329662190606918926019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27121699460066280937088405 1271329662190606918926019)
                    ·
                      rfl

theorem cell23_7427717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 2, 3, 6].length) (baseStart_7427717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7427717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7427717 prefixEnd_7427717 := by exact prefixLift 7427717
  have htrace : WordTrace (prefixWord ++ tailWord_7427717) baseStart_7427717 baseEnd_7427717 := by
    simpa [prefixWord, tailWord_7427717, baseEnd_7427717] using wordTrace_append hprefix tailTrace_7427717
  have hstable : (prefixWord ++ tailWord_7427717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7427717).length < 2 ^ (prefixWord ++ tailWord_7427717).sum := by decide
  have hdescent : baseEnd_7427717 < baseStart_7427717 := by decide
  rcases family_descends (prefixWord ++ tailWord_7427717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7427727 : List Nat := [1, 1, 2, 1, 1, 1, 1, 3, 1, 8, 3]
def baseStart_7427727 : Nat := 118140960795 + 7427727 * 2 ^ 59
def prefixEnd_7427727 : Nat := 4983230072969 + 3 ^ 40 * 7427727 * 2
def baseEnd_7427727 : Nat := 3813994121378365717653011

theorem tailTrace_7427727 : CollatzResearch.WordTrace tailWord_7427727 prefixEnd_7427727 3813994121378365717653011 := by
  unfold tailWord_7427727
  simp only [CollatzResearch.WordTrace]
  refine ⟨270911459961621108621905435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180607639974414072414603623 270911459961621108621905435)
  ·
    refine ⟨406367189942431662932858153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270911459961621108621905435 406367189942431662932858153)
    ·
      refine ⟨304775392456823747199643615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 406367189942431662932858153 304775392456823747199643615)
      ·
        refine ⟨457163088685235620799465423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304775392456823747199643615 457163088685235620799465423)
        ·
          refine ⟨685744633027853431199198135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 457163088685235620799465423 685744633027853431199198135)
          ·
            refine ⟨1028616949541780146798797203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 685744633027853431199198135 1028616949541780146798797203)
            ·
              refine ⟨1542925424312670220198195805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1028616949541780146798797203 1542925424312670220198195805)
              ·
                refine ⟨578597034117251332574323427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1542925424312670220198195805 578597034117251332574323427)
                ·
                  refine ⟨867895551175876998861485141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 578597034117251332574323427 867895551175876998861485141)
                  ·
                    refine ⟨10170650990342308580408029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 867895551175876998861485141 10170650990342308580408029)
                    ·
                      refine ⟨3813994121378365717653011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10170650990342308580408029 3813994121378365717653011)
                      ·
                        rfl

theorem cell23_7427727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 8, 3].length) (baseStart_7427727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7427727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7427727 prefixEnd_7427727 := by exact prefixLift 7427727
  have htrace : WordTrace (prefixWord ++ tailWord_7427727) baseStart_7427727 baseEnd_7427727 := by
    simpa [prefixWord, tailWord_7427727, baseEnd_7427727] using wordTrace_append hprefix tailTrace_7427727
  have hstable : (prefixWord ++ tailWord_7427727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7427727).length < 2 ^ (prefixWord ++ tailWord_7427727).sum := by decide
  have hdescent : baseEnd_7427727 < baseStart_7427727 := by decide
  rcases family_descends (prefixWord ++ tailWord_7427727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7427787 : List Nat := [1, 1, 1, 1, 3, 2, 1, 2, 4, 2, 5]
def baseStart_7427787 : Nat := 118140960795 + 7427787 * 2 ^ 59
def prefixEnd_7427787 : Nat := 4983230072969 + 3 ^ 40 * 7427787 * 2
def baseEnd_7427787 : Nat := 3814024930217635482902735

theorem tailTrace_7427787 : CollatzResearch.WordTrace tailWord_7427787 prefixEnd_7427787 3814024930217635482902735 := by
  unfold tailWord_7427787
  simp only [CollatzResearch.WordTrace]
  refine ⟨270913648341403738869089615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180609098894269159246059743 270913648341403738869089615)
  ·
    refine ⟨406370472512105608303634423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270913648341403738869089615 406370472512105608303634423)
    ·
      refine ⟨609555708768158412455451635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 406370472512105608303634423 609555708768158412455451635)
      ·
        refine ⟨914333563152237618683177453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 609555708768158412455451635 914333563152237618683177453)
        ·
          refine ⟨342875086182089107006191545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 914333563152237618683177453 342875086182089107006191545)
          ·
            refine ⟨257156314636566830254643659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 342875086182089107006191545 257156314636566830254643659)
            ·
              refine ⟨385734471954850245381965489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 257156314636566830254643659 385734471954850245381965489)
              ·
                refine ⟨289300853966137684036474117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 385734471954850245381965489 289300853966137684036474117)
                ·
                  refine ⟨54243910118650815756838897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 289300853966137684036474117 54243910118650815756838897)
                  ·
                    refine ⟨40682932588988111817629173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 54243910118650815756838897 40682932588988111817629173)
                    ·
                      refine ⟨3814024930217635482902735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40682932588988111817629173 3814024930217635482902735)
                      ·
                        rfl

theorem cell23_7427787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 4, 2, 5].length) (baseStart_7427787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7427787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7427787 prefixEnd_7427787 := by exact prefixLift 7427787
  have htrace : WordTrace (prefixWord ++ tailWord_7427787) baseStart_7427787 baseEnd_7427787 := by
    simpa [prefixWord, tailWord_7427787, baseEnd_7427787] using wordTrace_append hprefix tailTrace_7427787
  have hstable : (prefixWord ++ tailWord_7427787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7427787).length < 2 ^ (prefixWord ++ tailWord_7427787).sum := by decide
  have hdescent : baseEnd_7427787 < baseStart_7427787 := by decide
  rcases family_descends (prefixWord ++ tailWord_7427787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7427788 : List Nat := [2, 2, 1, 5, 2, 2, 1, 1, 1, 2, 4]
def baseStart_7427788 : Nat := 118140960795 + 7427788 * 2 ^ 59
def prefixEnd_7427788 : Nat := 4983230072969 + 3 ^ 40 * 7427788 * 2
def baseEnd_7427788 : Nat := 3814025443698289978990231

theorem tailTrace_7427788 : CollatzResearch.WordTrace tailWord_7427788 prefixEnd_7427788 3814025443698289978990231 := by
  unfold tailWord_7427788
  simp only [CollatzResearch.WordTrace]
  refine ⟨135456842407200058019938009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180609123209600077359917345 135456842407200058019938009)
  ·
    refine ⟨101592631805400043514953507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135456842407200058019938009 101592631805400043514953507)
    ·
      refine ⟨152388947708100065272430261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101592631805400043514953507 152388947708100065272430261)
      ·
        refine ⟨14286463847634381119290337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 152388947708100065272430261 14286463847634381119290337)
        ·
          refine ⟨10714847885725785839467753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14286463847634381119290337 10714847885725785839467753)
          ·
            refine ⟨8036135914294339379600815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10714847885725785839467753 8036135914294339379600815)
            ·
              refine ⟨12054203871441509069401223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8036135914294339379600815 12054203871441509069401223)
              ·
                refine ⟨18081305807162263604101835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12054203871441509069401223 18081305807162263604101835)
                ·
                  refine ⟨27121958710743395406152753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18081305807162263604101835 27121958710743395406152753)
                  ·
                    refine ⟨20341469033057546554614565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27121958710743395406152753 20341469033057546554614565)
                    ·
                      refine ⟨3814025443698289978990231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20341469033057546554614565 3814025443698289978990231)
                      ·
                        rfl

theorem cell23_7427788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_7427788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7427788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7427788 prefixEnd_7427788 := by exact prefixLift 7427788
  have htrace : WordTrace (prefixWord ++ tailWord_7427788) baseStart_7427788 baseEnd_7427788 := by
    simpa [prefixWord, tailWord_7427788, baseEnd_7427788] using wordTrace_append hprefix tailTrace_7427788
  have hstable : (prefixWord ++ tailWord_7427788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7427788).length < 2 ^ (prefixWord ++ tailWord_7427788).sum := by decide
  have hdescent : baseEnd_7427788 < baseStart_7427788 := by decide
  rcases family_descends (prefixWord ++ tailWord_7427788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7427791 : List Nat := [1, 1, 2, 1, 1, 3, 1, 7, 2, 1, 3]
def baseStart_7427791 : Nat := 118140960795 + 7427791 * 2 ^ 59
def prefixEnd_7427791 : Nat := 4983230072969 + 3 ^ 40 * 7427791 * 2
def baseEnd_7427791 : Nat := 3814026984140253467252717

theorem tailTrace_7427791 : CollatzResearch.WordTrace tailWord_7427791 prefixEnd_7427791 3814026984140253467252717 := by
  unfold tailWord_7427791
  simp only [CollatzResearch.WordTrace]
  refine ⟨270913794233389247552235227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180609196155592831701490151 270913794233389247552235227)
  ·
    refine ⟨406370691350083871328352841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270913794233389247552235227 406370691350083871328352841)
    ·
      refine ⟨304778018512562903496264631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 406370691350083871328352841 304778018512562903496264631)
      ·
        refine ⟨457167027768844355244396947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304778018512562903496264631 457167027768844355244396947)
        ·
          refine ⟨685750541653266532866595421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 457167027768844355244396947 685750541653266532866595421)
          ·
            refine ⟨257156453119974949824973283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 685750541653266532866595421 257156453119974949824973283)
            ·
              refine ⟨385734679679962424737459925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 257156453119974949824973283 385734679679962424737459925)
              ·
                refine ⟨9040656554999119329784217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 385734679679962424737459925 9040656554999119329784217)
                ·
                  refine ⟨6780492416249339497338163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9040656554999119329784217 6780492416249339497338163)
                  ·
                    refine ⟨10170738624374009246007245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6780492416249339497338163 10170738624374009246007245)
                    ·
                      refine ⟨3814026984140253467252717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10170738624374009246007245 3814026984140253467252717)
                      ·
                        rfl

theorem cell23_7427791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 7, 2, 1, 3].length) (baseStart_7427791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7427791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7427791 prefixEnd_7427791 := by exact prefixLift 7427791
  have htrace : WordTrace (prefixWord ++ tailWord_7427791) baseStart_7427791 baseEnd_7427791 := by
    simpa [prefixWord, tailWord_7427791, baseEnd_7427791] using wordTrace_append hprefix tailTrace_7427791
  have hstable : (prefixWord ++ tailWord_7427791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7427791).length < 2 ^ (prefixWord ++ tailWord_7427791).sum := by decide
  have hdescent : baseEnd_7427791 < baseStart_7427791 := by decide
  rcases family_descends (prefixWord ++ tailWord_7427791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7427798 : List Nat := [5, 2, 1, 3, 1, 1, 1, 9]
def baseStart_7427798 : Nat := 118140960795 + 7427798 * 2 ^ 59
def prefixEnd_7427798 : Nat := 4983230072969 + 3 ^ 40 * 7427798 * 2
def baseEnd_7427798 : Nat := 141260391796475368143155

theorem tailTrace_7427798 : CollatzResearch.WordTrace tailWord_7427798 prefixEnd_7427798 141260391796475368143155 := by
  unfold tailWord_7427798
  simp only [CollatzResearch.WordTrace]
  refine ⟨16932128096522742984233753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 180609366362909258498493365 16932128096522742984233753)
  ·
    refine ⟨12699096072392057238175315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16932128096522742984233753 12699096072392057238175315)
    ·
      refine ⟨19048644108588085857262973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12699096072392057238175315 19048644108588085857262973)
      ·
        refine ⟨7143241540720532196473615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19048644108588085857262973 7143241540720532196473615)
        ·
          refine ⟨10714862311080798294710423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7143241540720532196473615 10714862311080798294710423)
          ·
            refine ⟨16072293466621197442065635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10714862311080798294710423 16072293466621197442065635)
            ·
              refine ⟨24108440199931796163098453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16072293466621197442065635 24108440199931796163098453)
              ·
                refine ⟨141260391796475368143155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24108440199931796163098453 141260391796475368143155)
                ·
                  rfl

theorem cell23_7427798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 9].length) (baseStart_7427798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7427798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7427798 prefixEnd_7427798 := by exact prefixLift 7427798
  have htrace : WordTrace (prefixWord ++ tailWord_7427798) baseStart_7427798 baseEnd_7427798 := by
    simpa [prefixWord, tailWord_7427798, baseEnd_7427798] using wordTrace_append hprefix tailTrace_7427798
  have hstable : (prefixWord ++ tailWord_7427798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7427798).length < 2 ^ (prefixWord ++ tailWord_7427798).sum := by decide
  have hdescent : baseEnd_7427798 < baseStart_7427798 := by decide
  rcases family_descends (prefixWord ++ tailWord_7427798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7427809 : List Nat := [1, 2, 3, 1, 6, 1, 1, 3, 1, 2, 2]
def baseStart_7427809 : Nat := 118140960795 + 7427809 * 2 ^ 59
def prefixEnd_7427809 : Nat := 4983230072969 + 3 ^ 40 * 7427809 * 2
def baseEnd_7427809 : Nat := 3814036226792034396827635

theorem tailTrace_7427809 : CollatzResearch.WordTrace tailWord_7427809 prefixEnd_7427809 3814036226792034396827635 := by
  unfold tailWord_7427809
  simp only [CollatzResearch.WordTrace]
  refine ⟨270914450747324036626390481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180609633831549357750926987 270914450747324036626390481)
  ·
    refine ⟨203185838060493027469792861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270914450747324036626390481 203185838060493027469792861)
    ·
      refine ⟨76194689272684885301172323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 203185838060493027469792861 76194689272684885301172323)
      ·
        refine ⟨114292033909027327951758485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76194689272684885301172323 114292033909027327951758485)
        ·
          refine ⟨5357439089485655997738679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 114292033909027327951758485 5357439089485655997738679)
          ·
            refine ⟨8036158634228483996608019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5357439089485655997738679 8036158634228483996608019)
            ·
              refine ⟨12054237951342725994912029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8036158634228483996608019 12054237951342725994912029)
              ·
                refine ⟨4520339231753522248092011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12054237951342725994912029 4520339231753522248092011)
                ·
                  refine ⟨6780508847630283372138017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4520339231753522248092011 6780508847630283372138017)
                  ·
                    refine ⟨5085381635722712529103513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6780508847630283372138017 5085381635722712529103513)
                    ·
                      refine ⟨3814036226792034396827635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5085381635722712529103513 3814036226792034396827635)
                      ·
                        rfl

theorem cell23_7427809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 1, 3, 1, 2, 2].length) (baseStart_7427809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7427809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7427809 prefixEnd_7427809 := by exact prefixLift 7427809
  have htrace : WordTrace (prefixWord ++ tailWord_7427809) baseStart_7427809 baseEnd_7427809 := by
    simpa [prefixWord, tailWord_7427809, baseEnd_7427809] using wordTrace_append hprefix tailTrace_7427809
  have hstable : (prefixWord ++ tailWord_7427809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7427809).length < 2 ^ (prefixWord ++ tailWord_7427809).sum := by decide
  have hdescent : baseEnd_7427809 < baseStart_7427809 := by decide
  rcases family_descends (prefixWord ++ tailWord_7427809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7427818 : List Nat := [3, 1, 3, 1, 1, 1, 4, 3, 1, 3, 2]
def baseStart_7427818 : Nat := 118140960795 + 7427818 * 2 ^ 59
def prefixEnd_7427818 : Nat := 4983230072969 + 3 ^ 40 * 7427818 * 2
def baseEnd_7427818 : Nat := 3814040848117924861615093

theorem tailTrace_7427818 : CollatzResearch.WordTrace tailWord_7427818 prefixEnd_7427818 3814040848117924861615093 := by
  unfold tailWord_7427818
  simp only [CollatzResearch.WordTrace]
  refine ⟨67728694751072857790867027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180609852669527620775645405 67728694751072857790867027)
  ·
    refine ⟨101593042126609286686300541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67728694751072857790867027 101593042126609286686300541)
    ·
      refine ⟨38097390797478482507362703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 101593042126609286686300541 38097390797478482507362703)
      ·
        refine ⟨57146086196217723761044055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38097390797478482507362703 57146086196217723761044055)
        ·
          refine ⟨85719129294326585641566083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57146086196217723761044055 85719129294326585641566083)
          ·
            refine ⟨128578693941489878462349125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85719129294326585641566083 128578693941489878462349125)
            ·
              refine ⟨24108505114029352211690461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 128578693941489878462349125 24108505114029352211690461)
              ·
                refine ⟨9040689417761007079383923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24108505114029352211690461 9040689417761007079383923)
                ·
                  refine ⟨13561034126641510619075885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9040689417761007079383923 13561034126641510619075885)
                  ·
                    refine ⟨5085387797490566482153457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13561034126641510619075885 5085387797490566482153457)
                    ·
                      refine ⟨3814040848117924861615093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5085387797490566482153457 3814040848117924861615093)
                      ·
                        rfl

theorem cell23_7427818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 3, 1, 3, 2].length) (baseStart_7427818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7427818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7427818 prefixEnd_7427818 := by exact prefixLift 7427818
  have htrace : WordTrace (prefixWord ++ tailWord_7427818) baseStart_7427818 baseEnd_7427818 := by
    simpa [prefixWord, tailWord_7427818, baseEnd_7427818] using wordTrace_append hprefix tailTrace_7427818
  have hstable : (prefixWord ++ tailWord_7427818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7427818).length < 2 ^ (prefixWord ++ tailWord_7427818).sum := by decide
  have hdescent : baseEnd_7427818 < baseStart_7427818 := by decide
  rcases family_descends (prefixWord ++ tailWord_7427818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7427834 : List Nat := [3, 1, 1, 1, 1, 3, 1, 3, 2, 4, 3]
def baseStart_7427834 : Nat := 118140960795 + 7427834 * 2 ^ 59
def prefixEnd_7427834 : Nat := 4983230072969 + 3 ^ 40 * 7427834 * 2
def baseEnd_7427834 : Nat := 3814049063808396799015019

theorem tailTrace_7427834 : CollatzResearch.WordTrace tailWord_7427834 prefixEnd_7427834 3814049063808396799015019 := by
  unfold tailWord_7427834
  simp only [CollatzResearch.WordTrace]
  refine ⟨67728840643058366474012639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 180610241714822310597367037 67728840643058366474012639)
  ·
    refine ⟨101593260964587549711018959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 67728840643058366474012639 101593260964587549711018959)
    ·
      refine ⟨152389891446881324566528439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101593260964587549711018959 152389891446881324566528439)
      ·
        refine ⟨228584837170321986849792659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152389891446881324566528439 228584837170321986849792659)
        ·
          refine ⟨342877255755482980274688989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228584837170321986849792659 342877255755482980274688989)
          ·
            refine ⟨128578970908306117603008371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 342877255755482980274688989 128578970908306117603008371)
            ·
              refine ⟨192868456362459176404512557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128578970908306117603008371 192868456362459176404512557)
              ·
                refine ⟨72325671135922191151692209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 192868456362459176404512557 72325671135922191151692209)
                ·
                  refine ⟨54244253351941643363769157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 72325671135922191151692209 54244253351941643363769157)
                  ·
                    refine ⟨10170797503489058130706717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 54244253351941643363769157 10170797503489058130706717)
                    ·
                      refine ⟨3814049063808396799015019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10170797503489058130706717 3814049063808396799015019)
                      ·
                        rfl

theorem cell23_7427834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 3, 2, 4, 3].length) (baseStart_7427834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7427834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7427834 prefixEnd_7427834 := by exact prefixLift 7427834
  have htrace : WordTrace (prefixWord ++ tailWord_7427834) baseStart_7427834 baseEnd_7427834 := by
    simpa [prefixWord, tailWord_7427834, baseEnd_7427834] using wordTrace_append hprefix tailTrace_7427834
  have hstable : (prefixWord ++ tailWord_7427834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7427834).length < 2 ^ (prefixWord ++ tailWord_7427834).sum := by decide
  have hdescent : baseEnd_7427834 < baseStart_7427834 := by decide
  rcases family_descends (prefixWord ++ tailWord_7427834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7427854 : List Nat := [4, 1, 1, 2, 1, 1, 2, 4, 7]
def baseStart_7427854 : Nat := 118140960795 + 7427854 * 2 ^ 59
def prefixEnd_7427854 : Nat := 4983230072969 + 3 ^ 40 * 7427854 * 2
def baseEnd_7427854 : Nat := 423784370380165191196103

theorem tailTrace_7427854 : CollatzResearch.WordTrace tailWord_7427854 prefixEnd_7427854 423784370380165191196103 := by
  unfold tailWord_7427854
  simp only [CollatzResearch.WordTrace]
  refine ⟨33864511504020126163972327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180610728021440672874519077 33864511504020126163972327)
  ·
    refine ⟨50796767256030189245958491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33864511504020126163972327 50796767256030189245958491)
    ·
      refine ⟨76195150884045283868937737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50796767256030189245958491 76195150884045283868937737)
      ·
        refine ⟨57146363163033962901703303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76195150884045283868937737 57146363163033962901703303)
        ·
          refine ⟨85719544744550944352554955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57146363163033962901703303 85719544744550944352554955)
          ·
            refine ⟨128579317116826416528832433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85719544744550944352554955 128579317116826416528832433)
            ·
              refine ⟨96434487837619812396624325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 128579317116826416528832433 96434487837619812396624325)
              ·
                refine ⟨18081466469553714824367061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 96434487837619812396624325 18081466469553714824367061)
                ·
                  refine ⟨423784370380165191196103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18081466469553714824367061 423784370380165191196103)
                  ·
                    rfl

theorem cell23_7427854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 4, 7].length) (baseStart_7427854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7427854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7427854 prefixEnd_7427854 := by exact prefixLift 7427854
  have htrace : WordTrace (prefixWord ++ tailWord_7427854) baseStart_7427854 baseEnd_7427854 := by
    simpa [prefixWord, tailWord_7427854, baseEnd_7427854] using wordTrace_append hprefix tailTrace_7427854
  have hstable : (prefixWord ++ tailWord_7427854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7427854).length < 2 ^ (prefixWord ++ tailWord_7427854).sum := by decide
  have hdescent : baseEnd_7427854 < baseStart_7427854 := by decide
  rcases family_descends (prefixWord ++ tailWord_7427854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7427871 : List Nat := [1, 1, 2, 4, 2, 1, 2, 5, 5]
def baseStart_7427871 : Nat := 118140960795 + 7427871 * 2 ^ 59
def prefixEnd_7427871 : Nat := 4983230072969 + 3 ^ 40 * 7427871 * 2
def baseEnd_7427871 : Nat := 423785340288068128250261

theorem tailTrace_7427871 : CollatzResearch.WordTrace tailWord_7427871 prefixEnd_7427871 423785340288068128250261 := by
  unfold tailWord_7427871
  simp only [CollatzResearch.WordTrace]
  refine ⟨270916712073099421215147467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180611141382066280810098311 270916712073099421215147467)
  ·
    refine ⟨406375068109649131822721201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 270916712073099421215147467 406375068109649131822721201)
    ·
      refine ⟨304781301082236848867040901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 406375068109649131822721201 304781301082236848867040901)
      ·
        refine ⟨57146493952919409162570169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 304781301082236848867040901 57146493952919409162570169)
        ·
          refine ⟨42859870464689556871927627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57146493952919409162570169 42859870464689556871927627)
          ·
            refine ⟨64289805697034335307891441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42859870464689556871927627 64289805697034335307891441)
            ·
              refine ⟨48217354272775751480918581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64289805697034335307891441 48217354272775751480918581)
              ·
                refine ⟨4520376963072726701336117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48217354272775751480918581 4520376963072726701336117)
                ·
                  refine ⟨423785340288068128250261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4520376963072726701336117 423785340288068128250261)
                  ·
                    rfl

theorem cell23_7427871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 5, 5].length) (baseStart_7427871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7427871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7427871 prefixEnd_7427871 := by exact prefixLift 7427871
  have htrace : WordTrace (prefixWord ++ tailWord_7427871) baseStart_7427871 baseEnd_7427871 := by
    simpa [prefixWord, tailWord_7427871, baseEnd_7427871] using wordTrace_append hprefix tailTrace_7427871
  have hstable : (prefixWord ++ tailWord_7427871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7427871).length < 2 ^ (prefixWord ++ tailWord_7427871).sum := by decide
  have hdescent : baseEnd_7427871 < baseStart_7427871 := by decide
  rcases family_descends (prefixWord ++ tailWord_7427871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7427921 : List Nat := [1, 2, 2, 1, 5, 2, 1, 1, 1, 3, 4]
def baseStart_7427921 : Nat := 118140960795 + 7427921 * 2 ^ 59
def prefixEnd_7427921 : Nat := 4983230072969 + 3 ^ 40 * 7427921 * 2
def baseEnd_7427921 : Nat := 3814093736625337958627119

theorem tailTrace_7427921 : CollatzResearch.WordTrace tailWord_7427921 prefixEnd_7427921 3814093736625337958627119 := by
  unfold tailWord_7427921
  simp only [CollatzResearch.WordTrace]
  refine ⟨270918535722918279754467617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180612357148612186502978411 270918535722918279754467617)
  ·
    refine ⟨203188901792188709815850713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270918535722918279754467617 203188901792188709815850713)
    ·
      refine ⟨152391676344141532361888035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 203188901792188709815850713 152391676344141532361888035)
      ·
        refine ⟨228587514516212298542832053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152391676344141532361888035 228587514516212298542832053)
        ·
          refine ⟨21430079485894902988390505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 228587514516212298542832053 21430079485894902988390505)
          ·
            refine ⟨16072559614421177241292879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21430079485894902988390505 16072559614421177241292879)
            ·
              refine ⟨24108839421631765861939319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16072559614421177241292879 24108839421631765861939319)
              ·
                refine ⟨36163259132447648792908979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24108839421631765861939319 36163259132447648792908979)
                ·
                  refine ⟨54244888698671473189363469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36163259132447648792908979 54244888698671473189363469)
                  ·
                    refine ⟨20341833262001802446011301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 54244888698671473189363469 20341833262001802446011301)
                    ·
                      refine ⟨3814093736625337958627119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20341833262001802446011301 3814093736625337958627119)
                      ·
                        rfl

theorem cell23_7427921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 1, 1, 3, 4].length) (baseStart_7427921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7427921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7427921 prefixEnd_7427921 := by exact prefixLift 7427921
  have htrace : WordTrace (prefixWord ++ tailWord_7427921) baseStart_7427921 baseEnd_7427921 := by
    simpa [prefixWord, tailWord_7427921, baseEnd_7427921] using wordTrace_append hprefix tailTrace_7427921
  have hstable : (prefixWord ++ tailWord_7427921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7427921).length < 2 ^ (prefixWord ++ tailWord_7427921).sum := by decide
  have hdescent : baseEnd_7427921 < baseStart_7427921 := by decide
  rcases family_descends (prefixWord ++ tailWord_7427921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7427941 : List Nat := [1, 3, 1, 3, 1, 1, 1, 3, 4, 2, 3]
def baseStart_7427941 : Nat := 118140960795 + 7427941 * 2 ^ 59
def prefixEnd_7427941 : Nat := 4983230072969 + 3 ^ 40 * 7427941 * 2
def baseEnd_7427941 : Nat := 3814104006238427880377027

theorem tailTrace_7427941 : CollatzResearch.WordTrace tailWord_7427941 prefixEnd_7427941 3814104006238427880377027 := by
  unfold tailWord_7427941
  simp only [CollatzResearch.WordTrace]
  refine ⟨270919265182845823170195677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180612843455230548780130451 270919265182845823170195677)
  ·
    refine ⟨101594724443567183688823379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 270919265182845823170195677 101594724443567183688823379)
    ·
      refine ⟨152392086665350775533235069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101594724443567183688823379 152392086665350775533235069)
      ·
        refine ⟨57147032499506540824963151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 152392086665350775533235069 57147032499506540824963151)
        ·
          refine ⟨85720548749259811237444727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57147032499506540824963151 85720548749259811237444727)
          ·
            refine ⟨128580823123889716856167091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85720548749259811237444727 128580823123889716856167091)
            ·
              refine ⟨192871234685834575284250637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 128580823123889716856167091 192871234685834575284250637)
              ·
                refine ⟨72326713007187965731593989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 192871234685834575284250637 72326713007187965731593989)
                ·
                  refine ⟨13561258688847743574673873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 72326713007187965731593989 13561258688847743574673873)
                  ·
                    refine ⟨10170944016635807681005405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13561258688847743574673873 10170944016635807681005405)
                    ·
                      refine ⟨3814104006238427880377027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10170944016635807681005405 3814104006238427880377027)
                      ·
                        rfl

theorem cell23_7427941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 3, 4, 2, 3].length) (baseStart_7427941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7427941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7427941 prefixEnd_7427941 := by exact prefixLift 7427941
  have htrace : WordTrace (prefixWord ++ tailWord_7427941) baseStart_7427941 baseEnd_7427941 := by
    simpa [prefixWord, tailWord_7427941, baseEnd_7427941] using wordTrace_append hprefix tailTrace_7427941
  have hstable : (prefixWord ++ tailWord_7427941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7427941).length < 2 ^ (prefixWord ++ tailWord_7427941).sum := by decide
  have hdescent : baseEnd_7427941 < baseStart_7427941 := by decide
  rcases family_descends (prefixWord ++ tailWord_7427941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7427948 : List Nat := [2, 2, 1, 1, 4, 3, 2, 1, 3, 4]
def baseStart_7427948 : Nat := 118140960795 + 7427948 * 2 ^ 59
def prefixEnd_7427948 : Nat := 4983230072969 + 3 ^ 40 * 7427948 * 2
def baseEnd_7427948 : Nat := 1271369200201003117663165

theorem tailTrace_7427948 : CollatzResearch.WordTrace tailWord_7427948 prefixEnd_7427948 1271369200201003117663165 := by
  unfold tailWord_7427948
  simp only [CollatzResearch.WordTrace]
  refine ⟨135459760246910231682850249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180613013662546975577133665 135459760246910231682850249)
  ·
    refine ⟨101594820185182673762137687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 135459760246910231682850249 101594820185182673762137687)
    ·
      refine ⟨152392230277774010643206531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101594820185182673762137687 152392230277774010643206531)
      ·
        refine ⟨228588345416661015964809797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 152392230277774010643206531 228588345416661015964809797)
        ·
          refine ⟨42860314765623940493401837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 228588345416661015964809797 42860314765623940493401837)
          ·
            refine ⟨16072618037108977685025689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42860314765623940493401837 16072618037108977685025689)
            ·
              refine ⟨12054463527831733263769267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16072618037108977685025689 12054463527831733263769267)
              ·
                refine ⟨18081695291747599895653901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12054463527831733263769267 18081695291747599895653901)
                ·
                  refine ⟨6780635734405349960870213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18081695291747599895653901 6780635734405349960870213)
                  ·
                    refine ⟨1271369200201003117663165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6780635734405349960870213 1271369200201003117663165)
                    ·
                      rfl

theorem cell23_7427948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 4].length) (baseStart_7427948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7427948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7427948 prefixEnd_7427948 := by exact prefixLift 7427948
  have htrace : WordTrace (prefixWord ++ tailWord_7427948) baseStart_7427948 baseEnd_7427948 := by
    simpa [prefixWord, tailWord_7427948, baseEnd_7427948] using wordTrace_append hprefix tailTrace_7427948
  have hstable : (prefixWord ++ tailWord_7427948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7427948).length < 2 ^ (prefixWord ++ tailWord_7427948).sum := by decide
  have hdescent : baseEnd_7427948 < baseStart_7427948 := by decide
  rcases family_descends (prefixWord ++ tailWord_7427948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7427984 : List Nat := [2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 5]
def baseStart_7427984 : Nat := 118140960795 + 7427984 * 2 ^ 59
def prefixEnd_7427984 : Nat := 4983230072969 + 3 ^ 40 * 7427984 * 2
def baseEnd_7427984 : Nat := 3814126085906571212139329

theorem tailTrace_7427984 : CollatzResearch.WordTrace tailWord_7427984 prefixEnd_7427984 3814126085906571212139329 := by
  unfold tailWord_7427984
  simp only [CollatzResearch.WordTrace]
  refine ⟨135460416760845020757005503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180613889014460027676007337 135460416760845020757005503)
  ·
    refine ⟨203190625141267531135508255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135460416760845020757005503 203190625141267531135508255)
    ·
      refine ⟨304785937711901296703262383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203190625141267531135508255 304785937711901296703262383)
      ·
        refine ⟨457178906567851945054893575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304785937711901296703262383 457178906567851945054893575)
        ·
          refine ⟨685768359851777917582340363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 457178906567851945054893575 685768359851777917582340363)
          ·
            refine ⟨1028652539777666876373510545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 685768359851777917582340363 1028652539777666876373510545)
            ·
              refine ⟨771489404833250157280132909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1028652539777666876373510545 771489404833250157280132909)
              ·
                refine ⟨289308526812468808980049841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 771489404833250157280132909 289308526812468808980049841)
                ·
                  refine ⟨216981395109351606735037381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 289308526812468808980049841 216981395109351606735037381)
                  ·
                    refine ⟨40684011583003426262819509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 216981395109351606735037381 40684011583003426262819509)
                    ·
                      refine ⟨3814126085906571212139329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40684011583003426262819509 3814126085906571212139329)
                      ·
                        rfl

theorem cell23_7427984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 5].length) (baseStart_7427984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7427984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7427984 prefixEnd_7427984 := by exact prefixLift 7427984
  have htrace : WordTrace (prefixWord ++ tailWord_7427984) baseStart_7427984 baseEnd_7427984 := by
    simpa [prefixWord, tailWord_7427984, baseEnd_7427984] using wordTrace_append hprefix tailTrace_7427984
  have hstable : (prefixWord ++ tailWord_7427984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7427984).length < 2 ^ (prefixWord ++ tailWord_7427984).sum := by decide
  have hdescent : baseEnd_7427984 < baseStart_7427984 := by decide
  rcases family_descends (prefixWord ++ tailWord_7427984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7428005 : List Nat := [1, 3, 1, 2, 1, 1, 1, 8, 1, 1, 3]
def baseStart_7428005 : Nat := 118140960795 + 7428005 * 2 ^ 59
def prefixEnd_7428005 : Nat := 4983230072969 + 3 ^ 40 * 7428005 * 2
def baseEnd_7428005 : Nat := 3814136869000315629976733

theorem tailTrace_7428005 : CollatzResearch.WordTrace tailWord_7428005 prefixEnd_7428005 3814136869000315629976733 := by
  unfold tailWord_7428005
  simp only [CollatzResearch.WordTrace]
  refine ⟨270921599454613962100525469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180614399636409308067016979 270921599454613962100525469)
  ·
    refine ⟨101595599795480235787697051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 270921599454613962100525469 101595599795480235787697051)
    ·
      refine ⟨152393399693220353681545577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 101595599795480235787697051 152393399693220353681545577)
      ·
        refine ⟨114295049769915265261159183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 152393399693220353681545577 114295049769915265261159183)
        ·
          refine ⟨171442574654872897891738775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114295049769915265261159183 171442574654872897891738775)
          ·
            refine ⟨257163861982309346837608163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171442574654872897891738775 257163861982309346837608163)
            ·
              refine ⟨385745792973464020256412245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 257163861982309346837608163 385745792973464020256412245)
              ·
                refine ⟨4520458511407781487379831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 385745792973464020256412245 4520458511407781487379831)
                ·
                  refine ⟨6780687767111672231069747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4520458511407781487379831 6780687767111672231069747)
                  ·
                    refine ⟨10171031650667508346604621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6780687767111672231069747 10171031650667508346604621)
                    ·
                      refine ⟨3814136869000315629976733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10171031650667508346604621 3814136869000315629976733)
                      ·
                        rfl

theorem cell23_7428005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 8, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 8, 1, 1, 3].length) (baseStart_7428005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7428005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7428005 prefixEnd_7428005 := by exact prefixLift 7428005
  have htrace : WordTrace (prefixWord ++ tailWord_7428005) baseStart_7428005 baseEnd_7428005 := by
    simpa [prefixWord, tailWord_7428005, baseEnd_7428005] using wordTrace_append hprefix tailTrace_7428005
  have hstable : (prefixWord ++ tailWord_7428005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7428005).length < 2 ^ (prefixWord ++ tailWord_7428005).sum := by decide
  have hdescent : baseEnd_7428005 < baseStart_7428005 := by decide
  rcases family_descends (prefixWord ++ tailWord_7428005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7428041 : List Nat := [1, 2, 1, 1, 2, 1, 2, 6, 1, 2, 4]
def baseStart_7428041 : Nat := 118140960795 + 7428041 * 2 ^ 59
def prefixEnd_7428041 : Nat := 4983230072969 + 3 ^ 40 * 7428041 * 2
def baseEnd_7428041 : Nat := 3814155354303877489126567

theorem tailTrace_7428041 : CollatzResearch.WordTrace tailWord_7428041 prefixEnd_7428041 3814155354303877489126567 := by
  unfold tailWord_7428041
  simp only [CollatzResearch.WordTrace]
  refine ⟨270922912482483540248835977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180615274988322360165890651 270922912482483540248835977)
  ·
    refine ⟨203192184361862655186626983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270922912482483540248835977 203192184361862655186626983)
    ·
      refine ⟨304788276542793982779940475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203192184361862655186626983 304788276542793982779940475)
      ·
        refine ⟨457182414814190974169910713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304788276542793982779940475 457182414814190974169910713)
        ·
          refine ⟨342886811110643230627433035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 457182414814190974169910713 342886811110643230627433035)
          ·
            refine ⟨514330216665964845941149553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 342886811110643230627433035 514330216665964845941149553)
            ·
              refine ⟨385747662499473634455862165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 514330216665964845941149553 385747662499473634455862165)
              ·
                refine ⟨18081921679662826615118539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 385747662499473634455862165 18081921679662826615118539)
                ·
                  refine ⟨27122882519494239922677809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18081921679662826615118539 27122882519494239922677809)
                  ·
                    refine ⟨20342161889620679942008357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 27122882519494239922677809 20342161889620679942008357)
                    ·
                      refine ⟨3814155354303877489126567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20342161889620679942008357 3814155354303877489126567)
                      ·
                        rfl

theorem cell23_7428041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 6, 1, 2, 4].length) (baseStart_7428041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7428041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7428041 prefixEnd_7428041 := by exact prefixLift 7428041
  have htrace : WordTrace (prefixWord ++ tailWord_7428041) baseStart_7428041 baseEnd_7428041 := by
    simpa [prefixWord, tailWord_7428041, baseEnd_7428041] using wordTrace_append hprefix tailTrace_7428041
  have hstable : (prefixWord ++ tailWord_7428041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7428041).length < 2 ^ (prefixWord ++ tailWord_7428041).sum := by decide
  have hdescent : baseEnd_7428041 < baseStart_7428041 := by decide
  rcases family_descends (prefixWord ++ tailWord_7428041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7428048 : List Nat := [2, 1, 1, 1, 1, 2, 4, 5, 1, 2, 3]
def baseStart_7428048 : Nat := 118140960795 + 7428048 * 2 ^ 59
def prefixEnd_7428048 : Nat := 4983230072969 + 3 ^ 40 * 7428048 * 2
def baseEnd_7428048 : Nat := 3814158948668458961739035

theorem tailTrace_7428048 : CollatzResearch.WordTrace tailWord_7428048 prefixEnd_7428048 3814158948668458961739035 := by
  unfold tailWord_7428048
  simp only [CollatzResearch.WordTrace]
  refine ⟨135461583896729090222170399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180615445195638786962893865 135461583896729090222170399)
  ·
    refine ⟨203192375845093635333255599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135461583896729090222170399 203192375845093635333255599)
    ·
      refine ⟨304788563767640452999883399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203192375845093635333255599 304788563767640452999883399)
      ·
        refine ⟨457182845651460679499825099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 304788563767640452999883399 457182845651460679499825099)
        ·
          refine ⟨685774268477191019249737649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 457182845651460679499825099 685774268477191019249737649)
          ·
            refine ⟨514330701357893264437303237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 685774268477191019249737649 514330701357893264437303237)
            ·
              refine ⟨96437006504604987081994357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 514330701357893264437303237 96437006504604987081994357)
              ·
                refine ⟨9040969359806717538936971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 96437006504604987081994357 9040969359806717538936971)
                ·
                  refine ⟨13561454039710076308405457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9040969359806717538936971 13561454039710076308405457)
                  ·
                    refine ⟨10171090529782557231304093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13561454039710076308405457 10171090529782557231304093)
                    ·
                      refine ⟨3814158948668458961739035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10171090529782557231304093 3814158948668458961739035)
                      ·
                        rfl

theorem cell23_7428048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 5, 1, 2, 3].length) (baseStart_7428048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7428048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7428048 prefixEnd_7428048 := by exact prefixLift 7428048
  have htrace : WordTrace (prefixWord ++ tailWord_7428048) baseStart_7428048 baseEnd_7428048 := by
    simpa [prefixWord, tailWord_7428048, baseEnd_7428048] using wordTrace_append hprefix tailTrace_7428048
  have hstable : (prefixWord ++ tailWord_7428048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7428048).length < 2 ^ (prefixWord ++ tailWord_7428048).sum := by decide
  have hdescent : baseEnd_7428048 < baseStart_7428048 := by decide
  rcases family_descends (prefixWord ++ tailWord_7428048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7428121 : List Nat := [1, 2, 1, 2, 1, 1, 3, 2, 4, 1, 5]
def baseStart_7428121 : Nat := 118140960795 + 7428121 * 2 ^ 59
def prefixEnd_7428121 : Nat := 4983230072969 + 3 ^ 40 * 7428121 * 2
def baseEnd_7428121 : Nat := 3814196432756237176126199

theorem tailTrace_7428121 : CollatzResearch.WordTrace tailWord_7428121 prefixEnd_7428121 3814196432756237176126199 := by
  unfold tailWord_7428121
  simp only [CollatzResearch.WordTrace]
  refine ⟨270925830322193713911748217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180617220214795809274498811 270925830322193713911748217)
  ·
    refine ⟨203194372741645285433811163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270925830322193713911748217 203194372741645285433811163)
    ·
      refine ⟨304791559112467928150716745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 203194372741645285433811163 304791559112467928150716745)
      ·
        refine ⟨228593669334350946113037559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 304791559112467928150716745 228593669334350946113037559)
        ·
          refine ⟨342890504001526419169556339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 228593669334350946113037559 342890504001526419169556339)
          ·
            refine ⟨514335756002289628754334509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 342890504001526419169556339 514335756002289628754334509)
            ·
              refine ⟨192875908500858610782875441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 514335756002289628754334509 192875908500858610782875441)
              ·
                refine ⟨144656931375643958087156581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 192875908500858610782875441 144656931375643958087156581)
                ·
                  refine ⟨27123174632933242141341859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 144656931375643958087156581 27123174632933242141341859)
                  ·
                    refine ⟨40684761949399863212012789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 27123174632933242141341859 40684761949399863212012789)
                    ·
                      refine ⟨3814196432756237176126199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40684761949399863212012789 3814196432756237176126199)
                      ·
                        rfl

theorem cell23_7428121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 4, 1, 5].length) (baseStart_7428121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7428121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7428121 prefixEnd_7428121 := by exact prefixLift 7428121
  have htrace : WordTrace (prefixWord ++ tailWord_7428121) baseStart_7428121 baseEnd_7428121 := by
    simpa [prefixWord, tailWord_7428121, baseEnd_7428121] using wordTrace_append hprefix tailTrace_7428121
  have hstable : (prefixWord ++ tailWord_7428121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7428121).length < 2 ^ (prefixWord ++ tailWord_7428121).sum := by decide
  have hdescent : baseEnd_7428121 < baseStart_7428121 := by decide
  rcases family_descends (prefixWord ++ tailWord_7428121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7428129 : List Nat := [1, 2, 3, 2, 4, 1, 3, 1, 2, 1, 3]
def baseStart_7428129 : Nat := 118140960795 + 7428129 * 2 ^ 59
def prefixEnd_7428129 : Nat := 4983230072969 + 3 ^ 40 * 7428129 * 2
def baseEnd_7428129 : Nat := 3814200540601473144826163

theorem tailTrace_7428129 : CollatzResearch.WordTrace tailWord_7428129 prefixEnd_7428129 3814200540601473144826163 := by
  unfold tailWord_7428129
  simp only [CollatzResearch.WordTrace]
  refine ⟨270926122106164731278039441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 180617414737443154185359627 270926122106164731278039441)
  ·
    refine ⟨203194591579623548458529581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 270926122106164731278039441 203194591579623548458529581)
    ·
      refine ⟨76197971842358830671948593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 203194591579623548458529581 76197971842358830671948593)
      ·
        refine ⟨57148478881769123003961445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76197971842358830671948593 57148478881769123003961445)
        ·
          refine ⟨10715339790331710563242771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57148478881769123003961445 10715339790331710563242771)
          ·
            refine ⟨16073009685497565844864157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10715339790331710563242771 16073009685497565844864157)
            ·
              refine ⟨6027378632061587191824059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16073009685497565844864157 6027378632061587191824059)
              ·
                refine ⟨9041067948092380787736089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6027378632061587191824059 9041067948092380787736089)
                ·
                  refine ⟨6780800961069285590802067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9041067948092380787736089 6780800961069285590802067)
                  ·
                    refine ⟨10171201441603928386203101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6780800961069285590802067 10171201441603928386203101)
                    ·
                      refine ⟨3814200540601473144826163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10171201441603928386203101 3814200540601473144826163)
                      ·
                        rfl

theorem cell23_7428129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 3, 1, 2, 1, 3].length) (baseStart_7428129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7428129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7428129 prefixEnd_7428129 := by exact prefixLift 7428129
  have htrace : WordTrace (prefixWord ++ tailWord_7428129) baseStart_7428129 baseEnd_7428129 := by
    simpa [prefixWord, tailWord_7428129, baseEnd_7428129] using wordTrace_append hprefix tailTrace_7428129
  have hstable : (prefixWord ++ tailWord_7428129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7428129).length < 2 ^ (prefixWord ++ tailWord_7428129).sum := by decide
  have hdescent : baseEnd_7428129 < baseStart_7428129 := by decide
  rcases family_descends (prefixWord ++ tailWord_7428129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7428168 : List Nat := [2, 1, 3, 1, 1, 1, 2, 4, 2, 3, 3]
def baseStart_7428168 : Nat := 118140960795 + 7428168 * 2 ^ 59
def prefixEnd_7428168 : Nat := 4983230072969 + 3 ^ 40 * 7428168 * 2
def baseEnd_7428168 : Nat := 3814220566346998492238483

theorem tailTrace_7428168 : CollatzResearch.WordTrace tailWord_7428168 prefixEnd_7428168 3814220566346998492238483 := by
  unfold tailWord_7428168
  simp only [CollatzResearch.WordTrace]
  refine ⟨135463772276511720469354579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 180618363035348960625806105 135463772276511720469354579)
  ·
    refine ⟨203195658414767580704031869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 135463772276511720469354579 203195658414767580704031869)
    ·
      refine ⟨76198371905537842764011951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 203195658414767580704031869 76198371905537842764011951)
      ·
        refine ⟨114297557858306764146017927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76198371905537842764011951 114297557858306764146017927)
        ·
          refine ⟨171446336787460146219026891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 114297557858306764146017927 171446336787460146219026891)
          ·
            refine ⟨257169505181190219328540337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 171446336787460146219026891 257169505181190219328540337)
            ·
              refine ⟨192877128885892664496405253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 257169505181190219328540337 192877128885892664496405253)
              ·
                refine ⟨36164461666104874593075985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 192877128885892664496405253 36164461666104874593075985)
                ·
                  refine ⟨27123346249578655944806989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36164461666104874593075985 27123346249578655944806989)
                  ·
                    refine ⟨10171254843591995979302621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 27123346249578655944806989 10171254843591995979302621)
                    ·
                      refine ⟨3814220566346998492238483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10171254843591995979302621 3814220566346998492238483)
                      ·
                        rfl

theorem cell23_7428168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 4, 2, 3, 3].length) (baseStart_7428168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7428168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7428168 prefixEnd_7428168 := by exact prefixLift 7428168
  have htrace : WordTrace (prefixWord ++ tailWord_7428168) baseStart_7428168 baseEnd_7428168 := by
    simpa [prefixWord, tailWord_7428168, baseEnd_7428168] using wordTrace_append hprefix tailTrace_7428168
  have hstable : (prefixWord ++ tailWord_7428168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7428168).length < 2 ^ (prefixWord ++ tailWord_7428168).sum := by decide
  have hdescent : baseEnd_7428168 < baseStart_7428168 := by decide
  rcases family_descends (prefixWord ++ tailWord_7428168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7428190 : List Nat := [4, 4, 1, 1, 3, 1, 1, 2, 1, 3, 2]
def baseStart_7428190 : Nat := 118140960795 + 7428190 * 2 ^ 59
def prefixEnd_7428190 : Nat := 4983230072969 + 3 ^ 40 * 7428190 * 2
def baseEnd_7428190 : Nat := 3814231862921397406163383

theorem tailTrace_7428190 : CollatzResearch.WordTrace tailWord_7428190 prefixEnd_7428190 3814231862921397406163383 := by
  unfold tailWord_7428190
  simp only [CollatzResearch.WordTrace]
  refine ⟨33866043369867967337001253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 180618897972629159130673349 33866043369867967337001253)
  ·
    refine ⟨6349883131850243875687735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33866043369867967337001253 6349883131850243875687735)
    ·
      refine ⟨9524824697775365813531603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6349883131850243875687735 9524824697775365813531603)
      ·
        refine ⟨14287237046663048720297405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9524824697775365813531603 14287237046663048720297405)
        ·
          refine ⟨5357713892498643270111527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14287237046663048720297405 5357713892498643270111527)
          ·
            refine ⟨8036570838747964905167291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5357713892498643270111527 8036570838747964905167291)
            ·
              refine ⟨12054856258121947357750937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8036570838747964905167291 12054856258121947357750937)
              ·
                refine ⟨9041142193591460518313203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12054856258121947357750937 9041142193591460518313203)
                ·
                  refine ⟨13561713290387190777469805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9041142193591460518313203 13561713290387190777469805)
                  ·
                    refine ⟨5085642483895196541551177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13561713290387190777469805 5085642483895196541551177)
                    ·
                      refine ⟨3814231862921397406163383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5085642483895196541551177 3814231862921397406163383)
                      ·
                        rfl

theorem cell23_7428190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 1, 2, 1, 3, 2].length) (baseStart_7428190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7428190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7428190 prefixEnd_7428190 := by exact prefixLift 7428190
  have htrace : WordTrace (prefixWord ++ tailWord_7428190) baseStart_7428190 baseEnd_7428190 := by
    simpa [prefixWord, tailWord_7428190, baseEnd_7428190] using wordTrace_append hprefix tailTrace_7428190
  have hstable : (prefixWord ++ tailWord_7428190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7428190).length < 2 ^ (prefixWord ++ tailWord_7428190).sum := by decide
  have hdescent : baseEnd_7428190 < baseStart_7428190 := by decide
  rcases family_descends (prefixWord ++ tailWord_7428190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
